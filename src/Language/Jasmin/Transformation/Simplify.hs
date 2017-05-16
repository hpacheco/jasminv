{-# LANGUAGE TypeFamilies, RankNTypes, DoAndIfThenElse, ScopedTypeVariables, FlexibleContexts, ViewPatterns, ConstraintKinds, FlexibleInstances, MultiParamTypeClasses, DeriveDataTypeable, DeriveGeneric #-}

module Language.Jasmin.Transformation.Simplify where

import Data.Hashable.Exts
import Data.Binary
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Set (Set(..))
import qualified Data.Set as Set
import Text.PrettyPrint.Exts as PP
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State as State
import Data.Generics hiding (Generic)
import GHC.Generics
import Data.Foldable as Foldable
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Except
import Data.List as List
import Data.Maybe
import Data.Foldable as Foldable
import System.FilePath
import Data.Bifunctor

import Language.Position
import Language.Location
import Language.Jasmin.Syntax
import Language.Vars
import Language.Jasmin.TypeChecker
import Language.Jasmin.Error

import Utils

simplifyPprogram :: SimplifyK m => Pprogram TyInfo -> SimplifyM m (Pprogram TyInfo)
simplifyPprogram (Pprogram p) = do
    let go (ks,is') i = do
            i <- lift2 $ substConsts ks i
            e <- simplifyPitem i
            case e of
                Left i' -> return (ks,is'++[i'])
                Right k -> return (Map.union ks k,is')
    (_,p') <- foldM go (Map.empty,[]) p
    return $ Pprogram p'

simplifyPitem :: SimplifyK m => Pitem TyInfo -> SimplifyM m (Either (Pitem TyInfo) SubstConsts)
simplifyPitem (PParam p) = liftM (bimap PParam id) $ simplifyPparam p
simplifyPitem (PFundef f) = liftM (Left . PFundef) $ simplifyPfundef f
simplifyPitem (PAxiomdef f) = liftM (Left . PAxiomdef) $ simplifyPAnnAxiomDef f
simplifyPitem (PLemmadef f) = liftM (Left . PLemmadef) $ simplifyPAnnLemmaDef f
simplifyPitem (PAnnfunctiondef f) = liftM (Left . PAnnfunctiondef) $ simplifyPAnnFunDef f

simplifyPAnnAxiomDef :: SimplifyK m => AnnAxiomDeclaration TyInfo -> SimplifyM m (AnnAxiomDeclaration TyInfo)
simplifyPAnnAxiomDef (AnnAxiomDeclaration isLeak args anns i) = do
    args' <- mapM simplifyAnnarg args
    anns' <- mapM simplifyProcAnn anns
    i' <- simplifyTyInfo i
    return $ AnnAxiomDeclaration isLeak args' anns' i'

simplifyPAnnLemmaDef :: SimplifyK m => AnnLemmaDeclaration TyInfo -> SimplifyM m (AnnLemmaDeclaration TyInfo)
simplifyPAnnLemmaDef (AnnLemmaDeclaration isLeak n args anns body i) = do
    n' <- simplifyPident n
    args' <- mapM simplifyAnnarg args
    anns' <- mapM simplifyProcAnn anns
    body' <- mapM simplifyPblock body
    i' <- simplifyTyInfo i
    return $ AnnLemmaDeclaration isLeak n' args' anns' body' i'

simplifyPAnnFunDef :: SimplifyK m => AnnFunDeclaration TyInfo -> SimplifyM m (AnnFunDeclaration TyInfo)
simplifyPAnnFunDef (AnnFunDeclaration isLeak ret n args anns body i) = do
    ret' <- simplifyPtype ret
    n' <- simplifyPident n
    args' <- mapM simplifyAnnarg args
    anns' <- mapM simplifyProcAnn anns
    body' <- simplifyPexpr body
    i' <- simplifyTyInfo i
    return $ AnnFunDeclaration isLeak ret' n' args' anns' body' i'

simplifyPparam :: SimplifyK m => Pparam TyInfo -> SimplifyM m (Either (Pparam TyInfo) SubstConsts)
simplifyPparam (Pparam ty n e) = do
    return $ Right $ Map.singleton (funit n) e

simplifyPfundef :: SimplifyK m => Pfundef TyInfo -> SimplifyM m (Pfundef TyInfo)
simplifyPfundef (Pfundef cc n args rty ann body info) = do
    n' <- simplifyPident n
    args' <- mapM simplifyParg args
    rty' <- mapM (mapM simplifyPstotype) rty
    ann' <- mapM simplifyProcAnn ann
    body' <- simplifyPfunbody body
    info' <- simplifyTyInfo info
    return $ Pfundef cc n' args' rty' ann' body' info'

simplifyParg :: SimplifyK m => Parg TyInfo -> SimplifyM m (Parg TyInfo)
simplifyParg (Parg ty n) = do
    ty' <- simplifyPstotype ty
    n' <- mapM simplifyPident n
    return $ Parg ty' n'

simplifyAnnarg :: SimplifyK m => Annarg TyInfo -> SimplifyM m (Annarg TyInfo)
simplifyAnnarg (Annarg ty n e) = do
    ty' <- simplifyPtype ty
    n' <- simplifyPident n
    e' <- mapM simplifyPexpr e
    return $ Annarg ty' n' e'

simplifyPbodyarg :: SimplifyK m => Pbodyarg TyInfo -> SimplifyM m (Pbodyarg TyInfo)
simplifyPbodyarg (Pbodyarg ty n) = do
    ty' <- simplifyPstotype ty
    n' <- simplifyPident n
    return $ Pbodyarg ty' n'

simplifyPident :: SimplifyK m => Pident TyInfo -> SimplifyM m (Pident TyInfo)
simplifyPident (Pident t n) = do
    t' <- simplifyTyInfo t
    return $ Pident t' n

simplifyPfunbody :: SimplifyK m => Pfunbody TyInfo -> SimplifyM m (Pfunbody TyInfo)
simplifyPfunbody (Pfunbody pbvars pbinstrs pbret) = do
    pbvars' <- mapM simplifyPbodyarg pbvars
    pbinstrs' <- concatMapM simplifyPinstr pbinstrs
    pbret' <- mapM (mapM simplifyPident) pbret
    return $ Pfunbody pbvars' pbinstrs' pbret'

simplifyPinstr :: SimplifyK m => Pinstr TyInfo -> SimplifyM m [Pinstr TyInfo]
simplifyPinstr (Pinstr t i) = do
    t' <- simplifyTyInfo t
    simplifyPinstr_r t' i

simplifyProcAnn :: SimplifyK m => ProcedureAnnotation TyInfo -> SimplifyM m (ProcedureAnnotation TyInfo)
simplifyProcAnn (ProcedureAnnotation l x) = do
    l' <- simplifyTyInfo l
    x' <- simplifyProcAnn_r x
    return $ ProcedureAnnotation l' x'

simplifyProcAnn_r :: SimplifyK m => ProcedureAnnotation_r TyInfo -> SimplifyM m (ProcedureAnnotation_r TyInfo)
simplifyProcAnn_r (RequiresAnn isFree isLeak e) = do
    e' <- simplifyPexpr e
    return (RequiresAnn isFree isLeak e')
simplifyProcAnn_r (EnsuresAnn isFree isLeak e) = do
    e' <- simplifyPexpr e
    return (EnsuresAnn isFree isLeak e')
simplifyProcAnn_r (PDecreasesAnn e) = do
    e' <- simplifyPexpr e
    return (PDecreasesAnn e')

simplifyStatementAnn :: SimplifyK m => StatementAnnotation TyInfo -> SimplifyM m [StatementAnnotation TyInfo]
simplifyStatementAnn (StatementAnnotation l x) = do
    l' <- simplifyTyInfo l
    x' <- simplifyStatementAnn_r x
    return $ map (StatementAnnotation l') x'

simplifyStatementAnn_r :: SimplifyK m => StatementAnnotation_r TyInfo -> SimplifyM m [StatementAnnotation_r TyInfo]
simplifyStatementAnn_r (AssumeAnn isLeak e) = do
    e' <- simplifyPexpr e
    return [AssumeAnn isLeak e']
simplifyStatementAnn_r (AssertAnn isLeak e) = do
    e' <- simplifyPexpr e
    return [AssertAnn isLeak e']
simplifyStatementAnn_r (EmbedAnn isLeak e) = do
    e' <- simplifyPinstr e
    return $ map (EmbedAnn isLeak) e'
simplifyStatementAnn_r (VarDefAnn ann) = do
    ann' <- simplifyAnnarg ann
    return [VarDefAnn ann']

simplifyLoopAnn :: SimplifyK m => LoopAnnotation TyInfo -> SimplifyM m (LoopAnnotation TyInfo)
simplifyLoopAnn (LoopAnnotation l x) = do
    l' <- simplifyTyInfo l
    x' <- simplifyLoopAnn_r x
    return $ LoopAnnotation l' x'

simplifyLoopAnn_r :: SimplifyK m => LoopAnnotation_r TyInfo -> SimplifyM m (LoopAnnotation_r TyInfo)
simplifyLoopAnn_r (LDecreasesAnn isFree e) = do
    e' <- simplifyPexpr e
    return (LDecreasesAnn isFree e')
simplifyLoopAnn_r (LInvariantAnn isFree isLeak e) = do
    e' <- simplifyPexpr e
    return (LInvariantAnn isFree isLeak e')

simplifyPinstr_r :: SimplifyK m => TyInfo -> Pinstr_r TyInfo -> SimplifyM m [Pinstr TyInfo]
simplifyPinstr_r i (PIFor n dir from to anns (Pblock bi b)) = do
    let v1 = funit n
    let vty = locTyNote "simplifyPinstr_r" n
    let p = infoLoc i
    fromvs::Set Piden <- lift2 $ usedVars from
    tovs::Set Piden <- lift2 $ usedVars to
    let initi = decInfoLoc ((Map.empty,False),(Map.singleton v1 (vty,False),False)) p
    let binit = Pinstr initi $ PIAssign [varPlvalue n] RawEq from Nothing
    let cmp = case dir of { Up -> Lt2; Down -> Gt2 }
    let c = Pexpr (tyInfoLoc TBool p) $ PEOp2 (cmp Unsigned) (varPexpr n) to
    let bi' = bi { infoDecClass' = let ((rs,isg1),(ws,isg2)) = infoDecClass bi in Just ((Map.insert v1 (vty,False) rs,isg1),(Map.insert v1 (vty,False) ws,isg2)) }
    let incop = case dir of { Up -> Add2; Down -> Sub2 }
    let b' = Pblock bi' $ b ++ [Pinstr bi' $ PIAssign [varPlvalue n] RawEq (Pexpr (tyInfoLoc vty p) $ PEOp2 incop (varPexpr n) (intPexpr 1)) Nothing]
    let i' = i { infoDecClass' = let ((rs,isg1),(ws,isg2)) = infoDecClass i in Just ((Map.insert v1 (vty,False) rs,isg1),(Map.insert v1 (vty,False) ws,isg2)) }
    let invop = case dir of { Up -> Le2 ; Down -> Ge2 }
    let anninv0 = case dir of
                    Down -> LoopAnnotation (noTyInfo p) $ LDecreasesAnn False $ varPexpr n
                    Up -> LoopAnnotation (noTyInfo p) $ LDecreasesAnn False $ Pexpr (tyInfoLoc vty p) $ PEOp2 Sub2 to (varPexpr n)
    let anninv1 = LoopAnnotation (noTyInfo p) $ LInvariantAnn False False $ Pexpr (tyInfo TBool) $ PEOp2 (invop Unsigned) from (varPexpr n)
    let anninv2 = LoopAnnotation (noTyInfo p) $ LInvariantAnn False False $ Pexpr (tyInfo TBool) $ PEOp2 (invop Unsigned) (varPexpr n) to
    let anninvp = LoopAnnotation (noTyInfo p) $ LInvariantAnn False True $ Pexpr (tyInfo TBool) $ LeakExpr $ varPexpr n
    concatMapM simplifyPinstr [binit,Pinstr i' $ PIWhile Nothing c (anns++[anninv0,anninv1,anninv2,anninvp]) $ Just b']
simplifyPinstr_r i (PIWhile (Just b@(Pblock _ is)) c anns Nothing) = do
    (ianns1,ianns2) <- Utils.mapAndUnzipM loopAnn2StmtAnn anns
    concatMapM simplifyPinstr (concat ianns1 ++ is ++ concat ianns2 ++ [Pinstr i $ PIWhile Nothing c anns (Just b)])
simplifyPinstr_r i (PIWhile Nothing c ann (Just b)) = do
    c' <- simplifyPexpr c
    b' <- simplifyPblock b
    ann' <- mapM simplifyLoopAnn ann
    return [Pinstr i $ PIWhile Nothing c' ann' (Just b')]
simplifyPinstr_r i (Copn lvs o es) = do
    lvs' <- mapM simplifyPlvalue lvs
    o' <- simplifyOp o
    es' <- mapM simplifyPexpr es
    return [Pinstr i $ Copn lvs' o' es']
simplifyPinstr_r i (Ccall lvs n es) = do
    lvs' <- mapM simplifyPlvalue lvs
    n' <- simplifyPident n
    es' <- mapM simplifyPexpr es
    return [Pinstr i $ Ccall lvs' n' es']
simplifyPinstr_r i (PIIf isPrivate c b1 b2) = do
    c' <- simplifyPexpr c
    b1' <- simplifyPblock b1
    b2' <- mapM simplifyPblock b2
    return [Pinstr i $ PIIf isPrivate c' b1' b2']
simplifyPinstr_r i (PIAssign lvs o re Nothing) = do
    lvs' <- mapM simplifyPlvalue lvs
    o' <- simplifyPeqop o
    re' <- simplifyPexpr re
    return [Pinstr i $ PIAssign lvs' o' re' Nothing]
simplifyPinstr_r i (Anninstr x) = do
    x' <- simplifyStatementAnn_r x
    return $ map (Pinstr i . Anninstr) x'

simplifyPeqop :: SimplifyK m => Peqop -> SimplifyM m Peqop
simplifyPeqop = return

simplifyOp :: SimplifyK m => Op -> SimplifyM m Op
simplifyOp = return

simplifyPeop1 :: SimplifyK m => Peop1 -> SimplifyM m Peop1
simplifyPeop1 = return

simplifyPeop2 :: SimplifyK m => Peop2 -> SimplifyM m Peop2
simplifyPeop2 = return

simplifyPblock :: SimplifyK m => Pblock TyInfo -> SimplifyM m (Pblock TyInfo)
simplifyPblock (Pblock i is) = do
    i' <- simplifyTyInfo i
    is' <- concatMapM simplifyPinstr is
    return $ Pblock i' is'

simplifyPexpr :: SimplifyK m => Pexpr TyInfo -> SimplifyM m ([Pinstr TyInfo],Pexpr TyInfo)
simplifyPexpr (Pexpr i e) = do
    i' <- simplifyTyInfo i
    (ss,e') <- simplifyPexpr_r e
    return (ss,Pexpr i' e')

simplifyPexpr_r :: SimplifyK m => Pexpr_r TyInfo -> SimplifyM m ([Pinstr TyInfo],Pexpr_r TyInfo)
simplifyPexpr_r (PEParens es) = do
    (concat -> ss,es') <- Utils.mapAndUnzipM simplifyPexpr es
    return (ss,PEParens es')
simplifyPexpr_r (PEVar n) = do
    n' <- simplifyPident n
    return $ PEVar n'
simplifyPexpr_r (PEGet n e) = do
    n' <- simplifyPident n
    (ss,e') <- simplifyPexpr e
    return (ss,PEGet n' e')
simplifyPexpr_r (PEFetch t n e) = do
    t' <- mapM simplifyPtype t
    n' <- simplifyPident n
    e' <- simplifyPexpr e
    return $ PEFetch t' n' e'
simplifyPexpr_r (PEBool b) = return $ PEBool b
simplifyPexpr_r (Pcast w e) = do
    e' <- simplifyPexpr e
    return $ Pcast w e'
simplifyPexpr_r (PEInt i) = return $ PEInt i
simplifyPexpr_r (PECall n es) = do
    n' <- simplifyPident n
    es' <- mapM simplifyPexpr es
    return $ PECall n' es'
simplifyPexpr_r (PEOp1 o e) = do
    o' <- simplifyPeop1 o
    e' <- simplifyPexpr e
    return $ PEOp1 o' e'
simplifyPexpr_r (PEOp2 o e1 e2) = do
    o' <- simplifyPeop2 o
    e1' <- simplifyPexpr e1
    e2' <- simplifyPexpr e2
    return $ PEOp2 o' e1' e2'
simplifyPexpr_r (LeakExpr e) = do
    e' <- simplifyPexpr e
    return $ LeakExpr e'
simplifyPexpr_r (ValidExpr e) = do
    e' <- mapM simplifyPexpr e
    return $ ValidExpr e'

simplifyPstotype :: SimplifyK m => Pstotype TyInfo -> SimplifyM m (Pstotype TyInfo)
simplifyPstotype (sto,ty) = do
    ty' <- simplifyPtype ty
    return (sto,ty')

simplifyPtype :: SimplifyK m => Ptype TyInfo -> SimplifyM m (Ptype TyInfo)
simplifyPtype TBool = return TBool
simplifyPtype (TInt w) = return $ TInt w
simplifyPtype (TWord w) = return $ TWord w
simplifyPtype (TArray w e) = do
    e' <- simplifyPexpr e
    return $ TArray w e'

simplifyPlvalue :: SimplifyK m => Plvalue TyInfo -> SimplifyM m (Plvalue TyInfo)
simplifyPlvalue (Plvalue i x) = do
    i' <- simplifyTyInfo i
    x' <- simplifyPlvalue_r x
    return $ Plvalue i' x'

simplifyPlvalue_r :: SimplifyK m => Plvalue_r TyInfo -> SimplifyM m (Plvalue_r TyInfo)
simplifyPlvalue_r PLIgnore = return PLIgnore
simplifyPlvalue_r (PLVar n) = do
    n' <- simplifyPident n
    return $ PLVar n'
simplifyPlvalue_r (PLArray n e) = do
    n' <- simplifyPident n
    e' <- simplifyPexpr e
    return $ PLArray n' e'
simplifyPlvalue_r (PLMem t n e) = do
    t' <- mapM simplifyPtype t
    n' <- simplifyPident n
    e' <- simplifyPexpr e
    return $ PLMem t' n' e'
simplifyPlvalue_r (PLParens lvs) = do
    lvs' <- mapM simplifyPlvalue lvs
    return $ PLParens lvs'

simplifyTyInfo :: SimplifyK m => TyInfo -> SimplifyM m TyInfo
simplifyTyInfo (TyInfo sto ty dec p) = do
    ty' <- mapM simplifyPtype ty
    dec' <- mapM simplifyDecClass dec
    return $ TyInfo sto ty' dec' p

-- drop all global variables
simplifyDecClass :: SimplifyK m => DecClass -> SimplifyM m DecClass
simplifyDecClass ((rs,b1),(ws,b2)) = do
    let rs' = Map.filter (not . snd) rs
    let ws' = Map.filter (not . snd) ws
    return ((rs',False),(ws',False))

-- ** State

type SubstConsts = Map Piden (Pexpr TyInfo)

type SimplifyK m = GenVar Piden m
type SimplifyM m = StateT SimplifyEnv (ExceptT JasminError m)

data SimplifyEnv = SimplifyEnv
    {
    }
  deriving (Eq,Ord,Show,Data,Typeable,Generic)


runSimplifyM :: SimplifyK m => SimplifyM m a -> m (Either JasminError a)
runSimplifyM m = runExceptT (State.evalStateT m emptySimplifyEnv)

emptySimplifyEnv = SimplifyEnv

substsFromConsts :: SubstConsts -> Substs Piden m
substsFromConsts ss = case substsProxyFromConsts ss of
    SubstsProxy f -> (f Proxy)

substsProxyFromConsts :: SubstConsts -> SubstsProxy Piden m
substsProxyFromConsts f = SubstsProxy $ \pb b v -> case eqTypeOf (typeOfProxy pb) (typeOfProxy (Proxy :: Proxy (Pexpr TyInfo))) of
            EqT -> return $ Map.lookup v f
            NeqT -> return Nothing

substConsts :: (Vars Piden m Piden,Vars Piden m a) => SubstConsts -> a -> m a
substConsts ssvars x = subst dontStop (substsFromConsts ssvars) False Map.empty x



loopAnn2StmtAnn :: SimplifyK m => LoopAnnotation TyInfo -> SimplifyM m ([Pinstr TyInfo],[Pinstr TyInfo])
loopAnn2StmtAnn (LoopAnnotation l x) = do
    (xs,ys) <- loopAnn_r2StmtAnn_r l x
    let f (StatementAnnotation l x) = Pinstr l $ Anninstr x
    return (map f xs,map f ys)

loopAnn_r2StmtAnn_r :: SimplifyK m => TyInfo -> LoopAnnotation_r TyInfo -> SimplifyM m ([StatementAnnotation TyInfo],[StatementAnnotation TyInfo])
loopAnn_r2StmtAnn_r p (LInvariantAnn True isLeak e) = return ([StatementAnnotation p $ AssumeAnn isLeak e],[])
loopAnn_r2StmtAnn_r p (LInvariantAnn False isLeak e) = return ([StatementAnnotation p $ AssertAnn isLeak e],[])
loopAnn_r2StmtAnn_r l (LDecreasesAnn isFree e) = do
    let p = infoLoc l
    let ie = loc e
    c@(Pident () n) <- lift2 $ mkNewVar "cond"
    let c' = Pident ie n
    let def = StatementAnnotation l $ VarDefAnn $ Annarg (locTy e) c' Nothing
    let ass = StatementAnnotation l $ EmbedAnn False $ Pinstr l $ PIAssign [varPlvalue c'] RawEq e Nothing
    let cons = if isFree then AssumeAnn else AssertAnn
    let assert = StatementAnnotation l $ cons False $ Pexpr (tyInfoLoc TBool p) $ PEOp2 (Le2 Unsigned) e (varPexpr c')
    return ([def,ass],[assert])





