{-# LANGUAGE TupleSections, TypeFamilies, RankNTypes, DoAndIfThenElse, ScopedTypeVariables, FlexibleContexts, ViewPatterns, ConstraintKinds, FlexibleInstances, MultiParamTypeClasses, DeriveDataTypeable, DeriveGeneric #-}

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
    args' <- mapM (simplifyPure simplifyAnnarg) args
    anns' <- mapM simplifyProcAnn anns
    i' <- simplifyTyInfo i
    return $ AnnAxiomDeclaration isLeak args' anns' i'

simplifyPAnnLemmaDef :: SimplifyK m => AnnLemmaDeclaration TyInfo -> SimplifyM m (AnnLemmaDeclaration TyInfo)
simplifyPAnnLemmaDef (AnnLemmaDeclaration isLeak n args anns body i) = do
    n' <- simplifyPident n
    args' <- mapM (simplifyPure simplifyAnnarg) args
    anns' <- mapM simplifyProcAnn anns
    body' <- mapM simplifyPblock body
    i' <- simplifyTyInfo i
    return $ AnnLemmaDeclaration isLeak n' args' anns' body' i'

simplifyPAnnFunDef :: SimplifyK m => AnnFunDeclaration TyInfo -> SimplifyM m (AnnFunDeclaration TyInfo)
simplifyPAnnFunDef (AnnFunDeclaration isLeak ret n args anns body i) = do
    ret' <- simplifyPure simplifyPtype ret
    n' <- simplifyPident n
    args' <- mapM (simplifyPure simplifyAnnarg) args
    anns' <- mapM simplifyProcAnn anns
    body' <- simplifyPure simplifyPexpr body
    i' <- simplifyTyInfo i
    return $ AnnFunDeclaration isLeak ret' n' args' anns' body' i'

simplifyPparam :: SimplifyK m => Pparam TyInfo -> SimplifyM m (Either (Pparam TyInfo) SubstConsts)
simplifyPparam (Pparam ty n e) = do
    return $ Right $ Map.singleton (funit n) e

simplifyPfundef :: SimplifyK m => Pfundef TyInfo -> SimplifyM m (Pfundef TyInfo)
simplifyPfundef (Pfundef cc n args rty ann body info) = do
    n' <- simplifyPident n
    args' <- mapM simplifyParg args
    rty' <- mapM (mapM (simplifyPure simplifyPstotype)) rty
    ann' <- mapM simplifyProcAnn ann
    body' <- simplifyPfunbody body
    info' <- simplifyTyInfo info
    return $ Pfundef cc n' args' rty' ann' body' info'

simplifyParg :: SimplifyK m => Parg TyInfo -> SimplifyM m (Parg TyInfo)
simplifyParg (Parg ty n) = do
    ty' <- simplifyPure simplifyPstotype ty
    n' <- mapM simplifyPident n
    return $ Parg ty' n'

simplifyAnnarg :: SimplifyK m => Bool -> Annarg TyInfo -> SimplifyM m ([Pinstr TyInfo],Annarg TyInfo)
simplifyAnnarg isPure (Annarg ty n e) = do
    (ssty,ty') <- simplifyPtype isPure ty
    n' <- simplifyPident n
    (concat -> sse,e') <- Utils.mapAndUnzipM (simplifyPexpr isPure) e
    return (ssty++sse,Annarg ty' n' e')

simplifyPbodyarg :: SimplifyK m => Pbodyarg TyInfo -> SimplifyM m (Pbodyarg TyInfo)
simplifyPbodyarg (Pbodyarg ty n) = do
    ty' <- simplifyPure simplifyPstotype ty
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
    e' <- simplifyPure simplifyPexpr e
    return (RequiresAnn isFree isLeak e')
simplifyProcAnn_r (EnsuresAnn isFree isLeak e) = do
    e' <- simplifyPure simplifyPexpr e
    return (EnsuresAnn isFree isLeak e')
simplifyProcAnn_r (PDecreasesAnn e) = do
    e' <- simplifyPure simplifyPexpr e
    return (PDecreasesAnn e')

simplifyStatementAnn :: SimplifyK m => StatementAnnotation TyInfo -> SimplifyM m [StatementAnnotation TyInfo]
simplifyStatementAnn (StatementAnnotation l x) = do
    l' <- simplifyTyInfo l
    x' <- simplifyStatementAnn_r x
    return $ map (StatementAnnotation l') x'

simplifyStatementAnn_r :: SimplifyK m => StatementAnnotation_r TyInfo -> SimplifyM m [StatementAnnotation_r TyInfo]
simplifyStatementAnn_r (AssumeAnn isLeak e) = do
    (ss,e') <- simplifyPexpr False e
    return $ map (EmbedAnn isLeak) ss ++ [AssumeAnn isLeak e']
simplifyStatementAnn_r (AssertAnn isLeak e) = do
    (ss,e') <- simplifyPexpr False e
    return $ map (EmbedAnn isLeak) ss ++ [AssertAnn isLeak e']
simplifyStatementAnn_r (EmbedAnn isLeak e) = do
    e' <- simplifyPinstr e
    return $ map (EmbedAnn isLeak) e'
simplifyStatementAnn_r (VarDefAnn ann) = do
    (ss,ann') <- simplifyAnnarg False ann
    return $ map (EmbedAnn False) ss ++ [VarDefAnn ann']

simplifyLoopAnn :: SimplifyK m => LoopAnnotation TyInfo -> SimplifyM m (LoopAnnotation TyInfo)
simplifyLoopAnn (LoopAnnotation l x) = do
    l' <- simplifyTyInfo l
    x' <- simplifyLoopAnn_r x
    return $ LoopAnnotation l' x'

simplifyLoopAnn_r :: SimplifyK m => LoopAnnotation_r TyInfo -> SimplifyM m (LoopAnnotation_r TyInfo)
simplifyLoopAnn_r (LDecreasesAnn isFree e) = do
    e' <- simplifyPure simplifyPexpr e
    return (LDecreasesAnn isFree e')
simplifyLoopAnn_r (LInvariantAnn isFree isLeak e) = do
    e' <- simplifyPure simplifyPexpr e
    return (LInvariantAnn isFree isLeak e')

simplifyPinstr_r :: SimplifyK m => TyInfo -> Pinstr_r TyInfo -> SimplifyM m [Pinstr TyInfo]
simplifyPinstr_r i (PIFor n dir from to anns (Pblock bi b)) = do
    let p = infoLoc i
    let v1 = funit n
    let vty = locTyNote "simplifyPinstr_r" n
    -- inclusive ranges
    fromvs::Set Piden <- lift2 $ usedVars from
    tovs::Set Piden <- lift2 $ usedVars to
    let initi = decInfoLoc (DecClass (Map.empty,False) (Map.singleton v1 (vty,False),False) NoMem) p
    let binit = Pinstr initi $ PIAssign [varPlvalue n] RawEq from Nothing
    let cmp = case dir of { Up -> Le2; Down -> Ge2 }
    let c = Pexpr (tyInfoLoc TBool p) $ PEOp2 (cmp Unsigned) (varPexpr n) to
    let bi' = bi { infoDecClass' = let (DecClass (rs,isg1) (ws,isg2) mem) = infoDecClass bi in Just (DecClass (Map.insert v1 (vty,False) rs,isg1) (Map.insert v1 (vty,False) ws,isg2) mem) }
    let incop = case dir of { Up -> Add2; Down -> Sub2 }
    let incn = Pexpr (tyInfoLoc vty p) $ PEOp2 incop (varPexpr n) (intPexpr 1)
    let incto = Pexpr (tyInfoLoc vty p) $ PEOp2 incop to (intPexpr 1)
    let b' = Pblock bi' $ b ++ [Pinstr bi' $ PIAssign [varPlvalue n] RawEq (incn) Nothing]
    let i' = i { infoDecClass' = let (DecClass (rs,isg1) (ws,isg2) mem) = infoDecClass i in Just (DecClass (Map.insert v1 (vty,False) rs,isg1) (Map.insert v1 (vty,False) ws,isg2) mem) }
    let invop = case dir of { Up -> Le2 ; Down -> Ge2 }
    let anninv0 = case dir of
                    Down -> LoopAnnotation (noTyInfo p) $ LDecreasesAnn False $ varPexpr n
                    Up -> LoopAnnotation (noTyInfo p) $ LDecreasesAnn False $ Pexpr (tyInfoLoc vty p) $ PEOp2 Sub2 to (varPexpr n)
    let anninv1 = LoopAnnotation (noTyInfo p) $ LInvariantAnn False False $ Pexpr (tyInfo TBool) $ PEOp2 (invop Unsigned) from (varPexpr n)
    let anninv2 = LoopAnnotation (noTyInfo p) $ LInvariantAnn False False $ Pexpr (tyInfo TBool) $ PEOp2 (invop Unsigned) (varPexpr n) incto
    let anninvp = LoopAnnotation (noTyInfo p) $ LInvariantAnn False True $ Pexpr (tyInfo TBool) $ LeakExpr $ varPexpr n
    concatMapM simplifyPinstr [binit,Pinstr i' $ PIWhile Nothing c (anns++[anninv0,anninv1,anninv2,anninvp]) $ Just b']
simplifyPinstr_r i (PIWhile (Just b@(Pblock _ is)) c anns Nothing) = do
    (ianns1,ianns2) <- Utils.mapAndUnzipM loopAnn2StmtAnn anns
    concatMapM simplifyPinstr (concat ianns1 ++ is ++ concat ianns2 ++ [Pinstr i $ PIWhile Nothing c anns (Just b)])
simplifyPinstr_r i (PIWhile Nothing c ann (Just b)) = do
    c' <- simplifyPure simplifyPexpr c
    b' <- simplifyPblock b
    ann' <- mapM simplifyLoopAnn ann
    return [Pinstr i $ PIWhile Nothing c' ann' (Just b')]
simplifyPinstr_r i (Copn lvs o es) = do
    (concat -> sslv,lvs') <- Utils.mapAndUnzipM simplifyPlvalue lvs
    o' <- simplifyOp o
    (concat -> sse,es') <- Utils.mapAndUnzipM (simplifyPexpr False) es
    return $ sse ++ sslv ++ [Pinstr i $ Copn lvs' o' es']
simplifyPinstr_r i (Ccall lvs n es) = do
    (concat -> sslv,lvs') <- Utils.mapAndUnzipM simplifyPlvalue lvs
    n' <- simplifyPident n
    (concat -> sse,es') <- Utils.mapAndUnzipM (simplifyPexpr False) es
    return $ sse ++ sslv ++ [Pinstr i $ Ccall lvs' n' es']
simplifyPinstr_r i (PIIf isPrivate c b1 b2) = do
    (ssc,c') <- simplifyPexpr False c
    b1' <- simplifyPblock b1
    b2' <- mapM simplifyPblock b2
    return $ ssc ++ [Pinstr i $ PIIf isPrivate c' b1' b2']
simplifyPinstr_r i (PIAssign lvs o re Nothing) = do
    (concat -> sslvs,lvs') <- Utils.mapAndUnzipM simplifyPlvalue lvs
    o' <- simplifyPeqop o
    (sse,re') <- simplifyPexpr False re
    return $ sse ++ sslvs ++ [Pinstr i $ PIAssign lvs' o' re' Nothing]
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

simplifyPexpr :: SimplifyK m => Bool -> Pexpr TyInfo -> SimplifyM m ([Pinstr TyInfo],Pexpr TyInfo)
simplifyPexpr isPure (Pexpr i e) = do
    i' <- simplifyTyInfo i
    (ss,e') <- simplifyPexpr_r isPure i' e
    return (ss,Pexpr i' e')

simplifyPexpr_r :: SimplifyK m => Bool -> TyInfo -> Pexpr_r TyInfo -> SimplifyM m ([Pinstr TyInfo],Pexpr_r TyInfo)
simplifyPexpr_r isPure l (PEParens es) = do
    (concat -> ss,es') <- Utils.mapAndUnzipM (simplifyPexpr isPure) es
    return (ss,PEParens es')
simplifyPexpr_r isPure l (PEVar n) = do
    n' <- simplifyPident n
    return ([],PEVar n')
simplifyPexpr_r isPure l (PEGet n e) = do
    n' <- simplifyPident n
    (ss,e') <- simplifyPexpr isPure e
    return (ss,PEGet n' e')
simplifyPexpr_r False l@(infoTy -> TWord w) (PEFetch t v i) | w > 8 = do -- FIXME: martelada para criar variáveis locais!
    let p = infoLoc l
    let tw8 = tyInfoLoc (TWord 8) p
    let n = w `div` 8
    js <- forM [0..n-1] $ \j -> do
        (Pident () jn) <- lift2 $ mkNewVar ("v"++show j)
        return (j,Pident tw8 jn)
    let mklv (j,jv) = do
        let def = Pinstr (noTyInfo p) $ Anninstr $ VarDefAnn $ Annarg (TWord 8) jv Nothing
        let ass = Pinstr (noTyInfo p) $ PIAssign [varPlvalue jv] RawEq (Pexpr tw8 $ PEFetch Nothing v $ Pexpr (loc i) $ PEOp2 Add2 i $ intPexpr (toEnum j)) Nothing
        return [def,ass]
    defs <- concatMapM mklv js
    (is',e') <- simplifyPexpr_r False l $ PEParens $ map (varPexpr . snd) js 
    return (defs++is',e')
simplifyPexpr_r isPure l (PEFetch t n e) = do
    (concat -> ss1,t') <- Utils.mapAndUnzipM (simplifyPtype isPure) t
    n' <- simplifyPident n
    (ss2,e') <- simplifyPexpr isPure e
    return (ss1++ss2,PEFetch t' n' e') 
simplifyPexpr_r isPure l (PEBool b) = return ([],PEBool b)
simplifyPexpr_r isPure l (Pcast w e) = do
    (ss,e') <- simplifyPexpr isPure e
    return (ss,Pcast w e')
simplifyPexpr_r isPure l (PEInt i) = return ([],PEInt i)
simplifyPexpr_r isPure l (PECall n es) = do
    n' <- simplifyPident n
    (concat -> ss,es') <- Utils.mapAndUnzipM (simplifyPexpr isPure) es
    return (ss,PECall n' es')
simplifyPexpr_r isPure l (PEOp1 o e) = do
    o' <- simplifyPeop1 o
    (ss,e') <- simplifyPexpr isPure e
    return (ss,PEOp1 o' e')
simplifyPexpr_r isPure l (PEOp2 o e1 e2) = do
    o' <- simplifyPeop2 o
    (ss1,e1') <- simplifyPexpr isPure e1
    (ss2,e2') <- simplifyPexpr isPure e2
    return (ss1++ss2,PEOp2 o' e1' e2')
simplifyPexpr_r isPure l (LeakExpr e) = do
    (ss,e') <- simplifyPexpr isPure e
    return (ss,LeakExpr e')
simplifyPexpr_r isPure l (ValidExpr e) = do
    (concat -> ss,e') <- Utils.mapAndUnzipM (simplifyPexpr isPure) e
    return (ss,ValidExpr e')

simplifyPstotype :: SimplifyK m => Bool -> Pstotype TyInfo -> SimplifyM m ([Pinstr TyInfo],Pstotype TyInfo)
simplifyPstotype isPure (sto,ty) = do
    (ss,ty') <- simplifyPtype isPure ty
    return (ss,(sto,ty'))

simplifyPure :: SimplifyK m => (Bool -> a -> SimplifyM m ([Pinstr TyInfo],a)) -> a -> SimplifyM m a
simplifyPure f x = do
    ([],x') <- f True x
    return x'

simplifyPtype :: SimplifyK m => Bool -> Ptype TyInfo -> SimplifyM m ([Pinstr TyInfo],Ptype TyInfo)
simplifyPtype isPure TBool = return ([],TBool)
simplifyPtype isPure (TInt w) = return ([],TInt w)
simplifyPtype isPure (TWord w) = return ([],TWord w)
simplifyPtype isPure (TArray w e) = do
    (ss,e') <- simplifyPexpr isPure e
    return (ss,TArray w e')

simplifyPlvalue :: SimplifyK m => Plvalue TyInfo -> SimplifyM m ([Pinstr TyInfo],Plvalue TyInfo)
simplifyPlvalue (Plvalue i x) = do
    i' <- simplifyTyInfo i
    (ss,x') <- simplifyPlvalue_r i' x
    return (ss,Plvalue i' x')

simplifyPlvalue_r :: SimplifyK m => TyInfo -> Plvalue_r TyInfo -> SimplifyM m ([Pinstr TyInfo],Plvalue_r TyInfo)
simplifyPlvalue_r l PLIgnore = return ([],PLIgnore)
simplifyPlvalue_r l (PLVar n) = do
    n' <- simplifyPident n
    return ([],PLVar n')
simplifyPlvalue_r l (PLArray n e) = do
    n' <- simplifyPident n
    (ss,e') <- simplifyPexpr False e
    return (ss,PLArray n' e')
simplifyPlvalue_r l (PLMem t n e) = do
    (concat -> ss1,t') <- Utils.mapAndUnzipM (simplifyPtype False) t
    n' <- simplifyPident n
    (ss2,e') <- simplifyPexpr False e
    return (ss1++ss2,PLMem t' n' e')
simplifyPlvalue_r l (PLParens lvs) = do
    (concat -> ss,lvs') <- Utils.mapAndUnzipM simplifyPlvalue lvs
    return (ss,PLParens lvs')

simplifyTyInfo :: SimplifyK m => TyInfo -> SimplifyM m TyInfo
simplifyTyInfo (TyInfo sto ty dec p) = do
    ty' <- mapM (simplifyPure simplifyPtype) ty
    dec' <- mapM simplifyDecClass dec
    return $ TyInfo sto ty' dec' p

-- drop all global variables
simplifyDecClass :: SimplifyK m => DecClass -> SimplifyM m DecClass
simplifyDecClass (DecClass (rs,b1) (ws,b2) mem) = do
    let rs' = Map.filter (not . snd) rs
    let ws' = Map.filter (not . snd) ws
    return $ DecClass (rs',False) (ws',False) mem

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

splitProcAnns :: [ProcedureAnnotation info] -> ([StatementAnnotation info],[StatementAnnotation info])
splitProcAnns [] = ([],[])
splitProcAnns (x:xs) = let (ys1,ys2) = splitProcAnns xs in case split x of
    Left ys -> (ys++ys1,ys2)
    Right ys -> (ys1,ys++ys2)
  where
    split (ProcedureAnnotation t (RequiresAnn isFree isLeak e))   = Left [StatementAnnotation t $ if isFree then AssumeAnn isLeak e else AssertAnn isLeak e]
    split (ProcedureAnnotation t (PDecreasesAnn e)) = Left []
    split (ProcedureAnnotation t (EnsuresAnn isFree isLeak e))    = Right [StatementAnnotation t $ if isFree then AssumeAnn isLeak e else AssertAnn isLeak e]



