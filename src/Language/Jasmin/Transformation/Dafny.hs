{-# LANGUAGE TupleSections, DoAndIfThenElse, ScopedTypeVariables, FlexibleContexts, ViewPatterns, ConstraintKinds, FlexibleInstances, MultiParamTypeClasses, DeriveDataTypeable, DeriveGeneric #-}

module Language.Jasmin.Transformation.Dafny where

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

import Language.Position
import Language.Location
import Language.Jasmin.Syntax
import Language.Vars
import Language.Jasmin.TypeChecker
import Language.Jasmin.Error

import Utils

toDafny :: DafnyK m => FilePath -> FilePath -> Bool -> Pprogram TyInfo -> m (Either JasminError Doc)
toDafny prelude prelude_leak leakMode prog = runExceptT $ flip State.evalStateT (DafnySt leakMode Nothing [] KeepF) $ do
    let preludefile = if leakMode then prelude_leak else prelude
    dfy <- liftIO $ readFile preludefile
    let pdfy = text dfy
    let pname = dropExtension $ takeFileName $ posFileName $ infoLoc $ loc prog
    pprog <- pprogramtoDafny prog
    let pcode = text "class" <+> text pname <+> text "extends Mem" $+$ vbraces pprog
    return $ pdfy $+$ pcode

pprogramtoDafny :: DafnyK m => Pprogram TyInfo -> DafnyM m Doc
pprogramtoDafny (Pprogram prog) = do
    pprog <- mapM pitemToDafny prog
    return $ vcat pprog
    --return $ text "class" $+$ vbrackets pprog

pitemToDafny :: DafnyK m => Pitem TyInfo -> DafnyM m Doc
pitemToDafny (PFundef f) = pfundefToDafny f
pitemToDafny (PParam p) = pparamToDafny p
pitemToDafny i = error "TODO: pitemToDafny annotations"

pfundefToDafny :: DafnyK m => Pfundef TyInfo -> DafnyM m Doc
pfundefToDafny def@(Pfundef cc pn pargs pret procann (Pfunbody pbvars pbinstrs pbret) info) = insideDecl did $ resetAssumptions $ do
    let p = infoLoc info
    ppn <- procidenToDafny pn
    (ppargs,parganns) <- procedureArgsToDafny IsPrivate False pargs
    (pbvars',pbinstrs',ssargs) <- newDafnyArgs p pargs
    newvs <- lift2 $ bvsSet pbvars'
    (newpbinstrs,newpbret) <- lift2 $ substVars dontStop ssargs False Map.empty (pbinstrs,pbret)
    (pret,pretanns) <- case pret of
        Nothing -> return (PP.empty,[])
        Just results -> do
            tvs <- forM results $ \t -> do
                vret::Maybe Piden <- lift2 $ liftM Just $ mkNewVar "result"
                return (Parg t $ fmap (fconst $ pstotypeTyInfo t) vret)
            (pret,pretanns) <- procedureArgsToDafny IsPrivate True tvs
            return (text "returns" <+> pret,pretanns)
    let cl = infoDecClass info
    pcl <- decClassToDafny True cl
    pprocann <- procAnnsToDafny procann
    (pbody1,annb1) <- pbodyargsToDafny IsPrivate (pbvars++pbvars')
    (pbody2,annb2) <- pblock_rToDafny info (pbinstrs'++newpbinstrs)
    (pbody3) <- case newpbret of
        Nothing -> return (PP.empty)
        Just erets -> do
            (perets) <- mapM (pidentToDafny) erets
            return (text "return" <+> sepBy perets comma <> semicolon)
    let tag = text "method"
    let anns' = parganns ++ pretanns
    annframes <- dropAssumptions newvs $ propagateDafnyAssumptions p EnsureK cl
    let (pk1,annk1) = annLinesProcC True (annframes++pprocann++anns') 
    let (pk2,annk2) = annLinesProcC True annb1
    let (pk3,annk3) = annLinesProcC True annb2
    return $ (tag <+> ppn <+> ppargs <+> pret $+$ pcl $+$ pk1 $+$ pk2 $+$ pk3 $+$ annk1 $+$ vbraces (pbody1 $+$ annk2 $+$ pbody2 $+$ annk3 $+$ pbody3))
  where
    did = pidentToDafnyId pn

-- to work around the fact that Dafny does not allow inputs to be mutated
newDafnyArgs :: DafnyK m => Position -> [Parg TyInfo] -> DafnyM m ([Pbodyarg TyInfo],[Pinstr TyInfo],SubstVars Piden)
newDafnyArgs l xs = do
    (as,is,ss) <- Utils.mapAndUnzip3M (newDafnyArg l) xs
    return (concat as,concat is,mconcat ss)

newDafnyArg :: DafnyK m => Position -> Parg TyInfo -> DafnyM m ([Pbodyarg TyInfo],[Pinstr TyInfo],SubstVars Piden)
newDafnyArg l (Parg _ Nothing) = return ([],[],mempty)
newDafnyArg l (Parg stoty (Just oldv@(Pident i oldn))) = do
    newv@(Pident _ newn)::Piden <- lift2 $ newVar (funit oldv)
    let newv = Pident i newn
    let barg = (Pbodyarg stoty newv)
    let rs = (Map.singleton (funit oldv) (infoTyNote "newDafnyArg" i,False),False)
    let ws = (Map.singleton (funit newv) (infoTyNote "newDafnyArg" i,False),False)
    let cl = (DecClass rs ws NoMem)
    let bass = Pinstr (decInfoLoc cl l) $ PIAssign [varPlvalue newv] RawEq (varPexpr oldv) Nothing
    copyDafnyAssumptions l oldv newv
    let bss = substVarsFromList [(funit oldv,funit newv)]
    return ([barg],[bass],bss)

pbodyargsToDafny :: DafnyK m => CtMode -> [Pbodyarg TyInfo] -> DafnyM m (Doc,AnnsDoc)
pbodyargsToDafny ct xs = do
    (ys,anns) <- State.mapAndUnzipM (pbodyargToDafny ct) xs
    return (vcat ys,concat anns)

pbodyargToDafny :: DafnyK m => CtMode -> Pbodyarg TyInfo -> DafnyM m (Doc,AnnsDoc)
pbodyargToDafny ct (Pbodyarg t v) = do
    (parg,anns) <- pargToDafny False StmtK ct $ Parg t (Just v)
    let (anns',parg1) = annLinesC StmtKC anns
    return (parg $+$ parg1,anns')

procedureArgsToDafny :: DafnyK m => CtMode -> Bool -> [Parg TyInfo] -> DafnyM m (Doc,AnnsDoc)
procedureArgsToDafny ct isPost xs = do
    (vs,as) <- State.mapAndUnzipM (procedureArgToDafny ct isPost) xs
    return (parens $ sepBy vs comma,concat as)

procedureArgToDafny :: DafnyK m => CtMode -> Bool -> Parg TyInfo -> DafnyM m (Doc,AnnsDoc)
procedureArgToDafny ct isPost v = do
    let annK = if isPost then EnsureK else RequireK
    pargToDafny True annK ct v

pargToDafny :: DafnyK m => Bool -> AnnKind -> CtMode -> Parg TyInfo -> DafnyM m (Doc,AnnsDoc)
pargToDafny isProcArg annK ct (Parg ty Nothing) = ptypeToDafny annK Nothing (snd ty)
pargToDafny isProcArg annK ct (Parg ty (Just v)) = do
    vs <- lift2 $ usedVars v
    pv <- pidentToDafny v
    (pty,annty) <- ptypeToDafny annK (Just v) (snd ty)
    annp <- genDafnyAssumptions annK ct vs pv (pstotypeTyInfo ty)
    let pdecl = pv <+> char ':' <+> pty
    let pvar = if isProcArg then pdecl else text "var" <+> pdecl <> semicolon
    return (pvar,annp ++ annty)

pparamToDafny :: DafnyK m => Pparam TyInfo -> DafnyM m Doc
pparamToDafny p = genError (infoLoc $ loc p) $ text "unsupported param"
--pparamToDafny (Pparam ty v e) = resetAssumptions $ do
--    (pe,anne) <- pexprToDafny AxiomK IsPublic e
--    State.modify $ \env -> env { consts = Map.insert (funit v) pe (consts env) }
--    return PP.empty
--pparamToDafny (Pparam ty v e) = resetAssumptions $ do
--    pv <- pidentToDafny v
--    (pty,annty) <- ptypeToDafny AxiomK (Just v) ty
--    (pe,anne) <- pexprToDafny AxiomK IsPublic e
--    return (text "var" <+> pv <+> char ':' <+> pty <+> text ":=" <+> pe)

pblockToDafny :: DafnyK m => Pblock TyInfo -> DafnyM m (Doc,AnnsDoc)
pblockToDafny (Pblock l x) = do
    (d,anns) <- pblock_rToDafny l x
    let (anns',d') = annLinesC StmtKC anns
    return (vbraces (d $+$ d'),anns')

pblock_rToDafny :: DafnyK m => TyInfo -> [Pinstr TyInfo] -> DafnyM m (Doc,AnnsDoc)
pblock_rToDafny l xs = do
    (ys,anns) <- pinstrsToDafny xs
    return (ys,anns)

pinstrsToDafny :: DafnyK m => [Pinstr TyInfo] -> DafnyM m (Doc,AnnsDoc)
pinstrsToDafny xs = do
    (ys,anns) <- State.mapAndUnzipM pinstrToDafny xs
    return (vcat ys,concat anns)

pinstrs_rToDafny :: DafnyK m => TyInfo -> [Pinstr_r TyInfo] -> DafnyM m (Doc,AnnsDoc)
pinstrs_rToDafny p xs = do
    (ys,anns) <- State.mapAndUnzipM (pinstr_rToDafny p) xs
    return (vcat ys,concat anns)

pinstrToDafny :: DafnyK m => Pinstr TyInfo -> DafnyM m (Doc,AnnsDoc)
pinstrToDafny (Pinstr l i) = pinstr_rToDafny l i
    
pinstr_rToDafny :: DafnyK m => TyInfo -> Pinstr_r TyInfo -> DafnyM m (Doc,AnnsDoc)
pinstr_rToDafny l (PIIf isPrivate c s1 s2) = pif_rToDafny isPrivate l c s1 s2
pinstr_rToDafny l (PIWhile Nothing e ann (Just s)) = do
    let p = infoLoc l
    let cl = infoDecClass $ loc s
    annframes <- propagateDafnyAssumptions p InvariantK cl
    (pe,anne) <- pexprToDafny InvariantK IsCt e
    annns <- loopAnnsToDafny ann
    let (pk,invs) = annLinesC LoopKC (annns++annframes++anne)
    (ps,ann2) <- pblockToDafny s
    return (text "while" <+> pe $+$ invs $+$ vbraces (ps),pk++ann2)
pinstr_rToDafny l (PIAssign ls RawEq re Nothing) = do
    (pre,pres) <- pexprToDafny StmtK IsPrivate re
    lvs <- lift2 $ usedVars ls    
    (pass,pres',post) <- dropAssumptions lvs $ passToDafny (infoLoc l) StmtK ls (Just [re],pre)
    let (anns1,pres'') = annLinesC StmtKC (pres++pres')
    let (anns2,post') = annLinesC StmtKC post
    return (pres'' $+$ pass $+$ post',anns1++anns2)
pinstr_rToDafny l (Copn ls Oaddcarry es) = carry_opToDafny l ls Oaddcarry es
pinstr_rToDafny l (Copn ls Osubcarry es) = carry_opToDafny l ls Osubcarry es
pinstr_rToDafny l (Ccall ls n args) = do
    pn <- procidenToDafny n
    lvs <- lift2 $ usedVars ls
    (pargs,pres) <- procCallArgsToDafny StmtK args
    let pcall = pn <> parens (sepBy pargs comma)
    (pass,pres',post) <- dropAssumptions lvs $ passToDafny (infoLoc l) StmtK ls (Nothing,pcall)
    let (anns1,pres'') = annLinesC StmtKC (pres++pres')
    let (anns2,post') = annLinesC StmtKC post
    return (pres'' $+$ pass $+$ post',anns1++anns2)
pinstr_rToDafny l (Anninstr i) = instrAnn_rToDafny l i
pinstr_rToDafny l i = do
    pi <- pp i
    genError (infoLoc l) $ text "pinstr_rToDafny: unsupported instruction " <+> pi

carry_opToDafny :: DafnyK m => TyInfo -> [Plvalue TyInfo] -> Op -> [Pexpr TyInfo] -> DafnyM m (Doc,AnnsDoc)
carry_opToDafny p ls@[l1,l2] op es@[e1,e2,e3] = do
    let pp = infoLoc p
    let t1 = locTy e1
    (pt1,annt1) <- ptypeToDafny StmtK Nothing t1
    let (pop,cmp) = case op of
                Oaddcarry -> (text "addcarry_" <> pt1,text "<")
                Osubcarry -> (text "subcarry_" <> pt1,text ">")
    
    (pe1,anne1) <- pexprToDafny StmtK IsPrivate e1
    (pe2,anne2) <- pexprToDafny StmtK IsPrivate e2
    (pe3,anne3) <- pexprToDafny StmtK IsPrivate e3
    let pes = sepBy [pe1,pe2,pe3] comma
    let annes = anne1++anne2++anne3
    tup0::Piden <- lift2 $ mkNewVar "tup0"
    tup1::Piden <- lift2 $ mkNewVar "tup1"
    ptup0 <- pidentToDafny tup0
    ptup1 <- pidentToDafny tup1
    let pcall = text "var" <+> parens (ptup0 <> comma <> ptup1) <+> text ":=" <+> pop <> parens pes <> semicolon
    --let passume = text "assume"  <+> ptup0 <+> text "==" <+> parens (pe1 <+> cmp <+> ptup1) <> semicolon;
    lvs <- lift2 $ usedVars ls    
    dropAssumptions lvs $ do
        (pass1,pres1,post1) <- passToDafny pp StmtK [l1] (Nothing,ptup0)
        (pass2,pres2,post2) <- passToDafny pp StmtK [l2] (Nothing,ptup1)
        let (annpres,pres) = annLinesC StmtKC (pres1++pres2)
        let (annpost,post) = annLinesC StmtKC (post1++post2)
        return (pres $+$ pcall $+$ pass1 $+$ pass2 $+$ post,annt1 ++ annes ++ annpres ++ annpost)

pif_rToDafny :: DafnyK m => Bool -> TyInfo -> Pexpr TyInfo -> Pblock TyInfo -> Maybe (Pblock TyInfo) -> DafnyM m (Doc,AnnsDoc)
pif_rToDafny isPrivate l c s1 s2 = do 
    let ctmode = if isPrivate then IsPrivate else IsCt
    (pc,ann1) <- pexprToDafny StmtK ctmode c
    (ps1,annthen) <- withAssumptions $ pblockToDafny s1
    (ps2,Foldable.concat -> annelse) <- withAssumptions $ Utils.mapAndUnzipM pblockToDafny s2
    let annthen' = addAnnsCond pc annthen
    let annelse' = addAnnsCond (char '!' <> parens pc) annelse
    ppo <- PP.ppOptM ps2 (return . (text "else" <+>))
    addAnnsC StmtKC (ann1++annthen'++annelse') $ text "if" <+> pc <+> ps1 $+$ ppo

isPLVar (Plvalue _ (PLVar _)) = True
isPLVar _ = False
arePLVars = and . map isPLVar

passToDafny :: DafnyK m => Position -> AnnKind -> [Plvalue TyInfo] -> (Maybe [Pexpr TyInfo],Doc) -> DafnyM m (Doc,AnnsDoc,AnnsDoc)
passToDafny p annK lvs@(arePLVars -> True) e = do
        (plvs,annlvs) <- State.mapAndUnzipM (plvalueToDafny annK IsPrivate) lvs
        pass <- assign p (zip lvs plvs) e
        return (pass,[],concat annlvs)
passToDafny p annK ls e = do
        ls' <- forM ls $ \l -> do
            Pident () n <- lift2 $ mkNewVar "aux"
            return $ Pident (loc l) n
        (pdefs,annsdefs) <- State.mapAndUnzipM (\l -> pargToDafny False StmtK IsPrivate $ Parg (infoStotyNote (pprid p ++ " passToDafny") $ loc l) (Just l)) ls'        
        ppls' <- mapM pidentToDafny ls'
        asse <- assign p (zip (map varPlvalue ls') ppls') e
        (assls,annpre,annpos) <- Utils.mapAndUnzip3M (uncurry (passToDafny' p annK)) (zip ls $ map Left $ zip (map (\x -> [varPexpr x]) ls') ppls')
        return (vcat pdefs $+$ asse $+$ vcat assls,concat annpre,concat annsdefs ++ concat annpos)

assign :: DafnyK m => Position -> [(Plvalue TyInfo,Doc)] -> (Maybe [Pexpr TyInfo],Doc) -> DafnyM m Doc
assign p [] (_,pe) = return $ pe <> semicolon
assign p xs (mb,pe) = do
    let (vxs,pxs) = unzip xs
    let copy (Plvalue _ (PLVar v)) (Pexpr _ (PEVar v')) = copyDafnyAssumptions p v' v
        copy v e = return ()
    case mb of
        Nothing -> return ()
        Just ys -> when (length xs == length ys) $ mapM_ (uncurry copy) (zip vxs ys)
    return $ sepBy pxs comma <+> text ":=" <+> pe <> semicolon

-- left = variable, right = update
passToDafny' :: DafnyK m => Position -> AnnKind -> Plvalue TyInfo -> Either ([Pexpr TyInfo],Doc) Doc -> DafnyM m (Doc,AnnsDoc,AnnsDoc)
passToDafny' p annK lv@(Plvalue li lvr) re = passToDafny'' lvr re
    where
    passToDafny'' :: DafnyK m => Plvalue_r TyInfo -> Either ([Pexpr TyInfo],Doc) Doc -> DafnyM m (Doc,AnnsDoc,AnnsDoc)
    passToDafny'' PLIgnore re = return (PP.empty,[],[])
    passToDafny'' (PLVar v) (Left (re,pre)) = do
        (plv,annlv) <- plvalueToDafny annK IsPrivate lv
        pass <- assign p [(lv,plv)] (Just re,pre)
        return (pass,[],annlv)
    passToDafny'' (PLVar v) (Right upd) = do
        (plv,annlv) <- plvalueToDafny annK IsPrivate lv
        pass <- assign p [(lv,plv)] (Nothing,plv <> upd)
        return (pass,annlv,annlv)
    passToDafny'' (PLParens [lv]) re = passToDafny' p annK lv re
    passToDafny'' lv@(PLParens ps) (Left (re,pre)) = do
        let TWord wtot = infoTyNote "passToDafny" li
        let mask doc 0 wx = doc
            mask doc offset wx = doc <+> text "&" <+> text "0x" <> hcat (replicate (div (wtot-wx) 4) $ text "0") <> hcat (replicate (div wx 4) $ text "F")
        let getbits offset [] = return (PP.empty,[],[])
            getbits offset (Plvalue tx PLIgnore:xs) = do
                let TWord wx = infoTyNote "passToDafny" tx 
                getbits (offset + wx) xs
            getbits offset (x:xs) = do
                (ppx,annx) <- plvalueToDafny annK IsPrivate x
                case locTyNote "passToDafny" x of
                    TWord wx -> do
                        let px = ppx <+> text ":=" <+> castAs (mask (shift_right pre (wtot - offset - wx)) offset wx) (text "bv" <> int wx) <> semicolon
                        (pxs,[],annxs) <- getbits (offset + wx) xs
                        return (px $+$ pxs,[],annx++annxs)
                    twx -> genError p $ text "passToDafny parens" <+> ppid twx <+> ppid lv
        getbits 0 ps
    passToDafny'' (PLArray v i) (Left (re,pre)) = do
        (pi,anni) <- pexprToDafny annK IsCt i
        (plv,annlv) <- plvalueToDafny annK IsPrivate lv
        (doc,annpre,annpos) <- passToDafny' p annK (varPlvalue v) (Right $ brackets (castAs pi (text "int") <+> text ":=" <+> pre))
        return (doc,anni++annlv++annpre,annlv++annpos)
    passToDafny'' (PLArray v i) (Right upd) = do
        (pi,anni) <- pexprToDafny annK IsCt i
        (plv,annlv) <- plvalueToDafny annK IsPrivate lv
        (doc,annpre,annpos) <- passToDafny' p annK (varPlvalue v) (Right $ brackets (castAs pi (text "int") <+> text ":=" <+> plv <> upd))
        return (doc,anni++annlv++annpre,annlv++annpos)
    passToDafny'' (PLMem _ v i) (Left (_,pe)) = do
        let tw8 = tyInfoLoc (TWord 8) p
        case infoTy li of
            TWord 8 -> do
                (pv) <- pidentToDafny v
                (pi,anni) <- pexprToDafny annK IsPrivate i
                let writeMem8 = text "WriteMem" <> parens (castAs pv (text "int") <+> text "+" <+> pi <> comma <> pe) <> semicolon
                --leakMode <- getLeakMode
--                modifiesk <- annExpr Nothing False leakMode ModifiesK Set.empty (text "this.memory")
                return (writeMem8,[],anni)
            TWord w -> do
                let tw8 = tyInfoLoc (TWord 8) p
                let n = w `div` 8
                ys <- forM [0..n-1] $ \j -> do
                    (Pident _ yv::Piden) <- lift2 $ mkNewVar ("y"++show j)
                    return (j,Pident tw8 yv)
                (pdefs,annsdef) <- liftM unzip $ forM ys $ \(_,y) -> do
                    py <- pidentToDafny y
                    (pty,anns) <- ptypeToDafny annK (Just y) (locTy y)
                    return (text "var" <+> py <+> text ":" <+> pty <> semicolon,anns)
                (p1,pres1,posts1) <- passToDafny'' (PLParens $ map (varPlvalue . snd) ys) re
                (p2,pres2,posts2) <- liftM unzip3 $ forM ys $ \(j,y) -> do
                    let ij = Pexpr (loc i) $ PEOp2 Add2 i $ intPexpr (toEnum j)
                    py <- pidentToDafny y
                    passToDafny' p annK (Plvalue tw8 $ PLMem Nothing v ij) (Left ([varPexpr y],py))
                return $ (vcat pdefs $+$ p1 $+$ vcat p2,concat annsdef++pres1,posts1++concat pres2++concat posts2)
    passToDafny'' _ _ = genError p $ text "unsupported assignment"
        
plvalueToDafny :: DafnyK m => AnnKind -> CtMode -> Plvalue TyInfo -> DafnyM m (Doc,AnnsDoc)
plvalueToDafny annK ct lv = do
    let mbe = expr_of_lvalue lv
    case mbe of
        Just e -> pexprToDafny annK ct e
        Nothing -> do
            plv <- pp lv
            genError (infoLoc $ loc lv) (text "plvalueToDafny " <+> plv)
        
pexprToDafny :: DafnyK m => AnnKind -> CtMode -> Pexpr TyInfo -> DafnyM m (Doc,AnnsDoc)
pexprToDafny annK ct (Pexpr l e) = pexpr_rToDafny annK ct l e

pexpr_rToDafny :: DafnyK m => AnnKind -> CtMode -> TyInfo -> Pexpr_r TyInfo -> DafnyM m (Doc,AnnsDoc)
pexpr_rToDafny annK ct l e@(PECall n args) = do
    vs <- lift2 $ usedVars e
    pn <- procidenToDafny n
    (pargs,annargs) <- procCallArgsToDafny annK args
    let pcall = pn <> parens (sepBy pargs comma)
    annp <- genDafnyAssumptions annK ct vs pcall l
    return (pcall,annargs++annp)
pexpr_rToDafny annK ct l (PEBool True) = return (text "true",[])
pexpr_rToDafny annK ct l (PEBool False) = return (text "false",[])
pexpr_rToDafny annK ct l (Pcast t e) = cast_pexpr_rToDafny annK ct l t e
pexpr_rToDafny annK ct l (PEInt i) = return (integer i,[])
pexpr_rToDafny annK ct l e@(PEVar v) = do
    vs <- lift2 $ usedVars e
    pv <- pidentToDafny v
    annp <- genDafnyAssumptions annK ct vs pv l
    return (pv,annp)
pexpr_rToDafny annK ct l e@(PEGet n i) = do
    vs <- lift2 $ usedVars e
    (pn,annn) <- pexprToDafny annK ct (varPexpr n)
    (pi,anni) <- pexprToDafny annK IsCt i
    let pse = pn <> brackets (castAs pi $ text "int")
    annp <- genDafnyAssumptions annK ct vs pse l
    return (pse,annn++anni++annp)
pexpr_rToDafny annK ct l (PEFetch t v i) = pefetch_rToDafny annK ct l v i
pexpr_rToDafny annK ct l (PEParens es) = parens_exprToDafny annK ct l es
pexpr_rToDafny annK ct l e@(PEOp1 o e1) = do
    vs <- lift2 $ usedVars e
    peop1ToDafny annK ct l vs o e1
pexpr_rToDafny annK ct l e@(PEOp2 o e1 e2) = do
    vs <- lift2 $ usedVars e
    peop2ToDafny annK ct l vs o e1 e2
pexpr_rToDafny annK ct l le@(LeakExpr e) = do
    (pe,anne) <- pexprToDafny annK IsPrivate e
    leakMode <- getLeakMode
    if leakMode
        then return (text "Leak" <> parens pe,anne)
        else return (text "true",anne)
pexpr_rToDafny annK ct l (ValidExpr [x,e]) = do
    (px,annx) <- pexprToDafny annK IsPrivate x
    (pe,anne) <- pexprToDafny annK IsPrivate e
    let ppx = castAs px (text "int")
    return (text "Valid" <> parens (ppx <+> text "+" <+> pe),annx++anne)
pexpr_rToDafny annK ct l (ValidExpr [x,e1,e2]) = do
    (px,annx) <- pexprToDafny annK IsPrivate x
    (pe1,anne1) <- pexprToDafny annK IsPrivate e1
    (pe2,anne2) <- pexprToDafny annK IsPrivate e2
    let ppx = castAs px (text "int")
    return (text "ValidRange" <> parens (ppx <+> text "+" <+> pe1 <> comma <> ppx <+> text "+" <+> pe2),annx++anne1++anne2)
pexpr_rToDafny annK ct l qe@(QuantifiedExpr q args e) = error "TODO: pexpr_rToDafny quantifier"

pefetch_rToDafny :: DafnyK m => AnnKind -> CtMode -> TyInfo -> Pident TyInfo -> Pexpr TyInfo -> DafnyM m (Doc,AnnsDoc)
pefetch_rToDafny annK ct l@(infoTy -> TWord 8) v i = do
    (pv) <- pidentToDafny v
    (pi,anni) <- pexprToDafny annK ct i
    let readMem8 = text "ReadMem" <> parens (castAs pv (text "int") <+> text "+" <+> pi)
    leakMode <- getLeakMode
--    readsk <- annExpr Nothing False leakMode ReadsK Set.empty (text "this.memory")
    return (readMem8,anni)
pefetch_rToDafny annK ct l@(infoTy -> TWord w) v i = do
    let p = infoLoc l
    let tw8 = tyInfoLoc (TWord 8) p
    let n = w `div` 8
    let mke j = Pexpr tw8 $ PEFetch Nothing v $ Pexpr (loc i) $ PEOp2 Add2 i $ intPexpr (toEnum j)
    let es = map mke [0..n-1]
    pexpr_rToDafny annK ct l $ PEParens es    

hasFunCast (isNumericType -> True) TBool = True
hasFunCast (TInt (Just w)) (TWord w') | w == w' = True
hasFunCast _ _ = False

cast_pexpr_rToDafny :: DafnyK m => AnnKind -> CtMode -> TyInfo -> Ptype TyInfo -> Pexpr TyInfo -> DafnyM m (Doc,AnnsDoc)
cast_pexpr_rToDafny annK ct l t e | hasFunCast t (locTy e) = do
    (pt,annt) <- ptypeToDafny annK Nothing t
    (pet,annet) <- ptypeToDafny annK Nothing (locTy e)
    (pe,anne) <- pexprToDafny annK ct e
    return (pet <> text "_to_" <> pt <> parens pe,anne++annt++annet)
cast_pexpr_rToDafny annK ct l t e = do
    (pe,anne) <- pexprToDafny annK ct e
    (pt,annt) <- ptypeToDafny annK Nothing t
    return (castAs pe pt,anne++annt)

parens_exprToDafny :: DafnyK m => AnnKind -> CtMode -> TyInfo -> [Pexpr TyInfo] -> DafnyM m (Doc,AnnsDoc)
parens_exprToDafny annK ct i [e] = pexprToDafny annK ct e
parens_exprToDafny annK ct i es = add 0 es
    where
    p = infoLoc i
    TWord wtot = infoTyNote "parens_exprToDafny" i
    add offset [] = return (PP.empty,[])
    add offset (e:es) = do
        (pe,anne) <- pexpr_rToDafny annK ct i $ Pcast (TWord wtot) e
        case infoTyNote "parens_exprToDafny" $ loc e of
            TWord we -> do
                (pes,annes) <- add (offset+we) es
                return (shift_left pe we <+> if null es then PP.empty else (char '+') <+> pes,anne++annes)
            twe -> genError p $ text "parens_exprToDafny" <+> ppid twe

procCallArgsToDafny :: DafnyK m => AnnKind -> [Pexpr TyInfo] -> DafnyM m ([Doc],AnnsDoc)
procCallArgsToDafny annK es = do
    (es',annes) <- State.mapAndUnzipM (procCallArgToDafny annK) es
    return (es',concat annes)
    
procCallArgToDafny :: DafnyK m => AnnKind -> Pexpr TyInfo -> DafnyM m (Doc,AnnsDoc)
procCallArgToDafny annK e = pexprToDafny annK IsPrivate e

peop1ToDafny :: DafnyK m => AnnKind -> CtMode -> TyInfo -> Set Piden -> Peop1 -> Pexpr TyInfo -> DafnyM m (Doc,AnnsDoc)
peop1ToDafny annK ct l vs Not1 e1 = nativeop1ToDafny annK ct l vs (char '!' <>) e1

peop2ToDafny :: DafnyK m => AnnKind -> CtMode -> TyInfo -> Set Piden -> Peop2 -> Pexpr TyInfo -> Pexpr TyInfo -> DafnyM m (Doc,AnnsDoc)
peop2ToDafny annK ct l vs Mod2 e1 e2  = nativeop2ToDafny annK ct l vs (fop2 "%") e1 e2
peop2ToDafny annK ct l vs Add2 e1 e2  = nativeop2ToDafny annK ct l vs (fop2 "+") e1 e2
peop2ToDafny annK ct l vs Sub2 e1 e2  = nativeop2ToDafny annK ct l vs (fop2 "-") e1 e2
peop2ToDafny annK ct l vs (Mul2) e1 e2  = nativeop2ToDafny annK ct l vs (fop2 "*") e1 e2
peop2ToDafny annK ct l vs (Eq2) e1 e2   = nativeop2ToDafny annK ct l vs (fop2 "==") e1 e2
peop2ToDafny annK ct l vs (Neq2) e1 e2  = nativeop2ToDafny annK ct l vs (fop2 "!=") e1 e2
peop2ToDafny annK ct l vs (Le2 Unsigned) e1 e2   = nativeop2ToDafny annK ct l vs (fop2 "<=") e1 e2
peop2ToDafny annK ct l vs (Lt2 Unsigned) e1 e2   = nativeop2ToDafny annK ct l vs (fop2 "<") e1 e2
peop2ToDafny annK ct l vs (Ge2 Unsigned) e1 e2   = nativeop2ToDafny annK ct l vs (fop2 ">=") e1 e2
peop2ToDafny annK ct l vs (Gt2 Unsigned) e1 e2   = nativeop2ToDafny annK ct l vs (fop2 ">") e1 e2
peop2ToDafny annK ct l vs (Le2 Signed) e1@(locTy -> TWord w) e2   = do
    -- x <=s y = (y - x) >> 63 == 0
    let fop x y = parens (parens (y <+> text "-" <+> x) <+> text ">>" <+> int (w-1)) <+> text "== 0"
    nativeop2ToDafny annK ct l vs fop e1 e2
peop2ToDafny annK ct l vs (Lt2 Signed) e1@(locTy -> TWord w) e2 = do
    -- x <s y = (x - y) >> 63 == 1
    let fop x y = parens (parens (x <+> text "-" <+> y) <+> text ">>" <+> int (w-1)) <+> text "== 1"
    nativeop2ToDafny annK ct l vs fop e1 e2
peop2ToDafny annK ct l vs (Gt2 Signed) e1@(locTy -> TWord w) e2   = do
    -- x >s y = (y - x) >> 63 == 1
    let fop x y = parens (parens (y <+> text "-" <+> x) <+> text ">>" <+> int (w-1)) <+> text "== 1"
    nativeop2ToDafny annK ct l vs fop e1 e2
peop2ToDafny annK ct l vs (Ge2 Signed) e1@(locTy -> TWord w) e2   = do
    -- x >=s y = (x - y) >> 63 == 0
    let fop x y = parens (parens (x <+> text "-" <+> y) <+> text ">>" <+> int (w-1)) <+> text "== 0"
    nativeop2ToDafny annK ct l vs fop e1 e2
peop2ToDafny annK ct l vs Shl2 e1 e2  = nativeop2ToDafny annK ct l vs (fop2 "<<") e1 e2
peop2ToDafny annK ct l vs (Shr2 Unsigned) e1 e2  = nativeop2ToDafny annK ct l vs (fop2 ">>") e1 e2
peop2ToDafny annK ct l vs And2 e1 e2  = nativeop2ToDafny annK ct l vs (fop2 "&&") e1 e2
peop2ToDafny annK ct l vs Or2 e1 e2   = nativeop2ToDafny annK ct l vs (fop2 "||") e1 e2
peop2ToDafny annK ct l vs BAnd2 e1 e2 = nativeop2ToDafny annK ct l vs (fop2 "&") e1 e2
peop2ToDafny annK ct l vs BOr2 e1 e2  = nativeop2ToDafny annK ct l vs (fop2 "|") e1 e2
peop2ToDafny annK ct l vs BXor2 e1 e2 = nativeop2ToDafny annK ct l vs (fop2 "^") e1 e2
peop2ToDafny annK ct l vs op e1 e2 = do
    po <- pp op
    pe1 <- pp e1
    pe2 <- pp e2
    genError (infoLoc l) $ text "unsupported binary operation: " <+> po <+> pe1 <+> pe2

fop2 o x y = x <+> text o <+> y
castInt e = Pexpr (tyInfo $ TInt Nothing) $ Pcast (TInt Nothing) e

nativeop1ToDafny :: DafnyK m => AnnKind -> CtMode -> TyInfo -> Set Piden -> (Doc -> Doc) -> Pexpr TyInfo -> DafnyM m (Doc,AnnsDoc)
nativeop1ToDafny annK ct l vs fop e1 = do
    (pe1,anne1) <- pexprToDafny annK IsPrivate e1
    let pe = parens $ fop pe1
    annp <- genDafnyAssumptions annK ct vs pe l
    return (pe,anne1++annp)

nativeop2ToDafny :: DafnyK m => AnnKind -> CtMode -> TyInfo -> Set Piden -> (Doc -> Doc -> Doc) -> Pexpr TyInfo -> Pexpr TyInfo -> DafnyM m (Doc,AnnsDoc)
nativeop2ToDafny annK ct l vs fop e1 e2 = do
    (pe1,anne1) <- pexprToDafny annK IsPrivate e1
    (pe2,anne2) <- pexprToDafny annK IsPrivate e2
    let pe = parens $ fop pe1 pe2
    annp <- genDafnyAssumptions annK ct vs pe l
    return (pe,anne1++anne2++annp)

instrAnnsToDafny :: DafnyK m => [StatementAnnotation TyInfo] -> DafnyM m (Doc,AnnsDoc)
instrAnnsToDafny ss = do
    (docs,anns) <- Utils.mapAndUnzipM instrAnnToDafny ss
    return (vcat docs,concat anns)

instrAnnToDafny :: DafnyK m => StatementAnnotation TyInfo -> DafnyM m (Doc,AnnsDoc)
instrAnnToDafny (StatementAnnotation l x) = do
    instrAnn_rToDafny l x

instrAnn_rToDafny :: DafnyK m => TyInfo -> StatementAnnotation_r TyInfo -> DafnyM m (Doc,AnnsDoc)
instrAnn_rToDafny l (AssumeAnn isLeak e) = do
    leakMode <- getLeakMode
    withLeakMode isLeak $ do
        vs <- lift2 $ usedVars e
        (pe,anne) <- pexprToDafny StmtK IsPrivate e
        assume <- annExpr (Just False) isLeak leakMode StmtK vs pe
        addAnnsC StmtKC (anne++assume) PP.empty
instrAnn_rToDafny l (AssertAnn isLeak e) = do
    leakMode <- getLeakMode
    withLeakMode isLeak $ do
        vs <- lift2 $ usedVars e
        (pe,anne) <- pexprToDafny StmtK IsPrivate e
        assert <- annExpr Nothing isLeak leakMode StmtK vs pe
        addAnnsC StmtKC (anne++assert) PP.empty
instrAnn_rToDafny l (EmbedAnn isLeak e) = do
    leakMode <- getLeakMode
    withLeakMode isLeak $ withFreeMode (genFree isLeak leakMode) $ do
        (call,anns) <- pinstrToDafny e
        addAnnsC StmtKC (anns) call
instrAnn_rToDafny l (VarDefAnn ann) = annargToDafny False StmtK IsPrivate ann

annargToDafny :: DafnyK m => Bool -> AnnKind -> CtMode -> Annarg TyInfo -> DafnyM m (Doc,AnnsDoc)
annargToDafny isProcArg annK ct (Annarg ty v mbe) = do
    vs <- lift2 $ usedVars v
    pv <- pidentToDafny v
    (pty,annty) <- ptypeToDafny annK (Just v) (ty)
    annp <- genDafnyAssumptions annK ct vs pv (tyInfo ty)
    let pdecl = pv <+> char ':' <+> pty
    let pvar = if isProcArg then pdecl else text "var" <+> pdecl <> semicolon
    (pass,annsass) <- case mbe of
        Nothing -> return (PP.empty,[])
        Just e -> do
            (pe,anne) <- pexprToDafny StmtK IsPrivate e
            let pass = pv <+> text ":=" <+> pe <> semicolon;
            let (anne',pre) = annLinesC StmtKC anne
            return (pre $+$ pass,anne')
    return (pvar $+$ pass,annp ++ annty ++ annsass)

loopAnnsToDafny :: DafnyK m => [LoopAnnotation TyInfo] -> DafnyM m AnnsDoc
loopAnnsToDafny xs = concatMapM loopAnnToDafny xs

loopAnnToDafny :: DafnyK m => LoopAnnotation TyInfo -> DafnyM m AnnsDoc
loopAnnToDafny (LoopAnnotation l x) = do
    loopAnn_rToDafny l x

loopAnn_rToDafny :: DafnyK m => TyInfo -> LoopAnnotation_r TyInfo -> DafnyM m AnnsDoc
loopAnn_rToDafny p (LDecreasesAnn isLeak e) = do
    leakMode <- getLeakMode
    withLeakMode isLeak $ do
        vs <- lift2 $ usedVars e
        (pe,anne) <- pexprToDafny InvariantK IsPrivate e
        decrease <- annExpr Nothing isLeak leakMode DecreaseK vs pe
        return $ anne ++ decrease
loopAnn_rToDafny p (LInvariantAnn isFree isLeak e) = do
    leakMode <- getLeakMode
    withLeakMode isLeak $ do
        vs <- lift2 $ usedVars e
        (pe,anne) <- pexprToDafny InvariantK IsPrivate e
        inv <- annExpr (boolIsFree isFree) isLeak leakMode InvariantK vs pe
        return $ anne ++ inv

procAnnsToDafny :: DafnyK m => [ProcedureAnnotation TyInfo] -> DafnyM m AnnsDoc
procAnnsToDafny xs = concatMapM (procAnnToDafny) xs

procAnnToDafny :: DafnyK m => ProcedureAnnotation TyInfo -> DafnyM m AnnsDoc
procAnnToDafny (ProcedureAnnotation l x) = procAnn_rToDafny l x

procAnn_rToDafny :: DafnyK m => TyInfo -> ProcedureAnnotation_r TyInfo -> DafnyM m AnnsDoc
procAnn_rToDafny p (RequiresAnn isFree isLeak e) = do
    leakMode <- getLeakMode
    withLeakMode isLeak $ do
        vs <- lift2 $ usedVars e
        (pe,anne) <- pexprToDafny RequireK IsPrivate e
        req <- annExpr (boolIsFree isFree) isLeak leakMode RequireK vs pe
        return $ anne ++ req
procAnn_rToDafny p (EnsuresAnn isFree isLeak e) = do
    leakMode <- getLeakMode
    withLeakMode isLeak $ do
        vs <- lift2 $ usedVars e
        (pe,anne) <- pexprToDafny EnsureK IsPrivate e
        ens <- annExpr (boolIsFree isFree) isLeak leakMode EnsureK vs pe
        return $ anne ++ ens
procAnn_rToDafny p (PDecreasesAnn e) = do
    leakMode <- getLeakMode
    vs <- lift2 $ usedVars e
    (pe,anne) <- pexprToDafny EnsureK IsPrivate e
    decr <- annExpr Nothing False leakMode DecreaseK vs pe
    return $ anne ++ decr

procidenToDafny :: DafnyK m => Pident info -> DafnyM m Doc
procidenToDafny v = do
    pv <- pp v
    return $ pv <> text "ShadowProc"

pidentToDafny :: DafnyK m => Pident info -> DafnyM m Doc
pidentToDafny v = pp v

pidentToDafnyId :: Pident info -> String
pidentToDafnyId (Pident _ v) = v

ptypeToDafny :: DafnyK m => AnnKind -> Maybe (Pident TyInfo) -> Ptype TyInfo -> DafnyM m (Doc,AnnsDoc)
ptypeToDafny annK v TBool = return (text "bool",[])
ptypeToDafny annK v (TInt w) = do
    let pw = maybe PP.empty PP.int w
    return (text "int" <> pw,[])
ptypeToDafny annK v (TWord sz) = return (text "bv" <> int sz,[])
ptypeToDafny annK v (TArray sz e) = do
    (pe,anne) <- pexprToDafny annK IsCt e
    let pty = text "seq" <> abrackets (text "bv" <> int sz)
    anns <- case v of
        Nothing -> return []
        Just v -> do
            pv <- pidentToDafny v
            leakMode <- getLeakMode
            annExpr (Just False) False leakMode annK (Set.singleton $ funit v) (dafnySize pv <+> text "==" <+> pe)
    return (pty,anne++anns)

dafnySize :: Doc -> Doc
dafnySize x = char '|' <> x <> char '|'

genDafnyAssumptions :: DafnyK m => AnnKind -> CtMode -> Set Piden -> Doc -> TyInfo -> DafnyM m AnnsDoc
genDafnyAssumptions annK ct vs pv tv = do
    let p = infoLoc tv
    let ty = infoTyNote "genDafnyAssumptions" tv
    anns1 <- genDafnyArrays p annK vs pv ty
    anns2 <- genDafnyPublics p annK ct vs pv ty
    return $ anns1++anns2

genDafnyArrays :: DafnyK m => Position -> AnnKind -> Set Piden -> Doc -> Ptype TyInfo -> DafnyM m AnnsDoc
genDafnyArrays l annK vs pv tv = case tv of
    TArray _ sz -> do
        (pe,anns) <- pexprToDafny annK IsPublic sz
        annsz <- annExpr (Just False) False False annK vs $ dafnySize pv <+> text "==" <+> pe
        return $ anns++annsz
    otherwise -> return []

publicAnn :: AnnKind -> String
publicAnn StmtK      = "PublicMid"
publicAnn InvariantK = "PublicMid"
publicAnn EnsureK    = "PublicOut"
publicAnn RequireK   = "PublicIn"
publicAnn NoK        = "PublicMid"

genDafnyPublics :: DafnyK m => Position -> AnnKind -> CtMode -> Set Piden -> Doc -> (Ptype TyInfo) -> DafnyM m AnnsDoc
genDafnyPublics l annK ct vs pv tv = whenLeakMode $ do
    d <- getInDecl
    if isLeakageInDecl d
        then do
            let publick = publicAnn annK
            -- generate public annotations
            let genPublic IsPrivate t = return []
                genPublic IsPublic t = annExpr (Just False) True True annK vs (text publick <> parens pv)
                genPublic IsCt t = annExpr Nothing True True annK vs (text publick <> parens pv)
            -- only generate public sizes for private types
            let genPublicSize IsPrivate t@(TArray {}) = do
                    let psize = dafnySize pv
                    annExpr (Just False) True True annK vs (text publick <> parens psize)
                genPublicSize ct t = return []
            ispublic <- genPublic ct tv
            publicsize <- genPublicSize ct tv
            return $ ispublic ++ publicsize
        else return []

isLeakageInDecl :: Maybe DafnyId -> Bool
isLeakageInDecl Nothing = False
isLeakageInDecl (Just _) = True

-- * State

type DafnyK m = (MonadIO m,GenVar Piden m)

type DafnyM m = StateT DafnySt (ExceptT JasminError m)

data DafnySt = DafnySt {
      leakageMode :: Bool -- True=leakage, False=correctness
    , inDecl :: Maybe DafnyId -- decl id
    , assumptions :: AnnsDoc
    , freeMode :: FreeMode
--    , consts :: Map Piden Doc -- global constant variables
    }

data CtMode = IsCt | IsPublic | IsPrivate
  deriving (Data,Typeable,Show,Eq,Ord)

data FreeMode = KeepF | FreeF | DeleteF
  deriving (Data,Typeable,Show,Eq,Ord)

type DafnyId = String

type AnnsDoc = [AnnDoc]
-- (kind,isFree (Nothing=not free,Just False=not inlined,Just True=inlined),used variables,dafny expression, is leakage expr)
type AnnDoc = (AnnKind,Maybe Bool,Set Piden,Doc,Bool)

data AnnKind = StmtK | EnsureK | RequireK | InvariantK | DecreaseK | NoK | ReadsK | ModifiesK | AxiomK
  deriving (Show,Eq)
instance Monad m => PP m AnnKind where
    pp = return . text . show

data AnnKindClass = ExprKC | StmtKC | LoopKC | ProcKC | GlobalKC
  deriving (Eq,Ord,Show)

-- * Utilities

annKindClass :: AnnKind -> AnnKindClass
annKindClass EnsureK = ProcKC
annKindClass RequireK = ProcKC
annKindClass StmtK = StmtKC
annKindClass InvariantK = LoopKC
annKindClass DecreaseK = LoopKC
annKindClass ReadsK = ProcKC
annKindClass ModifiesK = ProcKC
annKindClass NoK = ExprKC
annKindClass AxiomK = GlobalKC

annLine :: AnnDoc -> Doc
annLine (EnsureK,isFree,vs,x,isLeak) = ppIsFree isFree (text "ensures") (ppLeakageFun isLeak x) <> semicolon
annLine (RequireK,isFree,vs,x,isLeak) = ppIsFree isFree (text "requires") (ppLeakageFun isLeak x) <> semicolon
annLine (StmtK,Just _,vs,x,isLeak) = text "assume" <+> ppLeakageAtt isLeak <+> x <> semicolon
annLine (StmtK,Nothing,vs,x,isLeak) = text "assert" <+> ppLeakageAtt isLeak <+> x <> semicolon
annLine (InvariantK,isFree,vs,x,isLeak) = ppIsFree isFree (text "invariant") (ppLeakageFun isLeak x) <> semicolon
annLine (DecreaseK,isFree,vs,x,isLeak) = text "decreases" <+> x <> semicolon
annLine (ReadsK,_,vs,x,isLeak) = text "reads" <+> x <> semicolon
annLine (ModifiesK,_,vs,x,isLeak) = text "modifies" <+> x <> semicolon
annLine (NoK,isFree,vs,x,isLeak) = ppIsFree (fmap (const True) isFree) PP.empty x
annLine (AxiomK,_,_,_,_) = PP.empty

chgAnnK :: AnnKind -> AnnDoc -> AnnDoc
chgAnnK annK (_,isFree,vs,x,isLeak) = (annK,isFree,vs,x,isLeak)

annLines :: AnnKind -> AnnsDoc -> (AnnsDoc,Doc)
annLines c anns = annLinesC (annKindClass c) anns

-- the input boolean determines if we are in a procedure context or not
-- if not in a procedure context, we postpone procedure annotations
annLinesC :: AnnKindClass -> AnnsDoc -> (AnnsDoc,Doc)
annLinesC cl anns = (anns',vcat $ map annLine xs)
    where (anns',xs) = List.partition ((>cl) . annKindClass . fst5) anns

isReadsModifiesK ReadsK = True
isReadsModifiesK ModifiesK = True
isReadsModifiesK _ = False

annLinesProcC :: Bool -> AnnsDoc -> (Doc,Doc)
annLinesProcC isMethod anns = (l,r)
    where
    (frames,anns') = List.partition (isReadsModifiesK . fst5) anns
    (reads,modifies) = List.partition ((==ReadsK) . fst5) frames
    anns'' = List.nub anns'
    reads' = Set.fromList $ map fou5 reads
    modifies' = Set.fromList $ map fou5 modifies
    readk = if isMethod then [] else case Set.toList reads' of
                [] -> []
                xs -> [(ReadsK,Just False,Set.empty,sepBy xs comma,False)]
    modifyk = case Set.toList modifies' of
                [] -> []
                xs -> [(ModifiesK,Just False,Set.empty,sepBy xs comma,False)]
    ([],r) = annLinesC ProcKC (anns'')
    ([],l) = annLinesC ProcKC (readk++modifyk)

getLeakMode :: DafnyK m => DafnyM m Bool
getLeakMode = State.gets leakageMode

whenLeakMode :: (Monoid x,DafnyK m) => DafnyM m x -> DafnyM m x
whenLeakMode m = do
    leakMode <- getLeakMode
    if leakMode then m else return mempty

genFree :: Bool -> Bool -> FreeMode
genFree isLeak leakMode = case (leakMode,isLeak) of
    (True,True) -> KeepF
    (True,False) -> FreeF
    (False,True) -> DeleteF
    (False,False) -> KeepF

appendFreeMode :: FreeMode -> FreeMode -> FreeMode
appendFreeMode x y = max x y

withFreeMode :: DafnyK m => FreeMode -> DafnyM m a -> DafnyM m a
withFreeMode isFree m = do
    old <- State.gets freeMode
    State.modify $ \e -> e { freeMode = isFree }
    x <- m
    State.modify $ \e -> e { freeMode = old }
    return x
    
addFreeMode :: DafnyK m => FreeMode -> DafnyM m a -> DafnyM m a
addFreeMode isFree m = do
    old <- State.gets freeMode
    State.modify $ \e -> e { freeMode = appendFreeMode old isFree }
    x <- m
    State.modify $ \e -> e { freeMode = old }
    return x

getAssumptions :: DafnyK m => DafnyM m AnnsDoc
getAssumptions = State.gets assumptions

addAssumptions :: DafnyK m => DafnyM m AnnsDoc -> DafnyM m AnnsDoc
addAssumptions m = do
    ass <- getAssumptions
    anns <- m
    State.modify $ \env -> env { assumptions = assumptions env ++ anns }
    return anns

withAssumptions :: DafnyK m => DafnyM m a -> DafnyM m a
withAssumptions m = do
    anns <- getAssumptions
    x <- m
    State.modify $ \env -> env { assumptions = anns }
    return x

resetAssumptions :: DafnyK m => DafnyM m a -> DafnyM m a
resetAssumptions m = do
    anns <- getAssumptions
    inDecl <- getInDecl
    State.modify $ \env -> env { assumptions = keepaxioms (isJust inDecl) anns }
    x <- m
    State.modify $ \env -> env { assumptions = anns }
    return x
  where
    keepaxioms :: Bool -> AnnsDoc -> AnnsDoc
    keepaxioms inDecl [] = []
    keepaxioms True ((AxiomK,x2,x3,x4,x5):xs) = (RequireK,x2,x3,x4,x5) : keepaxioms True xs
    keepaxioms False ((AxiomK,x2,x3,x4,x5):xs) = (AxiomK,x2,x3,x4,x5) : keepaxioms False xs
    keepaxioms inDecl (x:xs) = keepaxioms inDecl xs

annExpr :: DafnyK m => Maybe Bool -> Bool -> Bool -> AnnKind -> Set Piden -> Doc -> DafnyM m AnnsDoc
annExpr isFree isLeak leakMode annK vs e = addAssumptions $ do
    mode <- State.gets freeMode
    case (appendFreeMode mode $ genFree isLeak leakMode) of
        DeleteF -> return []
        KeepF -> return [(annK,isFree,vs,e,isLeak)]
        FreeF -> return [(annK,Just False,vs,e,isLeak)]

addAnnsC :: DafnyK m => AnnKindClass -> AnnsDoc -> Doc -> DafnyM m (Doc,AnnsDoc)
addAnnsC c anns doc = do
    let (anns1,anns2) = annLinesC c anns
    return (anns2 $+$ doc,anns1)

addAnnsCond :: Doc -> AnnsDoc -> AnnsDoc
addAnnsCond c anns = map add anns
    where
    add ann@(isReadsModifiesK -> True,_,_,_,_) = ann
    add (x,y,z,w,q) = (x,y,z,c <+> text "==>" <+> parens w,q)

getInDecl :: DafnyK m => DafnyM m (Maybe DafnyId)
getInDecl = State.gets inDecl
    
insideDecl :: DafnyK m => DafnyId -> DafnyM m x -> DafnyM m x
insideDecl did m = do
    o <- getInDecl
    State.modify $ \env -> env { inDecl = Just did }
    lmode <- State.gets leakageMode
    let fmode = KeepF
    x <- addFreeMode fmode m
    State.modify $ \env -> env { inDecl = o }
    return x

ppIsFree :: Maybe Bool -> Doc -> Doc -> Doc
ppIsFree Nothing c d = c <+> d
ppIsFree (Just False) c d = ppFree True (c <+> d)
ppIsFree (Just True) c d = c <+> (ppFreeFun True d)

ppLeakageAtt :: Bool -> Doc
ppLeakageAtt False = PP.empty
ppLeakageAtt True = text "{:leakage}"

ppLeakageFun :: Bool -> Doc -> Doc
ppLeakageFun False d = d
ppLeakageFun True d = text "Leakage" <> parens d

ppFreeFun :: Bool -> Doc -> Doc
ppFreeFun False d = d
ppFreeFun True d = text "Free" <> parens d

unfreeAnn :: AnnDoc -> AnnDoc
unfreeAnn (k,isFree,vs,x,isLeak) = (k,fmap (const True) isFree,vs,x,isLeak)

unfreeAnns :: AnnsDoc -> AnnsDoc
unfreeAnns = map unfreeAnn

decClassToDafny :: DafnyK m => Bool -> DecClass -> DafnyM m Doc
decClassToDafny isMethod (DecClass rs ws mem) = do
    let ppVar (v@(Pident _ n),(t,_)) = pidentToDafny $ Pident (tyInfo t) n
    prs <- mapM ppVar $ Map.toList (Map.filter snd $ fst rs)
    pws <- mapM ppVar $ Map.toList (Map.filter snd $ fst ws)
    let pr = if null prs then PP.empty else if isMethod then PP.empty else text "reads" <+> sepBy prs space
    let pw = if null pws then PP.empty else text "modifies" <+> sepBy pws space
    pmem <- decMemToDafny isMethod mem
    return $ pr $+$ pw $+$ pmem

decMemToDafny :: DafnyK m => Bool -> DecMem -> DafnyM m Doc
decMemToDafny isMethod NoMem = return PP.empty
decMemToDafny isMethod ReadMem = if isMethod
    then return PP.empty else return $ text "reads" <+> text "this.memory" <> semicolon
decMemToDafny isMethod WriteMem = return $ text "modifies" <+> text "this.memory" <> semicolon 

propagateDafnyAssumptions :: DafnyK m => Position -> AnnKind -> DecClass -> DafnyM m AnnsDoc
propagateDafnyAssumptions p annK (DecClass (rs,_) (ws,_) _) = do
    let untouched = Map.toList $ Map.map fst $ Map.difference rs ws
    frames <- genDafnyFrames p annK untouched
    invs <- genDafnyInvariantAssumptions p annK untouched
    return (frames++invs)

-- propagate untouched asumptions into post-conditions or invariants
genDafnyInvariantAssumptions :: DafnyK m => Position -> AnnKind -> [(Piden,Ptype TyInfo)] -> DafnyM m AnnsDoc
genDafnyInvariantAssumptions p annK xs = do
    anns <- getAssumptions
    let anns' = filter isUntouched anns
    concatMapM propagate anns'
  where
    isUntouched (k,_,vs,_,_) = Set.null (Set.difference vs (Set.fromList $ map fst xs))
                            && List.elem k [StmtK,EnsureK,RequireK,InvariantK]
    propagate (_,_,vs,pe,isLeak) = annExpr (Just False) isLeak isLeak annK vs pe

-- generate a frame condition for every untouched variable
genDafnyFrames :: DafnyK m => Position -> AnnKind -> [(Piden,Ptype TyInfo)] -> DafnyM m AnnsDoc
genDafnyFrames p annK xs = concatMapM (genDafnyFrame p annK) xs
    where
    genDafnyFrame p annK (v@(Pident () n),t) = do
        pv <- pidentToDafny $ Pident (tyInfoLoc t p) n
        annExpr (Just False) False False annK (Set.singleton v) (pv <+> text "==" <+> text "old" <> parens pv)

-- copy dafny assumptions for variable assignments
copyDafnyAssumptions :: DafnyK m => Position -> Pident TyInfo -> Pident TyInfo -> DafnyM m ()
copyDafnyAssumptions p v v' = do
    anns <- getAssumptions
    let anns' = foldr chgVar [] anns
    State.modify $ \env -> env { assumptions = assumptions env ++ anns' }
  where
    chgVar (annk,isFree,vs,doc,isLeak) xs = if Set.member (funit v) vs
        then (annk,isFree,Set.insert (funit v') $ Set.delete (funit v) vs,doc,isLeak) : xs
        else xs

dropAssumptions :: DafnyK m => Set Piden -> DafnyM m a -> DafnyM m a
dropAssumptions xs m = do
    let aux (_,_,vs,_,_) = Set.null $ Set.intersection vs xs
    State.modify $ \env -> env { assumptions = filter aux $ assumptions env }
    m

--removeDecClassConsts :: DafnyK m => DecClass -> DafnyM m DecClass
--removeDecClassConsts ((rs,isg1),(ws,isg2)) = do
--    ks <- State.gets consts
--    let rs' = Map.filterWithKey (\k v -> isNothing $ Map.lookup k ks) rs
--    let ws' = Map.filterWithKey (\k v -> isNothing $ Map.lookup k ks) ws
--    return ((rs',isg1),(ws',isg2))

shift_left x 0 = x
shift_left x n = parens $ x <+> text "<<" <+> int n
shift_right x 0 = x
shift_right x n = parens $ x <+> text ">>" <+> int n

castAs doc t = parens (parens doc <+> text "as" <+> t)

boolIsFree :: Bool -> Maybe Bool
boolIsFree False = Nothing
boolIsFree True = Just False

withLeakMode :: DafnyK m => Bool -> DafnyM m x -> DafnyM m x
withLeakMode b m = do
    o <- getLeakMode
    State.modify $ \env -> env { leakageMode = o && b }
    x <- m
    State.modify $ \env -> env { leakageMode = o }
    return x

