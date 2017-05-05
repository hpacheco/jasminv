{-# LANGUAGE DoAndIfThenElse, ScopedTypeVariables, FlexibleContexts, ViewPatterns, ConstraintKinds, FlexibleInstances, MultiParamTypeClasses, DeriveDataTypeable, DeriveGeneric #-}

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

toDafny :: DafnyK m => FilePath -> Bool -> Bool -> Pprogram TyInfo -> m (Either JasminError Doc)
toDafny prelude leakMode noDafnyModules prog = runExceptT $ flip State.evalStateT (DafnySt leakMode Nothing [] KeepF Map.empty) $ do
    dfy <- liftIO $ readFile prelude
    let pdfy = if noDafnyModules
        then text dfy
        else text "module" <+> text "prelude" <+> vbraces (text dfy)
    let pname = dropExtension $ takeFileName $ posFileName $ infoLoc $ pprogramLoc prog
    pprog <- pprogramtoDafny prog
    let pimport = text "import opened prelude"
    let pcode = if noDafnyModules
        then pprog
        else text "module" <+> text pname <+> vbraces (pimport $+$ pprog)
    return $ pdfy $+$ pcode

pprogramtoDafny :: DafnyK m => Pprogram TyInfo -> DafnyM m Doc
pprogramtoDafny prog = do
    pprog <- mapM pitemToDafny prog
    return $ vcat pprog
    --return $ text "class" $+$ vbrackets pprog

pitemToDafny :: DafnyK m => Pitem TyInfo -> DafnyM m Doc
pitemToDafny (PFundef f) = pfundefToDafny f
pitemToDafny (PParam p) = pparamToDafny p

pfundefToDafny :: DafnyK m => Pfundef TyInfo -> DafnyM m Doc
pfundefToDafny def@(Pfundef pn pargs pret (Pfunbody pbvars pbinstrs pbret) info) = insideDecl did $ resetAssumptions $ do
    let p = infoLoc info
    ppn <- pidentToDafny pn
    (ppargs,parganns) <- procedureArgsToDafny IsPrivate False pargs
    (pbvars',pbinstrs',ssargs) <- newDafnyArgs p pargs
    (newpbinstrs,newpbret) <- lift2 $ substVars dontStop ssargs False Map.empty (pbinstrs,pbret)
    (pret,pretanns) <- case pret of
        Nothing -> return (PP.empty,[])
        Just results -> do
            tvs <- forM results $ \t -> do
                vret::Maybe Piden <- lift2 $ liftM Just $ mkVar "result" >>= newVar
                return (t,fmap (fconst $ pstotypeTyInfo t) vret)
            (pret,pretanns) <- procedureArgsToDafny IsPrivate True tvs
            return (text "returns" <+> pret,pretanns)
    let cl = infoDecClass info
    pcl <- decClassToDafny cl
    (pbody1,annb1) <- pbodyargsToDafny IsPrivate (pbvars++pbvars')
    (pbody2,annb2) <- pblock_rToDafny info (pbinstrs'++newpbinstrs)
    (pbody3) <- case newpbret of
        Nothing -> return (PP.empty)
        Just erets -> do
            (perets) <- mapM (pidentToDafny) erets
            return (text "return" <+> sepBy perets comma <> semicolon)
    let tag = text "method"
    let anns' = parganns ++ pretanns ++ annb1 ++ annb2
    annframes <- propagateDafnyAssumptions p EnsureK cl
    return $ (tag <+> ppn <+> ppargs <+> pret $+$ pcl $+$ annLinesProcC annframes $+$ annLinesProcC anns' $+$ vbraces (pbody1 $+$ pbody2 $+$ pbody3))
  where
    did = pidentToDafnyId pn

-- to work around the fact that Dafny does not allow inputs to be mutated
newDafnyArgs :: DafnyK m => Position -> [Parg TyInfo] -> DafnyM m ([Pbodyarg TyInfo],[Pinstr TyInfo],SubstVars Piden)
newDafnyArgs l xs = do
    (as,is,ss) <- Utils.mapAndUnzip3M (newDafnyArg l) xs
    return (concat as,concat is,mconcat ss)

newDafnyArg :: DafnyK m => Position -> Parg TyInfo -> DafnyM m ([Pbodyarg TyInfo],[Pinstr TyInfo],SubstVars Piden)
newDafnyArg l (_,Nothing) = return ([],[],mempty)
newDafnyArg l (stoty,Just oldv@(Pident i oldn)) = do
    newv@(Pident _ newn)::Piden <- lift2 $ newVar (funit oldv)
    let newv = Pident i newn
    let barg = (stoty,newv)
    let rs = (Map.singleton (funit oldv) (infoTy i,False),False)
    let ws = (Map.singleton (funit newv) (infoTy i,False),False)
    let cl = (rs,ws)
    let bass = Pinstr (decInfoLoc cl l) $ PIAssign [varPlvalue newv] RawEq (varPexpr oldv) Nothing
    copyDafnyAssumptions l oldv newv
    let bss = substVarsFromList [(funit oldv,funit newv)]
    return ([barg],[bass],bss)

pbodyargsToDafny :: DafnyK m => CtMode -> [Pbodyarg TyInfo] -> DafnyM m (Doc,AnnsDoc)
pbodyargsToDafny ct xs = do
    (ys,anns) <- State.mapAndUnzipM (pbodyargToDafny ct) xs
    return (vcat ys,concat anns)

pbodyargToDafny :: DafnyK m => CtMode -> Pbodyarg TyInfo -> DafnyM m (Doc,AnnsDoc)
pbodyargToDafny ct (t,v) = do
    (parg,anns) <- pargToDafny False StmtK ct (t,Just v)
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
pargToDafny isProcArg annK ct (ty,Nothing) = ptypeToDafny annK Nothing (snd ty)
pargToDafny isProcArg annK ct (ty,Just v) = do
    vs <- lift2 $ usedVars v
    pv <- pidentToDafny v
    (pty,annty) <- ptypeToDafny annK (Just v) (snd ty)
    annp <- genDafnyAssumptions annK ct vs pv (pstotypeTyInfo ty)
    let pdecl = pv <+> char ':' <+> pty
    let pvar = if isProcArg then pdecl else text "var" <+> pdecl <> semicolon
    return (pvar,annp ++ annty)

pparamToDafny :: DafnyK m => Pparam TyInfo -> DafnyM m Doc
pparamToDafny (Pparam ty v e) = resetAssumptions $ do
    (pe,anne) <- pexprToDafny AxiomK IsPublic e
    State.modify $ \env -> env { consts = Map.insert (funit v) pe (consts env) }
    return PP.empty
--pparamToDafny (Pparam ty v e) = resetAssumptions $ do
--    pv <- pidentToDafny v
--    (pty,annty) <- ptypeToDafny AxiomK (Just v) ty
--    (pe,anne) <- pexprToDafny AxiomK IsPublic e
--    return (text "var" <+> pv <+> char ':' <+> pty <+> text ":=" <+> pe)

pblockToDafny :: DafnyK m => Pblock TyInfo -> DafnyM m (Doc,AnnsDoc)
pblockToDafny (Pblock l x) = pblock_rToDafny l x

pblock_rToDafny :: DafnyK m => TyInfo -> [Pinstr TyInfo] -> DafnyM m (Doc,AnnsDoc)
pblock_rToDafny l xs = do
    (ys,anns) <- pinstrsToDafny xs
    return (vbraces ys,anns)

pinstrsToDafny :: DafnyK m => [Pinstr TyInfo] -> DafnyM m (Doc,AnnsDoc)
pinstrsToDafny xs = do
    (ys,anns) <- State.mapAndUnzipM pinstrToDafny xs
    return (vcat ys,concat anns)

pinstrToDafny :: DafnyK m => Pinstr TyInfo -> DafnyM m (Doc,AnnsDoc)
pinstrToDafny (Pinstr l i) = pinstr_rToDafny l i
    
pinstr_rToDafny :: DafnyK m => TyInfo -> Pinstr_r TyInfo -> DafnyM m (Doc,AnnsDoc)
pinstr_rToDafny l (PIIf c s1 s2) = pif_rToDafny True l c s1 s2
pinstr_rToDafny l (PIFor v dir from to (Pblock lb is)) = do
    let p = infoLoc l
    let vty = locTy v
    (pass,ann2) <- pinstr_rToDafny l $ PIAssign [varPlvalue v] RawEq from Nothing 
    let lb' = lb { infoDecClass' = let ((rs,isg1),(ws,isg2)) = infoDecClass lb in Just ((Map.insert (funit v) (vty,False) rs,isg1),(Map.insert (funit v) (vty,True) ws,isg2)) }
    let (op2,cmp2) = case dir of { Up -> (Add2,Le2); Down -> (Sub2,Ge2) }
    let clinc = ((Map.singleton (funit v) (vty,False),False),(Map.singleton (funit v) (vty,False),False))
    let inc = Pinstr (decInfoLoc clinc p) $ PIAssign [varPlvalue v] RawEq (Pexpr (loc v) $ PEOp2 op2 (varPexpr v) (Pexpr (loc v) $ PEInt 1)) Nothing
    let b' = Pblock lb' $ is ++ [inc]
    let cl = infoDecClass $ loc b'
    leakMode <- getLeakMode
    pfrom <- pp from
    pto <- pp to
    fromtovs <- lift2 $ usedVars (from,to)
    pv <- pidentToDafny v
    anninv <- annExpr Nothing False leakMode InvariantK (Set.insert (funit v) fromtovs) (parens (pfrom <+> text "<=" <+> pv) <+> text "&&" <+> parens (pv <+> text "<=" <+> pto <+> text "+1"))    
    annframes <- propagateDafnyAssumptions p InvariantK cl
    (pe,anne) <- pexpr_rToDafny InvariantK IsCt (tyInfoLoc TBool p) $ PEOp2 cmp2 (varPexpr v) to
    (ps,annb) <- pblockToDafny b'
    (pw,anns) <- addAnnsC StmtKC (anne++annb) $ vbraces ps
    let while = text "while" <+> pe $+$ annLinesProcC (anninv ++ annframes) $+$ pw
    return (pass $+$ while,ann2++anns)
pinstr_rToDafny l (PIWhile Nothing e (Just s)) = do
    let p = infoLoc l
    let cl = infoDecClass $ loc s
    annframes <- propagateDafnyAssumptions p InvariantK cl
    (pe,anne) <- pexprToDafny InvariantK IsCt e
    (ps,ann2) <- pblockToDafny s
    (pw,anns) <- addAnnsC StmtKC (anne++ann2) $ vbraces ps
    return (text "while" <+> pe $+$ annLinesProcC annframes $+$ pw,anns)
pinstr_rToDafny l (PIWhile (Just s) e Nothing) = do
    pblockToDafny s
    pinstr_rToDafny l (PIWhile Nothing e (Just s))
pinstr_rToDafny l (PIAssign ls o e (Just c)) = pif_rToDafny False l c (pblockTy [Pinstr l $ PIAssign ls o e Nothing]) Nothing
pinstr_rToDafny l (PIAssign ls RawEq re Nothing) = do
    (pre,pres) <- pexprToDafny StmtK IsPrivate re
    lvs <- lift2 $ usedVars ls    
    (pass,post) <- dropAssumptions lvs $ passToDafny (infoLoc l) StmtK ls (Just [re],pre)
    let (anns1,pres') = annLinesC StmtKC pres
    let (anns2,post') = annLinesC StmtKC post
    return (pres' $+$ pass $+$ post',anns1++anns2)
pinstr_rToDafny l (Copn ls Oaddcarry es) = carry_opToDafny (infoLoc l) ls Oaddcarry es
pinstr_rToDafny l (Copn ls Osubcarry es) = carry_opToDafny (infoLoc l) ls Osubcarry es
pinstr_rToDafny l (Ccall ls n args) = do
    pn <- pidentToDafny n
    lvs <- lift2 $ usedVars ls
    (pargs,pres) <- procCallArgsToDafny StmtK args
    let pcall = pn <> parens (sepBy pargs comma)
    (pass,post) <- dropAssumptions lvs $ passToDafny (infoLoc l) StmtK ls (Nothing,pcall)
    let (anns1,pres') = annLinesC StmtKC pres
    let (anns2,post') = annLinesC StmtKC post
    return (pres' $+$ pass $+$ post',anns1++anns2)

carry_opToDafny :: DafnyK m => Position -> [Plvalue TyInfo] -> Op -> [Pexpr TyInfo] -> DafnyM m (Doc,AnnsDoc)
carry_opToDafny p ls op es@(e1:_) = do
    let pop = case op of
                Oaddcarry -> text "addcarry"
                Osubcarry -> text "subcarry"
    let pt = case (locTy e1) of
                TWord w -> PP.int (wordSize w)
    (pes,concat -> pres) <- State.mapAndUnzipM (pexprToDafny StmtK IsPrivate) es
    let pe = pop <> pt <> parens (sepBy pes comma)
    let (annspres,pres') = annLinesC StmtKC pres
    lvs <- lift2 $ usedVars ls
    dropAssumptions lvs $ do
        (pass,post) <- passToDafny p StmtK ls (Nothing,pe)
        let (annspost,post') = annLinesC StmtKC post
        return $ (pass,annspres++annspost)

pif_rToDafny :: DafnyK m => Bool -> TyInfo -> Pexpr TyInfo -> Pblock TyInfo -> Maybe (Pblock TyInfo) -> DafnyM m (Doc,AnnsDoc)
pif_rToDafny isCt l c s1 s2 = do 
    let ctmode = if isCt then IsCt else IsPrivate
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

passToDafny :: DafnyK m => Position -> AnnKind -> [Plvalue TyInfo] -> (Maybe [Pexpr TyInfo],Doc) -> DafnyM m (Doc,AnnsDoc)
passToDafny p annK lvs@(arePLVars -> True) e = do
        (plvs,annlvs) <- State.mapAndUnzipM (plvalueToDafny annK IsPrivate) lvs
        pass <- assign p (zip lvs plvs) e
        return (pass,concat annlvs)

passToDafny p annK ls e = do
        ls' <- forM ls $ \l -> do
            Pident () n <- lift2 $ mkVar "aux" >>= newVar
            return $ Pident (loc l) n
        (pdefs,annsdefs) <- State.mapAndUnzipM (\l -> pargToDafny False StmtK IsPrivate (infoStoty $ loc l,Just l)) ls'        
        ppls' <- mapM pidentToDafny ls'
        asse <- assign p (zip (map varPlvalue ls') ppls') e
        (assls,anns) <- State.mapAndUnzipM (uncurry (passToDafny' p annK)) (zip ls $ map Left $ zip (map (\x -> [varPexpr x]) ls') ppls')
        return (vcat pdefs $+$ asse $+$ vcat assls,concat annsdefs ++ concat anns)

assign :: DafnyK m => Position -> [(Plvalue TyInfo,Doc)] -> (Maybe [Pexpr TyInfo],Doc) -> DafnyM m Doc
assign p xs (mb,pe) = do
    let (vxs,pxs) = unzip xs
    let copy (Plvalue _ (PLVar v)) (Pexpr _ (PEVar v')) = copyDafnyAssumptions p v v'
        copy v e = return ()
    case mb of
        Nothing -> return ()
        Just ys -> when (length xs == length ys) $ mapM_ (uncurry copy) (zip vxs ys)
    return $ sepBy pxs comma <+> text ":=" <+> pe <> semicolon

-- left = expression, right = update
passToDafny' :: DafnyK m => Position -> AnnKind -> Plvalue TyInfo -> Either ([Pexpr TyInfo],Doc) Doc -> DafnyM m (Doc,AnnsDoc)
passToDafny' p annK lv@(Plvalue _ PLIgnore) _ = return (PP.empty,[])
passToDafny' p annK lv@(Plvalue _ (PLVar v)) (Left (re,pre)) = do
    (plv,annlv) <- plvalueToDafny annK IsPrivate lv
    pass <- assign p [(lv,plv)] (Just re,pre)
    return (pass,annlv)
passToDafny' p annK lv@(Plvalue _ (PLVar v)) (Right upd) = do
    (plv,annlv) <- plvalueToDafny annK IsPrivate lv
    pass <- assign p [(lv,plv)] (Nothing,plv <> upd)
    return (pass,annlv)
passToDafny' p annK lv@(Plvalue _ (PLArray v i)) (Left (re,pre)) = do
    (pi,anni) <- pexprToDafny annK IsCt i
    (plv,annlv) <- plvalueToDafny annK IsPrivate lv
    (doc,ann) <- passToDafny' p annK (varPlvalue v) (Right $ brackets (parens (pi <+> text "as int") <+> text ":=" <+> pre))
    return (doc,anni++annlv++ann)
passToDafny' p annK lv@(Plvalue _ (PLArray v i)) (Right upd) = do
    (pi,anni) <- pexprToDafny annK IsCt i
    (plv,annlv) <- plvalueToDafny annK IsPrivate lv
    (doc,ann) <- passToDafny' p annK (varPlvalue v) (Right $ brackets (parens (pi <+> text "as int") <+> text ":=" <+> plv <> upd))
    return (doc,anni++annlv++ann)
passToDafny' p annK lv@(Plvalue _ (PLMem {})) _ = genError p $ text "unsupported assignment to lmem"
        
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
    pn <- pidentToDafny n
    (pargs,annargs) <- procCallArgsToDafny annK args
    let pcall = pn <> parens (sepBy pargs comma)
    annp <- genDafnyAssumptions annK ct vs pcall l
    return (pcall,annargs++annp)
pexpr_rToDafny annK ct l (PEBool True) = return (text "true",[])
pexpr_rToDafny annK ct l (PEBool False) = return (text "false",[])
pexpr_rToDafny annK ct l (Pcast w e) = do
    (pe,anne) <- pexprToDafny annK ct e
    let t = wsizeToDafny w
    return (pe <+> text "as" <+> t,anne)
pexpr_rToDafny annK ct l (PEInt i) = return (integer i,[])
pexpr_rToDafny annK ct l e@(PEVar v) = do
    ks <- State.gets consts
    case Map.lookup (funit v) ks of
        Just e -> return (e,[])
        Nothing -> do
            vs <- lift2 $ usedVars e
            pv <- pidentToDafny v
            annp <- genDafnyAssumptions annK ct vs pv l
            return (pv,annp)
pexpr_rToDafny annK ct l e@(PEGet n i) = do
    vs <- lift2 $ usedVars e
    (pn,annn) <- pexprToDafny annK ct (varPexpr n)
    (pi,anni) <- pexprToDafny annK IsCt i
    let pse = pn <> brackets pi
    annp <- genDafnyAssumptions annK ct vs pse l
    return (pse,annn++anni++annp)
pexpr_rToDafny annK ct l fe@(PEFetch t v e) = genError (infoLoc l) $ text "expression fetch not yet supported"
pexpr_rToDafny annK ct l (PEParens e) = pexprToDafny annK ct e
pexpr_rToDafny annK ct l e@(PEOp1 o e1) = do
    vs <- lift2 $ usedVars e
    peop1ToDafny annK ct l vs o e1
pexpr_rToDafny annK ct l e@(PEOp2 o e1 e2) = do
    vs <- lift2 $ usedVars e
    peop2ToDafny annK ct l vs o e1 e2

procCallArgsToDafny :: DafnyK m => AnnKind -> [Pexpr TyInfo] -> DafnyM m ([Doc],AnnsDoc)
procCallArgsToDafny annK es = do
    (es',annes) <- State.mapAndUnzipM (procCallArgToDafny annK) es
    return (es',concat annes)
    
procCallArgToDafny :: DafnyK m => AnnKind -> Pexpr TyInfo -> DafnyM m (Doc,AnnsDoc)
procCallArgToDafny annK e = pexprToDafny annK IsPrivate e

peop1ToDafny :: DafnyK m => AnnKind -> CtMode -> TyInfo -> Set Piden -> Peop1 -> Pexpr TyInfo -> DafnyM m (Doc,AnnsDoc)
peop1ToDafny annK ct l vs Not1 e1 = nativeop1ToDafny annK ct l vs (char '!') e1

peop2ToDafny :: DafnyK m => AnnKind -> CtMode -> TyInfo -> Set Piden -> Peop2 -> Pexpr TyInfo -> Pexpr TyInfo -> DafnyM m (Doc,AnnsDoc)
peop2ToDafny annK ct l vs Add2 e1 e2  = nativeop2ToDafny annK ct l vs (text "+") e1 e2
peop2ToDafny annK ct l vs Sub2 e1 e2  = nativeop2ToDafny annK ct l vs (text "-") e1 e2
peop2ToDafny annK ct l vs Mul2 e1 e2  = nativeop2ToDafny annK ct l vs (text "*") e1 e2
peop2ToDafny annK ct l vs Eq2 e1 e2   = nativeop2ToDafny annK ct l vs (text "==") e1 e2
peop2ToDafny annK ct l vs Neq2 e1 e2  = nativeop2ToDafny annK ct l vs (text "!=") e1 e2
peop2ToDafny annK ct l vs Le2 e1 e2   = nativeop2ToDafny annK ct l vs (text "<=") e1 e2
peop2ToDafny annK ct l vs Lt2 e1 e2   = nativeop2ToDafny annK ct l vs (text "<") e1 e2
peop2ToDafny annK ct l vs Ge2 e1 e2   = nativeop2ToDafny annK ct l vs (text ">=") e1 e2
peop2ToDafny annK ct l vs Gt2 e1 e2   = nativeop2ToDafny annK ct l vs (text ">") e1 e2
peop2ToDafny annK ct l vs Shl2 e1 e2  = nativeop2ToDafny annK ct l vs (text "<<") e1 e2
peop2ToDafny annK ct l vs Shr2 e1 e2  = nativeop2ToDafny annK ct l vs (text ">>") e1 e2
peop2ToDafny annK ct l vs And2 e1 e2  = nativeop2ToDafny annK ct l vs (text "&&") e1 e2
peop2ToDafny annK ct l vs Or2 e1 e2   = nativeop2ToDafny annK ct l vs (text "||") e1 e2
peop2ToDafny annK ct l vs BAnd2 e1 e2 = nativeop2ToDafny annK ct l vs (text "&") e1 e2
peop2ToDafny annK ct l vs BOr2 e1 e2  = nativeop2ToDafny annK ct l vs (text "|") e1 e2
peop2ToDafny annK ct l vs BXor2 e1 e2 = nativeop2ToDafny annK ct l vs (text "^") e1 e2

nativeop1ToDafny :: DafnyK m => AnnKind -> CtMode -> TyInfo -> Set Piden -> Doc -> Pexpr TyInfo -> DafnyM m (Doc,AnnsDoc)
nativeop1ToDafny annK ct l vs op e1 = do
    (pe1,anne1) <- pexprToDafny annK IsPrivate e1
    let pe = op <> pe1
    annp <- genDafnyAssumptions annK ct vs pe l
    return (pe,anne1++annp)

nativeop2ToDafny :: DafnyK m => AnnKind -> CtMode -> TyInfo -> Set Piden -> Doc -> Pexpr TyInfo -> Pexpr TyInfo -> DafnyM m (Doc,AnnsDoc)
nativeop2ToDafny annK ct l vs op e1 e2 = do
    (pe1,anne1) <- pexprToDafny annK IsPrivate e1
    (pe2,anne2) <- pexprToDafny annK IsPrivate e2
    let pe = pe1 <+> op <+> pe2
    annp <- genDafnyAssumptions annK ct vs pe l
    return (pe,anne1++anne2++annp)

pidentToDafny :: DafnyK m => Pident info -> DafnyM m Doc
pidentToDafny v = pp v

pidentToDafnyId :: Pident info -> String
pidentToDafnyId (Pident _ v) = v

ptypeToDafny :: DafnyK m => AnnKind -> Maybe (Pident TyInfo) -> Ptype TyInfo -> DafnyM m (Doc,AnnsDoc)
ptypeToDafny annK v TBool = return (text "bool",[])
ptypeToDafny annK v TInt = return (text "int",[])
ptypeToDafny annK v (TWord sz) = return (wsizeToDafny sz,[])
ptypeToDafny annK v (TArray sz e) = do
    (pe,anne) <- pexprToDafny annK IsCt e
    let pty = text "seq" <> abrackets (wsizeToDafny sz)
    anns <- case v of
        Nothing -> return []
        Just v -> do
            pv <- pidentToDafny v
            leakMode <- getLeakMode
            annExpr (Just False) False leakMode annK (Set.singleton $ funit v) (dafnySize pv <+> text "==" <+> pe)
    return (pty,anne++anns)

wsizeToDafny :: Wsize -> Doc
wsizeToDafny W8   = text "bv8"
wsizeToDafny W16  = text "bv16"
wsizeToDafny W32  = text "bv32"
wsizeToDafny W64  = text "bv64"
wsizeToDafny W128 = text "bv128"
wsizeToDafny W256 = text "bv256"

dafnySize :: Doc -> Doc
dafnySize x = char '|' <> x <> char '|'

genDafnyAssumptions :: DafnyK m => AnnKind -> CtMode -> Set Piden -> Doc -> TyInfo -> DafnyM m AnnsDoc
genDafnyAssumptions annK ct vs pv tv = do
    genDafnyPublics (infoLoc tv) annK ct vs pv (infoTy tv)

genDafnyPublics :: DafnyK m => Position -> AnnKind -> CtMode -> Set Piden -> Doc -> (Ptype TyInfo) -> DafnyM m AnnsDoc
genDafnyPublics l annK ct vs pv tv = whenLeakMode $ do
    d <- getInDecl
    if isLeakageInDecl d
        then do
            let publick = case annK of
                            StmtK -> "PublicMid"
                            InvariantK -> "PublicMid"
                            EnsureK -> "PublicOut"
                            RequireK -> "PublicIn"
                            NoK -> "PublicMid"
            -- generate public annotatiosn
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
    , consts :: Map Piden Doc -- global constant variables
    }

data CtMode = IsCt | IsPublic | IsPrivate
  deriving (Data,Typeable,Show,Eq,Ord)

data FreeMode = KeepF | FreeF | DeleteF
  deriving (Data,Typeable,Show,Eq,Ord)

type DafnyId = String

type AnnsDoc = [AnnDoc]
-- (kind,isFree (Nothing=not free,Just False=not inlined,Just True=inlined),used variables,dafny expression, is leakage expr)
type AnnDoc = (AnnKind,Maybe Bool,Set Piden,Doc,Bool)

data AnnKind = StmtK | EnsureK | RequireK | InvariantK | DecreaseK | NoK | ReadsK | AxiomK
  deriving (Show,Eq)
instance Monad m => PP m AnnKind where
    pp = return . text . show

data AnnKindClass = ExprKC | StmtKC | ProcKC | GlobalKC
  deriving (Eq,Ord,Show)

-- * Utilities

annKindClass :: AnnKind -> AnnKindClass
annKindClass EnsureK = ProcKC
annKindClass RequireK = ProcKC
annKindClass StmtK = StmtKC
annKindClass InvariantK = StmtKC
annKindClass DecreaseK = ProcKC
annKindClass ReadsK = ProcKC
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
annLine (NoK,isFree,vs,x,isLeak) = ppIsFree (fmap (const True) isFree) PP.empty x
annLine (AxiomK,_,_,_,_) = PP.empty

annLines :: AnnKind -> AnnsDoc -> (AnnsDoc,Doc)
annLines c anns = annLinesC (annKindClass c) anns

-- the input boolean determines if we are in a procedure context or not
-- if not in a procedure context, we postpone procedure annotations
annLinesC :: AnnKindClass -> AnnsDoc -> (AnnsDoc,Doc)
annLinesC cl anns = (anns',vcat $ map annLine xs)
    where (anns',xs) = List.partition ((>cl) . annKindClass . fst5) anns

annLinesProcC :: AnnsDoc -> Doc
annLinesProcC anns = d
    where
    (reads,anns') = List.partition ((==ReadsK) . fst5) anns
    anns'' = List.nub anns'
    reads' = Set.fromList $ map fou5 reads
    readk = case Set.toList reads' of
                [] -> []
                xs -> [(ReadsK,Just False,Set.empty,sepBy xs comma,False)]
    ([],d) = annLinesC ProcKC (readk++anns'')

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
    add ann@(ReadsK,_,_,_,_) = ann
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

ppFree isFree doc = if isFree then text "free" <+> doc else doc
ppLeak isLeak doc = if isLeak then text "leakage" <+> doc else doc

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

decClassToDafny :: DafnyK m => DecClass -> DafnyM m Doc
decClassToDafny (rs,ws) = do
    let ppVar (v@(Pident _ n),(t,_)) = pidentToDafny $ Pident (tyInfo t) n
    prs <- mapM ppVar $ Map.toList (Map.filter snd $ fst rs)
    pws <- mapM ppVar $ Map.toList (Map.filter snd $ fst ws)
    let pr = if null prs then PP.empty else text "reads" <+> sepBy prs space
    let pw = if null pws then PP.empty else text "modifies" <+> sepBy pws space
    return $ pr $+$ pw

propagateDafnyAssumptions :: DafnyK m => Position -> AnnKind -> DecClass -> DafnyM m AnnsDoc
propagateDafnyAssumptions p annK ((rs,_),(ws,_)) = do
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


