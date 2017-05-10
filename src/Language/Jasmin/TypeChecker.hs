{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleInstances, DeriveDataTypeable, DeriveGeneric, FlexibleContexts, ConstraintKinds, ScopedTypeVariables, ViewPatterns #-}

module Language.Jasmin.TypeChecker
    ( module Language.Jasmin.TypeChecker
    , module Language.Jasmin.TypeChecker.TyInfo
    ) where

import Language.Jasmin.TypeChecker.TyInfo
import Language.Jasmin.Syntax
import Language.Jasmin.Error
import Control.Monad.Except
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State as State
import Language.Position
import Language.Location

import Data.Maybe
import Data.Foldable as Foldable
import Data.Traversable as Traversable
import Data.Map (Map(..))
import qualified Data.Map as Map
import Utils
import Text.PrettyPrint.Exts
import GHC.Generics
import Data.Generics hiding (Generic)

tt_var :: TcK m => Pident Position -> Bool -> TcM m (Pident TyInfo)
tt_var (Pident l x) isWrite = getVar l (Pident () x) isWrite

tt_call :: TcK m => Pident Position -> TcM m (Pident TyInfo,[Ptype TyInfo],[Ptype TyInfo])
tt_call (Pident l n) = getCall l (Pident () n)

tt_as_array :: TcK m => Position -> Ptype TyInfo -> TcM m (Ptype TyInfo)
tt_as_array l (TArray ws _) = return $ TWord ws
tt_as_array l ty = tyError l $ InvalidType (ty) TPArray

tt_as_word :: TcK m => Position -> Ptype TyInfo -> TcM m Wsize
tt_as_word l (TWord ws) = return ws
tt_as_word l ty = tyError l $ InvalidType (ty) TPWord

peop2_of_eqop :: Peqop -> Maybe Peop2
peop2_of_eqop RawEq  = Nothing
peop2_of_eqop AddEq  = Just Add2
peop2_of_eqop SubEq  = Just Sub2
peop2_of_eqop MulEq  = Just (Mul2 Nothing)
peop2_of_eqop ShREq  = Just Shr2
peop2_of_eqop ShLEq  = Just Shl2
peop2_of_eqop BAndEq = Just BAnd2
peop2_of_eqop BXOrEq = Just BXor2
peop2_of_eqop BOrEq  = Just BOr2

max_ty :: TcK m => JasminError -> Ptype info -> Ptype info -> TcM m (Ptype info)
max_ty err TInt TInt = return TInt
max_ty err TInt t2@(TWord _) = return t2
max_ty err t1@(TWord _) TInt = return t1
max_ty err t1@(TWord w1) (TWord w2) | w1 == w2 = return t1
max_ty err _ _ = throwError err

cast_pexpr :: TcK m => Pexpr TyInfo -> Ptype TyInfo -> TcM m (Pexpr TyInfo)
cast_pexpr e ty = do
    let ety = infoTyNote "cast_pexpr" $ loc e
    let eloc = infoLoc $ loc e
    let cast' TInt TInt = return e
        cast' TInt (TWord w) = return $ Pexpr (tyInfo $ TWord w) (Pcast (TWord w) e)
        cast' (TWord w1) (TWord w2) | w1 == w2 = return e
        cast' ety ty = tyError eloc $ InvalidCast ety ty
    cast' ety ty

tt_op2 :: TcK m => Position -> Peop2 -> Pexpr TyInfo -> Pexpr TyInfo -> TcM m (Pexpr_r TyInfo,Ptype TyInfo)
tt_op2 l op e1 e2 = do
    let ty1 = infoTyNote "tt_op2" $ loc e1
    let ty2 = infoTyNote "tt_op2" $ loc e2
    case (op,ty1,ty2) of
        (isNumericPeop2 -> True,isNumericType -> True,isNumericType -> True) -> do
            ty <- max_ty (TypeCheckerError l $ InvOpInExpr op) ty1 ty2
            e1' <- cast_pexpr e1 ty1
            e2' <- cast_pexpr e2 ty2
            case wordSizePeop2 op of
                Just w -> do
                    let tw = TWord w
                    let e1'' = Pexpr (tyInfoLoc tw l) $ Pcast (TWord w) e1'
                    let e2'' = Pexpr (tyInfoLoc tw l) $ Pcast (TWord w) e2'
                    return (PEOp2 op e1'' e2'',tw)
                Nothing -> return (PEOp2 op e1' e2',ty)
        (isBoolPeop2 -> True,TBool,TBool) -> return (PEOp2 And2 e1 e2,TBool)
        (isCmpPeop2 -> Just _,ty1,ty2) -> do
            ty <- max_ty (TypeCheckerError l $ InvOpInExpr op) ty1 ty2
            e1' <- cast_pexpr e1 ty1
            e2' <- cast_pexpr e2 ty2
            return (PEOp2 op e1' e2',TBool)
        otherwise -> tyError l $ NoOperator op [ty1,ty2]

tt_expr :: TcK m => Pexpr Position -> TcM m (Pexpr TyInfo)
tt_expr (Pexpr l e) = do
    (e',t) <- tt_expr_r l e
    return $ Pexpr (tyInfoLoc t l) e'

tt_concat_types :: TcK m => Position -> [Ptype TyInfo] -> TcM m (Ptype TyInfo)
tt_concat_types p [] = genError p $ text "cannot concat empty types"
tt_concat_types p [x] = return x
tt_concat_types p xs = do
    ws <- mapM (liftM wordSize . tt_as_word p) xs
    let w = sum ws
    case sizeWord w of
        Just wsz -> return $ TWord wsz
        Nothing -> genError p $ text "concat needs to be a word type, not" <+> ppid w

tt_expr_r :: TcK m => Position -> Pexpr_r Position -> TcM m (Pexpr_r TyInfo,Ptype TyInfo)
tt_expr_r l (PEParens e) = do
    e' <- mapM tt_expr e
    t <- tt_concat_types l (map (infoTyNote "tt_expr_r_parens" . loc) e')
    return (PEParens e',t)
tt_expr_r l (PEBool b) = do
    return (PEBool b,TBool)
tt_expr_r l (PEInt i) = do
    return (PEInt i,TInt)
tt_expr_r l (PEVar v) = do
    v' <- tt_var v False
    return (PEVar v',infoTyNote "tt_expr" $ loc v')
tt_expr_r l (PEFetch ct x o) = do
    x' <- tt_var x False
    w <- tt_as_word l (infoTyNote "tt_expr" $ loc x')
    o' <- tt_index o
    ct' <- mapM tt_type ct
    ct'' <- case ct' of
        Nothing -> return $ TWord W64
        Just st -> do
            sty <- tt_as_word l st
            if sty < w
                then tyError l $ InvalidCast (TWord sty) (TWord w)
                else return st
    return (PEFetch (Just ct'') x' o',ct'')
tt_expr_r l (PECall {}) = tyError l $ CallNotAllowed
tt_expr_r l (PEGet x i) = do
    x' <- tt_var x False
    i' <- tt_index i
    ty <- tt_as_array l (infoTyNote "tt_expr_r_get" $ loc x')
    return (PEGet x' i',ty)
tt_expr_r l (PEOp1 Not1 pe) = do
    pe' <- tt_bool pe
    return (PEOp1 Not1 pe',TBool)
tt_expr_r l (PEOp2 pop pe1 pe2) = do
    pe1' <- tt_expr pe1
    pe2' <- tt_expr pe2
    tt_op2 l pop pe1' pe2'
tt_expr_r l (LeakExpr e) = checkAnn l (Just True) $ do
    e' <- tt_expr e
    return (LeakExpr e',TBool)
tt_expr_r l qe@(QuantifiedExpr q vs e) = checkAnn l (Just False) $ tt_local $ do
    vs' <- (tt_vardecls') vs
    e' <- tt_bool e
    return (QuantifiedExpr q vs' e',TBool)

tt_type :: TcK m => Ptype Position -> TcM m (Ptype TyInfo)
tt_type TBool = return TBool
tt_type TInt = return TInt
tt_type (TWord ws) = do
    ws' <- tt_ws ws
    return $ TWord ws'
tt_type (TArray ws e) = do
    ws' <- tt_ws ws
    e' <- tt_expr e
    return $ TArray ws' e'

tt_ws :: TcK m => Wsize -> TcM m Wsize
tt_ws w = return w

tt_vardecls' :: TcK m => [Parg Position] -> TcM m [Parg TyInfo]
tt_vardecls' = mapM tt_vardecl'

tt_vardecls :: TcK m => [Pbodyarg Position] -> TcM m [Pbodyarg TyInfo]
tt_vardecls = mapM tt_vardecl
    
tt_vardecl :: TcK m => Pbodyarg Position -> TcM m (Pbodyarg TyInfo)
tt_vardecl (Pbodyarg t v) = do
    Parg t' (Just v') <- tt_vardecl' $ Parg t (Just v)
    return (Pbodyarg t' v')

tt_vardecl' :: TcK m => Parg Position -> TcM m (Parg TyInfo)
tt_vardecl' (Parg (sto,xty) Nothing) = do
    sto' <- tt_sto sto
    xty' <- tt_type xty
    return $ Parg (sto',xty') Nothing
tt_vardecl' (Parg (sto,xty) (Just (Pident l n))) = do
    sto' <- tt_sto sto
    xty' <- tt_type xty
    let info = stotyInfoLoc sto' (xty') l
    let x' = Pident info n
    addVar x'
    return $ Parg (sto',xty') (Just x')

tt_sto :: TcK m => Pstorage -> TcM m Pstorage
tt_sto = return

tt_param :: TcK m => Pparam Position -> TcM m (Pparam TyInfo)
tt_param pp = tt_global $ do
    let l = loc $ ppa_name pp
    ty <- tt_type (ppa_ty pp)
    e <- tt_expr (ppa_init pp)
    e' <- check_ty_assign l e ty
    let Pident ln n = ppa_name pp
    let x = Pident (tyInfoLoc ty ln) n
    addVar x
    return $ Pparam ty x e'

tt_lbool' :: TcK m => Plvalue Position -> TcM m (Plvalue TyInfo)
tt_lbool' (Plvalue p PLIgnore) = return $ Plvalue (tyInfoLoc TBool p) PLIgnore
tt_lbool' x = do
    x' <- tt_lvalue x
    check_ty (loc x) TPBool (locTy x')
    return x'

tt_lword :: TcK m => Plvalue Position -> TcM m (Plvalue TyInfo)
tt_lword x = do
    x' <- tt_lvalue x
    tx <- locTyM x'
    return x'

tt_lvalue :: TcK m => Plvalue Position -> TcM m (Plvalue TyInfo)
tt_lvalue (Plvalue l v) = do
    (v',t) <- tt_lvalue_r l v
    return $ Plvalue (tyInfoLoc' t l) v'

tt_lvalue_r :: TcK m => Position -> Plvalue_r Position -> TcM m (Plvalue_r TyInfo,Maybe (Ptype TyInfo))
tt_lvalue_r p PLIgnore = return (PLIgnore,Nothing)
tt_lvalue_r l (PLParens e) = do
    e' <- mapM tt_lvalue e
    let tys = map locTy' e'
    t <- if all isJust tys
        then liftM Just $ tt_concat_types l (map fromJust tys)
        else return Nothing
    return (PLParens e',t)
tt_lvalue_r p (PLVar x) = do
    x' <- tt_var x True
    return (PLVar x',Just $ locTyNote "tt_lvalue_var" x')
tt_lvalue_r p (PLArray x pi) = do
    x' <- tt_var x True
    i <- tt_index pi
    ty <- tt_as_array p (locTyNote "tt_lvalue_array" x')
    return (PLArray x' i,Just ty)
tt_lvalue_r p (PLMem st x pe) = do
    x' <- tt_var x True
    pe' <- tt_index pe
    w <- tt_as_word p (locTyNote "tt_lvalue_mem" x')
    st' <- forM st $ \st -> do
        sty <- tt_type st >>= tt_as_word p
        if sty < w
            then tyError p $ InvalidCast (TWord sty) (TWord w)
            else return sty
    let st'' = Just $ TWord $ maybe w id st'
    return (PLMem st'' x' pe',st'')

tt_expr_of_lvalues :: TcK m => Position -> [Plvalue info] -> TcM m (Pexpr info)
tt_expr_of_lvalues p [] = tyError p EqOpWithNoLValue
tt_expr_of_lvalues p lvs = tt_expr_of_lvalue p (last lvs) 

tt_expr_of_lvalue :: TcK m => Position -> Plvalue info -> TcM m (Pexpr info)
tt_expr_of_lvalue p (Plvalue i lv) = do
    e <- tt_expr_of_lvalue' p lv
    return $ Pexpr i e
  where
    tt_expr_of_lvalue' :: TcK m => Position -> Plvalue_r info -> TcM m (Pexpr_r info)
    tt_expr_of_lvalue' p (PLVar x) = return $ PEVar x
    tt_expr_of_lvalue' p (PLArray x i) = return $ PEGet x i
    tt_expr_of_lvalue' p (PLParens es) = do
        es' <- mapM (tt_expr_of_lvalue p) es
        return $ PEParens es'
    tt_expr_of_lvalue' p (PLMem t x e) = return $ PEFetch t x e
    tt_expr_of_lvalue' p lv = tyError p $ InvalidLRValue (Plvalue () $ funit lv)

--tt_opsrc :: TcK m => Maybe Eqoparg -> Maybe Peop2 -> Loc Position -> TcM m Opsrc 
--tt_opsrc lv Nothing (Loc _ (PEOp2 op pe1 pe2)) = do
--    case pe2 of
--        Loc _ (PEOp2 op' pe2 pe3) -> do
--            pe1' <- tt_expr pe1
--            pe2' <- tt_expr pe2
--            pe3' <- tt_expr pe3
--            return $ TriOp op op' pe1' pe2' pe3'
--        _ -> do
--            pe1' <- tt_expr pe1
--            pe2' <- tt_expr pe2
--            return $ BinOp op pe1' pe2'
--tt_opsrc (Just e1) (Just eqop) (Loc _ (PEOp2 op pe2 pe3)) = do
--    pe2' <- tt_expr pe2
--    pe3' <- tt_expr pe3
--    return $ TriOp eqop op e1 pe2' pe3'
--tt_opsrc (Just e1) (Just eqop) pe = do
--    pe' <- tt_expr pe
--    return $ BinOp eqop e1 pe'
--tt_opsrc lv Nothing pe = do
--    pe' <- tt_expr pe
----    pe'' <- tt_shift_expr lv pe'
--    return $ NoOp pe'

-- special shift expressions
--tt_shift_expr :: TcK m => Eqoparg -> Pexpr TyInfo -> TcM m (PExpr TyInfo)
--tt_shift_expr lv@(locTy -> TWord wlv) re@(Loc _ (PEOp2 op@(flip elem [Shr2,Shl2] -> True) (Loc (infoTy -> TWord wtot) (PEParens es)) n@(locTy -> TInt))) = do
--    return $ Loc (loc lv) $ Pcast wlv $ Loc (loc re) $ PEOp2 Shr2 re (intLoc $ toEnum $ wordSize wtot - wordSize wlv)
--tt_shift_expr lv re = return re

carry_op :: Peop2 -> Op
carry_op Add2 = Oaddcarry
carry_op Sub2 = Osubcarry

tt_bool :: TcK m => Pexpr Position -> TcM m (Pexpr TyInfo)
tt_bool x = expect (loc x) TPBool (infoTyNote "tt_bool" . loc) (tt_expr x)

tt_index :: TcK m => Pexpr Position -> TcM m (Pexpr TyInfo)
tt_index x = do
    let p = loc x
    x' <- tt_expr x
    check_index p (locTy x')
    return x'

tt_indexvar :: TcK m => Pident Position -> Bool -> TcM m (Pident TyInfo)
tt_indexvar x isWrite = do
    let p = loc x
    x' <- tt_var x isWrite
    check_index p (locTy x')
    return x'

check_index :: TcK m => Position -> Ptype TyInfo -> TcM m ()
check_index p TInt = return ()
check_index p (TWord _) = return ()
check_index p t = tyError p $ TypeMismatch t TInt

--assign_index :: TcK m => Pexpr TyInfo -> TcM m (Pexpr TyInfo)
--assign_index x' = do
--    let p = infoLoc $ loc x'
--    case locTy x' of
--        TInt -> return x'
--        TWord w -> return $ Pexpr (tyInfoLoc TInt p) $ Pcast TInt x'
--        t -> tyError p $ TypeMismatch t TInt

tt_int :: TcK m => Pexpr Position -> TcM m (Pexpr TyInfo)
tt_int x = expect (loc x) TPInt (infoTyNote "tt_int" . loc) (tt_expr x)

tt_intvar :: TcK m => Pident Position -> Bool -> TcM m (Pident TyInfo)
tt_intvar x isWrite = expect (loc x) TPInt (infoTyNote "tt_intvar" . loc) (tt_var x isWrite)

tt_instr :: TcK m => Pinstr Position -> TcM m (Pinstr TyInfo)
tt_instr (Pinstr l i) = do
    i' <- tt_instr_r l i
    cl <- getDecClass
    return $ Pinstr (decInfoLoc cl l) i'

tt_instr_r :: TcK m => Position -> Pinstr_r Position -> TcM m (Pinstr_r TyInfo)
tt_instr_r p (PIIf isPrivate c st sf) = do
    c' <- tt_bool c
    st' <- tt_block st
    sf' <- mapM tt_block sf
    return $ PIIf isPrivate c' st' sf'
tt_instr_r p (PIFor x d i1 i2 anns s) = do
    x' <- tt_indexvar x False
    let tx = locTy x'
    i1' <- expr_ty_assign p i1 tx
    i2' <- expr_ty_assign p i2 tx
    anns' <- mapM tt_loop_ann anns
    s' <- tt_block s
    return $ PIFor x' d i1' i2' anns' s'
tt_instr_r p (PIWhile s1 c anns s2) = do
    s1' <- mapM tt_block s1
    c' <- tt_bool c
    anns' <- mapM tt_loop_ann anns
    s2' <- mapM tt_block s2
    return $ PIWhile s1' c' anns' s2'
tt_instr_r p (PIAssign ls eqop e (Just c)) = tt_instr_r p $ PIIf True c (Pblock p [Pinstr p $ PIAssign ls eqop e Nothing]) Nothing
tt_instr_r p (PIAssign ls (peop2_of_eqop -> Just o) re Nothing) = do
    lve <- tt_expr_of_lvalues p ls
    let re' = Pexpr (loc re) $ PEOp2 o lve re
    tt_instr_r p $ PIAssign ls RawEq re' Nothing
tt_instr_r p (PIAssign ls RawEq (Pexpr _ (PECall f args)) Nothing) = do
    (f_name',f_rty',f_ty_args') <- tt_call f
    lvs <- mapM tt_lvalue ls
    lvs' <- check_sig_lvs p False f_rty' lvs
    args' <- mapM tt_expr args
    args'' <- check_sig_call p f_ty_args' args'
    return $ Ccall lvs' f_name' args''
tt_instr_r p (PIAssign lvs RawEq re Nothing) = do
    tt_native_instr_r p lvs re `mplus` tt_basic_instr_r p lvs re
tt_instr_r p (Anninstr ann) = withAnn (Just False) $ do
    ann' <- tt_instr_ann_r p ann
    return $ Anninstr ann'

tt_instr_ann :: TcK m => StatementAnnotation Position -> TcM m (StatementAnnotation TyInfo)
tt_instr_ann (StatementAnnotation l x) = withAnn (Just False) $ do
    x' <- tt_instr_ann_r l x
    cl <- getDecClass
    return $ StatementAnnotation (decInfoLoc cl l) x'

tt_instr_ann_r :: TcK m => Position -> StatementAnnotation_r Position -> TcM m (StatementAnnotation_r TyInfo)
tt_instr_ann_r p (AssumeAnn isLeak e) = checkAnn p (Just isLeak) $ do
    e' <- tt_bool e
    return $ AssumeAnn isLeak e'
tt_instr_ann_r p (AssertAnn isLeak e) = checkAnn p (Just isLeak) $ do
    e' <- tt_bool e
    return $ AssertAnn isLeak e'
tt_instr_ann_r p (EmbedAnn isLeak e)  = checkAnn p (Just isLeak) $ do
    e' <- tt_instr e
    return $ EmbedAnn isLeak e'
    
tt_loop_ann :: TcK m => LoopAnnotation Position -> TcM m (LoopAnnotation TyInfo)
tt_loop_ann (LoopAnnotation l x) = withAnn (Just False) $ do
    x' <- tt_loop_ann_r l x
    cl <- getDecClass
    return $ LoopAnnotation (decInfoLoc cl l) x'
    
tt_loop_ann_r :: TcK m => Position -> LoopAnnotation_r Position -> TcM m (LoopAnnotation_r TyInfo)
tt_loop_ann_r p (LDecreasesAnn isLeak e) = checkAnn p (Just isLeak) $ do
    e' <- tt_expr e
    return $ LDecreasesAnn isLeak e'
tt_loop_ann_r p (LInvariantAnn isFree isLeak e) = checkAnn p (Just isLeak) $ do
    e' <- tt_bool e
    return $ LInvariantAnn isFree isLeak e'

tt_proc_ann :: TcK m => ProcedureAnnotation Position -> TcM m (ProcedureAnnotation TyInfo)
tt_proc_ann (ProcedureAnnotation p x) = withAnn (Just False) $ do
    x' <- tt_proc_ann_r p x
    cl <- getDecClass
    return $ ProcedureAnnotation (decInfoLoc cl p) x'

tt_proc_ann_r :: TcK m => Position -> ProcedureAnnotation_r Position -> TcM m (ProcedureAnnotation_r TyInfo)
tt_proc_ann_r p (PDecreasesAnn e) = checkAnn p (Just False) $ do
    e' <- tt_expr e
    return $ PDecreasesAnn e'
tt_proc_ann_r p (RequiresAnn isFree isLeak e) = checkAnn p (Just isLeak) $ do
    e' <- tt_bool e
    return $ RequiresAnn isFree isLeak e'
tt_proc_ann_r p (EnsuresAnn isFree isLeak e) = checkAnn p (Just isLeak) $ do
    e' <- tt_bool e
    return $ EnsuresAnn isFree isLeak e'

tt_basic_instr_r :: TcK m => Position -> [Plvalue Position] -> Pexpr Position -> TcM m (Pinstr_r TyInfo)
tt_basic_instr_r p [lv] re = do
    lv' <- tt_lvalue lv
    re' <- tt_expr re
    re' <- check_ty_assign p re' (locTy lv')
    return $ PIAssign [lv'] RawEq re' Nothing
tt_basic_instr_r p lvs re = genError p $ text "basic instruction not supported"

binOp2 :: Pexpr info -> Maybe (Peop2,Pexpr info,Pexpr info)
binOp2 (Pexpr _ (PEOp2 o x y)) = Just (o,x,y)
binOp2 _ = Nothing

triOp2 :: Pexpr info -> Maybe (Peop2,Pexpr info,Pexpr info,Pexpr info)
triOp2 (Pexpr _ (PEOp2 o1 x (Pexpr _ (PEOp2 o2 y z)))) | o1 == o2 = Just (o1,x,y,z)
triOp2 (Pexpr _ (PEOp2 o1 (Pexpr _ (PEOp2 o2 x y)) z)) | o1 == o2 = Just (o1,x,y,z)
triOp2 _ = Nothing

tt_native_instr_r :: TcK m => Position -> [Plvalue Position] -> Pexpr Position -> TcM m (Pinstr_r TyInfo)
tt_native_instr_r p lvs re = 
    tt_bv_carry_op p lvs re
    

tt_bv_carry_op :: TcK m => Position -> [Plvalue Position] -> Pexpr Position -> TcM m (Pinstr_r TyInfo)
tt_bv_carry_op p [lcf,lx] (triOp2 -> Just (o,ex,ey,ecf)) | isCarryOp o = do
    lcf' <- tt_lbool' lcf
    lx' <- tt_lword lx
    tw <- locTyM lx'    
    ex' <- expr_ty_assign p ex tw
    ey' <- expr_ty_assign p ey tw
    ecf' <- tt_bool ecf
    return $ Copn [lcf',lx'] (carry_op o) [ex',ey',ecf']
tt_bv_carry_op p [lcf,lx] (binOp2 -> Just (o,ex,ey)) | isCarryOp o = do
    lcf' <- tt_lbool' lcf
    lx' <- tt_lword lx
    tw <- locTyM lx'    
    ex' <- expr_ty_assign p ex tw
    ey' <- expr_ty_assign p ey tw
    return $ Copn [lcf',lx'] (carry_op o) [ex',ey',falsePexpr]
tt_bv_carry_op p lvs re = genError p $ text "native instruction not supported"

    
    
    
   
--tt_instr_r p (PIAssign ls eqop pe Nothing) = do
--    ct' <- mapM tt_type ct
--    lvs <- mapM tt_lvalue ls
--    let mksrc [flip elem [Just TInt,Just TBool] . locTy' -> True] (flip elem [RawEq,AddEq,SubEq] -> True) = do
--            e <- tt_expr pe
--            return $ ScalOp eqop e
--        mksrc lvs eqop = do
--            lve' <- catchErrorMaybe (tt_expr_of_lvalues p lvs)
--            let eqop' = peop2_of_eqop eqop
--            opsrc <- tt_opsrc lve' eqop' pe
--            return $ NoScalOp opsrc    
--    src <- mksrc lvs eqop
--    let mki :: TcK m => Maybe (Ptype TyInfo) -> [Loc TyInfo] -> IOp -> TcM m (Pinstr_r TyInfo)
--        mki Nothing [lv] (ScalOp eqop e) = do
--            e' <- case eqop of
--                RawEq -> return e
--                (flip elem [AddEq,SubEq] -> True) -> do
--                    lve <- tt_expr_of_lvalue lv
--                    check_ty_eq p (locTyNote "tt_instr_assignScal1" lv) TInt
--                    check_ty_eq p (locTyNote "tt_instr_assignScal2" e) TInt
--                    let Just op2 = peop2_of_eqop eqop
--                    return $ Loc (tyInfoLoc TInt p) (PEOp2 op2 lve e)
--            mapM_ (check_ty_eq p (locTyNote "tt_instr_assignScal3" e')) (locTy' lv)
--            return $ PIAssign Nothing [lv] RawEq e Nothing
--        mki Nothing [lv] (NoScalOp (NoOp e)) = do
--            forM (locTy' lv) (check_ty_assign p e)
--            return $ PIAssign Nothing [lv] RawEq e Nothing
--        mki Nothing [lv] (NoScalOp (BinOp o@(flip elem [Shl2,Shr2,BAnd2,BOr2,BXor2] -> True) e1 e2)) = do
--            let t1 = locTyNote "tt_instr_assignNoScal1" e1
--            check_ty p TPWord t1
--            e2 <- check_ty_assign p e2 (locTyNote "tt_instr_assignNoScal2" e1)
--            lvs <- check_sig_lvs p False [locTyNote "tt_instr_assignNoScal3" e1] lvs
--            let e = Loc (tyInfoLoc t1 p) $ PEOp2 o e1 e2
--            return $ PIAssign Nothing lvs RawEq e Nothing
--        -- carry-less operations
--        mki Nothing lvs (NoScalOp (BinOp o@(flip elem [Mul2] -> True) e1 e2)) = do
--            let t1 = locTyNote "tt_instr_assignNoScalMul1" e1
--            check_ty p TPWord t1
--            e2 <- check_ty_assign p e2 (locTyNote "tt_instr_assignNoScalMul2" e1)
--            lvs <- check_sig_lvs p False [locTyNote "tt_instr_assignNoScalMul3" e1] lvs
--            let e = Loc (tyInfoLoc t1 p) $ PEOp2 o e1 e2
--            return $ PIAssign Nothing lvs RawEq e Nothing
--        mki ct@(Just t@(TWord wres)) lvs (NoScalOp (BinOp o@(flip elem [Mul2] -> True) e1 e2)) = do
--            let t1 = locTyNote "tt_instr_assignNoScalMul4" e1
--            w1 <- tt_as_word p t1
--            unless (w1 <= wres) $ genError p $ text "word size unsupported"
--            e2 <- check_ty_assign p e2 (locTyNote "tt_instr_assignNOScalMul5" e1)
--            lvs <- check_sig_lvs p False [t] lvs
--            let e = Loc (tyInfoLoc t1 p) $ PEOp2 o (Loc (loc e1) $ Pcast wres e1) (Loc (loc e2) $ Pcast wres e2)
--            return $ PIAssign Nothing [Loc (tyInfoLoc (TWord wres) p) $ PLParens lvs] RawEq e Nothing
--        -- carry operations without explicit input carry flag
--        mki Nothing lvs (NoScalOp (BinOp o@(flip elem [Add2,Sub2] -> True) e1 e2)) = do
--            check_ty p TPWord (locTyNote "tt_instr_assignNoScalAdd1" e1)
--            e2 <- check_ty_assign p e2 (locTyNote "tt_instr_assignNoScalAdd2" e1)
--            lvs <- check_sig_lvs p True [TBool,locTyNote "tt_instr_assignNoScalAdd3" e1] lvs
--            return $ Copn lvs (carry_op o) [e1,e2,falsePexpr]
--        -- carry operations with explicit input carry flag
--        mki Nothing lvs (NoScalOp (TriOp op1@(flip elem [Add2,Sub2] -> True) op2 e1 e2 e3)) | op1 == op2 = do
--            check_ty p TPWord (locTyNote "tt_instr_assignTri1" e1)
--            e2 <- check_ty_assign p e2 (locTyNote "tt_instr_assignTri2" e1)
--            check_ty p TPBool (locTyNote "tt_instr_assignTri3" e3)
--            lvs <- check_sig_lvs p True [TBool,locTyNote "tt_instr_assignTri4" e1] lvs
--            return $ Copn lvs (carry_op op1) [e1,e2,e3]
--        mki ct lvs op = tyError p $ Unsupported $ text (show ct) <+> text (show lvs) <+> text "=" <+> text (show op)
--    mki ct' lvs src

tt_block :: TcK m => Pblock Position -> TcM m (Pblock TyInfo)
tt_block (Pblock l is) = tt_local $ do
    (is',cl) <- withDecClass $ mapM tt_instr is
    return $ Pblock (decInfoLoc cl l) is'

tt_funbody :: TcK m => Pfunbody Position -> TcM m (Pfunbody TyInfo)
tt_funbody (Pfunbody vars instrs ret) = tt_local $ do
    vars' <- tt_vardecls vars
    ret' <- mapM (mapM (flip tt_var False)) ret
    instrs' <- mapM tt_instr instrs
    return $ Pfunbody vars' instrs' ret'

tt_item :: TcK m => Pitem Position -> TcM m (Pitem TyInfo)
tt_item (PParam pp) = liftM PParam $ tt_param pp
tt_item (PFundef pf) = liftM PFundef $ tt_fundef pf
tt_item (PAxiomdef pf) = liftM PAxiomdef $ tt_axiomdef_ann pf
tt_item (PLemmadef pf) = liftM PLemmadef $ tt_lemmadef_ann pf
tt_item (PAnnfunctiondef pf) = liftM PAnnfunctiondef $ tt_fundef_ann pf

tt_fundef :: TcK m => Pfundef Position -> TcM m (Pfundef TyInfo)
tt_fundef pf@(Pfundef cc name args rty anns body l) = tt_global $ do
    let name' = fmap noTyInfo name
    args' <- tt_vardecls' args
    rty' <- mapM (mapM (mapSndM tt_type)) rty
    anns' <- mapM tt_proc_ann anns
    (body',cl) <- withDecClass $ tt_funbody body
    let pf' = Pfundef cc name' args' rty' anns' body' (decInfoLoc cl l)
    check_sig l (map (snd) $ Foldable.concat rty') (map (infoTyNote "tt_fundef" . loc) $ Foldable.concat $ pdb_ret body')
    addFun pf'
    return pf'

tt_axiomdef_ann :: TcK m => AnnAxiomDeclaration Position -> TcM m (AnnAxiomDeclaration TyInfo)
tt_axiomdef_ann  (AnnAxiomDeclaration isLeak args anns p) = tt_global $ withAnn (Just isLeak) $ do
    args' <- tt_vardecls' args
    anns' <- mapM tt_proc_ann anns
    return (AnnAxiomDeclaration isLeak args' anns' (decInfoLoc emptyDecClass p))

tt_lemmadef_ann :: TcK m => AnnLemmaDeclaration Position -> TcM m (AnnLemmaDeclaration TyInfo)
tt_lemmadef_ann  (AnnLemmaDeclaration isLeak name args anns body p) = tt_global $ withAnn (Just isLeak) $ do
    let name' = fmap noTyInfo name
    args' <- tt_vardecls' args
    anns' <- mapM tt_proc_ann anns
    (body',cl) <- withDecClass $ mapM tt_block body
    return (AnnLemmaDeclaration isLeak name' args' anns' body' (decInfoLoc cl p))

tt_fundef_ann :: TcK m => AnnFunDeclaration Position -> TcM m (AnnFunDeclaration TyInfo)
tt_fundef_ann  (AnnFunDeclaration isLeak ret name args anns body p) = tt_global $ withAnn (Just isLeak) $ do
    ret' <- tt_type ret
    let name' = fmap noTyInfo name
    args' <- tt_vardecls' args
    anns' <- mapM tt_proc_ann anns
    (body',cl) <- withDecClass $ tt_expr body
    check_sig p [ret'] [locTy body']
    return (AnnFunDeclaration isLeak ret' name' args' anns' body' (decInfoLoc cl p))

tt_program :: TcK m => Pprogram Position -> TcM m (Pprogram TyInfo)
tt_program (Pprogram pm) = liftM Pprogram $ mapM tt_item pm

-- * State

--type Eqoparg = (Loc TyInfo)

--data Opsrc
--    = NoOp Eqoparg
--    | BinOp Peop2 Eqoparg Eqoparg
--    | TriOp Peop2 Peop2 Eqoparg Eqoparg Eqoparg
--  deriving (Eq,Ord,Show,Data,Typeable,Generic)
--
--instance Monad m => PP m Opsrc where
--    pp (NoOp o) = pp o
--    pp (BinOp o e1 e2) = do
--        p1 <- pp e1
--        p2 <- pp e2
--        po <- pp o
--        return $ p1 <+> po <+> p2
--    pp (TriOp o1 o2 e1 e2 e3) = do
--        po1 <- pp o1
--        po2 <- pp o2
--        pe1 <- pp e1
--        pe2 <- pp e2
--        pe3 <- pp e3
--        return $ pe1 <+> po1 <+> pe2 <+> po2 <+> pe3
--
--data IOp
--    = ScalOp Peqop (Loc TyInfo)
--    | NoScalOp Opsrc
--  deriving (Eq,Ord,Show,Data,Typeable,Generic)
--
--instance Monad m => PP m IOp where
--    pp (ScalOp o e) = do
--        po <- pp o
--        pe <- pp e
--        return $ po <+> pe
--    pp (NoScalOp o) = pp o

type TcK m = Monad m
type TcM m = StateT TcEnv (ExceptT JasminError m)

data TcEnv = TcEnv
    { vars :: Map Piden (Bool,Maybe Pstorage,Ptype TyInfo) -- (isAnn,(global=Nothing,local=Just storage),type)
    , funs :: Map Piden (Pfundef TyInfo) -- functions
    , annfuns :: Map Piden (AnnFunDeclaration TyInfo)
    , annlemmas :: Map Piden (AnnLemmaDeclaration TyInfo)
    , decClass :: DecClass -- log of read/written variables
    , isAnn :: Maybe Bool -- if typechecking annotations (Nothing = no annotations, Just False = annotation, Just True = leakage annotations)
    }
  deriving (Eq,Ord,Show,Data,Typeable,Generic)

emptyTcEnv :: TcEnv
emptyTcEnv = TcEnv Map.empty Map.empty Map.empty Map.empty emptyDecClass Nothing

-- * Utilities

withAnn :: Monad m => Maybe Bool -> TcM m a -> TcM m a
withAnn ann m = do
    old <- State.gets isAnn
    State.modify $ \env -> env { isAnn = (max ann old) }
    x <- m
    State.modify $ \env -> env { isAnn = old }
    return x

checkAnn :: Monad m => Position -> Maybe Bool -> TcM m a -> TcM m a
checkAnn p ann m = do
    old <- State.gets isAnn
    if (ann <= old)
        then m
        else do
            genError p $ text "required annotation mode" <+> (text $ show ann) <+> text "inside" <+> (text $ show old)

isCarryOp Add2 = True
isCarryOp Sub2 = True
isCarryOp _ = False

runTcM :: TcK m => TcM m a -> m (Either JasminError a)
runTcM m = runExceptT (State.evalStateT m emptyTcEnv)

tt_local :: TcK m =>  TcM m a -> TcM m a
tt_local m = do
    env <- State.get
    let dropTest v (_,b) = if b then True else isJust (Map.lookup v (Map.filter (isJust . snd3) $ vars env))
    let dropLocals (xs,b) = (Map.filterWithKey dropTest xs,b)
    x <- m
    State.modify $ \e -> e
        { vars = Map.filter (isNothing . snd3) (vars e) `Map.union` Map.filter (isJust . snd3) (vars env)
        , decClass = let (rs,ws) = decClass e in (dropLocals rs,dropLocals ws)
        }
    return x

getDecClass :: Monad m => TcM m DecClass
getDecClass = State.gets decClass

tt_global :: TcK m => TcM m a -> TcM m a
tt_global m = resetDecClass $ localVars $ tt_local m

resetDecClass :: Monad m => TcM m a -> TcM m a
resetDecClass m = do
    cl <- getDecClass
    State.modify $ \env -> env { decClass = emptyDecClass }
    x <- m
    State.modify $ \env -> env { decClass = cl }
    return x

withDecClass :: Monad m => TcM m a -> TcM m (a,DecClass)
withDecClass m = do
    (rs,ws) <- getDecClass
    State.modify $ \env -> env { decClass = (mkEmpty rs,mkEmpty ws) }
    x <- m
    new@(newrs,newws) <- getDecClass
    State.modify $ \env -> env { decClass = addDecClassVars rs ws new }
    return (x,(newrs,newws))
  where
    mkEmpty xs = (Map.empty,isGlobalDecClassVars xs)

getVar :: TcK m => Position -> Piden -> Bool -> TcM m (Pident TyInfo)
getVar l pn@(Pident _ n) isWrite = do
    vs <- State.gets vars
    isAnn <- State.gets isAnn
    let annvs = Map.filter (\(ann,_,_) -> isJust isAnn >= ann) vs
    case Map.lookup pn annvs of
        Just (_,sto,vt) -> do
            let isGlobal = isNothing sto
            let rs = if isWrite then (Map.empty,isGlobal) else (Map.singleton pn (vt,isGlobal),isGlobal)
            let ws = if isWrite then (Map.singleton pn (vt,isGlobal),isGlobal) else (Map.empty,isGlobal)
            State.modify $ \env -> env { decClass = addDecClassVars rs ws (decClass env)  }
            return $ Pident (stotyInfoLoc' sto vt l) n
        Nothing -> tyError l $ UnknownVar pn (text $ show vs)

addVar :: TcK m => Pident TyInfo -> TcM m ()
addVar (Pident i n) = do
    isann <- State.gets isAnn
    let sto = infoSto' i
    let ty = infoTyNote "addVar" i
    State.modify $ \env -> env { vars = Map.insert (Pident () n) (isJust isann,sto,ty) (vars env) }

localVars :: TcK m => TcM m a -> TcM m a
localVars m = do
    x <- m
    State.modify $ \env -> env { vars = Map.filter (isNothing . snd3) (vars env) }
    return x

getCall :: TcK m => Position -> Piden -> TcM m (Pident TyInfo,[Ptype TyInfo],[Ptype TyInfo])
getCall p n =
    do      (getFun p n >>= \f -> return (pdf_name f,maybe [] (map snd) $ pdf_rty f,map (snd . pa_ty) $ pdf_args f))
    `mplus` (getAnnLemma p n >>= \f -> return (lemma_name f,[],map (snd . pa_ty) $ lemma_args f))
    `mplus` (getAnnFun p n >>= \f -> return (af_name f,[af_ty f],map (snd . pa_ty) $ af_args f))

getFun :: TcK m => Position -> Piden -> TcM m (Pfundef TyInfo)
getFun l n = do
    fs <- State.gets funs
    isAnn <- State.gets isAnn
    case Map.lookup n fs of
        Just fdef -> return fdef
        Nothing -> tyError l $ UnknownFun n (text $ show fs)

getAnnLemma :: TcK m => Position -> Piden -> TcM m (AnnLemmaDeclaration TyInfo)
getAnnLemma l n = do
    fs <- State.gets annlemmas
    isAnn <- State.gets isAnn
    let annfs = Map.filter (\def -> Just (lemma_leak def) <= isAnn) fs
    case Map.lookup n annfs of
        Just fdef -> return fdef
        Nothing -> tyError l $ UnknownFun n (text $ show annfs)

getAnnFun :: TcK m => Position -> Piden -> TcM m (AnnFunDeclaration TyInfo)
getAnnFun l n = do
    isAnn <- State.gets isAnn
    fs <- State.gets annfuns
    let annfs = Map.filter (\def -> Just (af_leak def) <= isAnn) fs
    case Map.lookup n annfs of
        Just fdef -> return fdef
        Nothing -> tyError l $ UnknownFun n (text $ show annfs)

addFun :: TcK m => Pfundef TyInfo -> TcM m ()
addFun pf = do
    fs <- State.gets funs
    let n = funit $ pdf_name pf
    let l = infoLoc $ pdf_info pf
    existsCall l n
    State.modify $ \env -> env { funs = Map.insert n pf (funs env) }

addAnnLemma :: TcK m => AnnLemmaDeclaration TyInfo -> TcM m ()
addAnnLemma pf = do
    fs <- State.gets annlemmas
    let n = funit $ lemma_name pf
    let l = infoLoc $ lemma_info pf
    existsCall l n
    State.modify $ \env -> env { annlemmas = Map.insert n pf (annlemmas env) }

addAnnFun :: TcK m => AnnFunDeclaration TyInfo -> TcM m ()
addAnnFun pf = do
    fs <- State.gets annfuns
    let n = funit $ af_name pf
    let l = infoLoc $ af_info pf
    existsCall l n
    State.modify $ \env -> env { annfuns = Map.insert n pf (annfuns env) }

existsCall :: TcK m => Position -> Piden -> TcM m ()
existsCall l n = do
    fs <- State.gets funs
    ls <- State.gets annlemmas
    afs <- State.gets annfuns
    case Map.lookup n fs of
        Just oldpf -> tyError l $ DuplicateFun n (infoLoc $ pdf_info oldpf)
        Nothing -> case Map.lookup n ls of
            Just oldpf -> tyError l $ DuplicateFun n (infoLoc $ lemma_info oldpf)
            Nothing -> case Map.lookup n afs of
                Just oldpf -> tyError l $ DuplicateFun n (infoLoc $ af_info oldpf)
                Nothing -> return ()
        

expect :: TcK m => Position -> Typattern -> (a -> Ptype TyInfo) -> TcM m a -> TcM m a
expect l pt g m = do
    x <- m
    check_ty l pt (g x)
    return x

check_ty' :: TcK m => Position -> Typattern -> Maybe (Ptype TyInfo) -> TcM m ()
check_ty' p pat Nothing = return ()
check_ty' p pat (Just t) = check_ty p pat t

check_ty :: TcK m => Position -> Typattern -> Ptype TyInfo -> TcM m ()
check_ty loc ety ty =
  case (ety,ty) of
    (TPBool , TBool {}) -> return ()
    (TPInt  , TInt {}) -> return ()
    (TPWord , TWord {}) -> return ()
    (TPArray, TArray {}) -> return ()
    _ -> tyError loc (InvalidType ty ety)

check_ty_eq :: TcK m => Position -> Ptype TyInfo -> Ptype TyInfo -> TcM m ()
check_ty_eq l from to | funit from == funit to = return ()
                      | otherwise = tyError l $ TypeMismatch from to
    
expr_ty_assign :: TcK m => Position -> Pexpr Position -> Ptype TyInfo -> TcM m (Pexpr TyInfo)
expr_ty_assign p e t = do
    e' <- tt_expr e
    check_ty_assign p e' t

check_ty_assign :: TcK m => Position -> Pexpr TyInfo -> Ptype TyInfo -> TcM m (Pexpr TyInfo)
check_ty_assign l e1@(locTyNote "check_ty_assign" -> t1) t2 | funit t1 == funit t2 = return e1
check_ty_assign l e1@(locTyNote "check_ty_assign" -> TInt) t2@(TWord ws) = return $ Pexpr (tyInfoLoc t2 l) $ Pcast (TWord ws) e1
check_ty_assign l e1@(locTyNote "check_ty_assign" -> t1) t2 = tyError l $ TypeMismatch t1 t2

check_sig :: TcK m => Position -> [Ptype TyInfo] -> [Ptype TyInfo] -> TcM m ()
check_sig l sig given | n1 == n2 = mapM_ (uncurry (check_ty_eq l)) (zip sig given)
                      | otherwise = tyError l $ InvalidArgCount n1 n2
  where
    n1 = length sig
    n2 = length given

check_sig_call :: TcK m => Position -> [Ptype TyInfo] -> [Pexpr TyInfo] -> TcM m [Pexpr TyInfo]
check_sig_call p sig_ given | n1 /= n2 = tyError p $ InvalidArgCount n1 n2
                            | otherwise = do
    mapM (uncurry (check_ty_assign p)) (zip given sig_)
  where
    n1 = length sig_
    n2 = length given

check_sig_lvs :: TcK m => Position -> Bool -> [Ptype TyInfo] -> [Plvalue TyInfo] -> TcM m [Plvalue TyInfo]
check_sig_lvs p canrem sig_ lvs | nlvs > nsig_ = tyError p $ LvalueTooWide
                                | not canrem && nlvs < nsig_ = tyError p $ LvalueTooNarrow
                                | otherwise = do
    let (sig_1,sig_2) = splitAt (nsig_ - nlvs) sig_
    lvs' <- forM (zip sig_2 lvs) $ \(t1,lv) -> check_lvalue_ty t1 lv
    return $ map (\s -> Plvalue (tyInfoLoc s p) PLIgnore) sig_1 ++ lvs'
  where
    nsig_ = length sig_
    nlvs = length lvs

check_lvalue_ty :: TcK m => Ptype TyInfo -> Plvalue TyInfo -> TcM m (Plvalue TyInfo)
check_lvalue_ty t1 lv@(Plvalue ilv lvr) = do
    case infoTy' ilv of
        Just t2 -> check_ty_eq p t1 t2 >> return lv
        Nothing -> check_lvalue_ty' lvr
  where
    p = infoLoc ilv
    check_lvalue_ty' PLIgnore = return $ Plvalue (tyInfoLoc t1 p) PLIgnore
    check_lvalue_ty' (PLParens [e]) = do
        e' <- check_lvalue_ty t1 e
        return $ Plvalue (loc e') $ PLParens [e]
    check_lvalue_ty' (PLParens es) = do
        let etys = map locTy' es
        let tys = catMaybes etys
        wtot <- tt_as_word p t1
        ws <- mapM (tt_as_word p) tys
        if length ws >= pred (length etys)
            then do
                let tgap = TWord $ fromJust $ sizeWord $ wordSize wtot - sum (map wordSize ws)
                es' <- forM es $ \e -> case locTy' e of
                    Just _ -> return e
                    Nothing -> check_lvalue_ty tgap e
                return $ Plvalue (tyInfoLoc t1 p) $ PLParens es'
            else genError p $ text "ambiguous left value"
    check_lvalue_ty' lv = genError p $ text "unexpected left value"

locTyM :: (TcK m,Located a,LocOf a ~ TyInfo) => a -> TcM m (Ptype TyInfo)
locTyM x = case locTy' x of
    Nothing -> genError (infoLoc $ loc x) $ text "non-typed lvalue"
    Just t -> return t

