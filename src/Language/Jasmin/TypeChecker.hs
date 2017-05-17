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

tt_as_word :: TcK m => Position -> Ptype TyInfo -> TcM m Int
tt_as_word l (TWord ws) = return ws
tt_as_word l ty = tyError l $ InvalidType (ty) TPWord

peop2_of_eqop :: Peqop -> Maybe Peop2
peop2_of_eqop RawEq  = Nothing
peop2_of_eqop AddEq  = Just Add2
peop2_of_eqop SubEq  = Just Sub2
peop2_of_eqop MulEq  = Just Mul2
peop2_of_eqop ShREq  = Just $ Shr2 Unsigned
peop2_of_eqop ShLEq  = Just Shl2
peop2_of_eqop BAndEq = Just BAnd2
peop2_of_eqop BXOrEq = Just BXor2
peop2_of_eqop BOrEq  = Just BOr2

max_ty :: TcK m => Position -> JasminError -> Ptype info -> Ptype info -> TcM m (Ptype info)
max_ty p err (TInt Nothing) (TInt Nothing) = return (TInt Nothing)
max_ty p err t1@(TInt (Just w)) (TInt Nothing) = return t1
max_ty p err (TInt Nothing) t2@(TInt (Just w)) = return t2
max_ty p err (TInt Nothing) t2@(TWord _) = return t2
max_ty p err t1@(TWord _) (TInt Nothing) = return t1
max_ty p err t1@(TWord w1) (TWord w2) | w1 == w2 = return t1
max_ty p err t1 t2 = do
    p1 <- pp t1
    p2 <- pp t2
    throwError $ GenericError p (text "max_ty" <+> p1 <+> p2) (Just err)

cast_pexpr :: TcK m => Pexpr TyInfo -> Ptype TyInfo -> TcM m (Pexpr TyInfo)
cast_pexpr e ty = do
    let ety = infoTyNote "cast_pexpr" $ loc e
    let eloc = infoLoc $ loc e
    let cast' (TInt w1) (TInt w2) | w1 == w2 = return e
        cast' (TInt Nothing) (TInt (Just w)) = return $ Pexpr (tyInfo $ TInt $ Just w) (Pcast (TInt $ Just w) e)
        cast' (TInt Nothing) (TWord w) = return $ Pexpr (tyInfo $ TWord w) (Pcast (TWord w) e)
        cast' (TWord w1) (TWord w2) | w1 == w2 = return e
        cast' (TWord w1) (TWord w2) | w1 < w2 = return $ Pexpr (tyInfo $ TWord w2) $ Pcast (TWord w2) e
        cast' (isNumericType -> True) (TInt Nothing) = return $ Pexpr (tyInfo $ TInt Nothing) $ Pcast (TInt Nothing) e
        cast' ety ty = tyError eloc $ InvalidCast ety ty
    cast' ety ty

tt_op2 :: TcK m => Position -> Peop2 -> Pexpr TyInfo -> Pexpr TyInfo -> TcM m (Pexpr_r TyInfo,Ptype TyInfo)
tt_op2 l op e1 e2 = do
    let ty1 = infoTyNote "tt_op2" $ loc e1
    let ty2 = infoTyNote "tt_op2" $ loc e2
    case (op,ty1,ty2) of
        (isLNumericPeop2 -> True,isNumericType -> True,isNumericType -> True) -> do
            e2' <- cast_pexpr e2 $ TInt Nothing
            return (PEOp2 op e1 e2',locTy e1)
        (isLRNumericPeop2 -> True,isNumericType -> True,isNumericType -> True) -> do
            ty <- max_ty l (TypeCheckerError l $ InvOpInExpr op) ty1 ty2
            e1' <- cast_pexpr e1 ty
            e2' <- cast_pexpr e2 ty
            return (PEOp2 op e1' e2',ty)
        (isBoolPeop2 -> True,TBool,TBool) -> return (PEOp2 op e1 e2,TBool)
        (isCmpPeop2 -> Just _,ty1,ty2) -> do
            ty <- max_ty l (TypeCheckerError l $ InvOpInExpr op) ty1 ty2
            e1' <- cast_pexpr e1 ty
            e2' <- cast_pexpr e2 ty
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
    ws <- mapM (tt_as_word p) xs
    let w = sum ws
    return $ TWord w

tt_expr_r :: TcK m => Position -> Pexpr_r Position -> TcM m (Pexpr_r TyInfo,Ptype TyInfo)
tt_expr_r l (PEParens e) = do
    e' <- mapM tt_expr e
    t <- tt_concat_types l (map (infoTyNote "tt_expr_r_parens" . loc) e')
    return (PEParens e',t)
tt_expr_r l (PEBool b) = do
    return (PEBool b,TBool)
tt_expr_r l (PEInt i) = do
    return (PEInt i,TInt Nothing)
tt_expr_r l (PEVar v) = do
    v' <- tt_var v False
    return (PEVar v',infoTyNote "tt_expr" $ loc v')
tt_expr_r l (PEFetch ct x o) = do
    x' <- tt_var x False
    w <- tt_as_word l (infoTyNote "tt_expr" $ loc x')
    o' <- tt_index o
    ct' <- mapM tt_type ct
    ct'' <- case ct' of
        Nothing -> return $ TWord 64
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
tt_expr_r l (ValidExpr (x:es)) = checkAnn l (Just False) $ do
    x' <- tt_expr x
    es' <- mapM tt_index es
    return (ValidExpr (x':es'),TBool)
tt_expr_r l qe@(QuantifiedExpr q vs e) = checkAnn l (Just False) $ tt_local $ do
    vs' <- mapM tt_annarg vs
    e' <- tt_bool e
    return (QuantifiedExpr q vs' e',TBool)
tt_expr_r l (Pcast t e) = checkAnn l (Just False) $ do -- FIXME: we do not verify casts
    t' <- tt_type t
    e' <- tt_expr e
    return (Pcast t' e',t')

tt_type :: TcK m => Ptype Position -> TcM m (Ptype TyInfo)
tt_type TBool = return TBool
tt_type (TInt w) = return $ TInt w
tt_type (TWord ws) = do
    return $ TWord ws
tt_type (TArray ws e) = do
    e' <- tt_expr e
    return $ TArray ws e'

tt_annarg :: TcK m => Annarg Position -> TcM m (Annarg TyInfo)
tt_annarg (Annarg t v@(Pident l n) e) = do
    t' <- tt_type t
    let info = tyInfoLoc t' l
    let v' = Pident info n
    addVar v'
    e' <- forM e $ \e -> do
        e' <- tt_expr e
        e'' <- check_ty_assign l e' t'
        return e''
    return (Annarg t' v' e')
    
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

tt_lwords' :: TcK m => [Plvalue Position] -> TcM m [Plvalue TyInfo]
tt_lwords' = aux Nothing
    where
    aux _ [] = return []
    aux (Just w) (x:xs) = do
        x' <- tt_lvalue x
        x' <- check_lvalue_ty w x'
        xs' <- aux (Just w) xs
        return (x':xs')
    aux Nothing (x:xs) = do
        x' <- tt_lvalue x
        xs' <- aux (locTy' x') xs
        return (x':xs')

tt_lword' :: TcK m => Plvalue Position -> TcM m (Plvalue TyInfo)
tt_lword' x = do
    x' <- tt_lvalue x
    tx <- locTyM x'
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
    e' <- mapM (tt_lvalue) e
    let tys = map locTy' e'
    t <- if all isJust tys
        then liftM Just $ tt_concat_types l (map fromJust tys)
        else return Nothing
    return (PLParens e',t)
tt_lvalue_r p (PLVar x) = do
    x' <- tt_var x True
    let tx' = locTyNote "tt_lvalue_var" x'
    return (PLVar x',Just tx')
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
    let st'' = TWord $ maybe w id st'
    return (PLMem (Just st'') x' pe',Just st'')

tt_expr_of_lvalues :: MonadError JasminError m => Position -> [Plvalue info] -> m (Pexpr info)
tt_expr_of_lvalues p [] = tyError p EqOpWithNoLValue
tt_expr_of_lvalues p lvs = tt_expr_of_lvalue p (last lvs) 

tt_expr_of_lvalue :: MonadError JasminError m => Position -> Plvalue info -> m (Pexpr info)
tt_expr_of_lvalue p (Plvalue i lv) = do
    e <- tt_expr_of_lvalue' p lv
    return $ Pexpr i e
  where
    tt_expr_of_lvalue' :: MonadError JasminError m => Position -> Plvalue_r info -> m (Pexpr_r info)
    tt_expr_of_lvalue' p (PLVar x) = return $ PEVar x
    tt_expr_of_lvalue' p (PLArray x i) = return $ PEGet x i
    tt_expr_of_lvalue' p (PLParens es) = do
        es' <- mapM (tt_expr_of_lvalue p) es
        return $ PEParens es'
    tt_expr_of_lvalue' p (PLMem t x e) = return $ PEFetch t x e
    tt_expr_of_lvalue' p lv = tyError p $ InvalidLRValue (Plvalue () $ funit lv)

carry_op :: Peop2 -> Op
carry_op Add2 = Oaddcarry
carry_op Sub2 = Osubcarry

tt_bool :: TcK m => Pexpr Position -> TcM m (Pexpr TyInfo)
tt_bool x = expect (loc x) TPBool (infoTyNote "tt_bool" . loc) (tt_expr x)

tt_index :: TcK m => Pexpr Position -> TcM m (Pexpr TyInfo)
tt_index = tt_int
--tt_index x = do
--    let p = loc x
--    x' <- tt_expr x
--    check_index p (locTy x')
--    return x'

tt_indexvar :: TcK m => Pident Position -> Bool -> TcM m (Pident TyInfo)
tt_indexvar x isWrite = do
    let p = loc x
    x' <- tt_var x isWrite
    check_index p (locTy x')
    return x'

check_index :: TcK m => Position -> Ptype TyInfo -> TcM m ()
check_index p (TInt Nothing) = return ()
check_index p (TWord _) = return ()
check_index p t = tyError p $ TypeMismatch t (TInt Nothing)

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
tt_instr_r p (PIAssign ls eqop e (Just c)) = do
    tt_instr_r p $ PIIf True c (Pblock p [Pinstr p $ PIAssign ls eqop e Nothing]) Nothing
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
tt_instr_ann_r p (VarDefAnn ann) = do
    ann' <- tt_annarg ann
    return $ VarDefAnn ann'
    
tt_loop_ann :: TcK m => LoopAnnotation Position -> TcM m (LoopAnnotation TyInfo)
tt_loop_ann (LoopAnnotation l x) = withAnn (Just False) $ do
    x' <- tt_loop_ann_r l x
    cl <- getDecClass
    return $ LoopAnnotation (decInfoLoc cl l) x'
    
tt_loop_ann_r :: TcK m => Position -> LoopAnnotation_r Position -> TcM m (LoopAnnotation_r TyInfo)
tt_loop_ann_r p (LDecreasesAnn isFree e) = withAnn (Just False) $ do
    e' <- tt_expr e
    return $ LDecreasesAnn isFree e'
tt_loop_ann_r p (LInvariantAnn isFree isLeak e) = withAnn (Just isLeak) $ do
    e' <- tt_bool e
    return $ LInvariantAnn isFree isLeak e'

tt_proc_ann :: TcK m => ProcedureAnnotation Position -> TcM m (ProcedureAnnotation TyInfo)
tt_proc_ann (ProcedureAnnotation p x) = withAnn (Just False) $ do
    x' <- tt_proc_ann_r p x
    cl <- getDecClass
    return $ ProcedureAnnotation (decInfoLoc cl p) x'

tt_proc_ann_r :: TcK m => Position -> ProcedureAnnotation_r Position -> TcM m (ProcedureAnnotation_r TyInfo)
tt_proc_ann_r p (PDecreasesAnn e) = withAnn (Just False) $ do
    e' <- tt_expr e
    return $ PDecreasesAnn e'
tt_proc_ann_r p (RequiresAnn isFree isLeak e) = withAnn (Just isLeak) $ do
    e' <- tt_bool e
    return $ RequiresAnn isFree isLeak e'
tt_proc_ann_r p (EnsuresAnn isFree isLeak e) = withAnn (Just isLeak) $ do
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
    do      tt_bv_carry_op p lvs re
    `mplus` tt_mul128_op p lvs re

tt_mul128_op :: TcK m => Position -> [Plvalue Position] -> Pexpr Position -> TcM m (Pinstr_r TyInfo)
tt_mul128_op p ls@[lx,ly] (binOp2 -> Just (Mul2,ex,ey)) = do
    ls'@[lx',ly'] <- tt_lwords' ls
    tx'@(TWord wx) <- locTyM lx'
    ty'@(TWord wy) <- locTyM ly'
    let txy = TWord (wx + wy)
    let ixy = tyInfoLoc txy p
    ex' <- expr_ty_assign p ex tx'
    ey' <- expr_ty_assign p ey ty'
    return $ PIAssign [Plvalue ixy $ PLParens ls'] RawEq (Pexpr ixy $ PEOp2 Mul2 (Pexpr ixy $ Pcast txy ex') (Pexpr ixy $ Pcast txy ey')) Nothing
tt_mul128_op p lvs re = genError p $ text "native instruction not supported"

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

tt_block :: TcK m => Pblock Position -> TcM m (Pblock TyInfo)
tt_block (Pblock l is) = tt_local $ do
    (is',cl) <- withDecClass $ mapM tt_instr is
    return $ Pblock (decInfoLoc cl l) is'

tt_funbody :: TcK m => Pfunbody Position -> TcM m (Pfunbody TyInfo)
tt_funbody (Pfunbody vars instrs ret) = tt_local $ do
    vars' <- mapM tt_vardecl vars
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
    args' <- mapM tt_vardecl' args
    rty' <- mapM (mapM (mapSndM tt_type)) rty
    anns' <- mapM tt_proc_ann anns
    (body',cl) <- withDecClass $ tt_funbody body
    let pf' = Pfundef cc name' args' rty' anns' body' (decInfoLoc cl l)
    check_sig l (map (snd) $ Foldable.concat rty') (map (infoTyNote "tt_fundef" . loc) $ Foldable.concat $ pdb_ret body')
    addFun pf'
    return pf'

tt_axiomdef_ann :: TcK m => AnnAxiomDeclaration Position -> TcM m (AnnAxiomDeclaration TyInfo)
tt_axiomdef_ann  (AnnAxiomDeclaration isLeak args anns p) = tt_global $ withAnn (Just isLeak) $ do
    args' <- mapM tt_annarg args
    anns' <- mapM tt_proc_ann anns
    return (AnnAxiomDeclaration isLeak args' anns' (decInfoLoc emptyDecClass p))

tt_lemmadef_ann :: TcK m => AnnLemmaDeclaration Position -> TcM m (AnnLemmaDeclaration TyInfo)
tt_lemmadef_ann  (AnnLemmaDeclaration isLeak name args anns body p) = tt_global $ withAnn (Just isLeak) $ do
    let name' = fmap noTyInfo name
    args' <- mapM tt_annarg args
    anns' <- mapM tt_proc_ann anns
    (body',cl) <- withDecClass $ mapM tt_block body
    return (AnnLemmaDeclaration isLeak name' args' anns' body' (decInfoLoc cl p))

tt_fundef_ann :: TcK m => AnnFunDeclaration Position -> TcM m (AnnFunDeclaration TyInfo)
tt_fundef_ann  (AnnFunDeclaration isLeak ret name args anns body p) = tt_global $ withAnn (Just isLeak) $ do
    ret' <- tt_type ret
    let name' = fmap noTyInfo name
    args' <- mapM tt_annarg args
    anns' <- mapM tt_proc_ann anns
    (body',cl) <- withDecClass $ tt_expr body
    check_sig p [ret'] [locTy body']
    return (AnnFunDeclaration isLeak ret' name' args' anns' body' (decInfoLoc cl p))

tt_program :: TcK m => Pprogram Position -> TcM m (Pprogram TyInfo)
tt_program (Pprogram pm) = liftM Pprogram $ mapM tt_item pm

-- * State

type TcK m = MonadIO m
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
    `mplus` (getAnnLemma p n >>= \f -> return (lemma_name f,[],map (aa_ty) $ lemma_args f))
    `mplus` (getAnnFun p n >>= \f -> return (af_name f,[af_ty f],map (aa_ty) $ af_args f))

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
check_ty_assign l e1@(locTyNote "check_ty_assign" -> TInt Nothing) t2@(TWord ws) = return $ Pexpr (tyInfoLoc t2 l) $ Pcast (TWord ws) e1
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
                let tgap = TWord $ wtot - sum ws
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

