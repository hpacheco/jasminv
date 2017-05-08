{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveDataTypeable, DeriveGeneric, FlexibleContexts, ConstraintKinds, ScopedTypeVariables, ViewPatterns #-}

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

tt_fun :: TcK m => Pident Position -> TcM m (Pfundef TyInfo)
tt_fun (Pident l n) = getFun l (Pident () n)

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
peop2_of_eqop MulEq  = Just Mul2
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
    let ety = infoTy $ loc e
    let eloc = infoLoc $ loc e
    let cast' TInt TInt = return e
        cast' TInt (TWord w) = return $ Pexpr (tyInfo $ TWord w) (Pcast w e)
        cast' (TWord w1) (TWord w2) | w1 == w2 = return e
        cast' ety ty = tyError eloc $ InvalidCast ety ty
    cast' ety ty

tt_op2 :: TcK m => Position -> Peop2 -> Pexpr TyInfo -> Pexpr TyInfo -> TcM m (Pexpr_r TyInfo,Ptype TyInfo)
tt_op2 l op e1 e2 = do
    let ty1 = infoTy $ loc e1
    let ty2 = infoTy $ loc e2
    case (op,ty1,ty2) of
        (flip elem [Add2,Sub2,Mul2] -> True,TInt,TInt) -> return (PEOp2 op e1 e2,TInt)
        (flip elem [And2,Or2] -> True,TBool,TBool) -> return (PEOp2 And2 e1 e2,TBool)
        (flip elem [Eq2,Neq2,Lt2,Le2,Gt2,Ge2] -> True,sty1,sty2) -> do
            sty <- max_ty (TypeCheckerError l $ InvOpInExpr op) sty1 sty2
            e1' <- cast_pexpr e1 sty1
            e2' <- cast_pexpr e2 sty2
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
    t <- tt_concat_types l (map (infoTy . loc) e')
    return (PEParens e',t)
tt_expr_r l (PEBool b) = do
    return (PEBool b,TBool)
tt_expr_r l (PEInt i) = do
    return (PEInt i,TInt)
tt_expr_r l (PEVar v) = do
    v' <- tt_var v False
    return (PEVar v',infoTy $ loc v')
tt_expr_r l (PEFetch ct x o) = do
    x' <- tt_var x False
    w <- tt_as_word l (infoTy $ loc x')
    o' <- tt_int o
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
    i' <- tt_int i
    ty <- tt_as_array l (infoTy $ loc x')
    return (PEGet x' i',ty)
tt_expr_r l (PEOp1 Not1 pe) = do
    pe' <- tt_bool pe
    return (PEOp1 Not1 pe',TBool)
tt_expr_r l (PEOp2 pop pe1 pe2) = do
    pe1' <- tt_expr pe1
    pe2' <- tt_expr pe2
    tt_op2 l pop pe1' pe2'

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
    let ety = locTy e
    when (funit ty /= funit ety) $ tyError l $ TypeMismatch ty ety
    let Pident ln n = ppa_name pp
    let x = Pident (tyInfoLoc ty ln) n
    addVar x
    return $ Pparam ty x e

tt_lvalue :: TcK m => Plvalue Position -> TcM m (Plvalue TyInfo)
tt_lvalue (Plvalue l v) = do
    (v',t) <- tt_lvalue_r l v
    return $ Plvalue (tyInfoLoc' t l) v'

tt_lvalue_r :: TcK m => Position -> Plvalue_r Position -> TcM m (Plvalue_r TyInfo,Maybe (Ptype TyInfo))
tt_lvalue_r p PLIgnore = return (PLIgnore,Nothing)
tt_lvalue_r p (PLVar x) = do
    x' <- tt_var x True
    return (PLVar x',Just $ locTy x')
tt_lvalue_r p (PLArray x pi) = do
    x' <- tt_var x True
    i <- tt_int pi
    ty <- tt_as_array p (locTy x')
    return (PLArray x' i,Just ty)
tt_lvalue_r p (PLMem st x pe) = do
    x' <- tt_var x True
    pe' <- tt_int pe
    w <- tt_as_word p (locTy x')
    st' <- forM st $ \st -> do
        sty <- tt_type st >>= tt_as_word p
        if sty < w
            then tyError p $ InvalidCast (TWord sty) (TWord w)
            else return sty
    let st'' = Just $ TWord $ maybe w id st'
    return (PLMem st'' x' pe',st'')

tt_expr_of_lvalue :: TcK m => Plvalue TyInfo -> TcM m (Pexpr TyInfo)
tt_expr_of_lvalue (Plvalue i lv) = do
    let p = infoLoc i
    e <- tt_expr_of_lvalue' p lv
    return $ Pexpr i e
  where
    tt_expr_of_lvalue' p (PLVar x) = return $ PEVar x
    tt_expr_of_lvalue' p (PLArray x i) = return $ PEGet x i
    tt_expr_of_lvalue' p (PLMem t x e) = return $ PEFetch t x e
    tt_expr_of_lvalue' p lv = tyError p $ InvalidLRValue (Plvalue () $ funit lv)

tt_opsrc :: TcK m => Eqoparg -> Maybe Peop2 -> Pexpr Position -> TcM m Opsrc 
tt_opsrc lv Nothing (Pexpr _ (PEOp2 op pe1 pe2)) = do
    case pe2 of
        Pexpr _ (PEOp2 op' pe2 pe3) -> do
            pe1' <- tt_expr pe1
            pe2' <- tt_expr pe2
            pe3' <- tt_expr pe3
            return $ TriOp op op' pe1' pe2' pe3'
        _ -> do
            pe1' <- tt_expr pe1
            pe2' <- tt_expr pe2
            return $ BinOp op pe1' pe2'
tt_opsrc e1 (Just eqop) (Pexpr _ (PEOp2 op pe2 pe3)) = do
    pe2' <- tt_expr pe2
    pe3' <- tt_expr pe3
    return $ TriOp eqop op e1 pe2' pe3'
tt_opsrc e1 (Just eqop) pe = do
    pe' <- tt_expr pe
    return $ BinOp eqop e1 pe'
tt_opsrc lv Nothing pe = do
    pe' <- tt_expr pe
    pe'' <- tt_shift_expr lv pe'
    return $ NoOp pe''

-- special shift expressions
tt_shift_expr :: TcK m => Eqoparg -> Pexpr TyInfo -> TcM m (Pexpr TyInfo)
tt_shift_expr lv@(locTy -> TWord wlv) re@(Pexpr _ (PEOp2 op@(flip elem [Shr2,Shl2] -> True) (Pexpr (infoTy -> TWord wtot) (PEParens es)) n@(locTy -> TInt))) = do
    return $ Pexpr (loc lv) $ Pcast wlv $ Pexpr (loc re) $ PEOp2 Shr2 re (intPexpr $ toEnum $ wordSize wtot - wordSize wlv)
tt_shift_expr lv re = return re

carry_op :: Peop2 -> Op
carry_op Add2 = Oaddcarry
carry_op Sub2 = Osubcarry

tt_bool :: TcK m => Pexpr Position -> TcM m (Pexpr TyInfo)
tt_bool x = expect (loc x) TPBool (infoTy . loc) (tt_expr x)

tt_int :: TcK m => Pexpr Position -> TcM m (Pexpr TyInfo)
tt_int x = expect (loc x) TPInt (infoTy . loc) (tt_expr x)

tt_intvar :: TcK m => Pident Position -> Bool -> TcM m (Pident TyInfo)
tt_intvar x isWrite = expect (loc x) TPInt (infoTy . loc) (tt_var x isWrite)

tt_instr :: TcK m => Pinstr Position -> TcM m (Pinstr TyInfo)
tt_instr (Pinstr l i) = do
    i' <- tt_instr_r l i
    cl <- getDecClass
    return $ Pinstr (decInfoLoc cl l) i'

tt_instr_r :: TcK m => Position -> Pinstr_r Position -> TcM m (Pinstr_r TyInfo)
tt_instr_r p (PIIf c st sf) = do
    c' <- tt_bool c
    st' <- tt_block st
    sf' <- mapM tt_block sf
    return $ PIIf c' st' sf'
tt_instr_r p (PIFor x d i1 i2 s) = do
    i1' <- tt_int i1
    i2' <- tt_int i2
    x' <- tt_intvar x False
    s' <- tt_block s
    return $ PIFor x' d i1' i2' s'
tt_instr_r p (PIWhile s1 c s2) = do
    c' <- tt_bool c
    s1' <- mapM tt_block s1
    s2' <- mapM tt_block s2
    return $ PIWhile s1' c' s2'
tt_instr_r p (PIAssign ls RawEq (Pexpr _ (PECall f args)) Nothing) = do
    f' <- tt_fun f
    lvs <- mapM tt_lvalue ls
    let rty = map (snd) $ Foldable.concat $ pdf_rty f'
    lvs' <- check_sig_lvs p False rty lvs
    args' <- mapM tt_expr args
    args'' <- check_sig_call p (map (snd . pa_ty) $ pdf_args f') args'
    return $ Ccall lvs' (pdf_name f') args''
tt_instr_r p (PIAssign ls eqop pe Nothing) = do
    lvs <- mapM tt_lvalue ls
    let mksrc [flip elem [TInt,TBool] . locTy -> True] (flip elem [RawEq,AddEq,SubEq] -> True) = do
            e <- tt_expr pe
            return $ ScalOp eqop e
        mksrc lvs eqop = do
            lve' <- if null lvs
                then tyError p EqOpWithNoLValue
                else tt_expr_of_lvalue (last lvs) 
            let eqop' = peop2_of_eqop eqop
            opsrc <- tt_opsrc lve' eqop' pe
            return $ NoScalOp opsrc    
    src <- mksrc lvs eqop
    let mki [lv] (ScalOp eqop e) = do
            e' <- case eqop of
                RawEq -> return e
                (flip elem [AddEq,SubEq] -> True) -> do
                    lve <- tt_expr_of_lvalue lv
                    check_ty_eq p (locTy lv) TInt
                    check_ty_eq p (locTy e) TInt
                    let Just op2 = peop2_of_eqop eqop
                    return $ Pexpr (tyInfoLoc TInt p) (PEOp2 op2 lve e)
            mapM_ (check_ty_eq p (locTy e')) (locTy' lv)
            return $ PIAssign [lv] RawEq e Nothing
        mki [lv] (NoScalOp (NoOp e)) = do
            forM (locTy' lv) (check_ty_assign p e)
            return $ PIAssign [lv] RawEq e Nothing
        -- carry operations without explicit input carry flag
        mki lvs (NoScalOp (BinOp o@(flip elem [Add2,Sub2] -> True) e1 e2)) = do
            check_ty p TPWord (locTy e1)
            e2 <- check_ty_assign p e2 (locTy e1)
            lvs <- check_sig_lvs p True [TBool,locTy e1] lvs
            return $ Copn lvs (carry_op o) [e1,e2,falsePexpr]
        -- carry operations with explicit input carry flag
        mki lvs (NoScalOp (TriOp op1@(flip elem [Add2,Sub2] -> True) op2 e1 e2 e3)) | op1 == op2 = do
            check_ty p TPWord (locTy e1)
            e2 <- check_ty_assign p e2 (locTy e1)
            check_ty p TPBool (locTy e3)
            lvs <- check_sig_lvs p True [TBool,locTy e1] lvs
            return $ Copn lvs (carry_op op1) [e1,e2,e3]
        mki lvs op = tyError p $ Unsupported $ text (show lvs) <+> text "=" <+> text (show op)
    mki lvs src
tt_instr_r p (PIAssign ls eqop e (Just c)) = do
    c' <- tt_bool c
    PIAssign ls' eqop' e' Nothing <- tt_instr_r p $ PIAssign ls eqop e Nothing
    return $ PIAssign ls' eqop' e' (Just c')
    
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

tt_fundef :: TcK m => Pfundef Position -> TcM m (Pfundef TyInfo)
tt_fundef pf@(Pfundef cc name args rty body l) = tt_global $ do
    let name' = fmap noTyInfo name
    args' <- tt_vardecls' args
    rty' <- mapM (mapM (mapSndM tt_type)) rty
    (body',cl) <- withDecClass $ tt_funbody body
    let pf' = Pfundef cc name' args' rty' body' (decInfoLoc cl l)
    check_sig l (map (snd) $ Foldable.concat rty') (map (infoTy . loc) $ Foldable.concat $ pdb_ret body')
    addFun pf'
    return pf'

tt_item :: TcK m => Pitem Position -> TcM m (Pitem TyInfo)
tt_item (PParam pp) = liftM PParam $ tt_param pp
tt_item (PFundef pf) = liftM PFundef $ tt_fundef pf

tt_program :: TcK m => Pprogram Position -> TcM m (Pprogram TyInfo)
tt_program (Pprogram pm) = liftM Pprogram $ mapM tt_item pm

-- * State

type Eqoparg = (Pexpr TyInfo)

data Opsrc
    = NoOp Eqoparg
    | BinOp Peop2 Eqoparg Eqoparg
    | TriOp Peop2 Peop2 Eqoparg Eqoparg Eqoparg
  deriving (Eq,Ord,Show,Data,Typeable,Generic)

instance Monad m => PP m Opsrc where
    pp (NoOp o) = pp o
    pp (BinOp o e1 e2) = do
        p1 <- pp e1
        p2 <- pp e2
        po <- pp o
        return $ p1 <+> po <+> p2
    pp (TriOp o1 o2 e1 e2 e3) = do
        po1 <- pp o1
        po2 <- pp o2
        pe1 <- pp e1
        pe2 <- pp e2
        pe3 <- pp e3
        return $ pe1 <+> po1 <+> pe2 <+> po2 <+> pe3

data IOp
    = ScalOp Peqop (Pexpr TyInfo)
    | NoScalOp Opsrc
  deriving (Eq,Ord,Show,Data,Typeable,Generic)

instance Monad m => PP m IOp where
    pp (ScalOp o e) = do
        po <- pp o
        pe <- pp e
        return $ po <+> pe
    pp (NoScalOp o) = pp o

type TcK m = Monad m
type TcM m = StateT TcEnv (ExceptT JasminError m)

data TcEnv = TcEnv
    { vars :: Map Piden (Maybe Pstorage,Ptype TyInfo) -- ((global=Nothing,local=Just storage),type)
    , funs :: Map Piden (Pfundef TyInfo) -- functions
    , decClass :: DecClass -- log of read/written variables
    }
  deriving (Eq,Ord,Show,Data,Typeable,Generic)

emptyTcEnv = TcEnv Map.empty Map.empty emptyDecClass

-- * Utilities

runTcM :: TcK m => TcM m a -> m (Either JasminError a)
runTcM m = runExceptT (State.evalStateT m emptyTcEnv)

tt_local :: TcK m =>  TcM m a -> TcM m a
tt_local m = do
    env <- State.get
    let dropTest v (_,b) = if b then True else isJust (Map.lookup v (Map.filter (isJust . fst) $ vars env))
    let dropLocals (xs,b) = (Map.filterWithKey dropTest xs,b)
    x <- m
    State.modify $ \e -> e
        { vars = Map.filter (isNothing . fst) (vars e) `Map.union` Map.filter (isJust . fst) (vars env)
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
    case Map.lookup pn vs of
        Just (sto,vt) -> do
            let isGlobal = isNothing sto
            let rs = if isWrite then (Map.empty,isGlobal) else (Map.singleton pn (vt,isGlobal),isGlobal)
            let ws = if isWrite then (Map.singleton pn (vt,isGlobal),isGlobal) else (Map.empty,isGlobal)
            State.modify $ \env -> env { decClass = addDecClassVars rs ws (decClass env)  }
            return $ Pident (stotyInfoLoc' sto vt l) n
        Nothing -> tyError l $ UnknownVar pn (text $ show vs)

addVar :: TcK m => Pident TyInfo -> TcM m ()
addVar (Pident i n) = do
    let sto = infoSto' i
    let ty = infoTy i
    State.modify $ \env -> env { vars = Map.insert (Pident () n) (sto,ty) (vars env) }

localVars :: TcK m => TcM m a -> TcM m a
localVars m = do
    x <- m
    State.modify $ \env -> env { vars = Map.filter (isNothing . fst) (vars env) }
    return x

getFun :: TcK m => Position -> Piden -> TcM m (Pfundef TyInfo)
getFun l n = do
    fs <- State.gets funs
    case Map.lookup n fs of
        Just fdef -> return fdef
        Nothing -> tyError l $ UnknownFun n (text $ show fs)

addFun :: TcK m => Pfundef TyInfo -> TcM m ()
addFun pf = do
    fs <- State.gets funs
    let n = funit $ pdf_name pf
    let l = infoLoc $ pdf_info pf
    case Map.lookup n fs of
        Just oldpf -> tyError l $ DuplicateFun n (infoLoc $ pdf_info oldpf)
        Nothing -> State.modify $ \env -> env { funs = Map.insert n pf (funs env) }

expect :: TcK m => Position -> Typattern -> (a -> Ptype TyInfo) -> TcM m a -> TcM m a
expect l pt g m = do
    x <- m
    check_ty l pt (g x)
    return x

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
    

check_ty_assign :: TcK m => Position -> Pexpr TyInfo -> Ptype TyInfo -> TcM m (Pexpr TyInfo)
check_ty_assign l e1@(locTy -> t1) t2 | funit t1 == funit t2 = return e1
check_ty_assign l e1@(locTy -> TInt) t2@(TWord ws) = return $ Pexpr (tyInfoLoc t2 l) $ Pcast ws e1
check_ty_assign l e1@(locTy -> t1) t2 = tyError l $ TypeMismatch t1 t2

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
    forM_ (zip sig_2 (map locTy' lvs)) $ \(t1,mbt2) -> mapM_ (check_ty_eq p t1) mbt2
    return $ map (\s -> Plvalue (tyInfoLoc s p) PLIgnore) sig_1 ++ lvs
  where
    nsig_ = length sig_
    nlvs = length lvs


