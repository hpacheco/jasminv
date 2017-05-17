{-# LANGUAGE StandaloneDeriving, TupleSections, DeriveGeneric, DeriveAnyClass, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, ViewPatterns, GADTs, ConstraintKinds, FlexibleContexts, ScopedTypeVariables #-}

module Language.Jasmin.Transformation.SBV where

import Data.IORef
import Data.Proxy
import Data.Bifunctor
import Data.LargeWord hiding (Word256)
import Data.SBV hiding ((<+>))
import Data.SBV.Dynamic (SVal,svJoin,svExtract)
import Data.SBV.Internals (SBV(..),genFromCW,genLiteral,genMkSymVar,liftDMod,liftQRem)
import qualified Data.SBV.Dynamic as SBV
import qualified Data.SBV.Internals as SBV
import Data.Map (Map(..))
import qualified Data.Map as Map
import Language.Vars
import Data.Generics hiding (Generic,typeOf)
import GHC.Generics
import Data.Maybe
import Safe

import Control.Monad.Except
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State as State

import Language.Jasmin.Syntax
import Language.Position
import Language.Location
import Language.Jasmin.Error
import Language.Jasmin.TypeChecker.TyInfo
import Language.Jasmin.Transformation.Simplify
import Language.Jasmin.Transformation.VCGen
import Text.PrettyPrint.Exts
import Options

import System.IO

import Utils

isOkThmResult :: ThmResult -> Bool
isOkThmResult (ThmResult (Unsatisfiable _)) = True
isOkThmResult _ = False

pprogramToSBV :: Options -> Pprogram TyInfo -> IO [ThmResult]
pprogramToSBV opts prog@(Pprogram xs) = do
    concatMapM (pitemToSBV opts) xs

pitemToSBV :: Options -> Pitem TyInfo -> IO [ThmResult]
pitemToSBV opts (PFundef f) = pfundefToSBV opts f
pitemToSBV opts (PParam i) = error "sbv param not supported"

pfundefToSBV :: Options -> Pfundef TyInfo -> IO [ThmResult]
pfundefToSBV opts f = do
    vcs <- genVCsPfundef f
    mapM (uncurry (vcToSBV opts)) vcs

vcToSBV :: Options -> [Pinstr TyInfo] -> Pexpr TyInfo -> IO ThmResult
vcToSBV opts is assert = do
    let go = do
        mapM_ pinstrToSBV is
        pexprToSBVBool assert
    proveSBVMWith opts (infoLoc $ loc assert) go

panninstr_rToSBV :: TyInfo -> StatementAnnotation_r TyInfo -> SBVM Symbolic ()
panninstr_rToSBV t (AssumeAnn False e) = do
    sbve <- pexprToSBVBool e
    lift2 $ constrain sbve
panninstr_rToSBV t (AssertAnn False e) = genError (infoLoc t) $ text "no SMT asserts"
panninstr_rToSBV t (EmbedAnn isLeak i) = unless isLeak $ pinstrToSBV i
panninstr_rToSBV t (VarDefAnn arg) = annargToSBV arg

annargToSBV :: Annarg TyInfo -> SBVM Symbolic ()
annargToSBV (Annarg ty n e) = do
    e' <- mapM pexprToSBV e
    addSBVar (infoLoc $ loc n) ty (funit n) e'    

pblockToSBV :: Pblock TyInfo -> SBVM Symbolic ()
pblockToSBV (Pblock t is) = mapM_ pinstrToSBV is

pinstrToSBV :: Pinstr TyInfo -> SBVM Symbolic ()
pinstrToSBV (Pinstr t i) = pinstr_rToSBV t i

pinstr_rToSBV :: TyInfo -> Pinstr_r TyInfo -> SBVM Symbolic ()
pinstr_rToSBV t (PIIf _ c s1 s2) = do
    c' <- pexprToSBVBool c
    let m1 = pblockToSBV s1
    let m2 = maybe (return ()) pblockToSBV s2
    sbvIf c' m1 m2
pinstr_rToSBV t (PIAssign lvs RawEq e Nothing) = do
    e' <- pexprToSBV e
    passignToSBV t lvs [e']
pinstr_rToSBV t (Copn ls o es) = popn_rToSBV t ls o es
pinstr_rToSBV t (Anninstr i) = panninstr_rToSBV t i
pinstr_rToSBV t i = genError (infoLoc t) $ text "instruction can't be converted to SMT"

passignToSBV :: TyInfo -> [Plvalue TyInfo] -> [SBVar] -> SBVM Symbolic ()
passignToSBV t [Plvalue ty (PLVar n)] [v] = addSBVar (infoLoc t) (infoTy ty) (funit n) (Just v)
passignToSBV t [Plvalue ty (PLArray n e)] [v] = do
    e' <- pexprToSBV e
    writeSBArr (infoLoc t) (funit n) e' v
passignToSBV t ls vs | length ls > 1 && length ls == length vs = do
    forM_ (zip ls vs) $ \(l,v) -> passignToSBV t [l] [v]
passignToSBV t lv v = genError (infoLoc t) $ text "lvalue not supported in SMT"

popn_rToSBV :: TyInfo -> [Plvalue TyInfo] -> Op -> [Pexpr TyInfo] -> SBVM Symbolic ()
popn_rToSBV t ls Oaddcarry [e1,e2,cf] = do
    SBVal e1' <- pexprToSBV e1
    SBVal e2' <- pexprToSBV e2
    cf' <- pexprToSBVBool cf
    let (vcf,ve) = sbvAdc (infoTy $ loc e1) e1' e2' cf'
    passignToSBV t ls [SBVal $ unSBV vcf,SBVal $ ve]
popn_rToSBV t ls o es = error "popn_rToSBV"

sbvAdc :: Ptype TyInfo -> SVal -> SVal -> SBool -> (SBool,SVal)
sbvAdc t x y cf = (mkSBool cf',s')
    where
    one = sbvInteger t 1
    zero = sbvInteger t 0
    s = x `SBV.svPlus` y
    scf = SBV.svIte (unSBV cf) one zero
    s' = s `SBV.svPlus` scf
    cf' = (SBV.svLessThan s x) `sbvOr` (SBV.svLessThan s y) `sbvOr` (SBV.svLessThan s' s)

sbvIf :: SBool -> SBVM Symbolic () -> SBVM Symbolic () -> SBVM Symbolic ()
sbvIf c m1 m2 = do
    env1 <- liftM snd $ blockSBVM m1
    env2 <- liftM snd $ blockSBVM m2
    let env' = ite c env1 env2
    State.put env'

pexprToSBVBool :: Pexpr TyInfo -> SBVM Symbolic SBool
pexprToSBVBool e = do
    SBVal e' <- pexprToSBV e
    return $ SBV e'

pexprToSBV :: Pexpr TyInfo -> SBVM Symbolic SBVar
pexprToSBV (Pexpr t e) = pexpr_rToSBV t e

pexpr_rToSBV :: TyInfo -> Pexpr_r TyInfo -> SBVM Symbolic SBVar
pexpr_rToSBV t (PEVar v) = getSBVar (infoLoc t) (funit v)
pexpr_rToSBV t (PEBool b) = return $ SBVal $ SBV.svBool b
pexpr_rToSBV t (PEInt i) = return $ SBVal $ sbvInteger (infoTy t) i
pexpr_rToSBV t (PEOp1 o e1) = op1_rToSBV t o e1
pexpr_rToSBV t (PEOp2 o e1 e2) = op2_rToSBV t o e1 e2
pexpr_rToSBV t (PEGet n e) = do
    e' <- pexprToSBV e
    readSBArr (infoLoc t) (funit n) e'
pexpr_rToSBV t (Pcast te e) = pcast_rToSBV t te e
pexpr_rToSBV t (PEParens [e]) = pexprToSBV e
pexpr_rToSBV t e = do
    pe <- pp e
    genError (infoLoc t) $ text "expression not encoded in SBV: " <+> pe
--pexpr_rToSBV t (QuantifiedExpr q args e) = forAll

pcast_rToSBV :: TyInfo -> Ptype TyInfo -> Pexpr TyInfo -> SBVM Symbolic SBVar
pcast_rToSBV l (TWord w) e@(locTy -> TWord w') | w >= w' = do
    SBVal e' <- pexprToSBV e
    return $ SBVal $ svJoin (sbvWord (w - w') 0) e'
pcast_rToSBV l (TWord 64) e@(locTy -> TInt Nothing) = do
    SBVal e' <- pexprToSBV e
    let (SBV we')::SWord64 = sFromIntegral $ mkSInteger e'
    return $ SBVal we'
pcast_rToSBV l t e@(locTy -> et) = do
    SBVal e' <- pexprToSBV e
    return $ SBVal $ sbvCast (TInt Nothing) (TWord 512) e'
    
sbvInteger :: Ptype TyInfo -> Integer -> SVal
sbvInteger t i = SBV.svInteger (ptypeKind t) i

sbvWord :: Int -> Integer -> SVal
sbvWord sz i = SBV.svInteger (KBounded False sz) i

op1_rToSBV :: TyInfo -> Peop1 -> Pexpr TyInfo -> SBVM Symbolic SBVar
op1_rToSBV t Not1 e = do
    e' <- pexprToSBVBool e
    return $ SBVal $ unSBV $ bnot e'

sbvAnd = \x y -> unSBV $ mkSBool x &&& mkSBool y
sbvOr = \x y -> unSBV $ mkSBool x ||| mkSBool y

sbvShiftLeft :: Ptype TyInfo -> Ptype TyInfo -> SVal -> SVal -> SVal
sbvShiftLeft = sbvShift SBV.svShiftLeft

sbvShiftRight :: Ptype TyInfo -> Ptype TyInfo -> SVal -> SVal -> SVal
sbvShiftRight = sbvShift SBV.svShiftRight

sbvShift :: (SVal -> SVal -> SVal) -> Ptype TyInfo -> Ptype TyInfo -> SVal -> SVal -> SVal
sbvShift f tx@(TWord w) ty x y = f x y'
    where
    ty' = TWord w -- $ round $ (log (realToFrac w) / log (realToFrac 2)) + 1
    y' = sbvCast ty ty' x
sbvShift f tx ty x y = error $ "sbvShift" ++ pprid tx ++ " " ++ pprid ty

sbvCast :: Ptype TyInfo -> Ptype TyInfo -> SVal -> SVal
sbvCast (TInt Nothing) (TWord 512) x = unSWord512 $ sFromIntegral $ mkSInteger x
sbvCast tx ty x = error $ show $ text "pcast_rToSBV" <+> ppid tx <+> ppid ty

unSWord512 :: SWord512 -> SVal
unSWord512 = unSBV

op2_rToSBV :: TyInfo -> Peop2 -> Pexpr TyInfo -> Pexpr TyInfo -> SBVM Symbolic SBVar
op2_rToSBV t Add2 e1 e2 = nativeOp2 (sbvOp2 SBV.svPlus) e1 e2
op2_rToSBV t Sub2 e1 e2 = nativeOp2 (sbvOp2 SBV.svMinus) e1 e2
op2_rToSBV t Mul2 e1 e2 = nativeOp2 (sbvOp2 SBV.svTimes) e1 e2
op2_rToSBV t And2 e1 e2 = nativeOp2 (sbvOp2 sbvAnd) e1 e2
op2_rToSBV t Or2 e1 e2 = nativeOp2 (sbvOp2 sbvOr) e1 e2
op2_rToSBV t BAnd2 e1 e2 = nativeOp2 (sbvOp2 SBV.svAnd) e1 e2
op2_rToSBV t BOr2 e1 e2 = nativeOp2 (sbvOp2 SBV.svOr) e1 e2
op2_rToSBV t BXor2 e1 e2 = nativeOp2 (sbvOp2 SBV.svXOr) e1 e2
op2_rToSBV t (Shr2 Unsigned) e1 e2 = nativeOp2 (sbvOp2 $ sbvShiftRight (locTy e1) (locTy e2)) e1 e2
op2_rToSBV t Shl2 e1 e2 = nativeOp2 (sbvOp2 $ sbvShiftLeft (locTy e1) (locTy e2)) e1 e2
op2_rToSBV t Eq2 e1 e2 = nativeOp2 (sbvOp2 SBV.svEqual) e1 e2
op2_rToSBV t Neq2 e1 e2 = nativeOp2 (sbvOp2 SBV.svNotEqual) e1 e2
op2_rToSBV t (Lt2 Unsigned) e1 e2 = nativeOp2 (sbvOp2 SBV.svLessThan) e1 e2
op2_rToSBV t (Le2 Unsigned) e1 e2 = nativeOp2 (sbvOp2 SBV.svLessEq) e1 e2
op2_rToSBV t (Gt2 Unsigned) e1 e2 = nativeOp2 (sbvOp2 SBV.svGreaterThan) e1 e2
op2_rToSBV t (Ge2 Unsigned) e1 e2 = nativeOp2 (sbvOp2 SBV.svGreaterEq) e1 e2
op2_rToSBV t Mod2 e1 e2 = nativeOp2 (sbvOp2 $ svMod' $ infoTy t) e1 e2
op2_rToSBV t o e1 e2 = error "op2_rToSBV"

nativeOp2 :: (SBVar -> SBVar -> SBVar) -> Pexpr TyInfo -> Pexpr TyInfo -> SBVM Symbolic SBVar
nativeOp2 f e1 e2 = do
    e1' <- pexprToSBV e1
    e2' <- pexprToSBV e2
    return $ f e1' e2'

-- * State

solverCfg :: Solver -> SMTConfig
solverCfg Boolector = boolector
solverCfg CVC4 = cvc4
solverCfg Yices = yices
solverCfg Z3 = z3
solverCfg MathSAT = mathSAT
solverCfg ABC = abc

proveSBVMWith :: Options -> Position -> SBVM Symbolic SBool -> IO ThmResult
proveSBVMWith opts p m = do
    let cfg = solverCfg (solver' opts)
    when (debugVerification opts) $ liftIO $ hPutStrLn stderr $ "Solving SMT verification condition at " ++ pprid p
    code <- compileToSMTLib SMTLib2 False mgoal
    liftIO $ putStrLn $ "code: " ++ code
    res <- proveWith cfg mgoal
    when (debugVerification opts) $ liftIO $ hPutStrLn stderr $ show res
    return res
  where
    mgoal = do
        e <- runSBVM m emptySBVSt
        case e of
            Left err -> do
                when (debugVerification opts) $ liftIO $ hPutStrLn stderr $ pprid err
                return false
            Right (b,_) -> return b

runSBVM :: SBVK m => SBVM m a -> SBVSt -> m (Either JasminError (a,SBVSt))
runSBVM m st = runExceptT $ runStateT m st

blockSBVM :: SBVK m => SBVM m a -> SBVM m (a,SBVSt)
blockSBVM m = do
    env <- State.get
    e <- lift2 $ runSBVM m env
    case e of
        Left err -> throwError err
        Right (x,env') -> return (x,env')
    
emptySBVSt = SBVSt Map.empty

type SBVK m = (MonadIO m,GenVar Piden m)

type SBVM m = StateT SBVSt (ExceptT JasminError m)

addSBVar :: Position -> Ptype TyInfo -> Piden -> Maybe SBVar -> SBVM Symbolic ()
addSBVar p t n mbv = do
    val <- maybe (sbVar p (pprid n) t) return mbv
    State.modify $ \env -> env { vars = Map.insert n val (vars env) }

sbVar :: Position -> String -> Ptype TyInfo -> SBVM Symbolic SBVar
sbVar p n t@TBool = liftM SBVal $ lift2 $ SBV.svMkSymVar Nothing (ptypeKind t) (Just n)
sbVar p n t@(TInt Nothing) = liftM SBVal $ lift2 $ SBV.svMkSymVar Nothing (ptypeKind t) (Just n)
sbVar p n t@(TInt (Just w)) = liftM SBVal $ lift2 $ SBV.svMkSymVar Nothing (ptypeKind t) (Just n)
sbVar p n t@(TWord w) = liftM SBVal $ lift2 $ SBV.svMkSymVar Nothing (ptypeKind t) (Just n)
sbVar p n (TArray w sz) = do
    SBVal sz' <- pexprToSBV sz
    case SBV.svAsInteger sz' of
        Just w -> do
            vs <- forM [0..w-1] $ \w -> liftM (SBV.svInteger KUnbounded w,) $ liftM unSBVal $ sbVar p ("n"++show w) (TWord $ fromEnum w)
            return $ SBArr $ list2fun vs
        Nothing -> return $ SBArr $ list2fun []

list2fun :: [(SVal,SVal)] -> (SVal -> SVal)
list2fun [] = const $ error "unitialized array"
list2fun ((x,y):xs) = \a -> ite (SBV $ SBV.svEqual x a) y (list2fun xs a)

readSBArr :: Position -> Piden -> SBVar -> SBVM Symbolic SBVar
readSBArr p n (SBVal i) = do
    vs <- State.gets vars
    case Map.lookup n vs of
        Just (SBArr arr) -> return $ SBVal $ arr i
        otherwise -> genError p $ text "readSBArr" <+> ppid n

writeSBArr :: Position -> Piden -> SBVar -> SBVar -> SBVM Symbolic ()
writeSBArr p n (SBVal i) (SBVal e) = do
    State.modify $ \env -> env { vars = Map.update writeArr n (vars env) }
        where writeArr (SBArr f) = Just $ SBArr $ \a' -> ite (SBV $ i `SBV.svEqual` a') e (f a')

getSBVar :: Position -> Piden -> SBVM Symbolic SBVar
getSBVar p n = do
    vs <- State.gets vars
    case Map.lookup n vs of
        Just x -> return x
        otherwise -> genError p $ text "getSBVal" <+> ppid n

data SBVSt = SBVSt
    { vars :: Map Piden SBVar
    }
    deriving (Generic,Mergeable)

instance (Ord k,Mergeable b) => Mergeable (Map k b) where
    symbolicMerge f b m1 m2 = Map.intersectionWith (symbolicMerge f b) m1 m2

instance Mergeable SVal where
    symbolicMerge f (SBV b) v1 v2 | kindOf v1 == kindOf v2 = SBV.svSymbolicMerge (kindOf v1) f b v1 v2
    
instance Mergeable SBVar where
    symbolicMerge f b (SBVal v1) (SBVal v2) = SBVal $ symbolicMerge f b v1 v2
    symbolicMerge _ b (SBArr g) (SBArr h) = SBArr $ \x -> ite b (g x) (h x)

data SBVar where
    SBVal :: SVal -> SBVar
    SBArr :: (SVal -> SVal) -> SBVar

unSBVal (SBVal x) = x

ptypeKind :: Ptype TyInfo -> Kind
ptypeKind (TInt Nothing) = KUnbounded
ptypeKind (TInt (Just w)) = KBounded True w
ptypeKind (TWord w) = KBounded False w
ptypeKind TBool = KBool
ptypeKind t = error $ "ptypeKind: " ++ pprid t

instance GenVar Piden Symbolic where
    mkVar str = liftIO $ mkVar str
    newVar x = liftIO $ newVar x

sbvOp2 :: (SVal -> SVal -> SVal) -> SBVar -> SBVar -> SBVar
sbvOp2 f (SBVal x) (SBVal y) = SBVal $ f x y

mkSBool :: SVal -> SBool
mkSBool x = SBV x

mkSWord512 :: SVal -> SWord512
mkSWord512 = SBV

mkSInteger :: SVal -> SInteger
mkSInteger = SBV

svMod' :: Ptype TyInfo -> SVal -> SVal -> SVal
svMod' (TWord 512) x y = unSBV $ sMod (mkSWord512 x) (mkSWord512 y)
svMod' _ _ _ = error "svMod"

type Word512 = LargeKey Word256 Word256
type SWord512 = SBV Word512
instance HasKind Word512   where kindOf _ = KBounded False 512
instance SDivisible SWord512 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod
instance SymWord Word512 where
  mkSymWord  = genMkSymVar (KBounded False 512)
  literal    = genLiteral  (KBounded False 512)
  fromCW     = genFromCW
instance Splittable SWord512 SWord256 where
    split (SBV x) = (SBV (svExtract 511 256 x), SBV (svExtract 255 0 x))
    SBV a # SBV b = SBV (svJoin a b)
    extend b = 0 # b

type Word256 = LargeKey Word128 Word128
type SWord256 = SBV Word256
instance HasKind Word256   where kindOf _ = KBounded False 256
instance SDivisible SWord256 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod
instance SymWord Word256 where
  mkSymWord  = genMkSymVar (KBounded False 256)
  literal    = genLiteral  (KBounded False 256)
  fromCW     = genFromCW
instance Splittable SWord256 SWord128 where
    split (SBV x) = (SBV (svExtract 255 128 x), SBV (svExtract 127 0 x))
    SBV a # SBV b = SBV (svJoin a b)
    extend b = 0 # b

type SWord128 = SBV Word128
instance HasKind Word128   where kindOf _ = KBounded False 128
instance SDivisible SWord128 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod
instance SymWord Word128 where
  mkSymWord  = genMkSymVar (KBounded False 128)
  literal    = genLiteral  (KBounded False 128)
  fromCW     = genFromCW    
instance Splittable SWord128 SWord64 where
    split (SBV x) = (SBV (svExtract 127 64 x), SBV (svExtract 63 0 x))
    SBV a # SBV b = SBV (svJoin a b)
    extend b = 0 # b


