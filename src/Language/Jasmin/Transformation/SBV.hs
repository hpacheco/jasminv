{-# LANGUAGE RankNTypes, StandaloneDeriving, TupleSections, DeriveGeneric, DeriveAnyClass, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, ViewPatterns, GADTs, ConstraintKinds, FlexibleContexts, ScopedTypeVariables #-}

module Language.Jasmin.Transformation.SBV where

import Data.IORef
import Data.Proxy
import Data.Bifunctor
import Data.SBV.Exts hiding ((<+>))
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
    e' <- pexprToSBVInteger e
    writeSBArr (infoLoc t) (funit n) e' v
passignToSBV t ls vs | length ls > 1 && length ls == length vs = do
    forM_ (zip ls vs) $ \(l,v) -> passignToSBV t [l] [v]
passignToSBV t lv v = genError (infoLoc t) $ text "lvalue not supported in SMT"

popn_rToSBV :: TyInfo -> [Plvalue TyInfo] -> Op -> [Pexpr TyInfo] -> SBVM Symbolic ()
popn_rToSBV t ls Oaddcarry [e1,e2,cf] = do
    e1' <- pexprToSBV e1
    e2' <- pexprToSBV e2
    cf' <- pexprToSBVBool cf
    let (vcf,ve) = sbvAdc e1' e2' cf'
    passignToSBV t ls [SBBool vcf,ve]
popn_rToSBV t ls o es = error "popn_rToSBV"

sbvAdc :: SBVar -> SBVar -> SBool -> (SBool,SBVar)
sbvAdc (SBWord64 x) (SBWord64 y) cf = let (cf',z) = adc x y cf in (cf',SBWord64 z)

adc :: SIntegral a => SBV a -> SBV a -> SBool -> (SBool,SBV a)
adc x y cf = (cf',s')
    where
    s = x + y
    scf = ite cf 1 0
    s' = s + scf
    cf' = s .< x ||| s .< y ||| s' .< s

sbvIf :: SBool -> SBVM Symbolic () -> SBVM Symbolic () -> SBVM Symbolic ()
sbvIf c m1 m2 = do
    env1 <- liftM snd $ blockSBVM m1
    env2 <- liftM snd $ blockSBVM m2
    let env' = ite c env1 env2
    State.put env'

pexprToSBVBool :: Pexpr TyInfo -> SBVM Symbolic SBool
pexprToSBVBool e = do
    SBBool e' <- pexprToSBV e
    return e'

pexprToSBVInteger :: Pexpr TyInfo -> SBVM Symbolic SInteger
pexprToSBVInteger e = do
    SBInteger e' <- pexprToSBV e
    return e'

pexprToSBV :: Pexpr TyInfo -> SBVM Symbolic SBVar
pexprToSBV (Pexpr t e) = pexpr_rToSBV t e

pexpr_rToSBV :: TyInfo -> Pexpr_r TyInfo -> SBVM Symbolic SBVar
pexpr_rToSBV t (PEVar v) = getSBVar (infoLoc t) (funit v)
pexpr_rToSBV t (PEBool b) = return $ SBBool $ literal b
pexpr_rToSBV t (PEInt i) = return $ sbvInteger (infoTy t) i
pexpr_rToSBV t (PEOp1 o e1) = op1_rToSBV t o e1
pexpr_rToSBV t (PEOp2 o e1 e2) = op2_rToSBV t o e1 e2
pexpr_rToSBV t (PEGet n e) = do
    e' <- pexprToSBVInteger e
    readSBArr (infoLoc t) (funit n) e'
pexpr_rToSBV t (Pcast te e) = pcast_rToSBV t te e
pexpr_rToSBV t (PEParens [e]) = pexprToSBV e
--pexpr_rToSBV t (QuantifiedExpr q args e) = forAll
pexpr_rToSBV t e = do
    pe <- pp e
    genError (infoLoc t) $ text "expression not encoded in SBV: " <+> pe

pcast_rToSBV :: TyInfo -> Ptype TyInfo -> Pexpr TyInfo -> SBVM Symbolic SBVar
pcast_rToSBV l t e = do
    e' <- pexprToSBV e
    return $ sbvCast t e'
    
sbvInteger :: Ptype TyInfo -> Integer -> SBVar
sbvInteger (TInt Nothing) i = SBInteger $ literal i
sbvInteger (TWord 8) i = SBWord8     $ literal $ fromIntegral i
sbvInteger (TWord 16) i = SBWord16   $ literal $ fromIntegral i
sbvInteger (TWord 32) i = SBWord32   $ literal $ fromIntegral i
sbvInteger (TWord 64) i = SBWord64   $ literal $ fromIntegral i
sbvInteger (TWord 128) i = SBWord128 $ literal $ fromIntegral i
sbvInteger (TWord 256) i = SBWord256 $ literal $ fromIntegral i
sbvInteger (TWord 512) i = SBWord512 $ literal $ fromIntegral i
sbvInteger t i = error $ "sbvInteger " ++ pprid t

op1_rToSBV :: TyInfo -> Peop1 -> Pexpr TyInfo -> SBVM Symbolic SBVar
op1_rToSBV t Not1 e1 = nativeOp1 (sbvBoolean1 bnot) e1
op1_rToSBV t o e1 = error "op1_rToSBV"

sbvCast :: Ptype TyInfo -> SBVar -> SBVar
sbvCast (TInt Nothing) (SBInteger i) = SBInteger $ sFromIntegral i
sbvCast (TInt Nothing) (SBWord8   i) = SBInteger $ sFromIntegral i
sbvCast (TInt Nothing) (SBWord16   i) = SBInteger $ sFromIntegral i
sbvCast (TInt Nothing) (SBWord32   i) = SBInteger $ sFromIntegral i
sbvCast (TInt Nothing) (SBWord64   i) = SBInteger $ sFromIntegral i
sbvCast (TInt Nothing) (SBWord128   i) = SBInteger $ sFromIntegral i
sbvCast (TInt Nothing) (SBWord256   i) = SBInteger $ sFromIntegral i
sbvCast (TInt Nothing) (SBWord512   i) = SBInteger $ sFromIntegral i
sbvCast (TWord 64) (SBInteger i) = SBWord64 $ sFromIntegral i
sbvCast (TWord 64) (SBWord8   i) = SBWord64 $ extend $ extend $ extend i
sbvCast (TWord 64) (SBWord16   i) = SBWord64 $ extend $ extend i
sbvCast (TWord 64) (SBWord32   i) = SBWord64 $ extend i
sbvCast (TWord 64) (SBWord64   i) = SBWord64 $ i
sbvCast (TWord 512) (SBInteger i) = SBWord512 $ sFromIntegral i
sbvCast (TWord 512) (SBWord8   i) = SBWord512 $ extend $ extend $ extend $ extend $ extend $ extend i
sbvCast (TWord 512) (SBWord16   i) = SBWord512 $ extend $ extend $ extend $ extend $ extend i
sbvCast (TWord 512) (SBWord32   i) = SBWord512 $ extend $ extend $ extend $ extend i
sbvCast (TWord 512) (SBWord64   i) = SBWord512 $ extend $ extend $ extend i
sbvCast (TWord 512) (SBWord128   i) = SBWord512 $ extend $ extend i
sbvCast (TWord 512) (SBWord256   i) = SBWord512 $ extend i
sbvCast (TWord 512) (SBWord512   i) = SBWord512 i
sbvCast t x = error $ show $ text "sbvCast" <+> ppid t <+> ppid x

op2_rToSBV :: TyInfo -> Peop2 -> Pexpr TyInfo -> Pexpr TyInfo -> SBVM Symbolic SBVar
op2_rToSBV t Add2 e1 e2 = nativeOp2 (sbvNum2 (+)) e1 e2
op2_rToSBV t Sub2 e1 e2 = nativeOp2 (sbvNum2 (-)) e1 e2
op2_rToSBV t Mul2 e1 e2 = nativeOp2 (sbvNum2 (*)) e1 e2
op2_rToSBV t And2 e1 e2 = nativeOp2 (sbvBoolean2 (&&&)) e1 e2
op2_rToSBV t Or2 e1 e2 = nativeOp2 (sbvBoolean2 (|||)) e1 e2
op2_rToSBV t BAnd2 e1 e2 = nativeOp2 (sbvBits2 (.&.)) e1 e2
op2_rToSBV t BOr2 e1 e2 = nativeOp2 (sbvBits2 (.|.)) e1 e2
op2_rToSBV t BXor2 e1 e2 = nativeOp2 (sbvBits2 xor) e1 e2
op2_rToSBV t (Shr2 Unsigned) e1 e2 = nativeOp2 (sbvIntegral2 sShiftRight) e1 e2
op2_rToSBV t Shl2 e1 e2 = nativeOp2 (sbvIntegral2 sShiftLeft) e1 e2
op2_rToSBV t Eq2 e1 e2  = nativeOp2Bool (sbvEqSymbolic2 (.==)) e1 e2
op2_rToSBV t Neq2 e1 e2 = nativeOp2Bool (sbvEqSymbolic2 (./=)) e1 e2
op2_rToSBV t (Lt2 Unsigned) e1 e2 = nativeOp2Bool (sbvOrdSymbolic2 (.<)) e1 e2
op2_rToSBV t (Le2 Unsigned) e1 e2 = nativeOp2Bool (sbvOrdSymbolic2 (.<=)) e1 e2
op2_rToSBV t (Gt2 Unsigned) e1 e2 = nativeOp2Bool (sbvOrdSymbolic2 (.>)) e1 e2
op2_rToSBV t (Ge2 Unsigned) e1 e2 = nativeOp2Bool (sbvOrdSymbolic2 (.>=)) e1 e2
op2_rToSBV t Mod2 e1 e2 = nativeOp2 (sbvDivisible2 sMod) e1 e2
op2_rToSBV t o e1 e2 = error "op2_rToSBV"

nativeOp1 :: (SBVar -> SBVar) -> Pexpr TyInfo -> SBVM Symbolic SBVar
nativeOp1 f e1 = do
    e1' <- pexprToSBV e1
    return $ f e1'

nativeOp2Bool :: (SBVar -> SBVar -> SBool) -> Pexpr TyInfo -> Pexpr TyInfo -> SBVM Symbolic SBVar
nativeOp2Bool f e1 e2 = nativeOp2 f' e1 e2
    where
    f' x y = SBBool $ f x y

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
sbVar p n TBool = liftM SBBool $ lift2 $ sBool n
sbVar p n (TInt Nothing) = liftM SBInteger $ lift2 $ sInteger n
sbVar p n (TWord 8) = liftM SBWord8 $ lift2 $ sWord8 n
sbVar p n (TWord 16) = liftM SBWord16 $ lift2 $ sWord16 n
sbVar p n (TWord 32) = liftM SBWord32 $ lift2 $ sWord32 n
sbVar p n (TWord 64) = liftM SBWord64 $ lift2 $ sWord64 n
sbVar p n (TWord 128) = liftM SBWord128 $ lift2 $ sWord128 n
sbVar p n (TWord 256) = liftM SBWord256 $ lift2 $ sWord256 n
sbVar p n (TWord 512) = liftM SBWord512 $ lift2 $ sWord512 n
sbVar p n (TArray w sz) = do
    sz' <- pexprToSBVInteger sz
    case unliteral sz' of
        Just szi -> do
            vs <- forM [0..szi-1] $ \wi -> do
                liftM (literal wi,) $ sbVar p ("n"++show wi) (TWord $ fromEnum w)
            return $ SBArr $ list2fun vs
        Nothing -> return $ SBArr $ list2fun []

list2fun :: [(SInteger,SBVar)] -> (SInteger -> SBVar)
list2fun [] = const $ error "unitialized array"
list2fun ((x,y):xs) = \a -> ite (x .== a) y (list2fun xs a)

readSBArr :: Position -> Piden -> SInteger -> SBVM Symbolic SBVar
readSBArr p n i = do
    vs <- State.gets vars
    case Map.lookup n vs of
        Just (SBArr arr) -> return $ arr i
        otherwise -> genError p $ text "readSBArr" <+> ppid n

writeSBArr :: Position -> Piden -> SInteger -> SBVar -> SBVM Symbolic ()
writeSBArr p n (i) (e) = do
    State.modify $ \env -> env { vars = Map.update writeArr n (vars env) }
        where writeArr (SBArr f) = Just $ SBArr $ \a' -> ite (i .== a') e (f a')

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
    
instance Mergeable SBVar where
    symbolicMerge f b (SBBool v1) (SBBool v2)           = SBBool $ symbolicMerge f b v1 v2
    symbolicMerge f b (SBInteger v1) (SBInteger v2)     = SBInteger $ symbolicMerge f b v1 v2
    symbolicMerge f b (SBWord8 v1) (SBWord8 v2)         = SBWord8 $ symbolicMerge f b v1 v2
    symbolicMerge f b (SBWord16 v1) (SBWord16 v2)       = SBWord16 $ symbolicMerge f b v1 v2
    symbolicMerge f b (SBWord32 v1) (SBWord32 v2)       = SBWord32 $ symbolicMerge f b v1 v2
    symbolicMerge f b (SBWord64 v1) (SBWord64 v2)       = SBWord64 $ symbolicMerge f b v1 v2
    symbolicMerge f b (SBWord128 v1) (SBWord128 v2)     = SBWord128 $ symbolicMerge f b v1 v2
    symbolicMerge f b (SBWord256 v1) (SBWord256 v2)     = SBWord256 $ symbolicMerge f b v1 v2
    symbolicMerge f b (SBWord512 v1) (SBWord512 v2)     = SBWord512 $ symbolicMerge f b v1 v2
    symbolicMerge _ b (SBArr g) (SBArr h)               = SBArr $ \x -> ite b (g x) (h x)

sbvEqual :: SBVar -> SBVar -> SBool
sbvEqual = undefined

data SBVar where
    SBBool :: SBool -> SBVar
    SBInteger :: SInteger -> SBVar
    SBWord8 :: SWord8 -> SBVar
    SBWord16 :: SWord16 -> SBVar
    SBWord32 :: SWord32 -> SBVar
    SBWord64 :: SWord64 -> SBVar
    SBWord128 :: SWord128 -> SBVar
    SBWord256 :: SWord256 -> SBVar
    SBWord512 :: SWord512 -> SBVar
    SBArr :: (SInteger -> SBVar) -> SBVar
  deriving (Generic)

instance Show SBVar where
    show = pprid

instance Monad m => PP m SBVar where
    pp (SBBool b) = do
        return $ parens (text "SBBool" <+> text "*")
    pp (SBInteger b) = do
        return $ parens (text "SBInteger" <+> text "*")
    pp (SBWord8 b) = do
        return $ parens (text "SBWord8" <+> text "*")
    pp (SBWord16 b) = do
        return $ parens (text "SBWord16" <+> text "*")
    pp (SBWord32 b) = do
        return $ parens (text "SBWord32" <+> text "*")
    pp (SBWord64 b) = do
        return $ parens (text "SBWord64" <+> text "*")
    pp (SBWord128 b) = do
        return $ parens (text "SBWord128" <+> text "*")
    pp (SBWord256 b) = do
        return $ parens (text "SBWord256" <+> text "*")
    pp (SBWord512 b) = do
        return $ parens (text "SBWord512" <+> text "*")
    pp (SBArr b) = do
        return $ parens (text "SBArr" <+> text "*")

instance GenVar Piden Symbolic where
    mkVar str = liftIO $ mkVar str
    newVar x = liftIO $ newVar x

sbvNum2 :: (forall a . Num a => a -> a -> a) -> SBVar -> SBVar -> SBVar
sbvNum2 f (SBInteger i1) (SBInteger i2) = SBInteger $ f i1 i2
sbvNum2 f (SBWord8 i1) (SBWord8 i2) = SBWord8 $ f i1 i2
sbvNum2 f (SBWord16 i1) (SBWord16 i2) = SBWord16 $ f i1 i2
sbvNum2 f (SBWord32 i1) (SBWord32 i2) = SBWord32 $ f i1 i2
sbvNum2 f (SBWord64 i1) (SBWord64 i2) = SBWord64 $ f i1 i2
sbvNum2 f (SBWord128 i1) (SBWord128 i2) = SBWord128 $ f i1 i2
sbvNum2 f (SBWord256 i1) (SBWord256 i2) = SBWord256 $ f i1 i2
sbvNum2 f (SBWord512 i1) (SBWord512 i2) = SBWord512 $ f i1 i2
sbvNum2 f x y = error $ "sbvNum2 " ++ show x ++ " " ++ show y

sbvDivisible2 :: (forall a . SDivisible a => a -> a -> a) -> SBVar -> SBVar -> SBVar
sbvDivisible2 f (SBWord8 i1) (SBWord8 i2) = SBWord8 $ f i1 i2
sbvDivisible2 f (SBWord16 i1) (SBWord16 i2) = SBWord16 $ f i1 i2
sbvDivisible2 f (SBWord32 i1) (SBWord32 i2) = SBWord32 $ f i1 i2
sbvDivisible2 f (SBWord64 i1) (SBWord64 i2) = SBWord64 $ f i1 i2
sbvDivisible2 f (SBWord128 i1) (SBWord128 i2) = SBWord128 $ f i1 i2
sbvDivisible2 f (SBWord256 i1) (SBWord256 i2) = SBWord256 $ f i1 i2
sbvDivisible2 f (SBWord512 i1) (SBWord512 i2) = SBWord512 $ f i1 i2
sbvDivisible2 f (SBWord8 i1) (SBInteger i2) = SBWord8 $ f i1 (sFromIntegral i2)
sbvDivisible2 f (SBWord16 i1) (SBInteger i2) = SBWord16 $ f i1 (sFromIntegral i2)
sbvDivisible2 f (SBWord32 i1) (SBInteger i2) = SBWord32 $ f i1 (sFromIntegral i2)
sbvDivisible2 f (SBWord64 i1) (SBInteger i2) = SBWord64 $ f i1 (sFromIntegral i2)
sbvDivisible2 f (SBWord128 i1) (SBInteger i2) = SBWord128 $ f i1 (sFromIntegral i2)
sbvDivisible2 f (SBWord256 i1) (SBInteger i2) = SBWord256 $ f i1 (sFromIntegral i2)
sbvDivisible2 f (SBWord512 i1) (SBInteger i2) = SBWord512 $ f i1 (sFromIntegral i2)
sbvDivisible2 f x y = error $ "sbvDivisible2 " ++ show x ++ " " ++ show y

sbvIntegral2 :: (forall a b. (SIntegral a,SIntegral b) => SBV a -> SBV b -> SBV a) -> SBVar -> SBVar -> SBVar
sbvIntegral2 f (SBWord8 i1) (SBWord8 i2) = SBWord8 $ f i1 i2
sbvIntegral2 f (SBWord16 i1) (SBWord16 i2) = SBWord16 $ f i1 i2
sbvIntegral2 f (SBWord32 i1) (SBWord32 i2) = SBWord32 $ f i1 i2
sbvIntegral2 f (SBWord64 i1) (SBWord64 i2) = SBWord64 $ f i1 i2
sbvIntegral2 f (SBWord128 i1) (SBWord128 i2) = SBWord128 $ f i1 i2
sbvIntegral2 f (SBWord256 i1) (SBWord256 i2) = SBWord256 $ f i1 i2
sbvIntegral2 f (SBWord512 i1) (SBWord512 i2) = SBWord512 $ f i1 i2
sbvIntegral2 f (SBWord8 i1) (SBInteger i2) = SBWord8 $ f i1 i2
sbvIntegral2 f (SBWord16 i1) (SBInteger i2) = SBWord16 $ f i1 i2
sbvIntegral2 f (SBWord32 i1) (SBInteger i2) = SBWord32 $ f i1 i2
sbvIntegral2 f (SBWord64 i1) (SBInteger i2) = SBWord64 $ f i1 i2
sbvIntegral2 f (SBWord128 i1) (SBInteger i2) = SBWord128 $ f i1 i2
sbvIntegral2 f (SBWord256 i1) (SBInteger i2) = SBWord256 $ f i1 i2
sbvIntegral2 f (SBWord512 i1) (SBInteger i2) = SBWord512 $ f i1 i2
sbvIntegral2 f x y = error $ "sbvIntegral2 " ++ show x ++ " " ++ show y

sbvBoolean1 :: (forall a . Boolean a => a -> a) -> SBVar -> SBVar
sbvBoolean1 f (SBBool x) = SBBool $ f x

sbvBoolean2 :: (forall a . Boolean a => a -> a -> a) -> SBVar -> SBVar -> SBVar
sbvBoolean2 f (SBBool x) (SBBool y) = SBBool (f x y)

sbvEqSymbolic2 :: (forall a. EqSymbolic a => a -> a -> SBool) -> SBVar -> SBVar -> SBool
sbvEqSymbolic2 f (SBBool i1) (SBBool i2) = f i1 i2
sbvEqSymbolic2 f (SBInteger i1) (SBInteger i2) = f i1 i2
sbvEqSymbolic2 f (SBWord8 i1) (SBWord8 i2) = f i1 i2
sbvEqSymbolic2 f (SBWord16 i1) (SBWord16 i2) = f i1 i2
sbvEqSymbolic2 f (SBWord32 i1) (SBWord32 i2) = f i1 i2
sbvEqSymbolic2 f (SBWord64 i1) (SBWord64 i2) = f i1 i2
sbvEqSymbolic2 f (SBWord128 i1) (SBWord128 i2) = f i1 i2
sbvEqSymbolic2 f (SBWord256 i1) (SBWord256 i2) = f i1 i2
sbvEqSymbolic2 f (SBWord512 i1) (SBWord512 i2) = f i1 i2
sbvEqSymbolic2 f x y = error $ "sbvEqSymbolic2 " ++ show x ++ " " ++ show y

sbvOrdSymbolic2 :: (forall a. OrdSymbolic a => a -> a -> SBool) -> SBVar -> SBVar -> SBool
sbvOrdSymbolic2 f (SBBool i1) (SBBool i2) = f i1 i2
sbvOrdSymbolic2 f (SBInteger i1) (SBInteger i2) = f i1 i2
sbvOrdSymbolic2 f (SBWord8 i1) (SBWord8 i2) = f i1 i2
sbvOrdSymbolic2 f (SBWord16 i1) (SBWord16 i2) = f i1 i2
sbvOrdSymbolic2 f (SBWord32 i1) (SBWord32 i2) = f i1 i2
sbvOrdSymbolic2 f (SBWord64 i1) (SBWord64 i2) = f i1 i2
sbvOrdSymbolic2 f (SBWord128 i1) (SBWord128 i2) = f i1 i2
sbvOrdSymbolic2 f (SBWord256 i1) (SBWord256 i2) = f i1 i2
sbvOrdSymbolic2 f (SBWord512 i1) (SBWord512 i2) = f i1 i2
sbvOrdSymbolic2 f x y = error $ "sbvOrdSymbolic2 " ++ show x ++ " " ++ show y

sbvBits2 :: (forall a. Bits a => a -> a -> a) -> SBVar -> SBVar -> SBVar
sbvBits2 f (SBWord8 i1) (SBWord8 i2) = SBWord8 $ f i1 i2
sbvBits2 f (SBWord16 i1) (SBWord16 i2) = SBWord16 $ f i1 i2
sbvBits2 f (SBWord32 i1) (SBWord32 i2) = SBWord32 $ f i1 i2
sbvBits2 f (SBWord64 i1) (SBWord64 i2) = SBWord64 $ f i1 i2
sbvBits2 f (SBWord128 i1) (SBWord128 i2) = SBWord128 $ f i1 i2
sbvBits2 f (SBWord256 i1) (SBWord256 i2) = SBWord256 $ f i1 i2
sbvBits2 f (SBWord512 i1) (SBWord512 i2) = SBWord512 $ f i1 i2
sbvBits2 f x y = error $ "sbvBits2 " ++ show x ++ " " ++ show y






