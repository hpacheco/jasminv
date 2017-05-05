{-# LANGUAGE ScopedTypeVariables, ConstraintKinds, TypeFamilies, FlexibleContexts, RankNTypes, MultiParamTypeClasses, FlexibleInstances #-}

module Language.Vars where

import qualified Data.Set as Set
import Data.Set (Set(..))
import qualified Data.Map as Map
import Data.Map (Map(..))
import Control.Monad.State (StateT(..))
import qualified Control.Monad.State as State
import Data.Typeable hiding (typeOf)
import Data.Proxy
import Control.Monad
import Data.Maybe

import Utils

type IsVar a = (Eq a,Ord a,Typeable a)

type Stop m = forall a . IsVar a => a -> m Bool
newtype StopProxy m = StopProxy { unStopProxy :: forall a . IsVar a => Proxy a -> a -> m Bool }

dontStop :: Monad m => StopProxy m
dontStop = StopProxy $ \_ x -> return False

type Substs id m = forall b . Vars id m b => b -> id -> m (Maybe b)
newtype SubstsProxy id m = SubstsProxy { unSubstsProxy :: forall b . Vars id m b => Proxy b -> b -> id -> m (Maybe b) }

newtype SubstVars id = SubstVars (id -> Maybe id)

instance Monoid (SubstVars id) where
    mempty = SubstVars $ const Nothing
    mappend (SubstVars f1) (SubstVars f2) = SubstVars $ \x -> maybe (f2 x) Just (f1 x)
    
substVarsFromList :: IsVar id => [(id,id)] -> SubstVars id
substVarsFromList xs = foldl (\(SubstVars f) (v,v') -> SubstVars $ \x -> if x==v then Just v' else f x) mempty xs

substsFromVars :: SubstVars id -> Substs id m
substsFromVars ss = case substsProxyFromVars ss of
    SubstsProxy f -> (f Proxy)

substsProxyFromVars :: SubstVars id -> SubstsProxy id m
substsProxyFromVars (SubstVars f::SubstVars id) = SubstsProxy $ \pb b v -> mapM (unSubstL b) (f v)

substVars :: (Vars id m id,Vars id m a) => StopProxy m -> SubstVars id -> Bool -> Map id id -> a -> m a
substVars stop ssvars isBound ss x = subst stop (substsFromVars ssvars) isBound ss x

class Monad m => GenVar id m where
    
    mkVar :: String -> m id
    newVar :: id -> m id

class (IsVar id,IsVar a,GenVar id m) => Vars id m a where
    
    traverseVars :: (forall b . Vars id m b => b -> VarsM id m b) -> a -> VarsM id m a
    
    -- tries to cast a value of type @a@ into a substitution variable
    substL :: Vars id m a => a -> m (Maybe id)
    substL = substL' Proxy
        where
        substL' :: Vars id m a => Proxy id -> (a -> m (Maybe id))
        substL' pl a = case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf a) of
            EqT -> return $ Just a
            NeqT -> return Nothing
    
    unSubstL :: Vars id m a => a -> id -> m a
    unSubstL a iden = case eqTypeOf (typeOfProxy $ proxyOf iden) (typeOfProxy $ proxyOf a) of
            EqT -> return iden
            NeqT -> return a
    
    substVarsM :: (Vars id m id) => StopProxy m -> Substs id m -> a -> VarsM id m a
    substVarsM stp@(StopProxy stop) f x = do
        mbiden <- State.lift $ substL x
        x' <- case mbiden of -- try to substitute first
            Nothing -> return x
            Just v -> do
                b <- isBound v
                isLHS <- getLHS
                if (maybe False not b || maybe False not isLHS)
                    then do
                        (_,_,(_,ss),_,_) <- State.get
                        let v' = maybe v id (Map.lookup v ss)
                        State.lift $ unSubstL x v'
                    else do
                        r <- State.lift $ f x v
                        case r of
                            Nothing -> return x
                            Just s -> do
                                s' <- substVarsM stp f s -- go recursively in case of substitution
                                return s'
        ko <- State.lift $ stop Proxy x'
        if ko
            then return x'
            else traverseVars (substVarsM stp f) $ x' -- descend into children
    
    subst :: (Vars id m id) => StopProxy m -> Substs id m -> Bool -> Map id id -> a -> m a
    subst stop f substBounds ss x = do
        x <- State.evalStateT (substVarsM stop f x) (Nothing,False,(substBounds,ss),Map.empty,Map.empty)
        return x
    
    substProxy :: (Vars id m id) => StopProxy m -> SubstsProxy id m -> Bool -> Map id id -> a -> m a
    substProxy stop (SubstsProxy f) substBounds ss x = subst stop (f Proxy) substBounds ss x
        
    fvs :: a -> m (Map id Bool)
    fvs a = do
        (x,lval,s,y,z) <- State.execStateT (varsM a) (Nothing,False,(False,Map.empty),Map.empty,Map.empty)
        return y
    bvs :: a -> m (Map id Bool)
    bvs a = do
        (x,lval,s,y,z) <- State.execStateT (varsM a) (Nothing,False,(False,Map.empty),Map.empty,Map.empty)
        return z
    uvs :: a -> m (Map id Bool,Map id Bool)
    uvs a = do
        (x,lval,s,y,z) <- State.execStateT (varsM a) (Nothing,False,(False,Map.empty),Map.empty,Map.empty)
        return (y,z)
    
    varsM :: a -> VarsM id m a
    varsM x = traverseVars varsM x
    
usedVars :: Vars id m a => a -> m (Set id)
usedVars x = do
    (fs,bs) <- uvs x
    return $ Set.union (Map.keysSet fs) (Map.keysSet bs)

fvsSet :: Vars id m a => a -> m (Set id)
fvsSet = liftM Map.keysSet . fvs

bvsSet :: Vars id m a => a -> m (Set id)
bvsSet = liftM Map.keysSet . bvs

substsFromMap :: (Vars id m r) => Map id r -> Substs id m
substsFromMap xs = let f = unSubstsProxy (substsProxyFromMap xs) in f Proxy

substsProxyFromMap :: (Vars id m r) => Map id r -> SubstsProxy id m
substsProxyFromMap = substsProxyFromList . Map.toList

substsFromList :: (Vars id m r) => [(id,r)] -> Substs id m
substsFromList xs = let f = unSubstsProxy (substsProxyFromList xs) in f Proxy

substsProxyFromList :: (Vars id m r) => [(id,r)] -> SubstsProxy id m
substsProxyFromList [] = SubstsProxy (\proxy b iden -> return Nothing)
substsProxyFromList ((x,y):xs) = SubstsProxy (\proxy b iden -> case (eqTypeOf (typeOf y) (typeOfProxy proxy)) of
    EqT -> if x==iden
        then return (Just y)
        else (unSubstsProxy $ substsProxyFromList xs) proxy b iden
    otherwise -> return Nothing)

isBound :: (Vars id m id) => id -> VarsM id m (Maybe Bool)
isBound v = do
    (_,lval,ss,fvs,bvs) <- State.get
    return $ Map.lookup v bvs

getLHS :: Monad m => VarsM id m (Maybe Bool)
getLHS = liftM (\(x,lval,ss,y,z) -> x) State.get

inLHS :: Monad m => Bool -> VarsM id m a -> VarsM id m a
inLHS isName m = do
    (lhs,lval,ss,fvs,bvs) <- State.get
    (x,(_,lval',ss',fvs',bvs')) <- State.lift $ State.runStateT m (Just isName,lval,ss,fvs,bvs)
    State.put (lhs,lval',ss',fvs',bvs')
    return x

inLVal :: Monad m => VarsM id m a -> VarsM id m a
inLVal m = do
    (lhs,lval,ss,fvs,bvs) <- State.get
    (x,(lhs',_,ss',fvs',bvs')) <- State.lift $ State.runStateT m (lhs,True,ss,fvs,bvs)
    State.put (lhs',lval,ss',fvs',bvs')
    return x

inRHS :: Monad m => VarsM id m a -> VarsM id m a
inRHS m = do
    (lhs,lval,ss,fvs,bvs) <- State.get
    (x,(_,lval',ss',fvs',bvs')) <- State.lift $ State.runStateT m (Nothing,lval,ss,fvs,bvs)
    State.put (lhs,lval',ss',fvs',bvs')
    return x

varsBlock :: (GenVar id m) => VarsM id m a -> VarsM id m a
varsBlock m = do
    (lhs,lval,ss,fvs,bvs) <- State.get
    (x,(lhs',lval',ss',fvs',bvs')) <- State.lift $ State.runStateT m (lhs,lval,ss,fvs,bvs)
    State.put (lhs',lval',ss,fvs',bvs) -- forget bound substitutions and bound variables
    return x

addFV :: (Vars id m id) => (id -> id) -> id -> VarsM id m id
addFV to x = do
    State.modify $ \(lhs,lval,ss,fvs,bvs) -> if isJust (Map.lookup (to x) bvs)
        then (lhs,lval,ss,fvs,bvs) -- don't add an already bound variable to the free variables
        else (lhs,lval,ss,Map.insertWith (||) (to x) lval fvs,bvs)
    return x
 
addBV :: (Vars id m id) => (id -> id) -> id -> VarsM id m id
addBV to x = do
    --liftIO $ putStrLn $ "addBV " ++ ppr x
    (lhs,lval,(substBounds,ss),fvs,bvs) <- State.get
    let isName = maybe False id lhs
    (x',ss') <- if not isName && substBounds then liftM (\x' -> (x',Map.insert (to x) (to x') ss)) (State.lift $ newVar x) else return (x,ss)
    State.put (lhs,lval,(substBounds,ss'),fvs,Map.insert (to x) isName bvs)
    return x'

type VarsM id m = StateT
    (Maybe Bool -- is left-hand side
    ,Bool -- is l-value
    ,(Bool,Map id id) -- bound substitutions
    ,Map id Bool -- free vars (read=False or written=True)
    ,Map id Bool-- bound vars (variable=false or name=True)
    )
    m

instance (IsVar id,GenVar id m) => Vars id m () where
    traverseVars f = return

instance (Vars id m a,Vars id m b) => Vars id m (a,b) where
    traverseVars f (x,y) = do
        x' <- f x
        y' <- f y
        return (x',y')

instance (Vars id m a) => Vars id m (Maybe a) where
    traverseVars f x = mapM f x

instance (Vars id m a) => Vars id m [a] where
    traverseVars f x = mapM f x

instance (IsVar id,GenVar id m) => Vars id m Bool where
    traverseVars f = return
instance (IsVar id,GenVar id m) => Vars id m Int where
    traverseVars f = return
instance (IsVar id,GenVar id m) => Vars id m Integer where
    traverseVars f = return

instance Vars iden m a => Vars iden m (Set a) where
    traverseVars f xs = liftM Set.fromList $! mapM f $! Set.toList xs

instance (Vars iden m a,Vars iden m b) => Vars iden m (Map a b) where
    traverseVars f xs = traverseMap f f xs

traverseMap :: (GenVar iden m,IsVar a,IsVar b,IsVar iden) => (a -> VarsM iden m a) -> (b -> VarsM iden m b) -> Map a b -> VarsM iden m (Map a b)
traverseMap f g xs = liftM Map.fromList $! aux $! Map.toList xs
        where
        aux [] = return []
        aux ((k,v):xs) = do
            k' <- f k
            v' <- g v
            xs' <- aux xs
            return ((k',v'):xs')
