{-# LANGUAGE ScopedTypeVariables, GADTs #-}

module Utils where

import Data.Set (Set(..))
import qualified Data.Set as Set
import Control.Monad.Trans
import Data.Traversable as Traversable
import Control.Monad
import qualified Data.Generics as Generics
import Data.Proxy
import Data.Typeable hiding (typeOf)
import Control.Monad.Except

import Unsafe.Coerce

mapSet f = Set.fromList . map f . Set.toList

fst3 (x,y,z) = x
snd3 (x,y,z) = y
thr3 (x,y,z) = z

fst5 = (\(x1,x2,x3,x4,x5) -> x1)
fou5 = (\(x1,x2,x3,x4,x5) -> x4)

funit :: Functor f => f a -> f ()
funit = fmap (const ())

fconst :: Functor f => b -> f a -> f b
fconst b = fmap (const b)

lift2 :: (MonadTrans t1,Monad (t2 m),MonadTrans t2,Monad m)  => m a -> t1 (t2 m) a
lift2 = lift . lift

funzip :: Traversable t => t (a,b) -> (t a,t b)
funzip xs = (fmap fst xs,fmap snd xs)

funzip3 :: Traversable t => t (a,b,c) -> (t a,t b,t c)
funzip3 xs = (fmap fst3 xs,fmap snd3 xs,fmap thr3 xs)

mapAndUnzipM :: (Monad m,Traversable t) => (c -> m (a,b)) -> t c -> m (t a,t b)
mapAndUnzipM f = liftM funzip . Traversable.mapM f

mapAndUnzip3M :: (Monad m,Traversable t) => (c -> m (a,b,d)) -> t c -> m (t a,t b,t d)
mapAndUnzip3M f = liftM funzip3 . Traversable.mapM f

mapFst :: (a -> b) -> (a,c) -> (b,c)
mapFst f (x,y) = (f x,y)

mapSnd :: (c -> b) -> (a,c) -> (a,b)
mapSnd f (x,y) = (x,f y)

mapSndM :: Monad m => (c -> m b) -> (a,c) -> m (a,b)
mapSndM f (x,y) = do
    y' <- f y
    return (x,y')

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f = liftM concat . mapM f

-- | A monomorphic type representation to support type equality
data TypeOf a where
    TypeOf :: Typeable a => TypeRep -> TypeOf a

compareTypeOf :: TypeOf a -> TypeOf b -> Ordering
compareTypeOf (TypeOf t1) (TypeOf t2) = compare t1 t2

data EqT a b where
    EqT :: EqT a a -- evidence that two types are equal
    NeqT :: EqT a b -- evidence that two types are not equal

typeRep :: Typeable a => TypeOf a
typeRep = typeOf (error "typeRep")

typeOf :: Typeable a => a -> TypeOf a
typeOf = typeOfProxy . proxyOf

proxyOf :: a -> Proxy a
proxyOf _ = Proxy

typeOfProxy :: Typeable a => Proxy a -> TypeOf a
typeOfProxy p = TypeOf (Generics.typeOf p)

eqTypeOf :: TypeOf a -> TypeOf b -> EqT a b
eqTypeOf (TypeOf t1) (TypeOf t2) = if t1 == t2 then unsafeCoerce EqT else NeqT

catchErrorMaybe :: MonadError e m => m a -> m (Maybe a)
catchErrorMaybe m = catchError (liftM Just m) (const $ return Nothing)



