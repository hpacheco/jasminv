{-# LANGUAGE TupleSections #-}

module Text.Parsec.Exts
    ( module Text.Parsec.Exts
    , module Text.Parsec.Pos
    , module Text.Parsec
    ) where

import Text.Parsec
import Text.Parsec.Pos

import Control.Monad
import Data.Foldable as Foldable

-- * Utility functions

infixr 1 >*< 
(>*<) :: ParsecT s u m a -> ParsecT s u m b -> ParsecT s u m (a,b)
p1 >*< p2 = do
    x <- p1
    y <- p2
    return (x,y)
    
infixr 1 >+< 
(>+<) :: ParsecT s u m a -> ParsecT s u m b -> ParsecT s u m (Either a b)
p1 >+< p2 = liftM Left p1 <|> liftM Right p2

infixr 1 <||>
(<||>) :: ParsecT s u m a -> ParsecT s u m a -> ParsecT s u m a
p1 <||> p2 = try p1 <|> p2

apA :: Applicative f => f a -> (a -> b) -> f b
apA m f = pure f <*> m

apA2 :: Applicative f => f a -> f b -> (a -> b -> c) -> f c
apA2 ma mb f = pure f <*> ma <*> mb

apA3 :: Applicative f => f a -> f b -> f c -> (a -> b -> c -> d) -> f d
apA3 ma mb mc f = pure f <*> ma <*> mb <*> mc

apA4 :: Applicative f => f a -> f b -> f c -> f d -> (a -> b -> c -> d -> e) -> f e
apA4 ma mb mc md f = pure f <*> ma <*> mb <*> mc <*> md

apA5 :: Applicative f => f a -> f b -> f c -> f d -> f e -> (a -> b -> c -> d -> e -> g) -> f g
apA5 ma mb mc md me f = pure f <*> ma <*> mb <*> mc <*> md <*> me

apA6 :: Applicative f => f a -> f b -> f c -> f d -> f e -> f g -> (a -> b -> c -> d -> e -> g -> h) -> f h
apA6 ma mb mc md me mg f = pure f <*> ma <*> mb <*> mc <*> md <*> me <*> mg

apA7 :: Applicative f => f a -> f b -> f c -> f d -> f e -> f g -> f h -> (a -> b -> c -> d -> e -> g -> h -> i) -> f i
apA7 ma mb mc md me mg mh f = pure f <*> ma <*> mb <*> mc <*> md <*> me <*> mg <*> mh

apA8 :: Applicative f => f a -> f b -> f c -> f d -> f e -> f g -> f h -> f i -> (a -> b -> c -> d -> e -> g -> h -> i -> j) -> f j
apA8 ma mb mc md me mg mh mi f = pure f <*> ma <*> mb <*> mc <*> md <*> me <*> mg <*> mh <*> mi

apA9 :: Applicative f => f a -> f b -> f c -> f d -> f e -> f g -> f h -> f i -> f j -> (a -> b -> c -> d -> e -> g -> h -> i -> j -> k) -> f k
apA9 ma mb mc md me mg mh mi mj f = pure f <*> ma <*> mb <*> mc <*> md <*> me <*> mg <*> mh <*> mi <*> mj

many' :: ParsecT tok st m a -> ParsecT tok st m [a]
many' p = maybeCont p $ \mb -> case mb of
    Nothing -> return []
    Just x -> do
        xs <- many' p
        return (x:xs)

many1' :: ParsecT tok st m a -> ParsecT tok st m [a]
many1' p = do
    x <- p
    xs <- many' p
    return (x:xs)

sepBy' :: ParsecT tok st m a -> ParsecT tok st m sep -> ParsecT tok st m [a]
sepBy' p sep = sepBy1' p sep <||> return []

sepBy1' :: ParsecT tok st m a -> ParsecT tok st m sep -> ParsecT tok st m [a]
sepBy1' p sep = do
    x <- p
    xs <- many' (sep >> p)
    return (x:xs)

maybeCont :: ParsecT tok st m a -> (Maybe a -> ParsecT tok st m b) -> ParsecT tok st m b
maybeCont p cont = (p >>= cont . Just) <||> cont Nothing
                
maybeContPair :: ParsecT tok st m a -> ParsecT tok st m b -> ParsecT tok st m (Maybe a,b)
maybeContPair p cont = maybeCont p (\mb -> liftM (mb,) cont)

foldl1 :: Stream s m t => (a -> b -> ParsecT s u m a) -> ParsecT s u m a -> ParsecT s u m b -> ParsecT s u m a
foldl1 f ma mb = do
    x <- ma
    ys <- many mb
    Foldable.foldlM f x ys
