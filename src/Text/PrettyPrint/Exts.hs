{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}

module Text.PrettyPrint.Exts
    ( module Text.PrettyPrint.Exts
    , module Text.PrettyPrint
    ) where

import Text.PrettyPrint
import Text.Ordinal

import Data.Foldable as Foldable
import Data.Binary
import Data.Int
import Data.Word
import Data.Hashable
import Data.Generics hiding (empty,GT)
import Data.ByteString.Lazy.Char8 hiding (empty)

import Control.Monad
import Control.Monad.Identity

ppSpaced3 :: (PP m x,PP m y,PP m z) => ((x,y),z) -> m Doc
ppSpaced3 ((x,y),z) = do
    px <- pp x
    py <- pp y
    pz <- pp z
    return $ px <+> py <+> pz

ppSpaced :: (PP m x,PP m y) => (x,y) -> m Doc
ppSpaced (x,y) = do
    px <- pp x
    py <- pp y
    return $ px <+> py

spaced :: Monad m => m Doc -> m Doc -> m Doc
spaced mx my = do
    x <- mx
    y <- my
    return $ x <+> y

suffix :: Monad m => m Doc -> Doc -> m Doc
suffix mx y = do
    x <- mx
    return $ x <> y

prefix :: Monad m => Doc -> m Doc -> m Doc
prefix x my = do
    y <- my
    return $ x <> y

instance Binary Doc where
    put d = do
        put ((pack $ show d) :: ByteString)
    get = do
        s <- get :: Get ByteString
        return $ text $ show $ unpack s
    
class (Monad m) => PP m a where
    pp :: a -> m Doc

sepByM :: Monad m => m [Doc] -> Doc -> m Doc
sepByM mx s = do
    x <- mx
    return $ sepBy x s

parensM :: Monad m => m Doc -> m Doc
parensM mx = mx >>= \x -> return $ parens x

semicolon = char ';'

nonemptyParens :: Doc -> Doc
nonemptyParens x = if isEmpty x then empty else parens x

ppid :: PP Identity a => a -> Doc
ppid x = runIdentity (pp x)

pprid :: PP Identity a => a -> String
pprid x = runIdentity (ppr x)

ppr :: PP m a => a -> m String
ppr = liftM show . pp

ppOptM :: Monad m => Maybe a -> (a -> m Doc) -> m Doc
ppOptM Nothing f = return empty
ppOptM (Just x) f = f x

ppMbM :: PP m a => Maybe a -> m Doc
ppMbM = flip ppOptM pp

abrackets p = char '<' <> p <> char '>'

sepBy :: Foldable t => t Doc -> Doc -> Doc
sepBy ps sep = hsep (punctuate sep $ toList ps)

vbraces x = char '{' $+$ nest 1 x $+$ char '}'

ppOrdinal :: (Show a,Integral a) => a -> Doc
ppOrdinal = text . show . showOrdinal

instance Monad m => PP m Doc where
    pp = return
    
instance Monad m => PP m Ordering where
    pp EQ = return $ text "="
    pp LT = return $ text "<"
    pp GT = return $ text ">"

instance PP m a => PP m (Maybe a) where
    pp Nothing = return empty
    pp (Just x) = pp x

instance Monad m => PP m Integer where
    pp = return . integer
    
instance Monad m => PP m Char where
    pp = return . char

instance Monad m => PP m Int where
    pp = return . int

instance PP m a => PP m [a] where
    pp xs = liftM hcat $ mapM pp xs
    
instance (PP m a,PP m b) => PP m (a,b) where
    pp (x,y) = do
        px <- pp x
        py <- pp y
        return $ px <> py

instance Monad m => PP m Int8 where
    pp = return . text . show
instance Monad m => PP m Int16 where
    pp = return . text . show
instance Monad m => PP m Int32 where
    pp = return . text . show
instance Monad m => PP m Int64 where
    pp = return . text . show

instance Monad m => PP m Word8 where
    pp = return . text . show
instance Monad m => PP m Word16 where
    pp = return . text . show
instance Monad m => PP m Word32 where
    pp = return . text . show
instance Monad m => PP m Word64 where
    pp = return . text . show
instance Monad m => PP m Float where
    pp = return . text . show
instance Monad m => PP m Double where
    pp = return . text . show

instance Monad m => PP m () where
    pp () = return empty

instance Data Doc where
    gunfold _ _ _ = error "gunfold Doc"
    toConstr = error "toConstr Doc"
    dataTypeOf = error "dataTypeOf Doc"

instance Ord Doc where
    compare x y = compare (show x) (show y)

instance Monad m => PP m Bool where
    pp = return . text . show

instance Hashable Doc where
    hashWithSalt i x = hashWithSalt i (show x)
