{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}

module Data.SBV.Exts
    ( module Data.SBV.Exts
    , module Data.SBV
    ) where

import Data.LargeWord hiding (Word256)
import Data.SBV.Dynamic (SVal,svJoin,svExtract)
import Data.SBV.Internals (SBV(..),genFromCW,genLiteral,genMkSymVar,liftDMod,liftQRem)
import qualified Data.SBV.Dynamic as SBV
import qualified Data.SBV.Internals as SBV
import Data.SBV

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

instance Mergeable SVal where
    symbolicMerge f (SBV b) v1 v2 | kindOf v1 == kindOf v2 = SBV.svSymbolicMerge (kindOf v1) f b v1 v2
    
sWord128 :: String -> Symbolic SWord128
sWord128 = symbolic
sWord256 :: String -> Symbolic SWord256
sWord256 = symbolic
sWord512 :: String -> Symbolic SWord512
sWord512 = symbolic

instance SIntegral Word128
instance SIntegral Word256
instance SIntegral Word512


