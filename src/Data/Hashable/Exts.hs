module Data.Hashable.Exts
    ( module Data.Hashable
    , module Data.Hashable.Exts
    ) where

import Data.Hashable
import Data.Map as Map
import qualified Data.Map (Map(..))
import Data.Set as Set
import qualified Data.Set (Set(..))

instance (Hashable a,Hashable b) => Hashable (Map a b) where
    hashWithSalt i x = hashWithSalt i (Map.toList x)

instance Hashable a => Hashable (Set a) where
    hashWithSalt i x = hashWithSalt i (Set.toList x)