{-# LANGUAGE DeriveGeneric, DeriveDataTypeable, FlexibleContexts, MultiParamTypeClasses, FlexibleInstances, TypeSynonymInstances, RankNTypes, TypeFamilies #-}

module Language.Jasmin.TypeChecker.TyInfo where

import Language.Jasmin.Syntax
import Language.Position
import Language.Location
import Language.Vars

import Data.Map (Map(..))
import qualified Data.Map as Map
import Utils
import Safe
import Control.Monad
import Data.Generics hiding (Generic)
import GHC.Generics
import Data.Unique
import Data.Binary
import Data.Hashable
import Control.DeepSeq as DeepSeq
import Control.DeepSeq.Generics hiding (force)

-- (read variables, written variables)
type DecClass = (DecClassVars,DecClassVars)

-- (variables,isglobal)
type DecClassVars = (Map Piden (Ptype TyInfo,Bool),Bool)

emptyDecClassVars = (Map.empty,False)
emptyDecClass = (emptyDecClassVars,emptyDecClassVars)

isGlobalDecClassVars :: DecClassVars -> Bool
isGlobalDecClassVars (xs,b) = b || not (Map.null $ Map.filter snd xs)

addDecClassVars :: DecClassVars -> DecClassVars -> DecClass -> DecClass
addDecClassVars r2 w2 (r1,w1) = (joinVs r1 r2,joinVs w1 w2)
      where
      joinVs (vs1,b1) (vs2,b2) = (Map.unionWith add vs1 vs2,b1 || b2)
          where add (x1,y1) (x2,y2) = (x1,y1 || y2)

data TyInfo = TyInfo { infoSto' :: Maybe Pstorage, infoTy' :: Maybe (Ptype TyInfo), infoDecClass' :: Maybe DecClass, infoLoc :: Position }
  deriving (Eq,Data,Ord,Typeable,Show,Generic)
instance Binary TyInfo
instance Hashable TyInfo
instance NFData TyInfo where
    rnf = genericRnf

instance Location TyInfo where
    locpos = infoLoc
    noloc = noTyInfo noloc
    updpos t l = t { infoLoc = l }

instance GenVar Piden m => Vars Piden m Position where
    traverseVars f = return

instance GenVar Piden m => Vars Piden m TyInfo where
    traverseVars f (TyInfo sto ty cl l) = do
        sto' <- f sto
        ty' <- f ty
        cl' <- forM cl $ \(rs,ws) -> do
            rs' <- traverseDecClassVars f rs
            ws' <- traverseDecClassVars f ws
            return (rs',ws')
        l' <- f l
        return $ TyInfo sto' ty' cl' l'

traverseDecClassVars :: GenVar Piden m => (forall b . Vars Piden m b => b -> VarsM Piden m b) -> DecClassVars -> VarsM Piden m DecClassVars
traverseDecClassVars f (y,b) = do
    y' <- liftM (Map.fromList . map (mapFst id) . Map.toList) $ f $ Map.fromList . map (mapFst id) $ Map.toList y
    b' <- f b
    return (y',b')

infoSto = fromJustNote "infoSto" . infoSto'
infoTy = fromJustNote "infoTy" . infoTy'
infoTyNote note = fromJustNote note . infoTy'
infoDecClass :: TyInfo -> DecClass
infoDecClass = maybe emptyDecClass id . infoDecClass'

infoStoty :: TyInfo -> Pstotype TyInfo
infoStoty i = (maybe Inline id $ infoSto' i,infoTyNote "infoStoTy" i)

infoStotyNote :: String -> TyInfo -> Pstotype TyInfo
infoStotyNote note i = (maybe Inline id $ infoSto' i,infoTyNote note i)

noTyInfo l = TyInfo Nothing Nothing Nothing l
tyInfo t = TyInfo Nothing (Just t) Nothing noloc
stotyInfo sto t = TyInfo (Just sto) (Just t) Nothing noloc
decInfo d = TyInfo Nothing Nothing (Just d) noloc
decInfoLoc d l = TyInfo Nothing Nothing (Just d) l
tyInfoLoc t l = TyInfo Nothing (Just t) Nothing l
tyInfoLoc' Nothing l = TyInfo Nothing Nothing Nothing l
tyInfoLoc' (Just t) l = TyInfo Nothing (Just t) Nothing l
stotyInfoLoc sto t l = TyInfo (Just sto) (Just t) Nothing l
stotyInfoLoc' Nothing t l = TyInfo Nothing (Just t) Nothing l
stotyInfoLoc' (Just sto) t l = TyInfo (Just sto) (Just t) Nothing l

pstotypeTyInfo :: Pstotype TyInfo -> TyInfo
pstotypeTyInfo (sto,t) = stotyInfo sto t

locTy :: (Located a,LocOf a ~ TyInfo) => a -> Ptype TyInfo
locTy = infoTyNote "locTy" . loc

locTyNote :: (Located a,LocOf a ~ TyInfo) => String -> a -> Ptype TyInfo
locTyNote str = infoTyNote str . loc

locTy' :: (Located a,LocOf a ~ TyInfo) => a -> Maybe (Ptype TyInfo)
locTy' = infoTy' . loc

pblockTy :: [Pinstr TyInfo] -> Pblock TyInfo
pblockTy is = Pblock (decInfoLoc cl p) is
    where
    p = maybe noloc (infoLoc . loc) (headMay is)
    cls = map (infoDecClass . loc) is
    cl = foldr (\(rs,ws) cl -> addDecClassVars rs ws cl) emptyDecClass cls

falsePexpr,truePexpr :: Pexpr TyInfo
falsePexpr = Pexpr (tyInfoLoc TBool noloc) $ PEBool False
truePexpr = Pexpr (tyInfoLoc TBool noloc) $ PEBool True
intPexpr :: Integer -> Pexpr TyInfo
intPexpr i = Pexpr (tyInfoLoc TInt noloc) $ PEInt i

instance GenVar Piden IO where
    mkVar str = return $ Pident () str
    newVar (Pident i n) = do
        u <- newUnique
        let n' = n++"_"++show (hashUnique u)
        return $ Pident i n'

locWordTy :: (Located a,LocOf a ~ TyInfo) => a -> Maybe Wsize
locWordTy = join . fmap wordTy . locTy'

locNumericTy :: (Located a,LocOf a ~ TyInfo) => a -> Bool
locNumericTy = maybe False id . fmap isNumericType . locTy'

locBoolTy :: (Located a,LocOf a ~ TyInfo) => a -> Bool
locBoolTy = maybe False id . fmap isBoolType . locTy'





