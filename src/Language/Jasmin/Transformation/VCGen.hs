{-# LANGUAGE ConstraintKinds #-}

module Language.Jasmin.Transformation.VCGen where

import Language.Jasmin.Syntax
import Utils
import Language.Jasmin.TypeChecker.TyInfo
import Language.Jasmin.Transformation.Simplify
import Language.Position
import Language.Location
import Control.Monad
import Control.Monad.IO.Class
import Text.PrettyPrint.Exts

-- converts a procedure into straightline code
straightPfundef :: VCK m => Pfundef TyInfo -> m [Pinstr TyInfo]
straightPfundef (Pfundef cc n args rty anns (Pfunbody vars instrs ret) info) = do
    args' <- concatMapM straightParg args
    let (pres,posts) = splitProcAnns anns 
    vars' <- concatMapM straightPbodyarg vars
    let pres' = map anninstr2instr pres
    let posts' = map anninstr2instr posts
    return $ args' ++ vars' ++ pres' ++ instrs ++ posts'

straightParg :: VCK m => Parg TyInfo -> m [Pinstr TyInfo]
straightParg (Parg t (Just n)) = do
    return [Pinstr (noTyInfo $ infoLoc $ loc n) $ Anninstr $ VarDefAnn $ Annarg (snd t) n Nothing]

straightPbodyarg :: VCK m => Pbodyarg TyInfo -> m [Pinstr TyInfo]
straightPbodyarg (Pbodyarg t n) = do
    return [Pinstr (noTyInfo $ infoLoc $ loc n) $ Anninstr $ VarDefAnn $ Annarg (snd t) n Nothing]

genVCsPfundef :: VCK m => Pfundef TyInfo -> m [([Pinstr TyInfo],Pexpr TyInfo)]
genVCsPfundef = straightPfundef >=> genTriples
    
-- generates a set of Hoare Triples from straightline code (pre-conditions within the code)
genTriples :: VCK m => [Pinstr TyInfo] -> m [([Pinstr TyInfo],Pexpr TyInfo)]
genTriples is = do
    res <- genTriples' [] is
    return res

genTriples' :: VCK m => [Pinstr TyInfo] -> [Pinstr TyInfo] -> m [([Pinstr TyInfo],Pexpr TyInfo)]
genTriples' acc [] = return []
genTriples' acc (x:xs) = do
    e <- genTriplePinstr x
    case e of
        Left x' -> genTriples' (acc++[x']) xs
        Right expr -> do
            let assume = Pinstr (loc x) $ Anninstr $ AssumeAnn False expr
            ys <- genTriples' (acc++[assume]) xs
            return $ (acc,expr) : ys

genTriplePinstr :: VCK m => Pinstr TyInfo -> m (Either (Pinstr TyInfo) (Pexpr TyInfo))
genTriplePinstr (Pinstr t i) = genTriplePinstr_r t i

genTriplePinstr_r :: VCK m => TyInfo -> Pinstr_r TyInfo -> m (Either (Pinstr TyInfo) (Pexpr TyInfo))
genTriplePinstr_r t (Anninstr i) = genTriplePanninstr_r t i
genTriplePinstr_r t i = return (Left $ Pinstr t i)

genTriplePanninstr_r :: VCK m => TyInfo -> StatementAnnotation_r TyInfo -> m (Either (Pinstr TyInfo) (Pexpr TyInfo))
genTriplePanninstr_r t (AssertAnn isLeak e) = if isLeak
    then return $ Left $ Pinstr t $ Anninstr $ AssumeAnn False truePexpr
    else return $ Right e
genTriplePanninstr_r t (EmbedAnn isLeak i) = if isLeak
    then return $ Left $ Pinstr t $ Anninstr $ AssumeAnn False truePexpr
    else genTriplePinstr i
genTriplePanninstr_r t i = return $ Left $ Pinstr t $ Anninstr i

-- * State

type VCK m = MonadIO m