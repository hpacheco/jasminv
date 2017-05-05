{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveDataTypeable, TypeFamilies, FlexibleContexts, DeriveGeneric #-}

module Language.Jasmin.Error where

import Language.Location
import Language.Jasmin.TypeChecker.TyInfo
import Language.Position
import Language.Jasmin.Syntax
import Language.Jasmin.Parser.Tokens

import Data.Generics hiding (empty,Generic)
import Data.Int
import Data.Word
import Data.Hashable
import Data.Binary

import GHC.Generics (Generic)

import Control.Monad.Except
import Control.Monad.Writer.Strict (tell,MonadWriter(..))
import Control.DeepSeq as DeepSeq
import Control.DeepSeq.Generics hiding (force)

import Text.Parsec (ParseError(..))
import Text.PrettyPrint.Exts as PP

data ParserException 
    = LexicalException String
    | ParserException String 
    deriving (Show,Typeable,Data,Eq,Ord,Generic)

instance Binary ParserException
instance Hashable ParserException
instance NFData ParserException where
    rnf = genericRnf

instance Monad m => PP m ParserException where
    pp (LexicalException s) = return $ text "Lexical error:" <+> text s
    pp (ParserException err) = return $ text "Parser error:" <+> text err

parserError :: ParserException -> JasminError
parserError = ParserError

data JasminError = ParserError ParserException
                 | GenericError
                     Position -- ^ position
                     Doc -- ^message
                     (Maybe JasminError) -- recursive error
                | TypeCheckerError Position TypeCheckerException
  deriving (Show,Typeable,Data,Eq,Ord,Generic)
  
instance Binary JasminError
instance Hashable JasminError
instance NFData JasminError where
    rnf = genericRnf

instance Located JasminError where
     type LocOf JasminError = Position
     loc (ParserError _) = noloc
     loc (GenericError p _ _) = p
     loc (TypeCheckerError p _) = p
     updLoc = error "cannot update location in errors"

instance Monad m => PP m JasminError where
    pp (ParserError err) = pp err
    pp (GenericError p msg Nothing) = do
        pp1 <- pp p
        return $ pp1 <> char ':' $+$ nest 4 msg
    pp (GenericError p msg (Just err)) = do
        pp1 <- pp p
        pp2 <- pp err
        return $ pp1 <> char ':' $+$ nest 4 msg $+$ text "Because of:" <+> pp2
    pp (TypeCheckerError p err) = do
        pp1 <- pp p
        pp2 <- pp err
        return $ pp1 <> char ':' $+$ pp2

genError :: MonadError JasminError m => Position -> Doc -> m a
genError pos msg = throwError $ GenericError pos msg Nothing

tyError :: MonadError JasminError m => Position -> TypeCheckerException -> m a
tyError pos msg = throwError $ TypeCheckerError pos msg

data Typattern = TPBool | TPInt | TPWord | TPArray
  deriving (Show,Typeable,Data,Eq,Ord,Generic)

instance Binary Typattern
instance Hashable Typattern
instance NFData Typattern where
    rnf = genericRnf

instance Monad m => PP m Typattern where
    pp = return . text . show

data TypeCheckerException
  = UnknownVar          Piden Doc
  | UnknownFun          Piden Doc
  | InvalidType         (Ptype TyInfo) Typattern
  | TypeMismatch        (Ptype TyInfo) (Ptype TyInfo)
  | InvOpInExpr         Peop2
  | NoOperator          Peop2 [Ptype TyInfo]
  | InvalidArgCount     Int Int
  | DuplicateFun        Piden Position
  | InvalidCast         (Ptype TyInfo) (Ptype TyInfo)
  | LvalueWithNoBaseTy
  | LvalueTooWide
  | LvalueTooNarrow
  | EqOpWithNoLValue
  | InvalidLRValue Plval
  | CallNotAllowed
  | Unsupported Doc
  deriving (Show,Typeable,Data,Eq,Ord,Generic)

instance Binary TypeCheckerException
instance Hashable TypeCheckerException
instance NFData TypeCheckerException where
    rnf = genericRnf

instance Monad m => PP m TypeCheckerException where
    pp = return . text . show

