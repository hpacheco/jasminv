{-# LANGUAGE DeriveDataTypeable, TypeFamilies, MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables #-}

module Language.Jasmin.Parser.Tokens where

import Text.PrettyPrint.Exts
import Language.Position
import Language.Location

import Data.Generics
import Data.Digits (digits, unDigits)
import Data.List as List

import Safe

data TokenInfo
    = TokenInfo 
        { tSymb :: Token
        , tText :: !String
        , tLoc  :: Position
        }
  deriving (Show,Read,Data,Typeable)

instance Eq TokenInfo where
    x == y = tSymb x == tSymb y
instance Ord TokenInfo where
    compare x y = compare (tSymb x) (tSymb y)

instance Located TokenInfo where
    type LocOf TokenInfo = Position
    loc = tLoc
    updLoc t l = t { tLoc = l }
 
instance Monad m => PP m TokenInfo where
    pp = pp . tSymb

data Token
    = T_U Int  
    | T_I Int  
    | T_BOOL
    | T_INT 
    | REG   
    | STACK 
    | INLINE
    | EXPORT
    | PARAM 
    | MEM   
    | TRUE  
    | FALSE 
    | FOR   
    | WHEN  
    | WHILE 
    | DO    
    | IF    
    | ELSE  
    | FN    
    | RETURN
    | TO
    | DOWNTO
    
    | INT Integer
    | NID String
    
    | AT
    | LBRACK     
    | RBRACK     
    | LBRACE    
    | RBRACE    
    | LPAREN     
    | RPAREN     
    | RARROW     
    | COLON      
    | UNDERSCORE 
    | MOD
    | EQ_         
    | EQEQ       
    | BANGEQ       
    | PLUSEQ     
    | STAREQ      
    | MINUSEQ    
    | AMPEQ     
    | LE         
    | LT_         
    | GE         
    | GT_         
    | LE_SIGNED         
    | LT_SIGNED         
    | GE_SIGNED         
    | GT_SIGNED
    | DOTDOT     
    | COMMA      
    | GTGTEQ      
    | LTLTEQ      
    | HATEQ      
    | PIPEEQ       
    | MINUS      
    | STAR       
    | PLUS       
    | AMP       
    | AMPAMP       
    | PIPEPIPE        
    | SEMICOLON  
    | BANG       
    | GTGT       
    | GTGT_SIGNED        
    | LTLT        
    | HAT        
    | PIPE       
    | QUESTION
    | TokenEOF  
    | TokenError
    
    | VALID
    | FREE
    | LEAKAGE
    | PUBLIC
    | FUNCTION
    | AXIOM
    | LEMMA
    | ASSUME
    | ASSERT
    | INVARIANT
    | DECREASES
    | REQUIRES
    | ENSURES
    | FORALL
    | EXISTS
    | ANNOTATION [String]
  deriving (Eq,Ord,Read,Show,Data,Typeable)

instance Monad m => PP m Token where
    pp (T_U i)     = return $ text "u" <> int i
    pp (T_I i)    = return $ text "int" <> int i
    pp T_BOOL   = return $ text "bool"
    pp T_INT    = return $ text "int"
    pp REG      = return $ text "reg"
    pp STACK    = return $ text "stack"
    pp INLINE   = return $ text "inline"
    pp EXPORT   = return $ text "export"
    pp PARAM    = return $ text "param"
    pp MEM      = return $ text "MEM"
    pp TRUE     = return $ text "true"
    pp FALSE    = return $ text "false"
    pp FOR      = return $ text "for"
    pp WHEN     = return $ text "when"
    pp WHILE    = return $ text "while"
    pp DO       = return $ text "do"
    pp IF       = return $ text "if"
    pp ELSE     = return $ text "else"
    pp FN       = return $ text "fn"
    pp RETURN   = return $ text "return"
    pp TO       = return $ text "to"
    pp DOWNTO   = return $ text "downto"
    
    pp (INT i) = return $ integer i
    pp (NID s) = return $ text s
    
    pp AT         = return $ text "@"
    pp LBRACK      = return $ text "["   
    pp RBRACK      = return $ text "]"   
    pp LBRACE     = return $ text "{"   
    pp RBRACE     = return $ text "}"   
    pp LPAREN      = return $ text "("   
    pp RPAREN      = return $ text ")"   
    pp RARROW      = return $ text "->"  
    pp COLON       = return $ text ":"   
    pp UNDERSCORE  = return $ text "_"   
    pp MOD         = return $ text "%"
    pp EQ_         = return $ text "="   
    pp EQEQ        = return $ text "=="  
    pp BANGEQ        = return $ text "!="  
    pp PLUSEQ      = return $ text "+="  
    pp STAREQ       = return $ text "*="  
    pp MINUSEQ     = return $ text "-="  
    pp AMPEQ      = return $ text "&="  
    pp LE          = return $ text "<="  
    pp LT_         = return $ text "<"   
    pp GE          = return $ text ">="  
    pp GT_         = return $ text ">"   
    pp LE_SIGNED          = return $ text "<=s"  
    pp LT_SIGNED         = return $ text "<s"   
    pp GE_SIGNED          = return $ text ">=s"  
    pp GT_SIGNED         = return $ text ">s"   
    pp DOTDOT      = return $ text ".."  
    pp COMMA       = return $ text ","   
    pp GTGTEQ       = return $ text ">>=" 
    pp LTLTEQ       = return $ text "<<=" 
    pp HATEQ       = return $ text "^="  
    pp PIPEEQ        = return $ text "|="  
    pp MINUS       = return $ text "-"   
    pp STAR        = return $ text "*"   
    pp PLUS        = return $ text "+"   
    pp AMP        = return $ text "&"   
    pp AMPAMP        = return $ text "&&"  
    pp PIPEPIPE         = return $ text "||"  
    pp SEMICOLON   = return $ text ";"   
    pp BANG        = return $ text "!"   
    pp GTGT         = return $ text ">>"  
    pp GTGT_SIGNED = return $ text ">>s"
    pp LTLT         = return $ text "<<"  
    pp HAT         = return $ text "^"   
    pp PIPE          = return $ text "|"   
    pp QUESTION      = return $ text "?"   
    pp TokenEOF =               return $ text "<EOF>"
    pp TokenError =             return $ text "error <unknown>"
    
    pp FREE              = return $ text "free"
    pp VALID              = return $ text "valid"
    pp LEAKAGE           = return $ text "leakage"
    pp PUBLIC            = return $ text "public"
    pp FUNCTION          = return $ text "function"
    pp AXIOM             = return $ text "axiom"
    pp LEMMA             = return $ text "lemma"
    pp ASSUME             = return $ text "assume"
    pp ASSERT             = return $ text "assert"
    pp INVARIANT          = return $ text "invariant"
    pp DECREASES          = return $ text "decreases"
    pp REQUIRES          = return $ text "requires"
    pp ENSURES          = return $ text "ensures"
    pp FORALL          = return $ text "forall" 
    pp EXISTS          = return $ text "exists" 
    pp (ANNOTATION anns) =      return $ text "/*" <+> vcat (map (\ann -> text "@" <> text ann) anns) <+> text "*/"
    
convertBase :: Integral a => a -> a -> [a] -> [a]
convertBase from to = digits to . unDigits from

convert_to_base :: Int -> String -> Integer
convert_to_base base input = unDigits (toEnum base) $ convertBase 10 (toEnum base) $ digits 10 $ readInteger input

convert_from_base :: Int -> Integer -> String
convert_from_base base input = concatMap show ds10
    where
    dsBase :: [Integer] = digits (toEnum base) input
    ds10 :: [Integer] = convertBase (toEnum base) 10 dsBase

readInteger :: String -> Integer
readInteger = readNote "read Integer"

isAnnotation :: String -> Maybe [String]
isAnnotation s = if ok then Just (map (takeWhile (/='@') . tail . dropWhile (/='@')) toks) else Nothing
    where
    toks = lines s
    ok = not (List.null toks) && and (map (maybe False (=="@") . headMay . words) toks)