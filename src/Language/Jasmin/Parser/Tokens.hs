{-# LANGUAGE DeriveDataTypeable, TypeFamilies, MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables #-}

module Language.Jasmin.Parser.Tokens where

import Text.PrettyPrint.Exts
import Language.Position
import Language.Location

import Data.Generics
import Data.Digits (digits, unDigits)

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
    = T_U8  
    | T_U16 
    | T_U32 
    | T_U64 
    | T_U128
    | T_U256
    | T_BOOL
    | T_INT 
    | REG   
    | STACK 
    | INLINE
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
    | LTLT        
    | HAT        
    | PIPE       
    | QUESTION
    | TokenEOF  
    | TokenError
  deriving (Eq,Ord,Read,Show,Data,Typeable)

instance Monad m => PP m Token where
    pp T_U8     = return $ text "u8"
    pp T_U16    = return $ text "u16"
    pp T_U32    = return $ text "u32"
    pp T_U64    = return $ text "u64"
    pp T_U128   = return $ text "u128"
    pp T_U256   = return $ text "u256"
    pp T_BOOL   = return $ text "bool"
    pp T_INT    = return $ text "int"
    pp REG      = return $ text "reg"
    pp STACK    = return $ text "stack"
    pp INLINE   = return $ text "inline"
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
    pp LTLT         = return $ text "<<"  
    pp HAT         = return $ text "^"   
    pp PIPE          = return $ text "|"   
    pp QUESTION      = return $ text "?"   
    pp TokenEOF =               return $ text "<EOF>"
    pp TokenError =             return $ text "error <unknown>"
    
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
