{-# LANGUAGE ViewPatterns #-}

module Language.Jasmin.Parser.Parser where

import Options
import Text.Parsec.Exts as Parsec
import Text.PrettyPrint.Exts (PP(..))
import qualified Text.PrettyPrint.Exts as PP
import Language.Jasmin.Syntax
import Language.Jasmin.Parser.Tokens
import Language.Jasmin.Parser.Lexer
import Language.Position
import Language.Location
import Language.Jasmin.Error

import System.IO

import Control.Monad.IO.Class
import Control.Monad
import Control.Monad.Except

type ParserT m a = ParsecT [TokenInfo] () m a

ident :: Monad m => ParserT m (Pident Position)
ident = liftM (\(Loc l x) -> Pident l x) (locp $ tokWith getNID) <?> "ident"
    where
    getNID t@(tSymb -> NID x) = Just x
    getNID _ = Nothing

var :: Monad m => ParserT m (Pident Position)
var = ident <?> "var"

-- (* ** Type expressions
--  * -------------------------------------------------------------------- *)
 
utype :: Monad m => ParserT m Wsize
utype = toK T_U8 W8
    <|> toK T_U16 W16
    <|> toK T_U32 W32
    <|> toK T_U64 W64
    <|> toK T_U128 W128
    <|> toK T_U256 W256
    <?> "utype"

ptype_ :: Monad m => ParserT m (Ptype Position)
ptype_ = toK T_BOOL TBool
     <|> toK T_INT TInt
     <|> apA2 utype (optionMaybe $ brackets pexpr) (\ut mbd -> case mbd of { Nothing -> TWord ut; Just d -> TArray ut d })
     <?> "ptype_"

-- (* ** Index expressions
--  * -------------------------------------------------------------------- *)

peop1 :: Monad m => ParserT m Peop1
peop1 = toK BANG Not1 <?> "peop1"

peop2 :: Monad m => ParserT m Peop2
peop2 = toK PLUS Add2
    <|> toK MINUS Sub2
    <|> toK STAR     Mul2  
    <|> toK AMPAMP   And2  
    <|> toK PIPEPIPE Or2   
    <|> toK AMP      BAnd2 
    <|> toK PIPE     BOr2  
    <|> toK HAT      BXor2 
    <|> toK LTLT     Shl2  
    <|> toK GTGT     Shr2  
    <|> toK EQEQ     Eq2   
    <|> toK BANGEQ   Neq2  
    <|> toK LT_      Lt2   
    <|> toK LE       Le2   
    <|> toK GT_      Gt2   
    <|> toK GE       Ge2   
    <?> "peop2"

pexpr :: Monad m => ParserT m (Pexpr Position)
pexpr = Parsec.foldl1 (\e1@(Pexpr l _) (o,e2) -> return $ Pexpr l $ PEOp2 o e1 e2) non2expr (peop2 >*< non2expr) <?> "pexpr"

non2expr :: Monad m => ParserT m (Pexpr Position)
non2expr = liftM (\(Loc l x) -> Pexpr l x) (locp non2expr_r) <?> "non2expr"

non2expr_r :: Monad m => ParserT m (Pexpr_r Position)
non2expr_r = apA2 ident (parens_tuple pexpr) (\fname args -> PECall fname args)
      <||> apA2 var (optionMaybe $ brackets pexpr) (\v mbi -> case mbi of { Nothing -> PEVar v; Just i -> PEGet v i })
      <|> toK TRUE (PEBool True)
      <|> toK FALSE (PEBool False)
      <|> tokWith getInt
      <|> apA2 peop1 non2expr (\o e -> PEOp1 o e)
--      <|> apA3 non2expr peop2 non2expr (\e1 o e2 -> PEOp2 o e1 e2)
      <|> apA (parens pexpr) (\e -> PEParens e)
      <||> apA6 (optionMaybe $ parens ptype_) (tok LBRACK) var (tok PLUS) pexpr (tok RBRACK) (\ct _ v _ e _ -> PEFetch ct v e)
      <?> "non2expr_r"
  where
  getInt t@(tSymb -> INT i) = Just $ PEInt i
  getInt t = Nothing

-- (* -------------------------------------------------------------------- *)
peqop :: Monad m => ParserT m Peqop
peqop = toK EQ_ RawEq
    <|> toK PLUSEQ  AddEq
    <|> toK MINUSEQ SubEq
    <|> toK STAREQ  MulEq
    <|> toK GTGTEQ  ShREq
    <|> toK LTLTEQ  ShLEq
    <|> toK AMPEQ   BAndEq
    <|> toK HATEQ   BXOrEq
    <|> toK PIPEEQ  BOrEq
    <?> "peqop"
 
-- (* ** Left value
--  * -------------------------------------------------------------------- *)
-- (* FIXME: missing syntax for Lmem *)

plvalue_r :: Monad m => ParserT m (Plvalue_r Position)
plvalue_r = toK UNDERSCORE PLIgnore
        <|> apA2 var (optionMaybe $ brackets pexpr) (\x mbi -> case mbi of { Nothing -> PLVar x; Just i -> PLArray x i })
        <|> apA6 (optionMaybe (parens ptype_)) (tok LBRACK) var (tok PLUS) pexpr (tok RBRACK) (\ct _ v _ e _ -> PLMem ct v e)
        <?> "plvalue_r"

plvalue :: Monad m => ParserT m (Plvalue Position)
plvalue = liftM (\(Loc l x) -> Plvalue l x) (locp plvalue_r) <?> "plvalue"

-- (* ** Control instructions
--  * -------------------------------------------------------------------- *)

pinstr_r :: Monad m => ParserT m (Pinstr_r Position)
pinstr_r = apA5 lval (peqop) pexpr (optionMaybe $ prefix (tok IF) pexpr) (tok SEMICOLON) (\x o e c _ -> PIAssign x o e c)
       <|> apA4 (tok IF) pexpr pblock (optionMaybe $ tok ELSE *> pblock) (\_ c i1s i2s -> PIIf c i1s i2s)
       <|> apA7 (tok FOR) var (tok EQ_) pexpr fordir pexpr pblock (\_ v _ ce1 dir ce2 is -> PIFor v dir ce1 ce2 is)
       <|> apA4 (tok WHILE) (optionMaybe pblock) pexpr (optionMaybe pblock) (\_ is1 b is2 -> PIWhile is1 b is2 )
       <?> "pinstr_r"

fordir :: Monad m => ParserT m Fordir
fordir = toK TO Up <|> toK DOWNTO Down

lval :: Monad m => ParserT m [Plvalue Position]
lval = (tuple1 plvalue)

pinstr :: Monad m => ParserT m (Pinstr Position)
pinstr = liftM (\(Loc l b) -> Pinstr l b) (locp pinstr_r) <?> "pinstr"
       
pblock_r :: Monad m => ParserT m (Pblock_r Position)
pblock_r = braces (many pinstr) <?> "pblock_r"

pblock :: Monad m => ParserT m (Pblock Position)
pblock = liftM (\(Loc l b) -> Pblock l b) (locp pblock_r) <?> "pblock"

-- (* ** Function definitions
--  * -------------------------------------------------------------------- *)

stor_type :: Monad m => ParserT m (Pstotype Position)
stor_type = storage >*< ptype_ <?> "stor_type"

storage :: Monad m => ParserT m Pstorage
storage = toK REG Reg
      <|> toK STACK Stack
      <|> toK INLINE Inline
      <?> "storage"
 
pvardecl :: Monad m => ParserT m (Pstotype Position,Pident Position)
pvardecl = stor_type >*< var <?> "pvardecl"

pfunbody :: Monad m => ParserT m (Pfunbody Position)
pfunbody = apA5
    (tok LBRACE)
    (many $ postfix pvardecl (tok SEMICOLON))
    (many pinstr)
    (optionMaybe $ tok RETURN *> tuple var <* tok SEMICOLON)
    (tok RBRACE)
    (\_ vs is rt _ -> Pfunbody vs is rt)
    <?> "pfunbody"

pfundef :: Monad m => ParserT m (Pfundef Position)
pfundef = apA6
    (optionMaybe pcall_conv)
    (locp $ tok FN)
    ident
    (parens_tuple (stor_type >*< optionMaybe var))
    (optionMaybe $ prefix (tok RARROW) (tuple stor_type))
    pfunbody
    (\cc (Loc p _) name args rty body -> Pfundef cc name args rty body p)
    <?> "pfundef"

pcall_conv :: Monad m => ParserT m Pcall_conv
pcall_conv = toK EXPORT CCExport <|> toK INLINE CCInline

-- (* -------------------------------------------------------------------- *)

pparam :: Monad m => ParserT m (Pparam Position)
pparam = apA6
    (tok PARAM)
    ptype_
    ident
    (tok EQ_)
    pexpr
    (tok SEMICOLON)
    (\_ ty xs _ pe _ -> Pparam ty xs pe)
    <?> "pparam"

-- (* -------------------------------------------------------------------- *)

top :: Monad m => ParserT m (Pitem Position)
top = apA pfundef PFundef
  <|> apA pparam PParam 
  <?> "top"

-- (* -------------------------------------------------------------------- *)
module_ :: Monad m => ParserT m (Pprogram Position)
module_ = (many top) <* tok TokenEOF <?> "module_"

-- (* -------------------------------------------------------------------- *)

plist1 x s = sepBy1 x (tok s)

prefix s x = s *> x
postfix x s = x <* s

delimited x m y = x *> m <* y

parens :: Monad m => ParserT m a -> ParserT m a
parens x = delimited (tok LPAREN) x (tok RPAREN)

brackets :: Monad m => ParserT m a -> ParserT m a
brackets x = delimited (tok LBRACK) x (tok RBRACK)

braces :: Monad m => ParserT m a -> ParserT m a
braces x = delimited (tok LBRACE) x (tok RBRACE)

angles :: Monad m => ParserT m a -> ParserT m a
angles x = delimited (tok LT_) x (tok GT_)

rtuple :: Monad m => ParserT m a -> ParserT m [a]
rtuple x = sepBy x (tok COMMA)

rtuple1 :: Monad m => ParserT m a -> ParserT m [a]
rtuple1 x = sepBy1 x (tok COMMA)

tuple :: Monad m => ParserT m a -> ParserT m [a]
tuple x = parens (rtuple x) <|> rtuple x

tuple1 :: Monad m => ParserT m a -> ParserT m [a]
tuple1 x = parens (rtuple1 x) <|> rtuple1 x

parens_tuple :: Monad m => ParserT m a -> ParserT m [a]
parens_tuple x = parens (rtuple x)

angles_tuple :: Monad m => ParserT m a -> ParserT m [a]
angles_tuple x = angles (rtuple x)
 
brackets_tuple :: Monad m => ParserT m a -> ParserT m [a]
brackets_tuple x = brackets (rtuple x)

-- * Tokens

tok :: (Monad m) => Token -> ParserT m TokenInfo
tok t = tokPred ((==t) . tSymb)

tokPred :: (Monad m) => (TokenInfo -> Bool) -> ParserT m TokenInfo
tokPred p = tokWith (\x -> if p x then Just x else Nothing)

tokWith :: (Monad m) => (TokenInfo -> Maybe a) -> ParserT m a
tokWith f = tokenPrim PP.pprid next f
    where
    next p t (s:ss) = positionToSourcePos $ tLoc s
    next p t ts = updatePosString (positionToSourcePos $ tLoc t) (PP.pprid t)

toK :: Monad m => Token -> a -> ParserT m a
toK t x = apA (tok t) (const x)

parseJasminFile :: Options -> FilePath -> IO (Either ParserException (Pprogram Position))
parseJasminFile opts file = do
    str <- readFile file
    parseJasminWith opts file str (startPos file) module_

parseJasminWith :: (MonadIO m,PP m a) => Options -> String -> String -> Position -> ParserT m a -> m (Either ParserException a)
parseJasminWith opts fn str pos parser = do
    case runLexerWith fn str (positionToAlexPos pos) return of
        Left err -> return $ Left $ LexicalException err
        Right toks -> do
            when (debugLexer opts) $ liftIO $ hPutStrLn stderr ("Lexed " ++ fn ++ ":") >> hPutStrLn stderr (show $ map tSymb toks)
            e <- runParserT (setPosition (positionToSourcePos pos) >> parser) () fn toks
            case e of
                Left err -> return $ Left $ ParserException $ show err
                Right a -> do
                    when (debugParser opts) $ do
                        ppa <- PP.ppr a
                        liftIO $ hPutStrLn stderr ("Parsed " ++ fn ++ ":") >> hPutStrLn stderr (ppa)
                    return $ Right a

locp :: Monad m => ParsecT tok st m a -> ParsecT tok st m (Loc Position a)
locp m = do
    sp <- getPosition
    x <- m
    return $ Loc (sourcePosToPosition sp) x
    
