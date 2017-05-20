{-# LANGUAGE TypeFamilies, RankNTypes, ViewPatterns #-}

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
import Safe
import Data.Maybe

import Control.Monad.IO.Class
import Control.Monad
import Control.Monad.Except

type ParserState = (Bool {- inside annotations -},Options)

type ParserT m a = ParsecT [TokenInfo] ParserState m a

ident :: Monad m => ParserT m (Pident Position)
ident = liftM (\(Loc l x) -> Pident l x) (locp $ tokWith getNID) <?> "ident"
    where
    getNID t@(tSymb -> NID x) = Just x
    getNID _ = Nothing

var :: Monad m => ParserT m (Pident Position)
var = ident <?> "var"

-- (* ** Type expressions
--  * -------------------------------------------------------------------- *)
 
utype :: Monad m => ParserT m (Ptype Position)
utype = tokWith getInt <?> "utype"
 where
 getInt t@(tSymb -> T_U i) = Just $ TWord i
 getInt t = Nothing

itype :: Monad m => ParserT m (Ptype Position)
itype = tokWith getInt <?> "inttype"
 where
 getInt t@(tSymb -> T_I i) = Just $ TInt $ Just i
 getInt t = Nothing

ptype_ :: MonadIO m => ParserT m (Ptype Position)
ptype_ = toK T_BOOL TBool
     <|> toK T_INT (TInt Nothing)
     <|> ann itype
     <|> apA2 utype (optionMaybe $ brackets pexpr) (\(TWord w) mbd -> case mbd of { Nothing -> TWord w; Just d -> TArray w d })
     <?> "ptype_"

-- (* ** Index expressions
--  * -------------------------------------------------------------------- *)

peop1 :: Monad m => ParserT m Peop1
peop1 = toK BANG Not1 <?> "peop1"

peop2 :: Monad m => Token -> ParserT m Peop2
peop2 PLUS          = toK PLUS Add2
peop2 IMPLIES          = ann $ toK IMPLIES Implies2
peop2 EQUIV          = ann $ toK EQUIV Equiv2
peop2 MINUS         = toK MINUS Sub2
peop2 AMPAMP        = toK AMPAMP   And2  
peop2 PIPEPIPE      = toK PIPEPIPE Or2   
peop2 AMP           = toK AMP      BAnd2 
peop2 PIPE          = toK PIPE     BOr2  
peop2 HAT           = toK HAT      BXor2 
peop2 LTLT          = toK LTLT     Shl2  
peop2 GTGT          = toK GTGT     (Shr2 Unsigned)
peop2 GTGT_SIGNED   = toK GTGT_SIGNED     (Shr2 Signed)
peop2 EQEQ          = (toK EQEQ Eq2)
peop2 BANGEQ        = (toK BANGEQ Neq2)
peop2 LT_           = (toK LT_ $ Lt2 Unsigned)
peop2 LE            = (toK LE $ Le2 Unsigned)
peop2 GT_           = (toK GT_ $ Gt2 Unsigned)
peop2 GE            = (toK GE $ Ge2 Unsigned)
peop2 LT_SIGNED     = (toK LT_SIGNED $ Lt2 Signed)
peop2 LE_SIGNED     = (toK LE_SIGNED $ Le2 Signed)
peop2 GT_SIGNED     = (toK GT_SIGNED $ Gt2 Signed)
peop2 GE_SIGNED     = (toK GE_SIGNED $ Ge2 Signed)
peop2 STAR          = (toK STAR Mul2)
peop2 MOD          = (toK MOD Mod2)

pexpr :: MonadIO m => ParserT m (Pexpr Position)
pexpr = mkPexprs2 atom_expr precedences
    where
    precedences =
        [(False,[IMPLIES,EQUIV])
        ,(False,[PIPEPIPE])
        ,(False,[AMPAMP])
        ,(False,[PIPE])
        ,(False,[HAT])
        ,(False,[AMP])
        ,(False,[EQEQ,BANGEQ])
        ,(False,[LE,LE_SIGNED,GE,GE_SIGNED,LT_,LT_SIGNED,GT_,GT_SIGNED])
        ,(False,[LTLT,GTGT,GTGT_SIGNED])
        ,(False,[PLUS,MINUS])
        ,(False,[STAR,MOD])
        ]

mkPexprs2 :: Monad m => ParserT m (Pexpr Position) -> [(Bool,[Token])] -> ParserT m (Pexpr Position)
mkPexprs2 atom [(x,y)] = mkPexpr2 atom x y
mkPexprs2 atom ((x,y):xs) = mkPexpr2 (mkPexprs2 atom xs) x y

mkPexpr2 :: Monad m => ParserT m (Pexpr Position) -> Bool -> [Token] -> ParserT m (Pexpr Position)
mkPexpr2 atom side os = atom `chain` (tries os)
    where
    chain = if side then chainr1 else chainl1
    tries [x] = try (mkOp2 x)
    tries (x:xs) = try (mkOp2 x) <|> tries xs
    mkOp2 tk = locp (peop2 tk) >>= \(Loc p o) -> return $ \e1 e2 -> Pexpr p $ PEOp2 o e1 e2

atom_expr :: MonadIO m => ParserT m (Pexpr Position)
atom_expr = (liftM (\(Loc l x) -> Pexpr l x) $ locp atom_expr_r) <?> "non2expr"

atom_expr_r :: MonadIO m => ParserT m (Pexpr_r Position)
atom_expr_r =
           apA2 (parens ptype_) atom_expr (\t e -> Pcast t e)
      <||> apA2 ident (parens_tuple pexpr) (\fname args -> PECall fname args)
      <||> apA2 var (optionMaybe $ brackets pexpr) (\v mbi -> case mbi of { Nothing -> PEVar v; Just i -> PEGet v i })
      <|> toK TRUE (PEBool True)
      <|> toK FALSE (PEBool False)
      <|> ann (apA2 (tok PUBLIC) (parens pexpr) (\x1 x2 -> LeakExpr x2))
      <|> ann (apA2 (tok VALID) (parens_tuple pexpr) (\x1 x2 -> ValidExpr x2))
      <|> quantifiedExpr
      <|> tokWith getInt
      <|> apA2 peop1 atom_expr (\o e -> PEOp1 o e)
      <|> apA (parens_tuple pexpr) (\e -> PEParens e)
      <||> apA6 (optionMaybe $ parens ptype_) (tok LBRACK) var (tok PLUS) pexpr (tok RBRACK) (\ct _ v _ e _ -> PEFetch ct v e)
      
      <?> "non2expr_r"
  where
  getInt t@(tSymb -> INT i) = Just $ PEInt i
  getInt t = Nothing

quantifiedExpr :: MonadIO m => ParserT m (Pexpr_r Position)
quantifiedExpr = ann $ apA4 quantifier (sepBy1 annargNoExpr (tok COMMA)) (tok SEMICOLON) pexpr (\x1 x2 x3 x4 -> QuantifiedExpr x1 x2 x4)

quantifier :: Monad m => ParserT m Quantifier
quantifier = toK FORALL ForallQ <|> toK EXISTS ExistsQ

-- (* -------------------------------------------------------------------- *)
peqop :: Monad m => ParserT m Peqop
peqop = toK EQ_ RawEq
    <|> toK PLUSEQ  AddEq
    <|> toK MINUSEQ SubEq
    <|> toK STAREQ  MulEq
    <|> toK GTGTEQ_SIGNED  (ShREq Signed)
    <|> toK GTGTEQ  (ShREq Unsigned)
    <|> toK LTLTEQ  ShLEq
    <|> toK AMPEQ   BAndEq
    <|> toK HATEQ   BXOrEq
    <|> toK PIPEEQ  BOrEq
    <?> "peqop"
 
-- (* ** Left value
--  * -------------------------------------------------------------------- *)
-- (* FIXME: missing syntax for Lmem *)

plvalue_r :: MonadIO m => ParserT m (Plvalue_r Position)
plvalue_r = toK UNDERSCORE PLIgnore
        <|> apA2 var (optionMaybe $ brackets pexpr) (\x mbi -> case mbi of { Nothing -> PLVar x; Just i -> PLArray x i })
        <|> apA (parens (plist1 plvalue COMMA)) (\es -> PLParens es)
        <||> apA6 (optionMaybe (parens ptype_)) (tok LBRACK) var (tok PLUS) pexpr (tok RBRACK) (\ct _ v _ e _ -> PLMem ct v e)
        <?> "plvalue_r"

plvalue :: MonadIO m => ParserT m (Plvalue Position)
plvalue = (liftM (\(Loc l x) -> Plvalue l x) $ locp plvalue_r) <?> "plvalue"

-- (* ** Control instructions
--  * -------------------------------------------------------------------- *)

pinstr_r :: MonadIO m => ParserT m (Pinstr_r Position)
pinstr_r = apA5 lval (peqop) pexpr (optionMaybe $ prefix (tok IF) pexpr) (tok SEMICOLON) (\x o e c _ -> PIAssign x o e c)
       <||> apA4 (locp ident) (parens_tuple pexpr) (optionMaybe $ prefix (tok IF) pexpr) (tok SEMICOLON) (\(Loc p n) args c _ -> PIAssign [] RawEq (Pexpr p $ PECall n args) c)
       <|> apA4 (tok IF) pexpr pblock (optionMaybe $ tok ELSE *> pblock) (\_ c i1s i2s -> PIIf False c i1s i2s)
       <|> apA8 (tok FOR) var (tok EQ_) pexpr fordir pexpr loopAnnotations pblock (\_ v _ ce1 dir ce2 anns is -> PIFor v dir ce1 ce2 anns is)
       <|> apA4 (tok WHILE) loopAnnotations pblock pexpr (\_ anns is1 b -> PIWhile (Just is1) b anns Nothing )
       <||> apA4 (tok WHILE) pexpr loopAnnotations pblock (\_ b anns is2 -> PIWhile Nothing b anns (Just is2) )
       <?> "pinstr_r"

fordir :: Monad m => ParserT m Fordir
fordir = toK TO Up <|> toK DOWNTO Down

lval :: MonadIO m => ParserT m [Plvalue Position]
lval = (rtuple1 plvalue)

pinstr :: MonadIO m => ParserT m (Pinstr Position)
pinstr = (liftM (\(Loc l x) -> Pinstr l x) $ locp pinstr_r) <?> "pinstr"
       
pblock_r :: MonadIO m => ParserT m (Pblock_r Position)
pblock_r = braces pinstrs <?> "pblock_r"

pinstrs :: MonadIO m => ParserT m [Pinstr Position]
pinstrs = liftM concat $ many' (apA statementAnnotations (map (\(StatementAnnotation l x) -> Pinstr l $ Anninstr x)) <||> liftM (:[]) pinstr)

pblock :: MonadIO m => ParserT m (Pblock Position)
pblock = (liftM (\(Loc l x) -> Pblock l x) $ locp pblock_r) <?> "pblock"

-- (* ** Function definitions
--  * -------------------------------------------------------------------- *)

stor_type :: MonadIO m => ParserT m (Pstotype Position)
stor_type = storage >*< ptype_ <?> "stor_type"

storage :: Monad m => ParserT m Pstorage
storage = toK REG Reg
      <|> toK STACK Stack
      <|> toK INLINE Inline
      <?> "storage"
 
pbodyarg :: MonadIO m => ParserT m (Pbodyarg Position)
pbodyarg = apA3 stor_type var (tok SEMICOLON) (\ty n _ -> Pbodyarg ty n) <?> "pvardecl"

pfunbody :: MonadIO m => ParserT m (Pfunbody Position)
pfunbody = apA5
    (tok LBRACE)
    (many pbodyarg)
    (pinstrs)
    (optionMaybe $ tok RETURN *> tuple var <* tok SEMICOLON)
    (tok RBRACE)
    (\_ vs is rt _ -> Pfunbody vs is rt)
    <?> "pfunbody"

parg :: MonadIO m => ParserT m (Parg Position)
parg = apA2 (stor_type) (optionMaybe var) (\ty n -> Parg ty n)

annargExpr :: MonadIO m => ParserT m (Annarg Position)
annargExpr = apA3 ptype_ var (optionMaybe $ tok EQ_ *> pexpr) (\ty n e -> Annarg ty n e)

annargNoExpr :: MonadIO m => ParserT m (Annarg Position)
annargNoExpr = apA2 ptype_ var (\ty n -> Annarg ty n Nothing)

pannaxiomdef :: MonadIO m => ParserT m (AnnAxiomDeclaration Position)
pannaxiomdef = apA4
    (locp leak)
    (tok AXIOM)
    (parens_tuple annargNoExpr)
    procedureAnnotations
    (\(Loc p isLeak) _ args anns -> AnnAxiomDeclaration isLeak args anns p)

pannlemmadef :: MonadIO m => ParserT m (AnnLemmaDeclaration Position)
pannlemmadef = apA6
    (locp leak)
    (tok LEMMA)
    ident
    (parens_tuple annargNoExpr)
    procedureAnnotations
    (optionMaybe pblock)
    (\(Loc p isLeak) _ name args anns body -> AnnLemmaDeclaration isLeak name args anns body p)

pannfundef :: MonadIO m => ParserT m (AnnFunDeclaration Position)
pannfundef = apA8
    (locp leak)
    (tok FUNCTION)
    ident
    (parens_tuple annargNoExpr)
    (tok RARROW)
    ptype_
    procedureAnnotations
    pexpr
    (\(Loc p isLeak) _ name args _ rty anns body -> AnnFunDeclaration isLeak rty name args anns body p)

pfundef :: MonadIO m => ParserT m (Pfundef Position)
pfundef = apA7
    (optionMaybe pcall_conv)
    (locp $ tok FN)
    ident
    (parens_tuple parg)
    (optionMaybe $ prefix (tok RARROW) (tuple stor_type))
    procedureAnnotations
    pfunbody
    (\cc (Loc p _) name args rty anns body -> Pfundef cc name args rty anns body p)
    <?> "pfundef"

pcall_conv :: Monad m => ParserT m Pcall_conv
pcall_conv = toK EXPORT CCExport <|> toK INLINE CCInline

-- (* -------------------------------------------------------------------- *)

pparam :: MonadIO m => ParserT m (Pparam Position)
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

top :: MonadIO m => ParserT m (Pitem Position)
top = apA pfundef PFundef
  <|> apA pparam PParam 
  <?> "top"
 
anntop :: MonadIO m => ParserT m (Pitem Position)
anntop = apA pannaxiomdef PAxiomdef
  <||> apA pannlemmadef PLemmadef
  <||> apA pannfundef PAnnfunctiondef
  <?> "ann top"

anntops :: MonadIO m => ParserT m [Pitem Position]
anntops = annotations1 $ many1' anntop

alltops :: MonadIO m => ParserT m [Pitem Position]
alltops = liftM concat $ many (anntops <||> apA top (:[]))

-- (* -------------------------------------------------------------------- *)
module_ :: MonadIO m => ParserT m (Pprogram Position)
module_ = (liftM Pprogram) (alltops <* tok TokenEOF) <?> "module_"

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
    parseJasminWith opts file str False (startPos file) module_

parseJasminWith :: (MonadIO m,PP m a) => Options -> String -> String -> Bool -> Position -> ParserT m a -> m (Either ParserException a)
parseJasminWith opts fn str insideAnn pos parser = do
    case runLexerWith insideAnn fn str (positionToAlexPos pos) return of
        Left err -> return $ Left $ LexicalException err
        Right toks -> do
            when (debugLexer opts) $ liftIO $ hPutStrLn stderr ("Lexed " ++ fn ++ ":") >> hPutStrLn stderr (show $ map tSymb toks)
            e <- runParserT (setPosition (positionToSourcePos pos) >> parser) (insideAnn,opts) fn toks
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

free :: Monad m => ParserT m Bool
free = liftM isJust $ optionMaybe (tok FREE)

leak :: Monad m => ParserT m Bool
leak = liftM isJust $ optionMaybe (tok SECURITY)

leak' :: Monad m => (Bool -> ParserT m a) -> ParserT m a
leak' f = maybeCont (tok SECURITY) (f . isJust)

statementAnnotations :: (MonadIO m) => ParserT m [StatementAnnotation Position]
statementAnnotations = annotations1 $ many1' (liftM (\(Loc l x) -> StatementAnnotation l x) $ locp statementAnnotation_r)

statementAnnotation_r :: (MonadIO m) => ParserT m (StatementAnnotation_r Position)
statementAnnotation_r = vardef <||> (do
    isLeak <- leak
    (o1 isLeak <|> o2 isLeak <||> o3 isLeak))
  where
    vardef = apA2 annargExpr (tok SEMICOLON) (\ann _ -> VarDefAnn ann)
    o1 isLeak = apA3 (tok ASSUME) pexpr (tok SEMICOLON) (\x1 x2 x3 -> AssumeAnn isLeak x2)
    o2 isLeak = apA3 (tok ASSERT) pexpr (tok SEMICOLON) (\x1 x2 x3 -> AssertAnn isLeak x2)
    o3 isLeak = apA pinstr (\x1 -> EmbedAnn isLeak x1)

procedureAnnotations :: (MonadIO m) => ParserT m [ProcedureAnnotation Position]
procedureAnnotations = annotations0 $ many' (liftM (\(Loc l x) -> ProcedureAnnotation l x) $ locp procedureAnnotation_r)

procedureAnnotation_r :: (MonadIO m) => ParserT m (ProcedureAnnotation_r Position)
procedureAnnotation_r = apA3 (tok DECREASES) pexpr (tok SEMICOLON) (\x1 x2 x3 -> PDecreasesAnn x2)
                   <|> try ((free >*< leak) >>= \(isFree,isLeak) -> requires isFree isLeak <|> ensures isFree isLeak)
  where
    requires isFree isLeak = apA3 (tok REQUIRES) pexpr (tok SEMICOLON) (\x1 x2 x3 -> RequiresAnn isFree isLeak x2)
    ensures isFree isLeak = apA3 (tok ENSURES) pexpr (tok SEMICOLON) (\x1 x2 x3 -> EnsuresAnn isFree isLeak x2)

loopAnnotations :: (MonadIO m) => ParserT m [LoopAnnotation Position]
loopAnnotations = annotations0 $ many' (liftM (\(Loc l x) -> LoopAnnotation l x) $ locp loopAnnotation_r)

loopAnnotation_r :: (MonadIO m) => ParserT m (LoopAnnotation_r Position)
loopAnnotation_r = do
    isFree <- free
    (o1 isFree <|> o2 isFree)
  where
    o1 isFree = apA3 (tok DECREASES) pexpr (tok SEMICOLON) (\x1 x2 x3 -> LDecreasesAnn isFree x2)
    o2 isFree = apA4 leak (tok INVARIANT) pexpr (tok SEMICOLON) (\x00 x1 x2 x3 -> LInvariantAnn isFree x00 x2)

annotation :: (PP m a,Monoid a,MonadIO m) => ParserT m a -> ParserT m a
annotation = annotations' (liftM (:[]))

annotations0 :: (PP m a,Monoid a,MonadIO m) => ParserT m a -> ParserT m a
annotations0 = annotations' (many')

annotations1 :: (PP m a,Monoid a,MonadIO m) => ParserT m a -> ParserT m a
annotations1 = annotations' (many1')

parseLoc :: (Monad m,LocOf a ~ Position,Located a) => Maybe a -> ParserT m Position
parseLoc (Just x) = return $ loc x
parseLoc Nothing = liftM sourcePosToPosition getPosition


annotations' :: (PP m a,Monoid a,MonadIO m) => (forall b . ParserT m b -> ParserT m [b]) -> ParserT m a -> ParserT m a
annotations' parseAnns parse = do
    (insideAnn,opts) <- getState
    if insideAnn
        then parse
        else do
            toks <- parseAnns (tokWith getAnn)
            let anns = unlines $ concat $ map ((\(ANNOTATION x) -> x) . tSymb) toks
            p <- parseLoc $ headMay toks
            --liftIO $ putStrLn $ "parsing annotations starting at" ++ ppr p
            e <- lift $ parseJasminWith opts (posFileName p) anns True p (parse <* tok TokenEOF)
            case e of
                Left err -> warn p err >> return mempty
                Right x -> return x            
  where
    getAnn tok@(tSymb -> ANNOTATION a) = Just tok
    getAnn tok = Nothing

ann :: (Monad m) => ParserT m a -> ParserT m a
ann m = do
    (insideAnn,_) <- getState
    if insideAnn then m else parserZero
