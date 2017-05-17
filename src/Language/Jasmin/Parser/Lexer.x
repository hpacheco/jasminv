{

{-# LANGUAGE MultiParamTypeClasses #-}

module Language.Jasmin.Parser.Lexer where

import Control.Monad.Except
import Control.Monad.State

import Language.Jasmin.Parser.Tokens
import Language.Position
import Language.Location
import Language.Jasmin.Error

import Text.PrettyPrint

}

%wrapper "monadUserState"

-- Character classes

$blank    = [  \t\r]
@newline  = (\n\r|\r\n|\n|\r)
$digit    = [0-9]
$hexdigit = [0-9a-fA-F]
$lower    = [a-z]
$upper    = [A-Z]
$underscore = _
@letter   = ($lower|$upper)
@idletter = (@letter|$underscore)
@ident    = @idletter(@idletter|$digit)*
@identifier = @ident+

@declit   = (\-?$digit+)
@hexlit   = (0x$hexdigit+)

@utype    = u$digit+
@inttype    = int$digit+

tokens :-


<0>       "//".*                                { lineComment }
<0>       "#".*                                 ;
<0>       \/\*                                  { enterNewComment }
<comment> \/\*                                  { embedComment    }
<comment> \*\/                                  { unembedComment  }
<comment> @newline                              { bufferComment }
<comment> .                                     { bufferComment }

<0>       $white+           ;

-- Keywords:

<0>                 @utype          { lexerTokenInfoFunc ( return . T_U . getusize) }
<0>                 @inttype         { lexerTokenInfoFunc ( return . T_U . getintsize) }
<0>                 bool        { lexerTokenInfo T_BOOL }
<0>                 int         { lexerTokenInfo T_INT }
<0>                 reg         { lexerTokenInfo REG }
<0>                 stack       { lexerTokenInfo STACK }
<0>                 inline      { lexerTokenInfo INLINE }
<0>                 export      { lexerTokenInfo EXPORT }
<0>                 param       { lexerTokenInfo PARAM }
<0>                 MEM         { lexerTokenInfo MEM }
<0>                 true        { lexerTokenInfo TRUE }
<0>                 false       { lexerTokenInfo FALSE }
<0>                 for         { lexerTokenInfo FOR }
<0>                 when        { lexerTokenInfo WHEN }
<0>                 while       { lexerTokenInfo WHILE }
<0>                 do          { lexerTokenInfo DO }
<0>                 to          { lexerTokenInfo TO }
<0>                 downto      { lexerTokenInfo DOWNTO }
<0>                 if          { lexerTokenInfo IF }
<0>                 else        { lexerTokenInfo ELSE }
<0>                 fn          { lexerTokenInfo FN }
<0>                 return      { lexerTokenInfo RETURN }

<0>                 free        { lexerAnnTokenInfo FREE }
<0>                 valid       { lexerAnnTokenInfo VALID }
<0>                 security    { lexerAnnTokenInfo SECURITY }
<0>                 public      { lexerAnnTokenInfo PUBLIC }
<0>                 function    { lexerAnnTokenInfo FUNCTION }
<0>                 axiom       { lexerAnnTokenInfo AXIOM }
<0>                 lemma       { lexerAnnTokenInfo LEMMA }
<0>                 assume      { lexerAnnTokenInfo ASSUME }
<0>                 assert      { lexerAnnTokenInfo ASSERT }
<0>                 invariant      { lexerAnnTokenInfo INVARIANT }
<0>                 decreases      { lexerAnnTokenInfo DECREASES }
<0>                 requires      { lexerAnnTokenInfo REQUIRES }
<0>                 ensures      { lexerAnnTokenInfo ENSURES }
<0>                 forall      { lexerAnnTokenInfo FORALL }
<0>                 exists      { lexerAnnTokenInfo EXISTS }

-- Literals:

<0>                 @declit            { lexerTokenInfoFunc (return . INT . convert_to_base 10) }
<0>                 @hexlit            { lexerTokenInfoFunc (return . INT . convert_to_base 16) }
<0>                 "_"                 { lexerTokenInfo UNDERSCORE }
<0>                 @identifier        { lexerTokenInfoFunc (return . NID) }

-- built-in functions:

<0>                 "@"                  { lexerTokenInfo AT }
<0>                 "["                  { lexerTokenInfo LBRACK }
<0>                 "]"                 { lexerTokenInfo RBRACK }
<0>                 "{"                  { lexerTokenInfo LBRACE }
<0>                 "}"                 { lexerTokenInfo RBRACE }
<0>                 "("                  { lexerTokenInfo LPAREN }
<0>                 ")"                  { lexerTokenInfo RPAREN }
<0>                 "->"                { lexerTokenInfo RARROW }
<0>                 ":"                  { lexerTokenInfo COLON }
<0>                 "="                  { lexerTokenInfo EQ_ }
<0>                 "=="                  { lexerTokenInfo EQEQ }
<0>                 "!="                 { lexerTokenInfo BANGEQ }
<0>                 "+="                { lexerTokenInfo PLUSEQ }
<0>                 "*="                  { lexerTokenInfo STAREQ }
<0>                 "-="                 { lexerTokenInfo MINUSEQ }
<0>                 "&="                 { lexerTokenInfo AMPEQ }

<0>                 "%"                 { lexerTokenInfo MOD }
<0>                 "<="                 { lexerTokenInfo LE }
<0>                 "<"                { lexerTokenInfo LT_ }
<0>                 ">="                  { lexerTokenInfo GE }
<0>                 ">"                  { lexerTokenInfo GT_ }

<0>                 "<=s"                 { lexerTokenInfo LE_SIGNED }
<0>                 "<s"                { lexerTokenInfo LT_SIGNED }
<0>                 ">=s"                  { lexerTokenInfo GE_SIGNED }
<0>                 ">s"                  { lexerTokenInfo GT_SIGNED }

<0>                 ".."                  { lexerTokenInfo DOTDOT }
<0>                 ","                  { lexerTokenInfo COMMA }
<0>                 ">>="                  { lexerTokenInfo GTGTEQ }
<0>                 "<<="                  { lexerTokenInfo LTLTEQ }
<0>                 "^="                  { lexerTokenInfo HATEQ }
<0>                 "|="                  { lexerTokenInfo PIPEEQ }
<0>                 "-"                  { lexerTokenInfo MINUS }
<0>                 "*"                  { lexerTokenInfo STAR }
<0>                 "+"                  { lexerTokenInfo PLUS }
<0>                 "&"                  { lexerTokenInfo AMP }
<0>                 "&&"                  { lexerTokenInfo AMPAMP }
<0>                 "||"                  { lexerTokenInfo PIPEPIPE }
<0>                 ";"                  { lexerTokenInfo SEMICOLON }
<0>                 "!"                 { lexerTokenInfo BANG }
<0>                 ">>"                  { lexerTokenInfo GTGT }
<0>                 ">>s"                  { lexerTokenInfo GTGT_SIGNED }
<0>                 "<<"                  { lexerTokenInfo LTLT }
<0>                 "^"                  { lexerTokenInfo HAT }
<0>                 "|"                  { lexerTokenInfo PIPE }
<0>                 "?"                  { lexerTokenInfo QUESTION }

<0>                     @newline                { skip }
<0>                     $blank                  { skip }

<0>                     .                       { lexerTokenInfoFunc handleError     }

{

-- Token Functions -------------------------------------------------------------

getusize :: String -> Int
getusize str = read $ tail str

getintsize :: String -> Int
getintsize str = read $ drop 3 str

lexerAnnTokenInfo :: Token -> AlexInput -> Int -> Alex TokenInfo
lexerAnnTokenInfo t inp l = do
    aus <- get
    if lexAnn aus
        then lexerTokenInfo t inp l
        else lexerTokenInfoFunc (return . NID) inp l

lexerTokenInfo :: Token -> AlexInput -> Int -> Alex TokenInfo
lexerTokenInfo t (AlexPn a ln c, _, _, s) l = do
    fn <- alexFilename
    return $ TokenInfo t (take l $ s) (pos fn ln c a)

lexerTokenInfoFunc :: (String -> Alex Token) -> AlexInput -> Int -> Alex TokenInfo
lexerTokenInfoFunc f (AlexPn a ln c, _, _, s) l = do 
    r <- f (take (fromIntegral l) s)
    fn <- alexFilename
    return $ TokenInfo r (take (fromIntegral l) s) (pos fn ln c a)

handleError :: String -> Alex Token
handleError _ = return TokenError

enterNewComment :: AlexInput -> Int -> Alex TokenInfo
enterNewComment input len = do
    modify (\ aus -> aus { commentDepth = 1, commentStr = "" })
    alexSetStartCode comment
    skip input len

bufferComment :: AlexInput -> Int -> Alex TokenInfo
bufferComment input@(AlexPn a ln c, _, _, s) len = do
    modify (\ aus -> aus { commentStr = commentStr aus ++ (take len s) } )
    skip input len

embedComment :: AlexInput -> Int -> Alex TokenInfo
embedComment input len = do
    modify (\ aus -> aus { commentDepth = commentDepth aus + 1 })
    skip input len

unembedComment :: AlexInput -> Int -> Alex TokenInfo
unembedComment input len = do
    aus <- get
    let cd = commentDepth aus
    put (aus { commentDepth = cd - 1 })
    if (cd == 1)
        then do
            alexSetStartCode 0
            case isAnnotation (commentStr aus) of
                Nothing -> skip input len
                Just ann -> do
                    aus <- get
                    modify (\aus -> aus { commentStr = "" })
                    lexerTokenInfo (ANNOTATION ann) input len
        else do
            skip input len

lineComment :: AlexInput -> Int -> Alex TokenInfo
lineComment input@(AlexPn a ln c, _, _, s) len = do
    let com = drop 2 $ take len s
    case isAnnotation com of
        Nothing -> skip input len
        Just ann -> lexerTokenInfo (ANNOTATION ann) input len

-- Alex Functions --------------------------------------------------------------

data AlexUserState = AlexUserState 
    { filename     :: !String
    , commentDepth :: Integer
    , commentStr   :: String
    , lexAnn       :: Bool -- lex tokens in the annotation language or not
    }

alexFilename :: Alex String
alexFilename = liftM filename get

alexInitUserState :: AlexUserState
alexInitUserState = AlexUserState "" 0 "" False

instance MonadState AlexUserState Alex where
    get = alexGetUserState
    put = alexSetUserState

instance MonadError JasminError Alex where
    throwError e = Alex $ \ s -> Left (show e)
    catchError (Alex un) f = Alex $ \ s -> either (catchMe s) Right (un s)
        where 
        catchMe s x = fmap (split (const s) id) $ runAlex "" $ f $ GenericError (UnhelpfulPos "lexer") (text x) Nothing

{-# INLINE split #-}
split :: (a -> b) -> (a -> c) -> a -> (b, c)
split f g a = (f a, g a)

alexEOF :: Alex TokenInfo
alexEOF = do 
    (AlexPn a ln c, _, _, _) <- alexGetInput
    fn <- alexFilename
    return $ TokenInfo TokenEOF "<EOF>" (pos fn ln c a)


-- Processing Functions --------------------------------------------------------

positionToAlexPos :: Position -> AlexPosn
positionToAlexPos (Pos fn l c a) = AlexPn a l c

alexSetPos :: AlexPosn -> Alex ()
alexSetPos p = do
    (_,x,y,z) <- alexGetInput
    alexSetInput (p,x,y,z)

runLexerWith :: Bool -> String -> String -> AlexPosn -> ([TokenInfo] -> Alex a) -> Either String a
runLexerWith isAnn fn str pos parse = runAlex str $ do
    alexSetPos pos
    put (alexInitUserState { filename = fn, lexAnn = isAnn })
    toks <- getTokens
    parse toks

runLexer :: Bool -> String -> String -> Either String [TokenInfo]
runLexer isAnn fn str = runLexerWith isAnn fn str alexStartPos return

injectResult :: Either String a -> Alex a
injectResult (Left err) = throwError (GenericError (UnhelpfulPos "inject") (text err) Nothing)
injectResult (Right a) = return a

-- | Alex lexer
lexer :: (TokenInfo -> Alex a) -> Alex a
lexer cont = alexMonadScan >>= cont

getTokens :: Alex [TokenInfo]
getTokens = do 
    tok <- alexMonadScan
    case tSymb tok of
        TokenEOF -> return [tok]
        _ -> liftM (tok:) getTokens

flushLexer :: Alex ()
flushLexer = return ()


}