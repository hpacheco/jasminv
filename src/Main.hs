{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module Main where

import System.Console.CmdArgs
import System.Environment
import System.IO
import System.FilePath

import Options
import Text.PrettyPrint.Exts (Doc,PP(..),pprid,text,(<+>),(<>),($+$))
import qualified Text.PrettyPrint.Exts as PP

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Writer (WriterT(..))
import qualified Control.Monad.Writer as Writer
import Control.Monad.Except
import Control.DeepSeq

import Language.Jasmin.Parser.Parser
import Language.Jasmin.Syntax
import Language.Jasmin.Transformation.Dafny
import Language.Jasmin.Transformation.Simplify
import Language.Jasmin.Transformation.SBV
import Language.Jasmin.TypeChecker
import Language.Jasmin.Error
import Language.Jasmin.IO
import Language.Location
import Language.Position
import Language.Vars
import Paths_jasminv
import Data.Version (showVersion)
import Data.List as List
import qualified Data.SBV as SBV
import qualified Text.Parsec as Parsec
import qualified Text.ParserCombinators.Parsec.Number as Parsec

import System.Posix.Escape
import Utils
import System.TimeIt

-- * main function

main :: IO ()
main = do
    opts <- getOpts
    case opts of
        Opts  {} -> jasmin opts

jasmin :: Options -> IO ()
jasmin opts = do
    let ins = inputs opts
    forM_ ins $ \fn -> printStatusM_ $ do
        ast <- parseJasmin opts fn
        ast' <- typecheckJasmin opts ast
        ast'' <- simplifyJasmin opts ast'
        case verify opts of
            Just SmtV -> verifySBV opts ast''
            otherwise -> verifyDafny opts ast''

parseJasmin :: MonadIO m => Options -> FilePath -> StatusM m (Pprogram Position)
parseJasmin opts fn = do
    e <- liftIO $ parseJasminFile opts fn
    case e of
        Left err -> throwError $ ParserError err
        Right ast -> return ast

typecheckJasmin :: MonadIO m => Options -> Pprogram Position -> StatusM m (Pprogram TyInfo)
typecheckJasmin opts prog = do
    e <- lift2 $ runTcM $ tt_program prog
    case e of
        Left err -> throwError err
        Right tprog -> do
            when (debugTypechecker opts) $ liftIO $ hPutStrLn stderr $ show $ text "Typechecked:" $+$ text (pprid tprog)
            return tprog

simplifyJasmin :: (GenVar Piden m,MonadIO m) => Options -> Pprogram TyInfo -> StatusM m (Pprogram TyInfo)
simplifyJasmin opts prog = do
    e <- lift2 $ runSimplifyM $ simplifyPprogram prog
    case e of
        Left err -> throwError err
        Right tprog -> do
            return tprog

verifySBV :: (GenVar Piden m,MonadIO m) => Options -> Pprogram TyInfo -> StatusM m ()
verifySBV opts prog = do
    res <- liftIO $ pprogramToSBV opts prog
    let (oks,kos) = partition isOkThmResult res
    let msg = text "Verified" <+> PP.int (length oks) <+> text "SMT properties with" <+> PP.int (length kos) <+> text "errors."
    Writer.tell msg

dafnyPreludeFiles :: IO (FilePath,FilePath)
dafnyPreludeFiles = do
    func <- getDataFileName ("imports" </> "prelude.dfy")
    leak <- getDataFileName ("imports" </> "prelude_leak.dfy")
    return (func,leak)

genDafny :: (GenVar Piden m,MonadIO m) => Options -> FilePath -> FilePath -> Bool -> Pprogram TyInfo -> StatusM m Doc
genDafny opts prelude prelude_leak isLeak prog = do
    e <- lift2 $ toDafny prelude prelude_leak isLeak prog
    case e of
        Left err -> throwError err
        Right dfy -> return dfy

verifyDafny :: Options -> Pprogram TyInfo -> StatusM IO ()
verifyDafny opts prog = do
    let fn = dropExtension $ posFileName $ infoLoc $ loc prog
    when (verify' opts /= NoneV) $ do
        let dfyfile = fn ++ ".dfy"
        let dfylfile = fn ++ "_leak.dfy"
        let bplfile = fn ++ ".bpl"
        let bplfile2 = fn ++ "_axiom.bpl"
        let bpllfile = fn ++ "_leak.bpl"
        let bpllfile2 = fn ++ "_leak_product.bpl"
        
        -- generate dafny files
        (prelude,prelude_leak) <- liftIO dafnyPreludeFiles
        when (isFuncV $ verify' opts) $ do
            when (debugVerification opts) $ liftIO $ hPutStrLn stderr $ show $ text "Generating Dafny output file" <+> text (show dfyfile)
            dfy <- genDafny opts prelude prelude_leak False prog
            liftIO $ writeFile dfyfile (show dfy)
        when (isLeakV $ verify' opts) $ do
            when (debugVerification opts) $ liftIO $ hPutStrLn stderr $ show $ text "Generating Dafny output leakage file" <+> text (show dfylfile)
            dfyl <- genDafny opts prelude prelude_leak True prog
            liftIO $ writeFile dfylfile (show dfyl)
        
        liftIO $ hSetBuffering stdout LineBuffering
        liftIO $ hSetBuffering stderr LineBuffering
        
        -- verify functional specification
        let func = do
                compileDafny False (debugVerification opts) dfyfile bplfile
                axiomatizeBoogaman (debugVerification opts) opts [] bplfile bplfile2
                runBoogie (verificationTimeOut opts) False (debugVerification opts) bplfile2
        
        -- verify leakage specification
        let spec = do
            compileDafny True (debugVerification opts) dfylfile bpllfile
            shadowBoogaman (debugVerification opts) opts [] bpllfile bpllfile2
            runBoogie (verificationTimeOut opts) True (debugVerification opts) bpllfile2

        case verify' opts of
            FuncV -> func
            LeakV -> spec
            BothV -> func >> spec
            NoneV -> return ()

compileDafny :: Bool -> Bool -> FilePath -> FilePath -> StatusM IO ()
compileDafny isLeak isDebug dfy bpl = do
    when isDebug $ liftIO $ hPutStrLn stderr $ show $ text "Compiling Dafny file" <+> text (show dfy)
    (time,res) <- lift2 $ timeItT $ runStatusM_ $ shellyOutput isDebug True "dafny" ["/compile:0",dfy,"/print:"++bpl,"/noVerify"]
    verifOutput time isLeak True res

runBoogie :: Int -> Bool -> Bool -> FilePath -> StatusM IO ()
runBoogie timeout isLeak isDebug bpl = do
    when isDebug $ liftIO $ hPutStrLn stderr $ show $ text "Verifying Boogie file" <+> text (show bpl)
    let dotrace = if isDebug then ["/trace"] else []
    let doTimeLimit = ["/timeLimit:"++show timeout]
    (time,res) <- lift2 $ timeItT $ runStatusM_ $ shellyOutput isDebug False "boogie" $ dotrace ++ doTimeLimit ++ ["/doModSetAnalysis",bpl]
    verifOutput time isLeak False res

verifOutput :: (MonadIO m) => Double -> Bool -> Bool -> Status -> StatusM m ()
verifOutput time isLeak isDafny st@(Left err) = verifErr isDafny st
verifOutput time isLeak isDafny st@(Right output) = do
    let ls = lines $ show output
    let w = last ls
    let errs = filter (List.isPrefixOf "Prover error:") $ init ls
    let tool = if isDafny then "Dafny" else "Boogie"
    let parser = do
        Parsec.string tool >> Parsec.space
        Parsec.string "program" >> Parsec.space
        Parsec.string "verifier" >> Parsec.space
        Parsec.string "finished" >> Parsec.space
        Parsec.string "with" >> Parsec.space
        verified <- Parsec.int
        Parsec.space
        Parsec.string "verified" >> Parsec.char ',' >> Parsec.space
        errors <- Parsec.int
        Parsec.space
        Parsec.string "errors"
        return (verified,errors)
    let e = Parsec.parse parser "output" w
    if (List.null errs)
        then case e of
            Left err -> verifErr isDafny st
            Right (oks,kos) -> do
                let c = if isLeak then "leakage" else "functional"
                let res = if isDafny then PP.empty else PP.text "Verified" <+> PP.int oks <+> PP.text c <+> PP.text "properties with" <+> PP.int kos <+> PP.text "errors in" <+> text (show time) <+> text "."
                case kos of
                    0 -> Writer.tell res
                    otherwise -> throwError $ GenericError noloc res Nothing
        else verifErr isDafny st

verifErr :: MonadIO m => Bool -> Status -> StatusM m ()
verifErr isDafny res = do
    let exec = if isDafny then "Dafny" else "Boogie"
    case res of
        Right output -> throwError $ GenericError noloc (text "Unexpected" <+> text exec <+> text "verification error: " <+> output) Nothing
        Left err -> throwError $ GenericError noloc (text "Unexpected" <+> text exec <+> text "verification error:") (Just err)

dafnyVCGen :: Options -> String
dafnyVCGen opts = "dafnynomodules"

axiomatizeBoogaman :: (MonadIO m) => Bool -> Options -> [String] -> FilePath -> FilePath -> StatusM m ()
axiomatizeBoogaman isDebug opts axioms bpl1 bpl2 = do
    when isDebug $ liftIO $ hPutStrLn stderr $ show $ text "Axiomatizing boogie file" <+> text (show bpl1) <+> text "into" <+> text (show bpl2) 
    let addaxiom x = text "--axioms=" <> text (escape x)
    command isDebug $ show $ text "cabal exec -- boogaman" <+> text bpl1
        <+> PP.text "--simplify"
        <+> PP.text ("--vcgen="++dafnyVCGen opts)
        <+> PP.sepBy (map addaxiom axioms) PP.space
        <+> PP.text ">" <+> PP.text bpl2
    
shadowBoogaman :: (MonadIO m) => Bool -> Options -> [String] -> FilePath -> FilePath -> StatusM m ()
shadowBoogaman isDebug opts axioms bpl1 bpl2 = do
    when isDebug $ liftIO $ hPutStrLn stderr $ show $ text "Shadowing boogie file" <+> text (show bpl1) <+> text "into" <+> text (show bpl2) 
    let addaxiom x = text "--axioms=" <> text (escape x)
    command isDebug $ show $ text "cabal exec -- boogaman" <+> text bpl1
        <+> PP.text "--simplify"
        <+> PP.text ("--vcgen="++dafnyVCGen opts)
--        <+> text "--filterleakage=true"
        <+> PP.text "--shadow"
        <+> PP.sepBy (map addaxiom $ axioms) PP.space
        <+> PP.text ">" <+> PP.text bpl2


