{-# LANGUAGE FlexibleContexts #-}

module Language.Jasmin.IO where

import System.Console.CmdArgs
import System.Environment
import System.FilePath
import System.IO
import System.Posix.Escape
import System.Process
import System.Exit

import qualified Data.List as List
import Data.List.Split
import Data.Either
import Data.Version (showVersion)
import Data.Maybe
import qualified Data.Text as Text

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Writer (WriterT(..))
import qualified Control.Monad.Writer as Writer
import Control.Monad.Except

import Language.Jasmin.Error
import Text.PrettyPrint.Exts
import Language.Position
import Language.Location

import Text.PrettyPrint hiding (mode,Mode(..))
import qualified Text.PrettyPrint as PP
import Text.Read hiding (lift)
import qualified Data.Text.IO as Text

import qualified Shelly as Shelly
import Utils

type StatusM m = WriterT Doc (ExceptT JasminError m)

type Status = Either JasminError Doc

statusM_ :: Monad m => m Status -> StatusM m ()
statusM_ m = do
    x <- lift2 m
    case x of
        Left err -> throwError err
        Right d -> Writer.tell d

runStatusM_ :: Monad m => StatusM m () -> m Status
runStatusM_ m = do
    x <- runExceptT $ Writer.execWriterT m
    case x of
        Left err -> return $ Left err
        Right (d) -> return $ Right d

printStatusM_ :: (MonadIO m) => StatusM m () -> m ()
printStatusM_ m = do
    st <- runStatusM_ m
    printStatus st

printStatus :: (MonadIO m) => Status -> m ()
printStatus (Right d) = liftIO $ putStrLn $ show d
printStatus (Left err) = error $ show $ pprid err

command :: (MonadIO m) => Bool -> String -> StatusM m ()
command doDebug cmd = do
    when doDebug $ liftIO $ hPutStrLn stderr $ "Running command " ++ show cmd
    exit <- liftIO $ system cmd
    case exit of
        ExitSuccess -> return ()
        ExitFailure err -> throwError $ GenericError noloc (int err) Nothing

commandOutput :: (MonadIO m) => Bool -> String -> StatusM m ()
commandOutput doDebug str = do
    when doDebug $ liftIO $ hPutStrLn stderr $ "Running command " ++ show str
    let process = (shell str) { std_out = CreatePipe }
    (_,Just hout,_,ph) <- liftIO $ createProcess process
    exit <- liftIO $ waitForProcess ph
    result <- liftIO $ hGetContents hout
    case exit of
        ExitSuccess -> Writer.tell $ text result
        ExitFailure code -> throwError $ GenericError noloc (text "Error running command:" <+> int code $+$ text result) Nothing

shellyOutput :: (MonadIO m) => Bool -> Bool -> String -> [String] -> StatusM m ()
shellyOutput doDebug doSilent name args = do
    let silence = if doSilent then Shelly.silently else id
    when doDebug $ liftIO $ hPutStrLn stderr $ "Running command " ++ show (name ++ " " ++ unwords args)
    statusM_ $ Shelly.shelly $ do
        result <- Shelly.errExit False $ silence $ Shelly.run (Shelly.fromText $ Text.pack name) (map Text.pack args)
        let uresult = Text.unpack result
        exit <- Shelly.lastExitCode
        case exit of
            0 -> return $ Right $ text uresult
            code -> return $ Left $ GenericError noloc (text "Error running command:" <+> int code $+$ text uresult) Nothing

