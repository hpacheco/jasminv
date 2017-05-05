{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Options where
    
import System.Console.CmdArgs
import System.Environment

import Data.Hashable
import Data.Generics hiding (Generic)
import GHC.Generics (Generic)
import Data.Binary

import Paths_jasminv
import Data.Version (showVersion)

-- * front-end options

printHelp :: IO ()
printHelp = withArgs ["--help"] $ cmdArgsRun mode >> return ()

-- | Jasmin options
data Options
    = Opts  { 
          inputs                :: [FilePath]
        , debugLexer            :: Bool
        , debugParser           :: Bool
        , debugTypechecker      :: Bool
        , debugVerification     :: Bool
        , typecheck             :: Bool
        , verify                :: VerifyOpt
        , verificationTimeOut   :: Int
        , noDafnyModules        :: Bool
        }
    deriving (Show, Data, Typeable,Generic)
instance Binary Options
instance Hashable Options

instance Monoid Options where
    mempty = Opts
        { inputs = []
        , debugLexer = False
        , debugParser = False
        , debugTypechecker = False
        , debugVerification = False
        , typecheck = True
        , verify = mempty
        , verificationTimeOut = 60
        , noDafnyModules = False
        }
    mappend x y = Opts
        { inputs = inputs x ++ inputs y
        , debugLexer = debugLexer x || debugLexer y
        , debugParser = debugParser x || debugParser y
        , debugTypechecker = debugTypechecker x || debugTypechecker y
        , debugVerification = debugVerification x || debugVerification y
        , typecheck = typecheck x && typecheck y
        , verify = verify x `mappend` verify y
        , verificationTimeOut = max (verificationTimeOut x) (verificationTimeOut y)
        , noDafnyModules = noDafnyModules x || noDafnyModules y
        }

data VerifyOpt = NoneV | FuncV | LeakV | BothV
    deriving (Data, Typeable,Generic,Eq,Show,Read)
instance Binary VerifyOpt
instance Hashable VerifyOpt

instance Monoid VerifyOpt where
    mempty = NoneV
    mappend x y | x == y = x
    mappend NoneV y = y
    mappend x NoneV = x
    mappend FuncV LeakV = BothV
    mappend FuncV BothV = BothV
    mappend LeakV FuncV = BothV
    mappend LeakV BothV = BothV
    mappend BothV _ = BothV

isFuncV BothV = True
isFuncV FuncV = True
isFuncV _ = False

isLeakV BothV = True
isLeakV LeakV = True
isLeakV _ = False

optionsDecl  :: Options
optionsDecl  = Opts { 
      inputs                = inputs mempty &= args &= typ "FILE.mil"
    , debugLexer            = debugLexer mempty &= help "Print lexer tokens to stderr" &= groupname "Debugging"
    , debugParser           = debugParser mempty &= help "Print parser result to stderr" &= groupname "Debugging"
    , debugTypechecker      = debugTypechecker mempty &= help "Print typechecker result to stderr" &= groupname "Debugging"
    , debugVerification     = debugVerification mempty &= help "Print verification result to stderr" &= groupname "Debugging"
    , typecheck             = typecheck mempty &= help "Typecheck" &= groupname "Typechecking"
    , verify                = verify mempty &= help "Verify" &= groupname "Verification"
    , verificationTimeOut   = verificationTimeOut mempty &= help "Timeout for verification" &= groupname "Verification"
    , noDafnyModules        = noDafnyModules mempty &= help "Do not generate Dafny modules" &= groupname "Verification"
    }
    &= help "Jasmin analyser"

mode  :: Mode (CmdArgs Options)
mode  = cmdArgsMode $
           modes [optionsDecl &= auto]
        &= help "Jasmin analyser"
        &= summary ("jasmin " ++ showVersion version ++ " \n\
                   \(C) HASLab 2017")

getOpts :: IO Options
getOpts = getArgs >>= doGetOpts
    where 
    doGetOpts as
        | null as   = withArgs ["--help"] $ cmdArgsRun mode >>= return
        | otherwise = cmdArgsRun mode >>= return