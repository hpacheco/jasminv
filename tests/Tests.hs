module Main where

import Data.List as List

import Control.Monad (when,liftM)

import System.IO (Handle, stderr, hPutStr, hPutStrLn)
import System.FilePath.Find as FilePath
import System.FilePath
import System.Process
import System.Exit
import System.Timeout

import Test.HUnit.Base
import Test.Hspec
import Test.Hspec.Contrib.HUnit (fromHUnitTest)
import Test.Hspec.Core.Runner (hspecWith, Config(..),defaultConfig)

-- Configs
fastfail = False
timelimit = 10 * 60

buildTestTree :: IO Test
buildTestTree = do
    tests1 <- buildTestDirectoryTree "resources/jasmin-lang/compiler" ".mil"
    tests2 <- buildTestDirectoryTree "resources/qhasm-translator" ".mil"
    return $ TestList [tests1,tests2]
    
buildLabeledTestDirectoryTree n path ext = liftM (TestLabel n) (buildTestDirectoryTree path ext)

buildTestDirectoryTree :: FilePath -> String -> IO Test
buildTestDirectoryTree path ext = fold (depth >=? 0) (addTestFile ext) (TestList []) path
    
addTestFile :: String -> Test -> FileInfo -> Test
addTestFile ext t i = if evalClause (extension ==? ext) i
    then let p = evalClause filePath i in addTestToTree t (splitPath p) p
    else t

addTestToTree :: Test -> [FilePath] -> FilePath -> Test
addTestToTree (TestList xs) [] f = TestList $ testTypeChecker f : xs
addTestToTree (TestList xs) (d:ds) f = TestList $ addTestToList xs d ds f
addTestToTree (TestLabel l t) (d:ds) f | l == d = TestLabel l (addTestToTree t ds f)
addTestToTree t ds f = TestList [t,addTestToTree (TestList []) ds f]

addTestToList :: [Test] -> FilePath -> [FilePath] -> FilePath -> [Test]
addTestToList [] d ds f = [TestLabel d $ addTestToTree (TestList []) ds f]
addTestToList (TestLabel l t:xs) d ds f | l == d = TestLabel l (addTestToTree t ds f) : xs
addTestToList (x:xs) d ds f = x : addTestToList xs d ds f

hasLabel :: String -> Test -> Bool
hasLabel s (TestLabel l _) = s == l
hasLabel s t = False

data Result = ResSuccess | ResFailure Int | ResTimeout Int
  deriving (Eq,Show)

instance Assertable Result where
    assert ResSuccess = return ()
    assert (ResFailure i) = assertFailure $ "test failed with error code " ++ show i
    assert (ResTimeout t) = assertFailure $ "test timed out after " ++ show t ++ " seconds"

testTypeChecker :: FilePath -> Test
testTypeChecker f = test $ do
    code <- timeout (timelimit *10^6) (system $ "cabal exec -- jasminv " ++ f)
    case code of
        Just ExitSuccess -> return ResSuccess
        Just (ExitFailure i) -> return $ ResFailure i
        Nothing -> return $ ResTimeout timelimit

--HSpec main
main :: IO ()
main = do
    testSuite <- buildTestTree
    let cfg = defaultConfig { configFastFail = fastfail }
    hspecWith cfg $ describe "jasminv tests" $ fromHUnitTest testSuite



