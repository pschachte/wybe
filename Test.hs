module Test where

import qualified Data.List as List
import           NewParser (parseWybe)
import           Parser (parse)
import           Scanner (fileTokens, Token)
import           System.Directory (listDirectory)
import           System.FilePath (takeExtension, combine, replaceExtension)
import           System.IO (openFile, IOMode(..))
import           System.Process
import           Test.Hspec
import           Test.Hspec.Core.Runner (hspecResult)



main :: IO ()
main = runCompilerTest


-----------------------------------------------------------------------------
-- Parser Test                                                             --
-----------------------------------------------------------------------------

runParserTest :: IO ()
runParserTest = do
    stoks <- wybeSourceTokens
    _ <- hspecResult $ parserTestSpec stoks
    return ()


parserTestSpec :: [(FilePath, [Token])] -> Spec
parserTestSpec fs =
    describe "Parsec Parser" $
        mapM_ (\(f, toks) ->
                     it ("builds parse tree for " ++ f) $
                         case parseWybe toks f of
                             Left err ->
                                 expectationFailure (show err)
                             Right t ->
                                 t `shouldBe` parse toks
              ) fs


runCompilerTest :: IO ()
runCompilerTest = do
    fs <- wybeSourceFiles
    _ <- hspecResult $ compilerTestSpec fs
    return ()



-----------------------------------------------------------------------------
-- Compiler Output Test                                                    --
-----------------------------------------------------------------------------

-- | Specification for testing expected compiler output
compilerTestSpec :: [FilePath] -> Spec
compilerTestSpec fs =
    describe "Wybemk compiler" $
        mapM_ (\f -> do
                      runIO (compileFile f)
                      let expFile = expectedFileFor f
                      let outFile = outputFileFor f
                      expected <- runIO (readFile expFile)
                      output <- runIO (readFile outFile)
                      it ("compiles " ++ f ++
                          " and returns matching expected output.") $
                          expected `shouldBe` output
              ) fs


compileFile :: FilePath -> IO ()
compileFile f = do
    let exec = "gtimeout" --log=FinalDump --force-all"
    let ofile = replaceExtension f ".o"
    let args = [ "2", "./wybemk", "--log=FinalDump", "--force-all", ofile ]
    -- outHandle <- openFile (outputFileFor f) WriteMode
    -- logHandle <- openFile (logFileFor f) WriteMode 
    -- let process = proc exec args
    (_, sout, serr) <- readProcessWithExitCode exec args []
    putStrLn $ "wybemk: compiling " ++ f
    writeFile (outputFileFor f) sout
    writeFile (logFileFor f) serr



-----------------------------------------------------------------------------
-- Helper Functions                                                        --
-----------------------------------------------------------------------------


-- | Tokenize wybe source files in the 'test-cases' directory.
wybeSourceTokens :: IO [(FilePath, [Token])]
wybeSourceTokens = do
    files <- wybeSourceFiles
    -- FilePath -> IO (FilePath, [Token])
    mapM (\f -> (,) <$> return f <*> fileTokens f) files

-- | All source files in the 'test-cases' dir, dynamically collected.
wybeSourceFiles :: IO [FilePath]
wybeSourceFiles = do
    let isWybe = List.filter ((== ".wybe") . takeExtension)
    let listDir d = List.map (combine d) <$> listDirectory d
    tests <- isWybe <$> listDir "test-cases"
    -- others <- isWybe <$> listDir "wybelibs"
    return $ tests



expectedFileFor :: FilePath -> FilePath
expectedFileFor f = replaceExtension f ".exp"

outputFileFor :: FilePath -> FilePath
outputFileFor f = replaceExtension f ".out"

logFileFor :: FilePath -> FilePath
logFileFor f = replaceExtension f ".log"
