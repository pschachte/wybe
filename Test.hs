--  File     : Test.hs
--  Author   : Ashutosh Rishi Ranjan
--  Purpose  : Test code for NewParser.hs parser

module Test where

import qualified Data.List as List
import           NewParser (parseWybe)
import           Parser (parse)
import AST (Item)
import           Scanner (fileTokens, Token)
import           Test.Hspec
import           System.Directory (listDirectory)
import System.FilePath (takeExtension, combine)




main :: IO ()
main = do
    stoks <- wybeSourceTokens
    hspec $ parserTestSpec stoks


parserTestSpec :: [(FilePath, [Token])] -> Spec
parserTestSpec fs = do
    describe "Parsec Parser" $
        mapM_ (\(f, toks) -> do
                     it ("build parse tree for " ++ f) $ do
                         case parseWybe toks f of
                             Left err ->
                                 expectationFailure (show err)
                             Right t ->
                                 t `shouldBe` parse toks
              ) fs


wybeSourceTokens :: IO [(FilePath, [Token])]
wybeSourceTokens = do
    files <- wybeSourceFiles
    -- FilePath -> IO (FilePath, [Token])
    mapM (\f -> (,) <$> return f <*> fileTokens f) files
    


wybeSourceFiles :: IO [FilePath]
wybeSourceFiles = do
    let isWybe = List.filter ((== ".wybe") . takeExtension)
    let listDir d = List.map (combine d) <$> listDirectory d
    tests <- isWybe <$> listDir "test-cases"
    others <- isWybe <$> listDir "wybelibs"
    return $ others ++ tests
