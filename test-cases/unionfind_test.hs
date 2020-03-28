import           AST
import           Data.List     as List
import           Data.Map      as Map
import           Util

unionFindUnittest :: IO ()
unionFindUnittest = do
    let argA = PrimVarName "a" 0
    let argB = PrimVarName "b" 0
    let argR = PrimVarName "r" 0

    let m1 = newUfItem argA initUnionFind
    let m2 = newUfItem argB m1
    let m3 = newUfItem argR m2
    let mapA = uniteUf m3 argR argA
    putStrLn $ "mapA: " ++ show mapA

    let n1 = newUfItem argA initUnionFind
    let n2 = newUfItem argB n1
    let n3 = newUfItem argR n2
    let mapB = uniteUf n3 argR argB
    putStrLn $ "mapB: " ++ show mapB

    let combined = combineUf mapA mapB
    let exp = fromList [(argA,argB),(argB,argB),(argR,argB)]
    putStrLn $ "\nexpect combineUf mapA mapB == "
                ++ show exp ++ " -> "
                ++ show (show combined == show exp)

    let united1 = uniteUf mapB argR argA
    let exp1 = fromList [(argA,argB),(argB,argB),(argR,argB)]
    putStrLn $ "\nexpect uniteUf mapB argR argA == "
                ++ show exp1 ++ " -> "
                ++ show (show united1 == show exp1)


    let united2 = uniteUf mapB argA argR
    let exp2 = fromList [(argA,argB),(argB,argB),(argR,argB)]
    putStrLn $ "\nexpect uniteUf mapB argA argR == "
                ++ show exp2 ++ " -> "
                ++ show (show united2 == show exp2)

    putStrLn "\nCalling foldr to unite args in aliasArgs to mapB:"
    let aliasArgs = [(argA, argR)]
    putStrLn $ "aliasArgs: " ++ show aliasArgs
    let testFoldr = List.foldr (\(inArg, outArg) aMap ->
                            uniteUf aMap outArg inArg) mapB aliasArgs
    let expRes = fromList [(argA,argB),(argB,argB),(argR,argB)]
    putStrLn $ "expect List.foldr (...) mapB aliasArgs == "
                ++ show expRes ++ " -> "
                ++ show (show testFoldr == show expRes)


main :: IO ()
main = unionFindUnittest
