-- Haskell solution to the n queens problem

import Control.Applicative

queens :: Int -> Maybe [Int]
queens n = placeQueens n (n - 1) 0 []

placeQueens :: Int -> Int -> Int -> [Int] -> Maybe [Int]
placeQueens n row col qs
    | row < 0 = Just qs
    | col >= n = Nothing
    | safe col (row - col) (row + col) (row + 1) qs =
        placeQueens n (row - 1) 0 (col : qs)
        <|> placeQueens n row (col + 1) qs
    | otherwise = placeQueens n row (col + 1) qs

safe :: Int -> Int -> Int -> Int -> [Int] -> Bool
safe col diag1 diag2 row [] = True
safe col diag1 diag2 row (q:qs) =
    q /= col && row - q /= diag1 && row + q /= diag2
    && safe col diag1 diag2 (row + 1) qs

showQueens :: [Int] -> IO ()
showQueens qs = mapM_ (showRow $ length qs) qs

showRow :: Int -> Int -> IO ()
showRow n q = do
    let rowStr = [if c == q then 'Q' else '.' | c <- [0..(n - 1)]]
    putStrLn rowStr

main :: IO ()
main = do
    let n = 32
    case queens n of
        Just qs  -> do
            putStrLn $ show n ++ " Queens Solution:"
            showQueens qs
        Nothing -> do
            putStrLn $ "No solution to " ++ show n ++ " queens problem."

