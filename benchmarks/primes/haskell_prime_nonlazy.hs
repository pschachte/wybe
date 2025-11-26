-- Print the n'th prime number

primes :: Integer -> Integer
primes n = primes' n 2 []

primes' n next known
  | isPrime next known =
        if n == 0   
        then next
        else primes' (n - 1) next' (known ++ [next])
  | otherwise = primes' n next' known
  where next' = next + 1

isPrime :: Integer -> [Integer] -> Bool
isPrime candidate known =
    all ((/= 0) . (candidate `mod`)) known

main :: IO ()
main = do
    let n = 75000
    print $ primes $ n - 1
