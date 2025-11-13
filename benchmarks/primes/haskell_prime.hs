-- Print the n'th prime number

primes :: [Integer]
primes = sieve [2..]

sieve :: [Integer] -> [Integer]
sieve (p:xs) = p : sieve (filter ((/=0) . (`mod` p)) xs)

main :: IO ()
main = do
    let n = 75000
    print (primes !! (n - 1))
