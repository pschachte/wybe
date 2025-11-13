-- Simple naive reverse benchmark

-- List type
data Mylist t = Nil | Cons t (Mylist t)

-- Append two lists
append :: Mylist t -> Mylist t -> Mylist t
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

-- Reverse a list
nrev :: Mylist t -> Mylist t
nrev Nil = Nil
nrev (Cons x xs) = append (nrev xs) (Cons x Nil)

-- Find the length of a list
len :: Mylist t -> Int
len Nil = 0
len (Cons _ xs) = 1 + len xs

-- Make a list of numbers from lo (inclusive) to hi (exclusive) 
fromTo :: Int -> Int -> Mylist Int
fromTo lo hi =
    if lo >= hi
    then Nil
    else Cons lo $ fromTo (lo + 1) hi

main :: IO ()
main = do
    let size = 100000
    let rev_size = len $ nrev $ fromTo 0 size
    putStrLn $ "Reversed list size = " ++ show rev_size
