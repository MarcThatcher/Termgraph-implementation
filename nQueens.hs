-- n-Queens (Haskell)
-- A board is a list of column positions, one per row (built up row by row).

all' :: (a -> Bool) -> [a] -> Bool
all' _ []     = True
all' p (x:xs) = p x && all' p xs

zip' :: [a] -> [b] -> [(a, b)]
zip' (x:xs) (y:ys) = (x, y) : zip' xs ys
zip' _      _      = []

filter' :: (a -> Bool) -> [a] -> [a]
filter' _ [] = []
filter' p (x:xs)
  | p x       = x : filter' p xs
  | otherwise = filter' p xs

concatMap' :: (a -> [b]) -> [a] -> [b]
concatMap' _ []     = []
concatMap' f (x:xs) = f x ++ concatMap' f xs

map' :: (a -> b) -> [a] -> [b]
map' _ []     = []
map' f (x:xs) = f x : map' f xs

safe :: Int -> [Int] -> Bool
safe q qs = all ok (zip [1..] qs)
  where ok (d, c) = c /= q && abs (c - q) /= d
-- d is the row distance to an already placed queen, c its column.
-- Same column or same diagonal (|column diff| == row diff) is unsafe.

queens :: Int -> [[Int]]
queens n = place n
  where
    place 0 = [[]]
    place k = concatMap extend (place (k - 1))
    extend qs = map (: qs) (filter (\q -> safe q qs) [1 .. n])

main :: IO ()
main = do
  let n = 8
  print (length (queens n))      -- number of solutions (92 for n=8)
  print (head (queens n))        -- one example solution