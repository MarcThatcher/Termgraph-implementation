data Nat = Z | S Nat

eq :: Nat -> Nat -> Bool
eq Z     Z     = True
eq Z     (S _) = False
eq (S _) Z     = False
eq (S x) (S y) = eq x y

absDiff :: Nat -> Nat -> Nat
absDiff Z     y     = y
absDiff x     Z     = x
absDiff (S x) (S y) = absDiff x y

queens :: Nat -> [[Nat]]
queens Z     = [[]]
queens (S k) = concatMap extend (queens k)
  where extend qs = map (: qs) (filter (\q -> check q qs (S Z)) (cols (S k)))

cols :: Nat -> [Nat]
cols Z     = []
cols (S n) = cols n ++ [S n]

main :: IO ()
main = print (length (queens (S (S (S (S (S (S (S (S Z))))))))))