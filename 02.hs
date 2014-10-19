-- Exercise 4

pair x y = 2^x * (2*y + 1) - 1

muP while p = minimum [x | x <- takeWhile while [0 ..], p x]
exP while p = or    [p x | x <- takeWhile while [0 ..]]

unpair1 z = muP (<= z) $ \ x -> exP (<= z) $ \ y -> z == pair x y
unpair2 z = muP (<= z) $ \ y -> exP (<= z) $ \ x -> z == pair x y


-- Exercise 6

slowsort [] = []
slowsort (x:xs) = insertInSorted x (slowsort xs)

insertInSorted x [] = [x]
insertInSorted x (y:ys)
  | x <= y    = x:y:ys
  | otherwise = y:insertInSorted x ys


-- Exercise 9

len' 0 = 0
len' x = 1 + len' (x - 2^(maxBinExp x))

maxBinExp x = muP (<= x) (\ e -> not $ exP (<= x) (\ e' -> e' > e && 2^e' <= x))

index' i x
  | 1 <= i && i <= len' x = f (len' x - i) x
  | otherwise            = 0
  where f 0 x = let m = maxBinExp x in
                m - (if 2^m == x then 0 else maxBinExp (next x) + 1)
        f i x = f (i - 1) (next x)
        next x = x - 2^(maxBinExp x)


-- Exercise 10

ack 0 y = y + 1
ack x 0 = ack (x-1) 1
ack x y = ack (x-1) $ ack x (y-1)
