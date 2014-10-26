import Prelude hiding (succ)
import Data.List (genericLength)

-- credit for prime number generation due to:
-- http://www.yellosoft.us/evilgenius/

sieve :: (Integral a) => [a] -> [a]
sieve (n:ns) = n : sieve ns'
  where ns' = filter ((/= 0) . flip rem n) (n:ns)

primes :: (Integral a) => [a]
primes = sieve [2..]


gödelSeq l = product $ zipWith (^) primes $ [genericLength l] ++ l

zero         = [0]
succ         = [1]
project n i  = [2, n, i]
compose g hs = [3, gödelSeq g] ++ map gödelSeq hs
recurse g h  = [4, gödelSeq g, gödelSeq h]

add = recurse g h where
  g = project 1 1
  h = compose succ [project 3 1]

multiply = recurse g h where
  g = zero
  h = compose add [project 3 1, project 3 3]

exponentiation = recurse g h where
  g = compose succ [zero]
  h = compose multiply [project 3 1, project 3 3]

main = print (add :: [Integer])
