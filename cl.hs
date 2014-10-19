{-# LANGUAGE OverloadedStrings #-}
import Control.Applicative ((<*), (<$>))
import Data.Char (isLower)
import Text.Parsec

data Constant = I | K | S | B | C | Y
  deriving (Show, Eq, Read)

data Term = Const Constant | Ap Term Term | Var Char
  deriving Eq

instance Show Term where
  show (Const c) = show c
  show (Var x) = [x]
  show (Ap t u@(Ap _ _)) = show t ++ "(" ++ show u ++ ")"
  show (Ap t u) = show t ++ show u


symbol :: Char -> Term
symbol c
  | isLower c = Var c
  | otherwise = Const $ read [c]

unit :: Parsec String st Term
unit =
      (symbol <$> noneOf "()")
  <|> between (char '(') (char ')') tree
  <?> "group or literal"

tree :: Parsec String st Term
tree = foldl1 Ap <$> many1 unit

readTerm :: String -> Term
readTerm str = case parse (tree <* eof) "" str of
  Right t -> t
  Left e -> error (show e)


reduceOuter :: Term -> Term
reduceOuter (Ap (Const I) t) = t
reduceOuter (Ap (Ap (Const K) t) _) = t
reduceOuter (Ap (Ap (Ap (Const S) t) u) v) = Ap (Ap t v) (Ap u v)
reduceOuter (Ap (Ap (Ap (Const B) t) u) v) = Ap t (Ap u v)
reduceOuter (Ap (Ap (Ap (Const C) t) u) v) = Ap (Ap t u) v
reduceOuter (Ap (Const Y) t) = Ap t (Ap (Const Y) t)
reduceOuter t = t

reduceLeftmost :: Term -> Term
reduceLeftmost s@(Ap t u)
  | s /= s'    = s'
  | t /= t'    = Ap t' u
  | u /= u'    = Ap t u'
  | otherwise = Ap (reduceLeftmost t) (reduceLeftmost u)
  where s' = reduceOuter s
        t' = reduceOuter t
        u' = reduceOuter u
reduceLeftmost t = t

reductions :: Term -> [Term]
reductions t
  | t == r    = [t]
  | otherwise = t : reductions r
  where r = reduceLeftmost t

reduceNF :: Term -> Term
reduceNF = until (\ x -> reduceLeftmost x == x) reduceLeftmost


church :: [Term]
church = iterate (Ap (readTerm "SB")) (readTerm "KI")

addChurch :: Term
addChurch = readTerm "((SI)(K(S((S(KS)))))K)"
