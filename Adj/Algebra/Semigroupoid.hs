module Adj.Algebra.Semigroupoid where

infixr 9 .

{- |
> * Associativity: f . (g . h) ≡ (f . g) . h
-}

class Semigroupoid morphism where
	(.) :: morphism b c -> morphism a b -> morphism a c
