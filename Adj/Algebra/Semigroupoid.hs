module Adj.Algebra.Semigroupoid where

infixr 9 .

{- |
> * Associativity: f . (g . h) ≡ (f . g) . h
-}

class Semigroupoid morphism where
	(.) :: morphism between target
		-> morphism source between
		-> morphism source target
