module Adj.Algebra.Category where

import Adj.Algebra.Semigroupoid (Semigroupoid)

{- |
> * Left identity: identity . f ≡ f
> * Right identity: f . identity ≡ f
-}

class Semigroupoid morphism => Category morphism where
	identity :: morphism source source

instance Category (->) where
	identity = \x -> x
