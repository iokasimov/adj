module Adj.Algebra.Category where

import Adj.Algebra.Semigroupoid (Semigroupoid)

{- |
> * Left identity: identity . f ≡ f
> * Right identity: f . identity ≡ f
-}

class Semigroupoid morphism => Category morphism where
	identity :: morphism source source

	(.:) :: morphism (morphism source target) (morphism source target)
	(.:) = identity

instance Category (->) where
	identity = \x -> x
