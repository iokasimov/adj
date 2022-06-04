module Adj.Algebra.Morphism.Flat where

import Adj.Algebra.Semigroupoid (Semigroupoid ((.)))
import Adj.Algebra.Category (Category (identity))

newtype Flat morphism source target = Flat (morphism source target)

type (-->) = Flat (->)

instance Semigroupoid (-->) where
	Flat g . Flat f = Flat (\x -> g (f x))

instance Category (-->) where
	identity = Flat (\x -> x)
