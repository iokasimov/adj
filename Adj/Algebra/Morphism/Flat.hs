module Adj.Algebra.Morphism.Flat where

import Adj.Algebra.Semigroupoid (Semigroupoid ((.)))
import Adj.Algebra.Category (Category (identity))

newtype Flat morphism source target = Flat (morphism source target)

type (-->) = Flat (->)

instance Semigroupoid morhism => Semigroupoid (Flat morhism) where
	Flat g . Flat f = Flat (g . f)

instance Category morhism => Category (Flat morhism) where
	identity = Flat identity
