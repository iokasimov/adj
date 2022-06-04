module Adj.Algebra.Morphism.Dual where

import Adj.Algebra.Semigroupoid (Semigroupoid ((.)))
import Adj.Algebra.Category (Category (identity, (.:)))

newtype Dual morphism source target = Dual (morphism target source)

type (<--) = Dual (->)

instance Semigroupoid morhism => Semigroupoid (Dual morhism) where
	Dual g . Dual f = Dual .: f . g

instance Category morhism => Category (Dual morhism) where
	identity = Dual identity
