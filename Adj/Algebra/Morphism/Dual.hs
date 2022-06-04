module Adj.Algebra.Morphism.Dual where

import Adj.Algebra.Semigroupoid (Semigroupoid ((.)))
import Adj.Algebra.Category (Category (identity))

newtype Dual morphism source target = Dual (morphism target source)

type (<--) = Dual (->)

instance Semigroupoid (<--) where
	Dual f . Dual g = Dual (\x -> g (f x))

instance Category (<--) where
	identity = Dual (\x -> x)
