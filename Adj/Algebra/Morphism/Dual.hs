module Adj.Algebra.Morphism.Dual where

import Adj.Algebra.Semigroupoid (Semigroupoid ((.)))

newtype Dual morphism source target = Dual (morphism target source)

type (<--) = Dual (->)

instance Semigroupoid (<--) where
	Dual f . Dual g = Dual (\x -> g (f x))
