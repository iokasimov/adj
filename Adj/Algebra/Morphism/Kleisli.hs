{-# LANGUAGE UndecidableInstances #-}
module Adj.Algebra.Morphism.Kleisli where

import Adj.Algebra.Semigroupoid (Semigroupoid ((.)))
import Adj.Algebra.Category (Category ((.:)))
import Adj.Algebra.Functor (Functor (map))
import Adj.Algebra.Morphism.Flat (type (-->))
import Adj.Algebra.Morphism.Dual (type (<--))

newtype Kleisli effect morphism source target = Kleisli (morphism source (effect target))

type (-/->) t = Kleisli t (-->)
type (<-\-) t = Kleisli t (<--)

instance Functor (Kleisli functor target) target functor
	=> Semigroupoid (Kleisli functor target) where
		g . Kleisli f = Kleisli .: map g . f

-- TODO: we need a monoidal functor here
-- instance Category (Kleisli functor target) where
