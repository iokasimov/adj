{-# LANGUAGE UndecidableInstances #-}
module Adj.Algebra.Morphism.Kleisli where

import Adj.Algebra.Semigroupoid (Semigroupoid ((.)))
import Adj.Algebra.Category (Category (identity))
import Adj.Algebra.Functor (Functor (map))
import Adj.Algebra.Morphism.Flat (Flat, type (-->))
import Adj.Algebra.Morphism.Dual (Dual)

newtype Kleisli effect morphism source target = Kleisli (morphism source (effect target))

type (-/->) t = Kleisli t (Flat (->))
type (<-\-) t = Kleisli t (Dual (->))

instance Functor ((-/->) t) (-->) t => Semigroupoid ((-/->) t) where
	g . Kleisli f = Kleisli (map @((-/->) _) @(-->) g . f)

-- TODO: we need a monoidal functor here
-- instance Category ((-/->) t) where
