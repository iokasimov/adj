module Adj.Algebra.Morphism.Kleisli where

import Adj.Algebra.Morphism.Flat (Flat)
import Adj.Algebra.Morphism.Dual (Dual)

newtype Kleisli effect morphism source target = Kleisli (morphism source (effect target))

type (-/->) = Kleisli (Flat (->))
type (<-\-) = Kleisli (Dual (->))
