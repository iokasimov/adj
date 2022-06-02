module Adj.Algebra.Morphism.Kleisli where

newtype Kleisli effect morphism source target = Kleisli (morphism source (effect target))

type (-/->) = Kleisli (Flat (->))
type (<-\-) = Kleisli (Dual (->))
