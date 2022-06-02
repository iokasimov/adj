module Adj.Algebra.Morphism.Dual where

newtype Dual morphism source target = Dual (morphism target source)

type (<--) = Dual (->)
