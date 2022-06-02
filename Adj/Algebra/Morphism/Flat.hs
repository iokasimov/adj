module Adj.Algebra.Morphism.Flat where

newtype Flat morphism source target = Flat (morphism source target)

type (-->) = Flat (->)
