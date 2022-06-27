module Adj.Algebra.Set where

infixr 7 :*:, :+:

-- Cartesian product
data (:*:) l r = l :*: r

-- Disjoint union
data (:+:) l r = This l | That r
