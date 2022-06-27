module Adj.Algebra.Set where

infixr 7 :*:, :+:

data (:*:) l r = l :*: r

data (:+:) l r = This l | That r
