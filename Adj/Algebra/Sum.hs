module Adj.Algebra.Sum where

infixr 7 :+:

data (:+:) left right = Option left | Adoption right
