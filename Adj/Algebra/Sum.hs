module Adj.Algebra.Sum where

import Adj.Algebra.Unit (Unit)
import Adj.Algebra.Initial (Initial)

infixr 7 :+:

data (:+:) left right = Option left | Adoption right

type instance Unit (:+:) = Initial
