module Adj.Algebra.Product where

import Adj.Algebra.Unit (Unit)
import Adj.Algebra.Terminal (Terminal)

infixr 7 :*:

data (:*:) left right = left :*: right

type instance Unit (:*:) = Terminal
