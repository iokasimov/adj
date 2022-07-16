module Adj.Program.Primitive.Predicate where

import Adj.Algebra.Category (type (<--))
import Adj.Program.Primitive.Boolean (Boolean)

type Predicate = (<--) Boolean
