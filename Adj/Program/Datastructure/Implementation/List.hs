module Adj.Program.Datastructure.Implementation.List where

import Adj.Auxiliary (type (=!?=))
import Adj.Program.Primitive.Maybe (Maybe)
import Adj.Program.Primitive.Generation (Construction)

type List = Maybe =!?= Construction Maybe
