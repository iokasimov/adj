module Adj.Program.Datastructure (module Exports, Nonempty, Emptiable) where

import Adj.Program.Datastructure.Implementation as Exports
import Adj.Program.Datastructure.Property as Exports

import Adj.Auxiliary (type (=!?=))
import Adj.Program.Primitive.Maybe (Maybe)
import Adj.Program.Primitive.Generation (Construction)

type family Nonempty datastructure where
	Nonempty (Maybe =!?= Construction Maybe) = Construction Maybe

type Emptiable datastructure = Maybe =!?= datastructure
