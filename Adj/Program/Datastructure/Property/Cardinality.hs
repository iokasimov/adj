module Adj.Program.Datastructure.Property.Cardinality where

import Adj.Algebra.Set ((:+:), Unit, Void)
import Adj.Algebra.Category (Identity)
import Adj.Program.Primitive.Maybe (Maybe)

type family Cardinality datastructure = cardinality where
	Cardinality Maybe = Void :+: Unit
	Cardinality Identity = Unit
