module Adj.Program.Primitive.Maybe where

import Adj.Algebra.Category (Flat (Flat))
import Adj.Algebra.Set ((:+:) (This, That), Unit (Unit))

type Maybe = Flat (:+:) Unit

pattern Some :: a -> Maybe a
pattern Some x <- Flat (That x)
	where Some x = Flat (That x)

pattern None :: Maybe a
pattern None <- Flat (This Unit)
	where None = Flat (This Unit)
