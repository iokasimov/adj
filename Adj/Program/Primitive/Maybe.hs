module Adj.Program.Primitive.Maybe where

import Adj.Algebra.Category (Straight (Straight))
import Adj.Algebra.Set ((:+:) (This, That), Unit (Unit))

type Maybe = Straight (:+:) Unit

pattern Some :: a -> Maybe a
pattern Some x <- Straight (That x)
	where Some x = Straight (That x)

pattern None :: Maybe a
pattern None <- Straight (This Unit)
	where None = Straight (This Unit)
