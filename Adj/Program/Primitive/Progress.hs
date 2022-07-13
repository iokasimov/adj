module Adj.Program.Primitive.Progress where

import Adj.Algebra.Category (Straight (Straight))
import Adj.Algebra.Set ((:+:) (This, That))

type Progress stop = Straight (:+:) stop

pattern Continue :: continue -> Progress stop continue
pattern Continue continue <- Straight (That continue)
	where Continue continue = Straight (That continue)

pattern Stop :: stop -> Progress stop continue
pattern Stop stop <- Straight (This stop)
	where Stop stop = Straight (This stop)
