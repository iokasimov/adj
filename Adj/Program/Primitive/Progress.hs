module Adj.Program.Primitive.Progress where

import Adj.Algebra.Category (Flat (Flat), (:+:) (This, That))

type Progress stop = Flat (:+:) stop

pattern Continue :: continue -> Progress stop continue
pattern Continue continue <- Flat (That continue)
	where Continue continue = Flat (That continue)

pattern Stop :: stop -> Progress stop continue
pattern Stop stop <- Flat (This stop)
	where Stop stop = Flat (This stop)
