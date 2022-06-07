module Adj.Program.Progress where

import Adj.Algebra.Category ((:+:) (This, That))

type Progress stop = (:+:) stop

pattern Continue :: continue -> Progress stop continue
pattern Continue continue <- That continue
	where Continue continue = That continue

pattern Stop :: stop -> Progress stop continue
pattern Stop stop <- This stop
	where Stop stop = This stop
