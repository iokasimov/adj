module Adj.Program.Primitive.Boolean where

import Adj.Algebra.Category (Unit (Unit))
import Adj.Algebra.Set ((:+:) (This, That))

type Boolean = Unit :+: Unit

pattern True :: Boolean
pattern True <- This Unit
	where True = This Unit

pattern False :: Boolean
pattern False <- That Unit
	where False = That Unit
