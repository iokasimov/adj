module Adj.Program.Primitive.Boolean where

import Adj.Algebra.Category (Terminal (Terminal))
import Adj.Algebra.Set ((:+:) (This, That))

type Boolean = Terminal :+: Terminal

pattern True :: Boolean
pattern True <- This Terminal
	where True = This Terminal

pattern False :: Boolean
pattern False <- That Terminal
	where False = That Terminal
