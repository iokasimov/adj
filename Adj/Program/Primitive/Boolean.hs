module Adj.Program.Primitive.Boolean where

import Adj.Algebra.Category ((:+:) (This, That), Terminal (Terminal))

type Boolean = Terminal :+: Terminal

pattern True :: Boolean
pattern True <- This Terminal
	where True = This Terminal

pattern False :: Boolean
pattern False <- That Terminal
	where False = That Terminal
