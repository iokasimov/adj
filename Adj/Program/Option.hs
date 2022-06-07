module Adj.Program.Option where

import Adj.Algebra.Category ((:+:) (This, That), Terminal (Terminal))

type Option = (:+:) Terminal

pattern Some :: a -> Option a
pattern Some x <- That x
	where Some x = That x

pattern None :: Option a
pattern None <- This Terminal
	where None = This Terminal
