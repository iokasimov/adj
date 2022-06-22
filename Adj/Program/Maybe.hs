module Adj.Program.Maybe where

import Adj.Algebra.Category ((:+:) (This, That), Terminal (Terminal))

type Maybe = (:+:) Terminal

pattern Some :: a -> Maybe a
pattern Some x <- That x
	where Some x = That x

pattern None :: Maybe a
pattern None <- This Terminal
	where None = This Terminal
