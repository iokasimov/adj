module Adj.Program.Option where

import Adj.Algebra.Category ((:+:) (Option, Adoption), Terminal (Terminal))

type Option = (:+:) Terminal

pattern Some :: a -> Option a
pattern Some x <- Adoption x
	where Some x = Adoption x

pattern None :: Option a
pattern None <- Option Terminal
	where None = Option Terminal
