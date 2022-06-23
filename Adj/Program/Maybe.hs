module Adj.Program.Maybe where

import Adj.Algebra.Category (Flat (Flat), (:+:) (This, That), Terminal (Terminal))

type Maybe = Flat (:+:) Terminal

pattern Some :: a -> Maybe a
pattern Some x <- Flat (That x)
	where Some x = Flat (That x)

pattern None :: Maybe a
pattern None <- Flat (This Terminal)
	where None = Flat (This Terminal)
