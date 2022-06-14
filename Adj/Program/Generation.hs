module Adj.Program.Generation where

import Adj.Auxiliary (Casting (Primary, (=-), (-=)))

newtype Generation p t a = Generation (p a (t (Generation p t a)))

instance Casting (Generation p  t) where
	type Primary (Generation p t) a = p a (t (Generation p t a))
	(=-) (Generation m) = m
	(-=) m = Generation m
