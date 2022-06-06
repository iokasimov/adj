module Adj.Program.Construction where

import Adj.Algebra ((.:), Functor (map), (|-|->), (:*:) ((:*:)), type (-->), Flat (Flat))
import Adj.Program.Casting (Casting (Primary, (=-), (-=)))

newtype Construction t a = Construction (a :*: t (Construction t a))

instance Casting (Construction t) where
	type Primary (Construction t) a = a :*: t (Construction t a)
	(=-) (Construction m) = m
	(-=) m = Construction m

instance Functor (-->) (-->) t => Functor (-->) (-->) (Construction t) where
	map (Flat m) = Flat .: \(Construction (x :*: xs)) ->
		Construction (m x :*: (xs |-|-> m))
