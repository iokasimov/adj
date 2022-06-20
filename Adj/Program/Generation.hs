module Adj.Program.Generation where

import Adj.Auxiliary (Casting (Primary, (=-), (-=)))
import Adj.Algebra (Category, (.), Functor (map), (-|--), (--|||--), (:*:), (:+:), Flat, Dual, (=-=))

newtype Generation p t a = Generation (p a (t (Generation p t a)))

instance Casting (->) (Generation p t) where
	type Primary (Generation p t) a = p a (t (Generation p t a))
	(=-) (Generation m) = m
	(-=) m = Generation m

instance
	( Category m
	, Functor m m t
	, Casting m (Generation p t)
	, forall b . Functor m m ((Flat p) b)
	, forall a . Functor m m ((Dual p) a)
	, forall b . Casting m (Flat p b)
	, forall a . Casting m (Dual p a)
	) => Functor m m (Generation p t) where
		map m = (=-=) @m @(Generation p t)
			((-|--) m . (--|||--) m)

type Construction = Generation (:*:)

type Instruction = Generation (:+:)
