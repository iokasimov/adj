{-# LANGUAGE UndecidableInstances #-}

module Adj.Program.Generation where

import Adj.Auxiliary (Casting (Primary, (=-), (-=)), type (=!?=), type (=!!??=))
import Adj.Algebra (Category, Functor (map), (:*:), (:+:), Identity, Flat, Dual, (=-=))

newtype Generation p f o = Generation
	((=!!??=) p Identity (f =!?= Generation p f) o)

instance Casting (->) (Generation p f) where
	type Primary (Generation p f) o = (=!!??=) p Identity (f =!?= Generation p f) o
	(=-) (Generation m) = m
	(-=) m = Generation m

instance
	( Category m
	, Functor m m f
	, Functor m m Identity
	, Casting m (Generation p f)
	, Casting m (f =!?= Generation p f)
	, Casting m ((=!!??=) p Identity (f =!?= Generation p f))
	, forall r . Casting m (Flat p (Identity r))
	, forall l . Casting m (Dual p ((f =!?= Generation p f) l))
	, forall r . Functor m m ((Flat p) r)
	, forall l . Functor m m ((Dual p) l)
	) => Functor m m (Generation p f) where
	map m = (=-=) (map @m m)


type Construction = Generation (:*:)

type Instruction = Generation (:+:)
