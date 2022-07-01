{-# LANGUAGE UndecidableInstances #-}

module Adj.Program.Primitive.Generation where

import Adj.Auxiliary (Casted, Casting ((=-), (-=)), type (=!?=), FG (FG), FFGH (FFGH), type (=!!??=), Structural (Structural))
import Adj.Algebra (Semigroupoid ((.)), Category ((.:), (...:)), Functor (map), Setoid, (:*:) ((:*:)), (:+:) (This, That), Identity (Identity), Flat, Dual, (=-=))

newtype Generation p f o = Generation
	((=!!??=) p Identity (f =!?= Generation p f) o)

type instance Casted (Generation p f) o = (=!!??=) p Identity (f =!?= Generation p f) o

deriving via (Structural ((=!!??=) p Identity (f =!?= Generation p f) o))
	instance Setoid (p (Identity o) ((=!?=) f (Generation p f) o)) => Setoid (Generation p f o)

instance Casting (->) (Generation p f) where
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

pattern Construct :: o -> f (Construction f o) -> Construction f o
pattern Construct x xs <- Generation (FFGH (Identity x :*: FG xs))
	where Construct x xs = Generation . FFGH ...: Identity x :*: FG xs

type Instruction = Generation (:+:)

pattern Instruct :: f (Instruction f o) -> Instruction f o
pattern Instruct xs <- Generation (FFGH (That (FG xs)))
	where Instruct xs = Generation . FFGH . That .: FG xs

pattern Load :: o -> Instruction f o
pattern Load x <- Generation (FFGH (This (Identity x)))
	where Load x = Generation . FFGH . This .: Identity x
