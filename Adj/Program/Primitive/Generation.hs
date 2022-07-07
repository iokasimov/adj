{-# LANGUAGE UndecidableInstances #-}

module Adj.Program.Primitive.Generation where

import Adj.Auxiliary (Casted, Casting ((=-), (-=)), type (=!?=), FG (FG), FFGH (FFGH), type (=!!??=), Structural (Structural))
import Adj.Algebra.Category (Semigroupoid ((.)), Category ((.:), (...:), (....:)), Functor, Covariant, Component (component), Identity (Identity), type (-->), Flat (Flat), (->-))
import Adj.Algebra.Set (Setoid, (:*:) ((:*:)), (:+:) (This, That))

newtype Generation p f o = Generation
	((=!!??=) p Identity (f =!?= Generation p f) o)

type instance Casted (Generation p f) o = (=!!??=) p Identity (f =!?= Generation p f) o

deriving via (Structural ((=!!??=) p Identity (f =!?= Generation p f) o))
	instance Setoid (p (Identity o) ((=!?=) f (Generation p f) o)) => Setoid (Generation p f o)

instance Casting (->) (Generation p f) where
	(=-) (Generation m) = m
	(-=) m = Generation m

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

instance Covariant Functor (->) (->) f => Component (-->) f (Instruction f) where
	component = Flat .: \x -> Generation . FFGH . That . FG
		....: Generation . FFGH . This . Identity ->- x
