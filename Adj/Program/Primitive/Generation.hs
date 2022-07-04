{-# LANGUAGE UndecidableInstances #-}

module Adj.Program.Primitive.Generation where

import Adj.Auxiliary (Casted, Casting ((=-), (-=)), type (=!?=), FG (FG), FFGH (FFGH), type (=!!??=), Structural (Structural))
import Adj.Algebra (Semigroupoid ((.)), Category ((.:), (...:), (....:)), Functor (map), Covariant, Component (component), Setoid, (:*:) ((:*:)), (:+:) (This, That), Identity (Identity), type (-->), Flat (Flat), (-|->))

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

-- TODO: keep it unitl defining Functor instance for FFGH
instance Covariant Functor (->) (->) f => Functor (-->) (-->) (Construction f) where
	map (Flat m) = Flat .: \case
		Generation (FFGH (Identity x :*: xs)) -> 
			Generation . FFGH ...: Identity .: m x :*: (xs -|-> m)

type Instruction = Generation (:+:)

pattern Instruct :: f (Instruction f o) -> Instruction f o
pattern Instruct xs <- Generation (FFGH (That (FG xs)))
	where Instruct xs = Generation . FFGH . That .: FG xs

pattern Load :: o -> Instruction f o
pattern Load x <- Generation (FFGH (This (Identity x)))
	where Load x = Generation . FFGH . This .: Identity x

-- TODO: keep it unitl defining Functor instance for FFGH
instance Covariant Functor (->) (->) f => Functor (-->) (-->) (Instruction f) where
	map (Flat m) = Flat .: \case
		Generation (FFGH (This x)) -> Generation . FFGH . This ....: x -|-> m
		Generation (FFGH (That xs)) -> Generation . FFGH . That ....: xs -|-> m

instance Covariant Functor (->) (->) f => Component (-->) f (Instruction f) where
	component = Flat .: \x -> Generation . FFGH . That . FG
		....: x -|-> Generation . FFGH . This . Identity
