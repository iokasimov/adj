{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Adj.Program.Primitive.Generation where

import Adj.Auxiliary (Casted, Casting ((=-), (-=)), type (=!?=), FG (FG), FFGH (FFGH), type (=!!??=), Structural (Structural))
import Adj.Algebra.Category (Semigroupoid ((.)), Category ((.:), (...:), (....:)), Functor (map), Functoriality (Natural), Covariant, Component (component), Identity (Identity), type (-->), Flat (Flat), Dual, (->-), (->>-), (->>--), (-->--), (=-=))
import Adj.Algebra.Set (Setoid, (:*:) ((:*:)), (:+:) (This, That))

newtype Generation f g o = Generation
	((=!!??=) f Identity (g =!?= Generation f g) o)

type instance Casted (Generation f g) o = (=!!??=) f Identity (g =!?= Generation f g) o

deriving via (Structural ((=!!??=) f Identity (g =!?= Generation f g) o))
	instance Setoid (f (Identity o) ((=!?=) g (Generation f g) o)) => Setoid (Generation f g o)

instance Casting (->) (Generation f g) where
	(=-) (Generation m) = m
	(-=) m = Generation m

instance
	( forall o . Functor (-->) (-->) (Flat f o)
	, forall o . Functor (-->) (-->) (Dual f o)
	, Covariant Natural Functor (->) (->) g
	) => Functor (-->) (-->) (Generation f g) where
	map (Flat m) = Flat . (=-=) . (=-=) .: (->>--) m . (-->--) ((=-=) (m ->>-))

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

instance Covariant Natural Functor (->) (->) f => Component (-->) f (Instruction f) where
	component = Flat .: \x -> Generation . FFGH . That . FG
		....: Generation . FFGH . This . Identity ->- x
