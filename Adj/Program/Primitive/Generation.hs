{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Adj.Program.Primitive.Generation where

import Adj.Auxiliary (Casted, Casting ((=-), (-=)), type (=!?=), FG (FG), FFGH (FFGH), type (=!!??=), Structural (Structural))
import Adj.Algebra.Category (Semigroupoid ((.)), Category ((.:), (...:), (....:), identity), Functor (map), Covariant, Bindable, Traversable, Semimonoidal, Component (component), Identity (Identity), Day (Day), type (-->), type (-/->), Flat (Flat), Dual, Kleisli (Kleisli), (->-), (->>-), (->>--), (->--), (-->--), (-/>/-), (-/>>/-), (=-=))
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
	, Covariant Flat Functor g (->) (->)
	) => Functor (-->) (-->) (Generation f g) where
	map (Flat m) = Flat . (=-=) . (=-=) .: (->>--) m . (-->--) ((=-=) (m ->>-))

instance
	( forall o . Functor (-->) (-->) (Flat f o)
	, forall o . Functor (-->) (-->) (Dual f o)
	, Covariant Flat Functor g (->) (->)
	, Semimonoidal Functor f f (-->) (-->) h
	-- TODO: how did we get to this?
	, Bindable Functor (->) (->) h
	, Traversable Functor (->) (->) h g
	) => Functor ((-/->) h) ((-/->) h) (Generation f g) where
	map (Kleisli (Flat m)) = Kleisli . Flat .: \(Generation (FFGH xs)) ->
		let new = (\(FG x) -> FG ->- (m -/>>/- x)) -->-- (m -/>/-) ->-- xs in
		Generation . FFGH ->- component @(-->) @(Day (-->) h h f f) =- Day new identity

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

instance Covariant Flat Functor f (->) (->) => Component (-->) f (Instruction f) where
	component = Flat .: \x -> Generation . FFGH . That . FG
		....: Generation . FFGH . This . Identity ->- x
