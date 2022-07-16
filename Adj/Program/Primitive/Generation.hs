{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Adj.Program.Primitive.Generation where

import Adj.Auxiliary (Casted, Casting ((=-), (-=)), type (=!?=), FG (FG), FFGH (FFGH), type (=!!??=), Structural (Structural))
import Adj.Algebra.Category (Semigroupoid ((.)), Category ((.:), (...:), identity), Functor (map), Covariant, Bindable, Traversable, Semimonoidal, Component (component), Identity (Identity), Day (Day), type (-->), type (-/->), Straight (Straight), Opposite, Kleisli (Kleisli), (->-), (->>-), (->>--), (->--), (-->--), (-/>/-), (-/>>/-), (=-=))
import Adj.Algebra.Set (Setoid, (:*:) ((:*:)), (:+:) (This, That))

newtype Generation f g o = Generation
	((=!!??=) f Identity (g =!?= Generation f g) o)

type instance Casted (Generation f g) o = (=!!??=) f Identity (g =!?= Generation f g) o

deriving via (Structural ((=!!??=) f Identity (g =!?= Generation f g) o))
	instance Setoid (f (Identity o) ((=!?=) g (Generation f g) o)) => Setoid (Generation f g o)

instance Casting (->) (Generation f g) where
	(=-) (Generation m) = m
	(-=) m = Generation m

pattern Generate :: f (Identity o) (FG g (Generation f g) o) -> Generation f g o
pattern Generate xs <- Generation (FFGH xs) where Generate xs = Generation (FFGH xs)

instance
	( forall o . Functor (-->) (-->) (Straight f o)
	, forall o . Functor (-->) (-->) (Opposite f o)
	, Covariant Straight Functor g (->) (->)
	) => Functor (-->) (-->) (Generation f g) where
	map (Straight m) = Straight . (=-=) . (=-=) .: (->>--) m . (-->--) ((=-=) (m ->>-))

instance
	( forall o . Functor (-->) (-->) (Straight f o)
	, forall o . Functor (-->) (-->) (Opposite f o)
	, Covariant Straight Functor g (->) (->)
	, Semimonoidal Functor f f (-->) (-->) h
	-- TODO: how did we get to this?
	, Bindable Functor (->) (->) h
	, Traversable Functor (->) (->) h g
	) => Functor ((-/->) h) ((-/->) h) (Generation f g) where
	map (Kleisli (Straight m)) = Kleisli . Straight .: \(Generation (FFGH xs)) ->
		let new = (\(FG x) -> FG ->- (m -/>>/- x)) -->-- (m -/>/-) ->-- xs in
		Generation . FFGH ->- component @(-->) @(Day (-->) h h f f) =- Day new identity

type Construction = Generation (:*:)

pattern Construct :: o -> f (Construction f o) -> Construction f o
pattern Construct x xs <- Generate (Identity x :*: FG xs)
	where Construct x xs = Generate ...: Identity x :*: FG xs

type Instruction = Generation (:+:)

pattern Instruct :: f (Instruction f o) -> Instruction f o
pattern Instruct xs <- Generate (That (FG xs))
	where Instruct xs = Generate . That .: FG xs

pattern Load :: o -> Instruction f o
pattern Load x <- Generate (This (Identity x))
	where Load x = Generate . This .: Identity x

instance Covariant Straight Functor f (->) (->) => Component (-->) f (Instruction f) where
	component = Straight .: \x -> Instruct ...: Load ->- x
