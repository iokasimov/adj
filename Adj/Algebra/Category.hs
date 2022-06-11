{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Adj.Algebra.Category where

import Adj.Auxiliary (Casting (Primary, (-=), (=-)))

infixl 8 .:
infixr 9 .

infixr 6 <-\-, -/->
infixr 7 <--, -->

infixr 7 :*:, :+:

infixl 4 -|-|-|
infixl 6 -|-|
infixl 8 -|

{- |
> * Associativity: f . (g . h) ≡ (f . g) . h
-}

class Semigroupoid m where
	(.) :: m between target
		-> m source between
		-> m source target

{- |
> * Left identity: identity . f ≡ f
> * Right identity: f . identity ≡ f
-}

class Semigroupoid m => Category m where
	identity :: m source source

	(.:) :: m (m source target) (m source target)
	(.:) = identity

{- |
> * Identity preserving: map identity ≡ identity
> * Composition preserving: map (f . g) ≡ map f . map g
-}

type family Betwixt from to = btw | btw -> from to where
	Betwixt category category = category

class (Category from, Category to) => Functor from to f where
	map :: from source target -> to (f source) (f target)

	(-|) :: from source target -> to (f source) (f target)
	(-|) = map @from @to

	(-|-|)
		:: Functor from (Betwixt from to) f
		=> Functor from (Betwixt from to) g
		=> Functor (Betwixt from to) from f
		=> Functor (Betwixt from to) from g
		=> from source target -> from (f (g source)) (f (g target))
	(-|-|) m
		= map @(Betwixt from to) @from
		. map @from @(Betwixt from to)
		.: m

	(-|-|-|)
		:: Functor from (Betwixt from (Betwixt from to)) h
		=> Functor (Betwixt from (Betwixt from to)) (Betwixt (Betwixt from to) to) g
		=> Functor (Betwixt (Betwixt from to) to) to f
		=> from source target -> to (f (g (h source))) (f (g (h target)))
	(-|-|-|) m
		= map @(Betwixt (Betwixt from to) to) @to
		. map @(Betwixt from (Betwixt from to)) @(Betwixt (Betwixt from to) to)
		. map @from @(Betwixt from (Betwixt from to))
		.: m

class Component m f g where
	component :: m (f object) (g object)

{- |
> * Associativity: (-|) m . component = component . (-|) m
-}

class (Functor from to f, Functor from to g) => Transformation from to f g where
	transformation :: from source target -> to (f source) (g target)

newtype Flat m source target = Flat (m source target)

instance Casting (Flat m source) where
	type Primary (Flat m source) target = m source target
	(=-) (Flat m) = m
	(-=) m = Flat m

instance Semigroupoid morhism => Semigroupoid (Flat morhism) where
	Flat g . Flat f = Flat .: g . f

instance Category morhism => Category (Flat morhism) where
	identity = Flat identity

newtype Dual m source target = Dual (m target source)

instance Casting (Dual m target) where
	type Primary (Dual m target) source = m source target
	(=-) (Dual m) = m
	(-=) m = Dual m

instance Semigroupoid morhism => Semigroupoid (Dual morhism) where
	Dual g . Dual f = Dual .: f . g

instance Category morhism => Category (Dual morhism) where
	identity = Dual identity

newtype Kleisli f m source target =
	Kleisli (m source (f target))

instance Casting (Kleisli f m source) where
	type Primary (Kleisli f m source) target =
		m source (f target)
	(=-) (Kleisli m) = m
	(-=) m = Kleisli m

instance Functor (Kleisli f target) target f
	=> Semigroupoid (Kleisli f target) where
		g . Kleisli f = Kleisli .: map g . f

type family Covariant x source target f where
	Covariant Functor source target f =
		Functor (Flat source) (Flat target) f

type family Contravariant x source target f where
	Contravariant Functor source target f =
		Functor (Flat source) (Dual target) f

type family Semimonoidal x from to morhism f where
	Semimonoidal Functor from to morhism f =
		Component (Flat morhism) (Day (Flat morhism) f f from to) f

type family Monoidal x from to morhism f where
	Monoidal Functor from to morhism f =
		( Component (Flat morhism) (Day (Flat morhism) f f from to) f
		, Component (Flat morhism) (Day (Flat morhism) Identity f from to) f
		, Component (Flat morhism) (Day (Flat morhism) f Identity from to) f
		, Component (Flat morhism) (Day (Flat morhism) Identity Identity from to) f
		)

-- instance (Functor (Kleisli f target) target f, Monoidal Functor (:*:) (:*:) (-->) f) => Category (Kleisli f target) where

type (-->) = Flat (->)

type (<--) = Dual (->)

type (-/->) t = Kleisli t (-->)

type (<-\-) t = Kleisli t (<--)

data (:*:) l r = l :*: r

type (:*:.) = Flat (:*:)

type (.:*:) = Dual (:*:)

data (:+:) l r = This l | That r

type (:+:.) = Flat (:+:)

type (.:+:) = Dual (:+:)

data Initial

data Terminal = Terminal

type family Unit p = r | r -> p where
	Unit (:*:) = Terminal
	Unit (:+:) = Initial

instance Category (->) where
	identity = \x -> x

instance Semigroupoid (->) where
	g . f = \x -> g (f x)

newtype Identity o = Identity o

instance Functor (-->) (-->) Identity where
	map (Flat m) = Flat .: \case
		Identity x -> Identity .: m x

data Day m f g from to result where
	Day :: from (f l) (g r)
		-> m (to l r) result
		-> Day m f g from to result

instance Functor (-->) (-->) (Day (-->) f g from to) where
	map m = Flat .: \case
		Day from to -> Day from .: m . to

instance Functor (-->) (-->) ((:*:.) l) where
	map (Flat m) = Flat .: \case
		Flat (l :*: r) -> Flat (l :*: m r)

instance Functor (-->) (-->) ((:+:.) l) where
	map (Flat m) = Flat .: \case
		Flat (This l) -> Flat (This l)
		Flat (That r) -> Flat (That .: m r)

instance Functor (-->) (-->) ((.:*:) r) where
	map (Flat m) = Flat .: \case
		Dual (l :*: r) -> Dual (m l :*: r)

instance Functor (-->) (-->) ((.:+:) r) where
	map (Flat m) = Flat .: \case
		Dual (This l) -> Dual (This .: m l)
		Dual (That r) -> Dual (That r)

instance Component (-->) (Day (-->) Identity Identity (:*:) (:*:)) Identity where
	component = Flat .: \case
		Day (Identity l :*: Identity r) (Flat m) -> Identity .: m (l :*: r)

instance Component (-->) (Day (-->) ((:+:.) l) ((:+:.) l) (:*:) (:*:)) ((:+:.) l) where
	component = Flat .: \case
		Day (Flat (That l) :*: Flat (That r)) (Flat m) -> Flat . That .: m (l :*: r)
		Day (Flat (This l) :*: _) _ -> Flat . This .: l
		Day (_ :*: Flat (This r)) _ -> Flat . This .: r

instance Component (-->) (Day (-->) ((:+:.) l) Identity (:*:) (:*:)) ((:+:.) l) where
	component = Flat .: \case
		Day (Flat (That l) :*: Identity r) (Flat m) -> Flat . That .: m (l :*: r)
		Day (Flat (This l) :*: _) _ -> Flat . This .: l

instance Component (-->) (Day (-->) Identity ((:+:.) l) (:*:) (:*:)) ((:+:.) l) where
	component = Flat .: \case
		Day (Identity l :*: Flat (That r)) (Flat m) -> Flat . That .: m (l :*: r)
		Day (_ :*: Flat (This r)) _ -> Flat . This .: r

instance Component (-->) (Day (-->) Identity Identity (:*:) (:*:)) ((:+:.) l) where
	component = Flat .: \case
		Day (Identity l :*: Identity r) (Flat m) -> Flat . That .: m (l :*: r)

instance Component (-->) (Day (-->) ((.:+:) r) ((.:+:) r) (:*:) (:*:)) ((.:+:) r) where
	component = Flat .: \case
		Day (Dual (This l) :*: Dual (This r)) (Flat m) -> Dual . This .: m (l :*: r)
		Day (Dual (That l) :*: _) _ -> Dual . That .: l
		Day (_ :*: Dual (That r)) _ -> Dual . That .: r

instance Component (-->) (Day (-->) ((.:+:) r) Identity (:*:) (:*:)) ((.:+:) r) where
	component = Flat .: \case
		Day (Dual (This l) :*: Identity r) (Flat m) -> Dual . This .: m (l :*: r)
		Day (Dual (That l) :*: _) _ -> Dual . That .: l

instance Component (-->) (Day (-->) Identity ((.:+:) r) (:*:) (:*:)) ((.:+:) r) where
	component = Flat .: \case
		Day (Identity l :*: Dual (This r)) (Flat m) -> Dual . This .: m (l :*: r)
		Day (_ :*: Dual (That r)) _ -> Dual . That .: r

instance Component (-->) (Day (-->) Identity Identity (:*:) (:*:)) ((.:+:) r) where
	component = Flat .: \case
		Day (Identity l :*: Identity r) (Flat m) -> Dual . This .: m (l :*: r)

(|->) :: Covariant Functor (->) (->) f => f s -> (s -> t) -> f t
x |-> m = (-|) @(-->) @(-->) (Flat m) =- x

(|-|->) :: (Covariant Functor (->) (->) f, Covariant Functor (->) (->) g) => f (g s) -> (s -> t) -> f (g t)
x |-|-> m = (-|-|) @(-->) @(-->) (Flat m) =- x

(|-|-|->) :: (Covariant Functor (->) (->) f, Covariant Functor (->) (->) g, Covariant Functor (->) (->) h) => f (g (h s)) -> (s -> t) -> f (g (h t))
x |-|-|-> m = (-|-|-|) @(-->) @(-->) (Flat m) =- x
