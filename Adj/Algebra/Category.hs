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

class Semigroupoid morphism where
	(.) :: morphism between target
		-> morphism source between
		-> morphism source target

{- |
> * Left identity: identity . f ≡ f
> * Right identity: f . identity ≡ f
-}

class Semigroupoid morphism => Category morphism where
	identity :: morphism source source

	(.:) :: morphism (morphism source target) (morphism source target)
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
	(-|-|) morphism 
		= map @(Betwixt from to) @from
		. map @from @(Betwixt from to)
		.: morphism

	(-|-|-|)
		:: Functor from (Betwixt from (Betwixt from to)) h
		=> Functor (Betwixt from (Betwixt from to)) (Betwixt (Betwixt from to) to) g
		=> Functor (Betwixt (Betwixt from to) to) to f
		=> from source target -> to (f (g (h source))) (f (g (h target)))
	(-|-|-|) morphism
		= map @(Betwixt (Betwixt from to) to) @to
		. map @(Betwixt from (Betwixt from to)) @(Betwixt (Betwixt from to) to)
		. map @from @(Betwixt from (Betwixt from to)) 
		.: morphism

class (Functor category category f, Functor category category g) => Component category f g where
	component :: category (f object) (g object)

{- |
> * Associativity: (-|) morphism . component = component . (-|) morphism
-}

class (Functor from to f, Functor from to g) => Transformation from to f g where
	transformation :: from source target -> to (f source) (g target)

newtype Flat morphism source target = Flat (morphism source target)

instance Casting (Flat morphism source) where
	type Primary (Flat morphism source) target = morphism source target
	(=-) (Flat m) = m
	(-=) m = Flat m

instance Semigroupoid morhism => Semigroupoid (Flat morhism) where
	Flat g . Flat f = Flat .: g . f

instance Category morhism => Category (Flat morhism) where
	identity = Flat identity

newtype Dual morphism source target = Dual (morphism target source)

instance Casting (Dual morphism target) where
	type Primary (Dual morphism target) source = morphism source target
	(=-) (Dual m) = m
	(-=) m = Dual m

instance Semigroupoid morhism => Semigroupoid (Dual morhism) where
	Dual g . Dual f = Dual .: f . g

instance Category morhism => Category (Dual morhism) where
	identity = Dual identity

newtype Kleisli effect morphism source target = Kleisli (morphism source (effect target))

instance Casting (Kleisli effect morphism source) where
	type Primary (Kleisli effect morphism source) target = morphism source (effect target)
	(=-) (Kleisli m) = m
	(-=) m = Kleisli m

instance Functor (Kleisli functor target) target functor
	=> Semigroupoid (Kleisli functor target) where
		g . Kleisli f = Kleisli .: map g . f

newtype Tensor effect from to morphism source target = 
	Tensor (morphism (from (effect source) (effect target)) (effect (to source target)))

type family Covariant x source target functor where
	Covariant Functor source target functor =
		Functor (Flat source) (Flat target) functor

type family Contravariant x source target functor where
	Contravariant Functor source target functor =
		Functor (Flat source) (Dual target) functor

type family Semimonoidal x from to morphism functor where
	Semimonoidal Component from to morphism functor =
		Component (Tensor functor from to morphism) functor functor

-- TODO: we need a monoidal functor here
-- instance Category (Kleisli functor target) where

type (-->) = Flat (->)

type (<--) = Dual (->)

type (-/->) t = Kleisli t (-->)

type (<-\-) t = Kleisli t (<--)

data (:*:) left right = left :*: right

data (:+:) left right = This left | That right

data Initial

data Terminal = Terminal

type family Unit p = r | r -> p where
	Unit (:*:) = Terminal
	Unit (:+:) = Initial

instance Category (->) where
	identity = \x -> x

instance Semigroupoid (->) where
	g . f = \x -> g (f x)

type (-*~*->) t = Tensor t (:*:) (:*:) (-->)

type (-+~*->) t = Tensor t (:+:) (:*:) (-->)

type (-*~+->) t = Tensor t (:*:) (:+:) (-->)

type (-+~+->) t = Tensor t (:+:) (:+:) (-->)

instance Functor (-->) (-->) ((Flat (:*:)) left) where
	map (Flat m) = Flat .: \case
		Flat (left :*: right) -> Flat (left :*: m right)

instance Functor (-->) (-->) ((Flat (:+:)) left) where
	map (Flat m) = Flat .: \case
		Flat (This left) -> Flat (This left)
		Flat (That right) -> Flat (That .: m right)

instance Functor (-->) (-->) ((Dual (:*:)) right) where
	map (Flat m) = Flat .: \case
		Dual (left :*: right) -> Dual (m left :*: right)

instance Functor (-->) (-->) ((Dual (:+:)) right) where
	map (Flat m) = Flat .: \case
		Dual (This left) -> Dual (This .: m left)
		Dual (That right) -> Dual (That right)

(|->) :: Covariant Functor (->) (->) f => f s -> (s -> t) -> f t
x |-> m = (-|) @(-->) @(-->) (Flat m) =- x

(|-|->) :: (Covariant Functor (->) (->) f, Covariant Functor (->) (->) g) => f (g s) -> (s -> t) -> f (g t)
x |-|-> m = (-|-|) @(-->) @(-->) (Flat m) =- x

(|-|-|->) :: (Covariant Functor (->) (->) f, Covariant Functor (->) (->) g, Covariant Functor (->) (->) h) => f (g (h s)) -> (s -> t) -> f (g (h t))
x |-|-|-> m = (-|-|-|) @(-->) @(-->) (Flat m) =- x
