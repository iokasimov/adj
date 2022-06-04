{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
module Adj.Algebra.Category where

infixr 7 :*:, :+:
infixl 8 .:
infixr 9 .

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

class (Category from, Category to) => Functor from to functor where
	map :: from source target -> to (functor source) (functor target)

newtype Flat morphism source target = Flat (morphism source target)

instance Semigroupoid morhism => Semigroupoid (Flat morhism) where
	Flat g . Flat f = Flat .: g . f

instance Category morhism => Category (Flat morhism) where
	identity = Flat identity

newtype Dual morphism source target = Dual (morphism target source)

instance Semigroupoid morhism => Semigroupoid (Dual morhism) where
	Dual g . Dual f = Dual .: f . g

instance Category morhism => Category (Dual morhism) where
	identity = Dual identity

newtype Kleisli effect morphism source target = Kleisli (morphism source (effect target))

instance Functor (Kleisli functor target) target functor
	=> Semigroupoid (Kleisli functor target) where
		g . Kleisli f = Kleisli .: map g . f

type family Covariant x source target functor where
	Covariant Functor source target functor =
		Functor (Flat source) (Flat target) functor

type family Contravariant x source target functor where
	Contravariant Functor source target functor =
		Functor (Flat source) (Dual target) functor

-- TODO: we need a monoidal functor here
-- instance Category (Kleisli functor target) where

type (-->) = Flat (->)
type (<--) = Dual (->)
type (-/->) t = Kleisli t (-->)
type (<-\-) t = Kleisli t (<--)

data (:*:) left right = left :*: right

data (:+:) left right = Option left | Adoption right

data Initial

data Terminal = Terminal

type family Unit (p :: * -> * -> *) = r | r -> p
type instance Unit (:*:) = Terminal
type instance Unit (:+:) = Initial

instance Functor (-->) (-->) ((Flat (:*:)) left) where
	map (Flat m) = Flat .: \case
		Flat (left :*: right) -> Flat (left :*: m right)

instance Functor (-->) (-->) ((Flat (:+:)) left) where
	map (Flat m) = Flat .: \case
		Flat (Option left) -> Flat (Option left)
		Flat (Adoption right) -> Flat (Adoption .: m right)

instance Functor (-->) (-->) ((Dual (:*:)) right) where
	map (Flat m) = Flat .: \case
		Dual (left :*: right) -> Dual (m left :*: right)

instance Functor (-->) (-->) ((Dual (:+:)) right) where
	map (Flat m) = Flat .: \case
		Dual (Option left) -> Dual (Option .: m left)
		Dual (Adoption right) -> Dual (Adoption right)

instance Category (->) where
	identity = \x -> x

instance Semigroupoid (->) where
	g . f = \x -> g (f x)
