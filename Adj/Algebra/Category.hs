{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Adj.Algebra.Category where

infixr 6 <-\-, -/->
infixr 7 :*:, :+:, <--, -->
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

type family Betwixt from to = btw | btw -> from to where
	Betwixt category category = category

class (Category from, Category to) => Functor from to f where
	map :: from source target -> to (f source) (f target)

	(-|) :: from source target -> to (f source) (f target)
	(-|) = map
	
	(-|-|)
		:: Functor from (Betwixt from to) f 
		=> Functor from (Betwixt from to) g
		=> Functor (Betwixt from to) from f
		=> Functor (Betwixt from to) from g
		=> from source target -> from (f (g source)) (f (g target))
	(-|-|) m = ((-|) ((-|) @from @(Betwixt from to) m))
	
	(-|-|-|)
		:: Functor from (Betwixt from (Betwixt from to)) h
		=> Functor (Betwixt from (Betwixt from to)) (Betwixt (Betwixt from to) to) g
		=> Functor (Betwixt (Betwixt from to) to) to f
		=> from source target -> to (f (g (h source))) (f (g (h target)))
	(-|-|-|) m = ((-|) @(Betwixt (Betwixt from to) to) @to ((-|) @(Betwixt from (Betwixt from to)) @(Betwixt (Betwixt from to) to) @_ ((-|) @from @(Betwixt from (Betwixt from to)) @_ m)))

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

type family Unit p = r | r -> p where
	Unit (:*:) = Terminal
	Unit (:+:) = Initial

instance Category (->) where
	identity = \x -> x

instance Semigroupoid (->) where
	g . f = \x -> g (f x)

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

(|->) :: Covariant Functor (->) (->) f => f s -> (s -> t) -> f t
x |-> m = let Flat change = (-|) (Flat m) in change x

(|-|->) :: (Covariant Functor (->) (->) f, Covariant Functor (->) (->) f') => f (f' s) -> (s -> t) -> f (f' t)
x |-|-> m = let Flat change = (-|-|) (Flat m) in change x

(|-|-|->) :: (Covariant Functor (->) (->) f, Covariant Functor (->) (->) f', Covariant Functor (->) (->) f'') => f (f' (f'' s)) -> (s -> t) -> f (f' (f'' t))
x |-|-|-> m = let Flat change = (-|-|-|) (Flat m) in change x
