{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE EmptyCase #-}

module Adj.Algebra.Set where

import Adj.Auxiliary (type (<?>) ((<?>)), Structural (Structural), type (=!?=), type (=!?!=), type (=!!??=), FG (FG), FGF (FGF), FFGH (FFGH))

infixr 6 :+*:
infixr 7 :*:, :+:, =/=
infixr 8 ==
infixr 9 +, *

-- Cartesian product
data (:*:) l r = l :*: r

-- Disjoint union
data (:+:) l r = This l | That r

-- Canonical union
type (:+*:) l r = (l :+: r) :+: (l :*: r)

data Unit = Unit

boring :: o -> Unit
boring _ = Unit

data Void

absurd :: Void -> o
absurd x = case x of {}

type family Neutral p = r | r -> p where
	Neutral (:*:) = Unit
	Neutral (:+:) = Void

newtype Infinity = Infinity Infinity

{- |
> * Associativity: x + (y + z) ≡ (x + y) + z
-}

class Semigroup o where
	(+) :: o -> o -> o

{- |
> * Right absorption: zero + x ≡ x
> * Left absorption: x + zero ≡ x
-}

class Semigroup o => Monoid o where
	{-# MINIMAL zero #-}
	zero :: o

{- |
> * Right absorption: x + invert x ≡ zero
> * Left absorption: invert x + x ≡ zero
-}

class Monoid o => Group o where
	{-# MINIMAL invert #-}
	invert :: o -> o

	(-) :: o -> o -> o
	x - y = x + invert y

{- |
> * Reflexivity: x == x ≡ True
> * Symmetry: x == y ≡ y == x
> * Transitivity: x == y * y == z ≡ True --> x == z ≡ True
> * Negation: x /= y ≡ invert (x == y)
-}

class Setoid o where
	(==) :: o -> o -> Unit :+: Unit

	(=/=) :: o -> o -> Unit :+: Unit
	x =/= y = case x == y of
		This _ -> That Unit
		That _ -> This Unit

{- |
> * Left distributivity: x * (y + z) ≡ x * y + x * z
> * Right distributivity: (y + z) * x ≡ y * x + z * x
-}

class Semigroup o => Ringoid o where
	{-# MINIMAL (*) #-}
	(*) :: o -> o -> o

{- |
> When providing a new instance, you should ensure it satisfies:
> * Additive identity is a multiplicative annihilator: zero * x = x  * zero = zero
-}

class (Monoid o, Ringoid o) => Quasiring o where
	{-# MINIMAL one #-}
	one :: o

instance Setoid o => Setoid (Structural o) where
	Structural l == Structural r = l == r

instance Setoid Unit where
	_ == _ = This Unit

instance (Setoid l, Setoid r) => Setoid (l :+: r) where
	This l == This r = l == r
	That l == That r = l == r
	_ == _ = That Unit

instance (Setoid l, Setoid r) => Setoid (l :*: r) where
	(ll :*: lr) == (rl :*: rr) = (ll == rl) == (lr == rr)

deriving via (Structural (f (g o))) instance
	Setoid (f (g o)) => Setoid ((=!?=) f g o)

deriving via (Structural (f (g (f' o)))) instance
	Setoid (f (g (f' o))) => Setoid ((=!?!=) f g f' o)

type (=:*:=) = (=!!??=) (:*:)

type (=:+:=) = (=!!??=) (:+:)

type (=:+*:=) lf rf = (=:+:=) ((=:+:=) lf rf) ((=:*:=) lf rf)

deriving via (Structural (f (g o) (h o))) instance
	Setoid (f (g o) (h o)) => Setoid ((=!!??=) f g h o)
