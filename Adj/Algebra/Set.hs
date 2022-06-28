{-# LANGUAGE EmptyCase #-}

module Adj.Algebra.Set where

infixr 7 :*:, :+:, =/=
infixr 8 ==
infixr 9 +, *

-- Cartesian product
data (:*:) l r = l :*: r

-- Disjoint union
data (:+:) l r = This l | That r

data Unit = Unit

boring :: o -> Unit
boring _ = Unit

data Void

absurd :: Void -> o
absurd x = case x of {}

type family Neutral p = r | r -> p where
	Neutral (:*:) = Unit
	Neutral (:+:) = Void

{- |
> * Associativity: x + (y + z) ≡ (x + y) + z
-}

class Semigroup o where
	(+) :: o -> o -> o

{- |
> * Right absorption: zero + x ≡ x
> * Left absorption: x + zero ≡ x
-}

class Semigroup a => Monoid a where
	{-# MINIMAL zero #-}
	zero :: a

{- |
> * Right absorption: x + invert x ≡ zero
> * Left absorption: invert x + x ≡ zero
-}

class Monoid a => Group a where
	{-# MINIMAL invert #-}
	invert :: a -> a

	(-) :: a -> a -> a
	x - y = x + invert y

{- |
> * Reflexivity: x == x ≡ True
> * Symmetry: x == y ≡ y == x
> * Transitivity: x == y * y == z ≡ True --> x == z ≡ True
> * Negation: x /= y ≡ invert (x == y)
-}

-- TODO: Monoid => Group => Setoid
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

class Semigroup a => Ringoid a where
	{-# MINIMAL (*) #-}
	(*) :: a -> a -> a

{- |
> When providing a new instance, you should ensure it satisfies:
> * Additive identity is a multiplicative annihilator: zero * x = x  * zero = zero
-}

class (Monoid a, Ringoid a) => Quasiring a where
	one :: a
