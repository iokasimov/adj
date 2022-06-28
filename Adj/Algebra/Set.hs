{-# LANGUAGE EmptyCase #-}

module Adj.Algebra.Set where

infixr 7 :*:, :+:, =/=
infixr 8 ==
infixr 9 +

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
