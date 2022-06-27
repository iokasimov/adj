{-# LANGUAGE EmptyCase #-}

module Adj.Algebra.Set where

infixr 7 :*:, :+:

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
