module Adj.Program.Casting where

import Adj.Algebra (Flat (Flat), Dual (Dual), Kleisli (Kleisli))

infixl 7 =-=, -=-
infixl 8 =-, -=

class Casting t where
	{-# MINIMAL (=-), (-=) #-}
	type Primary t a :: *
	(=-) :: t a -> Primary t a
	(-=) :: Primary t a -> t a

	(=-=) :: (Primary t a -> Primary t b) -> t a -> t b
	m =-= x = (-=) (m ((=-) x))
	
	(-=-) :: (t a -> t b) -> Primary t a -> Primary t b
	m -=- x = (=-) (m ((-=) x))

instance Casting (Flat morphism source) where
	type Primary (Flat morphism source) target = morphism source target
	(=-) (Flat m) = m
	(-=) m = Flat m

instance Casting (Dual morphism target) where
	type Primary (Dual morphism target) source = morphism source target
	(=-) (Dual m) = m
	(-=) m = Dual m

instance Casting (Kleisli effect morphism source) where
	type Primary (Kleisli effect morphism source) target = morphism source (effect target)
	(=-) (Kleisli m) = m
	(-=) m = Kleisli m
