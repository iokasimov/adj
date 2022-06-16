module Adj.Auxiliary where

infixl 7 =-=, -=-
infixl 8 .:, =-, -=

type (.:) oo o = oo o

class Casting t where
	{-# MINIMAL (=-), (-=) #-}
	type Primary t a

	(=-) :: t a -> Primary t a
	(-=) :: Primary t a -> t a

	(=-=) :: (Primary t a -> Primary t b) -> t a -> t b
	m =-= x = (-=) (m ((=-) x))
	
	(-=-) :: (t a -> t b) -> Primary t a -> Primary t b
	m -=- x = (=-) (m ((-=) x))

newtype TU ct cu t u a = TU (t (u a))

instance Casting (TU ct cu t u) where
	type Primary (TU ct cu t u) a = t (u a)
	(=-) ~(TU x) = x
	(-=) = TU
