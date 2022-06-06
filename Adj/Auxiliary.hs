module Adj.Auxiliary where

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
