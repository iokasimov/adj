module Adj.Auxiliary where

infixl 8 .:, =-, -=

type (.:) oo o = oo o

class Casting m t where
	{-# MINIMAL (=-), (-=) #-}
	type Primary t a

	(=-) :: m .: t a .: Primary t a
	(-=) :: m .: Primary t a .: t a

newtype TU t u a = TU (t (u a))

instance Casting (->) (TU t u) where
	type Primary (TU t u) a = t (u a)
	(=-) ~(TU x) = x
	(-=) = TU
