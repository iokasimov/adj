module Adj.Auxiliary where

infixl 8 .:, =-, -=

infixr 6 |.:|

type (.:) oo o = oo o

type (|.:|) = FG

class Casting m t where
	{-# MINIMAL (=-), (-=) #-}
	type Primary t a

	(=-) :: m .: t a .: Primary t a
	(-=) :: m .: Primary t a .: t a

newtype FG f g a = FG (f (g a))

instance Casting (->) (FG f g) where
	type Primary (FG f g) a = f (g a)
	(=-) ~(FG x) = x
	(-=) = FG
