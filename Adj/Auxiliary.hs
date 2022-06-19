module Adj.Auxiliary where

infixl 8 .:, =-, -=

infixr 7 |.:.|
infixr 6 |.:|

type (.:) oo o = oo o

class Casting m t where
	{-# MINIMAL (=-), (-=) #-}
	type Primary t a

	(=-) :: m .: t a .: Primary t a
	(-=) :: m .: Primary t a .: t a

newtype FG f g a = FG (f (g a))

type (|.:|) = FG

instance Casting (->) (FG f g) where
	type Primary (FG f g) a = f (g a)
	(=-) ~(FG x) = x
	(-=) = FG

newtype FGF f g f' o = FGF (f (g (f' o)))

type (|.:.|) = FGF

instance Casting (->) (FGF f g f') where
	type Primary (FGF f g f') a = f (g (f' a))
	(=-) ~(FGF x) = x
	(-=) = FGF
