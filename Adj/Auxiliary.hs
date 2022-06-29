{-# LANGUAGE AllowAmbiguousTypes #-}

module Adj.Auxiliary where

infixl 8 .:, =-, -=

infixr 6 =!?=
infixr 5 =!?!=
infixr 4 =!!??=

infixr 2 ||

type (.:) oo o = oo o
type (..:) oo o = oo o
type (...:) oo o = oo o
type (....:) oo o = oo o
type (.....:) oo o = oo o
type (......:) oo o = oo o
type (.......:) oo o = oo o
type (........:) oo o = oo o

class c || d where
    resolve :: (c => r) -> (d => r) -> r

class Casting m t where
	{-# MINIMAL (=-), (-=) #-}
	type Primary t a

	(=-) :: m .: t a .: Primary t a
	(-=) :: m .: Primary t a .: t a

newtype FG f g o = FG (f (g o))

type (=!?=) = FG

instance Casting (->) (FG f g) where
	type Primary (f =!?= g) a = f (g a)
	(=-) ~(FG x) = x
	(-=) = FG

newtype FGF f g f' o = FGF (f (g (f' o)))

type (=!?!=) = FGF

instance Casting (->) (FGF f g f') where
	type Primary (FGF f g f') a = f (g (f' a))
	(=-) ~(FGF x) = x
	(-=) = FGF

newtype FFGH f g h o = FFGH (f (g o) (h o))

type (=!!??=) = FFGH

instance Casting (->) (FFGH f g h) where
	type Primary (FFGH f g h) o = f (g o) (h o)
	(=-) ~(FFGH x) = x
	(-=) = FFGH

newtype FGG f gg g o = FGG (f (gg g o))

type (=!??=) = FGG

instance Casting (->) (FGG f gg g) where
	type Primary (FGG f gg g) o = f (gg g o)
	(=-) ~(FGG x) = x
	(-=) = FGG

newtype Structural o = Structural o
