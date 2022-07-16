{-# LANGUAGE AllowAmbiguousTypes #-}

module Adj.Auxiliary where

infixl 8 .:, =-, -=

infixr 6 =!?=
infixr 5 =!?!=
infixr 4 =!!??=

infixr 6 <?>

type (.:) oo o = oo o
type (..:) oo o = oo o
type (...:) oo o = oo o
type (....:) oo o = oo o
type (.....:) oo o = oo o
type (......:) oo o = oo o
type (.......:) oo o = oo o
type (........:) oo o = oo o

class c <?> d where
	(<?>) :: (c => r) -> (d => r) -> r

type family Casted (f :: * -> *) a

class Casting m t where
	{-# MINIMAL (=-), (-=) #-}
	(=-) :: m .: t a .: Casted t a
	(-=) :: m .: Casted t a .: t a

newtype FG f g o = FG (f (g o))

type (=!?=) = FG

type instance Casted (f =!?= g) a = f (g a)

instance Casting (->) (FG f g) where
	(=-) ~(FG x) = x
	(-=) = FG

newtype FGF f g f' o = FGF (f (g (f' o)))

type (=!?!=) = FGF

type instance Casted (FGF f g f') a = f (g (f' a))

instance Casting (->) (FGF f g f') where
	(=-) ~(FGF x) = x
	(-=) = FGF

newtype FFGH f g h o = FFGH (f (g o) (h o))

type (=!!??=) = FFGH

type instance Casted (FFGH f g h) o = f (g o) (h o)

instance Casting (->) (FFGH f g h) where
	(=-) ~(FFGH x) = x
	(-=) = FFGH

newtype FGG f gg g o = FGG (f (gg g o))

type (=!??=) = FGG

type instance Casted (FGG f gg g) o = f (gg g o)

instance Casting (->) (FGG f gg g) where
	(=-) ~(FGG x) = x
	(-=) = FGG

newtype Structural o = Structural o

data I = I | II | III | IIII | IIIII | IIIIII | IIIIIII | IIIIIIII | IIIIIIIII
