{-# LANGUAGE AllowAmbiguousTypes #-}

module Adj.Auxiliary where

infixl 8 =-, -=

infixl 8 .:
infixl 7 ..:
infixl 6 ...:
infixl 5 ....:
infixl 4 .....:
infixl 3 ......:
infixl 2 .......:
infixl 1 ........:

infixr 8 :.
infixr 7 :..
infixr 6 :...
infixr 5 :....
infixr 4 :.....
infixr 3 :......
infixr 2 :.......
infixr 1 :........

infixr 6 =!?=
infixr 5 =!?!=
infixr 4 =!!??=

type (.:) oo o = oo o
type (..:) oo o = oo o
type (...:) oo o = oo o
type (....:) oo o = oo o
type (.....:) oo o = oo o
type (......:) oo o = oo o
type (.......:) oo o = oo o
type (........:) oo o = oo o

type (:.) oo o = oo o
type (:..) oo o = oo o
type (:...) oo o = oo o
type (:....) oo o = oo o
type (:.....) oo o = oo o
type (:......) oo o = oo o
type (:.......) oo o = oo o
type (:........) oo o = oo o

type family Casted (f :: * -> *) a

class Casting m t where
	{-# MINIMAL (=-), (-=) #-}
	(=-) :: m .: t a .: Casted t a
	(-=) :: m .: Casted t a .: t a

-- TODO: newtype FF f o = f (f o)

newtype FG f g o = FG (f (g o))

type (=!?=) = FG

type instance Casted (f =!?= g) a = f (g a)

instance Casting (->) (FG f g) where
	(=-) ~(FG x) = x
	(-=) = FG

newtype GF f g o = GF (g (f o))

type (=?!=) = GF

type instance Casted (f =?!= g) a = g (f a)

instance Casting (->) (GF f g) where
	(=-) ~(GF x) = x
	(-=) = GF

newtype FGF f g f' o = FGF (f (g (f' o)))

type (=!?!=) = FGF

type instance Casted (FGF f g f') o = f (g (f' o))

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

newtype FGFH f g h l r = FGFH (f (g l) (h r))

type instance Casted (FGFH f g h l) r = f (g l) (h r)

instance Casting (->) (FGFH f g l r) where
	(=-) ~(FGFH x) = x
	(-=) = FGFH

newtype Structural o = Structural o

data I = I | II | III | IIII
	| IIIII | IIIIII | IIIIIII
	| IIIIIIII | IIIIIIIII

newtype Tagged tag o = Tagged o

type instance Casted (Tagged tag) o = o

instance Casting (->) (Tagged tag) where
	(=-) (Tagged x) = x
	(-=) x = Tagged x
