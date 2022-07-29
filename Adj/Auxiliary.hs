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

newtype FG_ f g o = FG_ (f (g o))

type (=!?=) = FG_

type instance Casted (f =!?= g) a = f (g a)

instance Casting (->) (FG_ f g) where
	(=-) ~(FG_ x) = x
	(-=) = FG_

-- TODO: add underscore to names that indicate a number of parameters

newtype GF_ f g o = GF_ (g (f o))

type (=?!=) = GF_

type instance Casted (f =?!= g) a = g (f a)

instance Casting (->) (GF_ f g) where
	(=-) ~(GF_ x) = x
	(-=) = GF_

newtype FGF_ f g f' o = FGF_ (f (g (f' o)))

type (=!?!=) = FGF_

type instance Casted (FGF_ f g f') o = f (g (f' o))

instance Casting (->) (FGF_ f g f') where
	(=-) ~(FGF_ x) = x
	(-=) = FGF_

newtype FFGH_ f g h o = FFGH_ (f (g o) (h o))

type (=!!??=) = FFGH_

type instance Casted (FFGH_ f g h) o = f (g o) (h o)

instance Casting (->) (FFGH_ f g h) where
	(=-) ~(FFGH_ x) = x
	(-=) = FFGH_

newtype FGG_ f gg g o = FGG_ (f (gg g o))

type (=!??=) = FGG_

type instance Casted (FGG_ f gg g) o = f (gg g o)

instance Casting (->) (FGG_ f gg g) where
	(=-) ~(FGG_ x) = x
	(-=) = FGG_

newtype FFGH__ f g h l r = FFGH__ (f (g l) (h r))

type instance Casted (FFGH__ f g h l) r = f (g l) (h r)

instance Casting (->) (FFGH__ f g l r) where
	(=-) ~(FFGH__ x) = x
	(-=) = FFGH__

newtype Structural o = Structural o

data I = I | II | III | IIII
	| IIIII | IIIIII | IIIIIII
	| IIIIIIII | IIIIIIIII

newtype Tagged tag o = Tagged o

type instance Casted (Tagged tag) o = o

instance Casting (->) (Tagged tag) where
	(=-) (Tagged x) = x
	(-=) x = Tagged x
