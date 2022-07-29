{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Adj.Program.Primitive.Generation where

import Adj.Auxiliary (Casted, Casting ((=-), (-=)), type (=!?=), FG_ (FG_), type (=?!=), GF_ (GF_), FFGH_ (FFGH_), type (=!!??=), Structural (Structural))
import Adj.Algebra.Category (Semigroupoid ((.)), Category ((.:), (..:), (....:)), Functor (map), Transformation (transformation), Covariant, Traversable, Semimonoidal, Identity (Identity), type (-->), Straight (Straight), Opposite, (->>-), (->>>-), (->>>--), (-->>--), (=-=))
import Adj.Algebra.Set (Setoid, (:*:) ((:*:)), (:+:) (This, That))

newtype Generation f g o = Generation
	((=!!??=) f Identity (g =!?= Generation f g) o)

type instance Casted (Generation f g) o = (=!!??=) f Identity (g =!?= Generation f g) o

deriving via (Structural ((=!!??=) f Identity (g =!?= Generation f g) o))
	instance Setoid (f (Identity o) ((=!?=) g (Generation f g) o)) => Setoid (Generation f g o)

instance Casting (->) (Generation f g) where
	(=-) (Generation m) = m
	(-=) m = Generation m

pattern Generate :: f (Identity o) (FG_ g (Generation f g) o) -> Generation f g o
pattern Generate xs <- Generation (FFGH_ xs) where Generate xs = Generation (FFGH_ xs)

instance
	( forall o . Functor (-->) (-->) (Straight f o)
	, forall o . Functor (-->) (-->) (Opposite f o)
	, Covariant Straight Functor g (->) (->)
	) => Functor (-->) (-->) (Generation f g) where
	map (Straight m) = Straight . (=-=) . (=-=) .: (->>>--) m . (-->>--) ((=-=) (m ->>>-))

instance
	( forall o . Functor (-->) (-->) (Opposite f o)
	, forall o . Functor (-->) (-->) (Straight f o)
	, Functor (-->) (-->) g
	, Functor (-->) (-->) h
	, Semimonoidal Functor f f (-->) (-->) (-->) h
	, Traversable Functor g h (-->)
	) => Transformation (-->) (-->) (Generation f g =!?= h) (Generation f g =?!= h) where
	transformation morphism = Straight .: \case
		FG_ (Generation xs) -> GF_ ....: Generation
			->>- (=-) ..: transformation @(-->) @(-->)
				@((=!!??=) f Identity (g =!?= Generation f g) =!?= h)
				@((=!!??=) f Identity (g =!?= Generation f g) =?!= h)
				morphism =- FG_ xs

type Construction = Generation (:*:)

pattern Construct :: o -> f (Construction f o) -> Construction f o
pattern Construct x xs <- Generate (Identity x :*: FG_ xs)
	where Construct x xs = Generate (Identity x :*: FG_ xs)

-- TODO: instance Transformation (-->) (-->) (Construction f) f where

type Instruction = Generation (:+:)

pattern Instruct :: f (Instruction f o) -> Instruction f o
pattern Instruct xs <- Generate (That (FG_ xs))
	where Instruct xs = Generate (That (FG_ xs))

pattern Load :: o -> Instruction f o
pattern Load x <- Generate (This (Identity x))
	where Load x = Generate (This (Identity x))

instance Covariant Straight Functor f (->) (->)
	=> Transformation (-->) (-->) f (Instruction f) where
		transformation (Straight morphism) =
			Straight .: Instruct . (Load . morphism ->>-)
