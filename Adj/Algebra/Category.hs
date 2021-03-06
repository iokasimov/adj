{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Adj.Algebra.Category where

import Adj.Auxiliary (type (.:), type (=!?=), FG_ (FG_), type (=?!=), GF_ (GF_), type (=!?!=), type (=!!??=), FFGH_ (FFGH_), type Casted, Casting ((-=), (=-)))
import Adj.Algebra.Set ((:*:) ((:*:)), (:+:) (This, That), Unit (Unit), Neutral, absurd)

infixr 9 .
infixl 8 .:
infixl 7 ..:
infixl 6 ...:
infixl 5 ....:
infixl 4 .....:
infixl 3 ......:
infixl 2 .......:
infixl 1 ........:

infixr 6 <-\-, -/->
infixr 7 <--, -->, <->

infixr 6 <:*:, :*:>
infixr 6 <:+:, :+:>

infixl 3 --|||--
infixl 4 -|||--, --||--
infixl 5 -|||-, -||--, --|--
infixl 6 -||-, -|--
infixl 7 -|-

infixl 5 =----
infixl 6 =---
infixl 7 =-=, -=-, =--

infixl 1 --/>>>/--
infixl 2 --/>>/--, -/>>>/--
infixl 3 -->>>--, -/>>>/-, -/>>/--
infixl 4 -/>>/-, ->>>--, -->>--, -/>>>-, -/>>>/=
infixl 5 ->>>-, ->><-, -<>>-, ->>--
infixl 6 ->>-, -/>>-

infixr 5 -???-
infixr 6 -??-
infixr 7 -?-

infixl 3 <--||--
infixl 4 <-||--
infixl 5 <-||-
infixl 6 <-|-

infixr 5 |*|-|

{- |
> * Associativity: f . (g . h) ≡ (f . g) . h
-}

class Semigroupoid m where
	(.) :: m between target
		-> m source between
		-> m source target

{- |
> * Left identity: identity . f ≡ f
> * Right identity: f . identity ≡ f
-}

class Semigroupoid m => Category m where
	identity :: m source source

	(........:), (.......:), (......:),
		(.....:), (....:), (...:), (..:), (.:)
			:: m (m source target) (m source target)
	(........:) = identity
	(.......:) = identity
	(......:) = identity
	(.....:) = identity
	(....:) = identity
	(...:) = identity
	(..:) = identity
	(.:) = identity

{- |
> * Identity preserving: map identity ≡ identity
> * Composition preserving: map (f . g) ≡ map f . map g
-}

class (Category from, Category to) => Functor from to f where
	map :: from source target -> to .: f source .: f target

(-|-) :: forall from to f source target . Functor from to f
	=> from source target -> to .: f source .: f target
(-|-) = map @from @to @f

(-||-) :: forall from between to f g source target
	.  Functor .: from .: between .: g
	=> Functor .: between .: to .: f
	=> from source target -> to .: f (g source) .: f (g target)
(-||-) m = map @between @to @f . map @from @between @g .: m

(-|||-) :: forall from between between' to f g h source target
	.  Functor .: from .: between .: h
	=> Functor .: between .: between' .: g
	=> Functor .: between' .: to .: f
	=> from source target -> to .: f (g (h source)) .: f (g (h target))
(-|||-) m = map @between' @to @f . map @between @between' @g . map @from @between @h .: m

(-|--) :: forall from to f source target o
	. (Category to, Functor from to (Opposite f o), Casting to (Opposite f o))
	=> from source target -> to .: f source o .: f target o
(-|--) m = (-=-) ((-|-) @from @to @(Opposite f o) m)

(-||--) :: forall from between to f g source target o .
	( Casting to (Opposite f o)
	, Functor between to (Opposite f o)
	, Functor from between g
	) => from source target -> to .: f (g source) o .: f (g target) o
(-||--) m = (-=-) @to ((-||-) @from @between @to @(Opposite f o) @g @source @target m)

(-|||--) :: forall from between between' to f g h source target o .
	( Casting to (Opposite f o)
	, Functor .: from .: between .: h
	, Functor .: between .: between' .: g
	, Functor .: between' .: to .: Opposite f o
	) => from source target -> to .: f (g (h source)) o .: f (g (h target)) o
(-|||--) m = (-=-) ((-|||-) @from @between @between' @to @(Opposite f o) m)

(--|--) :: forall from to f source target o
	. (Category to, Functor from to (Straight f o), Casting to (Straight f o))
	=> from source target -> to .: f o source .: f o target
(--|--) m = (-=-) ((-|-) @from @to @(Straight f o) m)

(--||--) :: forall from between to f g source target o .
	( Category to, Casting to (Straight f o)
	, Functor from between g
	, Functor between to ((Straight f) o)
	) => from source target -> to .: f o (g source) .: f o (g target)
(--||--) m = (-=-) ((-||-) @from @between @to @(Straight f o) m)

(--|||--) :: forall from between between' to f g h source target o .
	( Category to, Casting to (Straight f o)
	, Functor .: from .: between .: h
	, Functor .: between .: between' .: g
	, Functor .: between' .: to .: Straight f o
	) => from source target -> to .: f o (g (h source)) .: f o (g (h target))
(--|||--) m = (-=-) ((-|||-) @from @between @between' @to @(Straight f o) m)

{- |
> * Associativity: (-|) m . component = component . (-|) m
-}

class (Functor from to f, Functor from to g) => Transformation from to f g where
	transformation :: from source target -> to .: f source .: g target

component :: forall from to f g object
	. (Category from, Category to, Transformation from to f g)
	=> to .: f object .: g object
component = transformation @from @to @f @g identity

-- TODO: find a way to define a horizontal composition without overlapped instances
-- instance
	-- ( Functor between to h
	-- , Functor between to i
	-- , Transformation from between f g
	-- , Transformation between to h i
	-- ) => Transformation from to (h =!?= f) (i =!?= g) where

-- TODO: find a way to define a vertical composition without overlapped instances
-- instance
	-- ( Functor from to f
	-- , Functor from to g
	-- , Functor from to h
	-- , Transformation from to f g
	-- , Transformation from to g h
	-- ) => Transformation from to f h where
--
newtype Straight m source target = Straight (m source target)

type instance Casted (Straight m source) target = m source target

instance Casting (->) (Straight m source) where
	(=-) (Straight m) = m
	(-=) m = Straight m

instance Semigroupoid morhism => Semigroupoid (Straight morhism) where
	Straight g . Straight f = Straight .: g . f

instance Category morhism => Category (Straight morhism) where
	identity = Straight identity

newtype Opposite m source target = Opposite (m target source)

type instance Casted (Opposite m target) source = m source target

instance Casting (->) (Opposite m target) where
	(=-) (Opposite m) = m
	(-=) m = Opposite m

instance Semigroupoid morhism => Semigroupoid (Opposite morhism) where
	Opposite g . Opposite f = Opposite .: f . g

instance Category morhism => Category (Opposite morhism) where
	identity = Opposite identity

newtype Endo m source target = Endo (m target target)

type instance Casted (Endo m source) target = m target target

instance Casting (->) (Endo m target) where
	(=-) (Endo m) = m
	(-=) m = Endo m

instance Category morphism => Semigroupoid (Endo morphism) where
	Endo _ . Endo _ = Endo identity

instance Category morphism => Category (Endo morphism) where
	identity = Endo identity

newtype Kleisli f m source target =
	Kleisli (m source .: f target)

type instance Casted ((-/->) f source) target = source -> f target

instance Casting (->) (Kleisli f (-->) source) where
	(=-) (Kleisli (Straight m)) = m
	(-=) m = Kleisli .: Straight m

instance Functor .: Kleisli f target .: target .: f
	=> Semigroupoid (Kleisli f target) where
		g . Kleisli f = Kleisli .: map g . f

instance
	( Monad f to
	, Transformation to to Identity f
	, Functor (Kleisli f to) to f
	, Casting to Identity
	) => Category (Kleisli f to) where
	identity = Kleisli .: return

type family Covariant m functor f from to where
	Covariant m Functor functor from to
		= Functor (m from) (m to) functor

type family Contravariant m functor f from to where
	Contravariant m Functor functor from to
		= Functor (m from) (OP (m to)) functor

type family OP direction where
	OP (Straight category) = Opposite category
	OP (Opposite category) = Straight category
	OP (Kleisli f (Straight category)) = Kleisli f (Opposite category)
	OP (Kleisli f (Opposite category)) = Kleisli f (Straight category)

type family Semimonoidal x source target from to tensor f where
	Semimonoidal Functor source target from to tensor f =
		(Functor from to f, Transformation .: from .: to .: Day tensor f f source target .: f)

type family Monoidal x source target from to tensor f where
	Monoidal Functor source target from to tensor f =
		( Functor from to f
		, Transformation .: from .: to .: Day tensor f f source target .: f
		, Transformation .: from .: to .: Day tensor Identity f source target .: f
		, Transformation .: from .: to .: Day tensor f Identity source target .: f
		, Transformation .: from .: to .: tensor (Neutral target) .: f
		)

type Monad f to = (Bindable Functor f to, Pointed Functor f to)

type Comonad f to =
	( Transformation .: Opposite to .: Opposite to .: FG_ f f .: f
	, Transformation .: Opposite to .: Opposite to .: Identity .: f
	)

type family Pointed x f to where
	Pointed Functor f to = Transformation .: to .: to .: Identity .: f

-- TODO: can we somehow include a notion about semigroupoids/semifunctors here?
type family Bindable x f to where
	Bindable Functor f to = Transformation .: to .: to .: FG_ f f .: f

-- TODO: we need to add laws here, maybe inherit them from functor composition
type family Traversable x f g to where
	Traversable Functor f g to =
		( Transformation .: to .: to .: FG_ f g .: GF_ f g
		, Functor .: to .: to .: f
		)

type family Adjunction f g from to where
	Adjunction f g from to =
		( Transformation .: to .: from .: FG_ f g .: Identity
		, Transformation .: from .: to .: Identity .: FG_ g f
		)

instance Semigroupoid (->) where
	g . f = \x -> g (f x)

instance Category (->) where
	identity = \x -> x

type (-->) = Straight (->)

instance Functor (-->) (-->) ((-->) i) where
	map m = Straight .: (m .)

instance Functor (<--) (<--) ((-->) i) where
	map (Opposite m) = Opposite .: (Straight m .)

type (<--) = Opposite (->)

instance Functor (-->) (<--) ((<--) o) where
	map (Straight m) = Opposite .: (Opposite m .)

instance Functor (<--) (-->) ((<--) o) where
	map (Opposite m) = Straight .: (Opposite m .)

type (<->) = Endo (->)

type (-/->) f = Kleisli f (-->)

type (<-\-) f = Kleisli f (<--)

newtype Identity o = Identity o

type instance Casted Identity o = o

instance Casting (->) Identity where
	(=-) (Identity x) = x
	(-=) x = Identity x

instance Functor (-->) (-->) Identity where
	map (Straight m) = Straight .: \case
		Identity x -> Identity .: m x

data Day m f g from to result where
	Day :: from (f l) (g r)
		-> m (to l r) result
		-> Day m f g from to result

instance Functor (-->) (-->) (Day (-->) f g from to) where
	map m = Straight .: \case
		Day from to -> Day from .: m . to

instance Functor (<--) (<--) (Day (-->) f g from to) where
	map (Opposite m) = Opposite .: \case
		Day from to -> Day from .: Straight m . to

instance Transformation (-->) (-->) (Day (-->) Identity Identity (:*:) (:*:)) Identity where
	transformation (Straight morphism) = Straight .: \case
		Day (Identity l :*: Identity r) (Straight tensor)
			-> Identity . morphism . tensor ...: l :*: r

-- TOOD: instance Transformation (<--) (<--) (Day (-->) Identity Identity (:*:) (:*:)) Identity where

type (:*:>) = Straight (:*:)

instance Functor (-->) (-->) ((:*:>) l) where
	map (Straight m) = Straight .: \case
		Straight (l :*: r) -> Straight (l :*: m r)

instance Functor (<--) (<--) ((:*:>) l) where
	map (Opposite m) = Opposite .: \case
		Straight (l :*: r) -> Straight (l :*: m r)

-- TODO: instance Transformation (-->) (-->) (((:*:>) l) =!?= g) (((:*:>) l) =?!= g) where

type (:+:>) = Straight (:+:)

instance Functor (-->) (-->) ((:+:>) l) where
	map (Straight m) = Straight .: \case
		Straight (This l) -> Straight .: This l
		Straight (That r) -> Straight . That .: m r

instance Functor (<--) (<--) ((:+:>) l) where
	map (Opposite m) = Opposite .: \case
		Straight (This l) -> Straight .: This l
		Straight (That r) -> Straight . That .: m r

instance Monoidal Functor (:*:) (:*:) (-->) (-->) (-->) g
	=> Transformation (-->) (-->) (((:+:>) l) =!?= g) (((:+:>) l) =?!= g) where
		transformation (Straight morphism) = Straight .: \case
			FG_ (Straight (That r)) -> GF_ ....: Straight . That . morphism ->>- r
			FG_ (Straight (This l)) -> GF_ ...: point . Straight . This .: l

type (<:*:) = Opposite (:*:)

instance Functor (-->) (-->) ((<:*:) r) where
	map (Straight m) = Straight . (=-=) .: \case
		l :*: r -> m l :*: r

instance Functor (<--) (<--) ((<:*:) r) where
	map (Opposite m) = Opposite . (=-=) .: \case
		l :*: r -> m l :*: r

-- TODO: instance Transformation (-->) (-->) (((<:*:) r) =!?= g) (((<:*:) r) =?!= g) where

type (<:+:) = Opposite (:+:)

instance Functor (-->) (-->) ((<:+:) r) where
	map (Straight m) = Straight . (=-=) .: \case
		This l -> This .: m l
		That r -> That r

instance Functor (<--) (<--) ((<:+:) r) where
	map (Opposite m) = Opposite . (=-=) .: \case
		This l -> This .: m l
		That r -> That r

instance Monoidal Functor (:*:) (:*:) (-->) (-->) (-->) g
	=> Transformation (-->) (-->) (((<:+:) r) =!?= g) (((<:+:) r) =?!= g) where
		transformation (Straight morphism) = Straight .: \case
			FG_ (Opposite (This l)) -> GF_ .....: Opposite . This . morphism ->>- l
			FG_ (Opposite (That r)) -> GF_ ..: point . Opposite . That .: r

instance Transformation (-->) (-->) (Day (-->) ((:+:>) l) ((:+:>) l) (:*:) (:*:)) ((:+:>) l) where
	transformation (Straight morphism) = Straight .: \case
		Day (Straight (That l) :*: Straight (That r)) (Straight tensor) 
			-> Straight . That . morphism . tensor ...: l :*: r
		Day (Straight (This l) :*: _) _ -> Straight . This .: l
		Day (_ :*: Straight (This r)) _ -> Straight . This .: r

instance Transformation (-->) (-->) (Day (-->) ((:+:>) l) Identity (:*:) (:*:)) ((:+:>) l) where
	transformation (Straight morphism) = Straight .: \case
		Day (Straight (That l) :*: Identity r) (Straight tensor)
			-> Straight . That . morphism . tensor ...: l :*: r
		Day (Straight (This l) :*: _) _ -> Straight . This .: l

instance Transformation (-->) (-->) (Day (-->) Identity ((:+:>) l) (:*:) (:*:)) ((:+:>) l) where
	transformation (Straight morphism) = Straight .: \case
		Day (Identity l :*: Straight (That r)) (Straight tensor)
			-> Straight . That . morphism . tensor ...: l :*: r
		Day (_ :*: Straight (This r)) _ -> Straight . This .: r

instance Transformation (-->) (-->) (Day (-->) Identity Identity (:*:) (:*:)) ((:+:>) l) where
	transformation (Straight morphism) = Straight .: \case
		Day (Identity l :*: Identity r) (Straight tensor) -> Straight . That . morphism . tensor ...: l :*: r

instance Transformation (-->) (-->) (Day (-->) ((<:+:) r) ((<:+:) r) (:*:) (:*:)) ((<:+:) r) where
	transformation (Straight morphism) = Straight .: \case
		Day (Opposite (This l) :*: Opposite (This r)) (Straight tensor)
			-> Opposite . This . morphism . tensor ...: l :*: r
		Day (Opposite (That l) :*: _) _ -> Opposite . That .: l
		Day (_ :*: Opposite (That r)) _ -> Opposite . That .: r

instance Transformation (-->) (-->) (Day (-->) ((<:+:) r) Identity (:*:) (:*:)) ((<:+:) r) where
	transformation (Straight morphism) = Straight .: \case
		Day (Opposite (This l) :*: Identity r) (Straight tensor)
			-> Opposite . This . morphism . tensor ...: l :*: r
		Day (Opposite (That l) :*: _) _ -> Opposite . That .: l

instance Transformation (-->) (-->) (Day (-->) Identity ((<:+:) r) (:*:) (:*:)) ((<:+:) r) where
	transformation (Straight morphism) = Straight .: \case
		Day (Identity l :*: Opposite (This r)) (Straight tensor)
			-> Opposite . This . morphism . tensor ...: l :*: r
		Day (_ :*: Opposite (That r)) _ -> Opposite . That .: r

instance Transformation (-->) (-->) (Day (-->) Identity Identity (:*:) (:*:)) ((<:+:) r) where
	transformation (Straight morphism) = Straight .: \case
		Day (Identity l :*: Identity r) (Straight tensor)
			-> Opposite . This . morphism . tensor ...: l :*: r

instance Transformation (<--) (<--) (Day (-->) ((<:*:) r) ((<:*:) r) (:*:) (:*:)) ((<:*:) r) where
	transformation (Opposite morphism) = Opposite .: \case
		Opposite (l :*: r) -> Day (Opposite (l :*: r) :*: Opposite (l :*: r)) (Straight .: \(o :*: _) -> morphism o)

instance Transformation (<--) (<--) (Day (-->) ((<:*:) r) Identity (:*:) (:*:)) ((<:*:) r) where
	transformation (Opposite morphism) = Opposite .: \case
		Opposite (l :*: r) -> Day (Opposite (l :*: r) :*: Identity l) (Straight .: \(o :*: _) -> morphism o)

instance Transformation (<--) (<--) (Day (-->) Identity ((<:*:) r) (:*:) (:*:)) ((<:*:) r) where
	transformation (Opposite morphism) = Opposite .: \case
		Opposite (l :*: r) -> Day (Identity l :*: Opposite (l :*: r)) (Straight .: \(o :*: _) -> morphism o)

instance Transformation (-->) (-->) ((-->) Unit) Identity where
	transformation (Straight morphism) = Straight .: \case
		Straight m -> Identity . morphism .: m Unit

instance Transformation (-->) (-->) ((-->) Unit) ((:+:>) l) where
	transformation (Straight morphism) = Straight .: \case
		Straight m -> Straight . That . morphism .: m Unit

instance Transformation (-->) (-->) ((-->) Unit) ((<:+:) r) where
	transformation (Straight morphism) = Straight .: \case
		Straight m -> Opposite . This . morphism .: m Unit

instance Transformation (<--) (<--) ((-->) Unit) (Straight (:*:) l) where
	transformation (Opposite morphism) = Opposite .: \case
		Straight (_ :*: r) -> Straight .: \_ -> morphism r

instance Transformation (<--) (<--) ((-->) Unit) (Opposite (:*:) r) where
	transformation (Opposite morphism) = Opposite .: \case
		Opposite (l :*: _) -> Straight .: \_ -> morphism l

instance Covariant Straight Functor g (->) (->) 
	=> Transformation (-->) (-->) (Identity =!?= g) (Identity =?!= g) where
	transformation (Straight morphism) = Straight .: \case
		FG_ (Identity x) -> GF_ (Identity . morphism ->>- x)

-- TODO: it would be nice to generatlize this instance with contstraint unions
-- (f =!? g) -> g: if f is Monoidal Functor (:*:) (:*:) (<--) (<--) (-->)
-- (f =!? g) -> g: if f is Co Pointed
-- (f =!? g) -> f: if g is Monoidal Functor (:*:) (:*:) (<--) (<--) (-->)
-- (f =!? g) -> f: if g is Co Pointed
-- instance Transformation (-->) (-->) (Identity =!?= Identity) Identity where
-- 	transformation (Straight morphism) = Straight .: \case
-- 		FG_ (Identity x) -> morphism ->>- x

-- TODO: amgibous intermediate category for =!?= Functor instance
-- instance Transformation (-->) (-->) ((:*:>) s =!?= (-->) s) Identity where
	-- transformation (Straight morphism) = Straight .: \case
		-- FG_ (Straight (s :*: Straight ms)) -> Identity . morphism .: ms s

-- TODO: amgibous intermediate category for =!?= Functor instance
-- instance Transformation (-->) (-->) Identity ((-->) s =!?= (:*:>) s) where
	-- transformation (Straight morphism) = Straight .: \case
		-- Identity x -> FG_ . Straight .: \s -> Straight ...: s :*: morphism x

(->>-) :: (->>-) f => (source -> target) -> f source -> f target
m ->>- x = map @(-->) @(-->) (Straight m) =- x

(-<<-) :: (-<<-) f => (target -> source) -> f target -> f source
m -<<- x = map @(<--) @(<--) (Opposite m) =- x

(->>>-) :: (->>>-) f g => (source -> target) -> f (g source) -> f (g target)
m ->>>- x = (-||-) @(-->) @(-->) @(-->) (Straight m) =- x

(->><-) :: (->><-) f g => (source -> target) -> f (g target) -> f (g source)
m ->><- x = (-||-) @(-->) @(-->) @(<--) (Straight m) =- x

(-<>>-) :: (-<>>-) f g => (source -> target) -> f (g target) -> f (g source)
m -<>>- x = (-||-) @(<--) @(-->) @(-->) (Opposite m) =- x

(-<><-) :: (-<><-) f g => (source -> target) -> f (g source) -> f (g target)
m -<><- x = (-||-) @(<--) @(-->) @(<--) (Opposite m) =- x

(-><>-) :: (-><>-) f g => (source -> target) -> f (g source) -> f (g target)
m -><>- x = (-||-) @(-->) @(<--) @(-->) (Straight m) =- x

(-<<<-) :: (-<<<-) f g => (source -> target) -> f (g source) -> f (g target)
m -<<<- x = (-||-) @(<--) @(<--) @(<--) (Opposite m) =- x

(->>>>-)
	:: Functor (-->) (-->) h
	=> Functor (-->) (-->) g
	=> Functor (-->) (-->) f
	=> (source -> target) -> f (g (h source)) -> f (g (h target))
m ->>>>- x = (-|||-) @(-->) @(-->) @(-->) @(-->) (Straight m) =- x

(->>--) :: (->>-) (Opposite f o) => (source -> target) -> f source o -> f target o
m ->>-- x = (-|--) @(-->) @(-->) (Straight m) =- x

(-->>--) :: (->>-) (Straight f o) => (source -> target) -> f o source -> f o target
m -->>-- x = (--|--) @(-->) @(-->) (Straight m) =- x

(->>>--) :: (->>>-) (Opposite f o) g => (source -> target) -> f (g source) o -> f (g target) o
m ->>>-- x = (-||--) @(-->) @(-->) @(-->) (Straight m) =- x

(-->>>--) :: (->>>-) (Straight f o) g => (source -> target) -> f o (g source) -> f o (g target)
m -->>>-- x = (--||--) @(-->) @(-->) @(-->) (Straight m) =- x

(->><--) :: (->><-) (Opposite f o) g => (source -> target) -> f (g target) o -> f (g source) o
m ->><-- x = (-||--) @(-->) @(-->) @(<--) (Straight m) =- x

(-->><--) :: (->><-) (Straight f o) g => (source -> target) -> f o (g target) -> f o (g source)
m -->><-- x = (--||--) @(-->) @(-->) @(<--) (Straight m) =- x

(-<>>--) :: (-<>>-) (Opposite f o) g => (source -> target) -> f (g target) o -> f (g source) o
m -<>>-- x = (-||--) @(<--) @(-->) @(-->) (Opposite m) =- x

(--<>>--) :: (-<>>-) (Straight f o) g => (source -> target) -> f o (g target) -> f o (g source)
m --<>>-- x = (--||--) @(<--) @(-->) @(-->) (Opposite m) =- x

(-<><--) :: (-<><-) (Opposite f o) g => (source -> target) -> f (g source) o -> f (g target) o
m -<><-- x = (-||--) @(<--) @(-->) @(<--) (Opposite m) =- x

(--<><--) :: (-<><-) (Straight f o) g => (source -> target) -> f o (g source) -> f o (g target)
m --<><-- x = (--||--) @(<--) @(-->) @(<--) (Opposite m) =- x

(-><>--) :: (-><>-) (Opposite f o) g => (source -> target) -> f (g source) o -> f (g target) o
m -><>-- x = (-||--) @(-->) @(<--) @(-->) (Straight m) =- x

(--><>--) :: (-><>-) (Straight f o) g => (source -> target) -> f o (g source) -> f o (g target)
m --><>-- x = (--||--) @(-->) @(<--) @(-->) (Straight m) =- x

(-<<<--) :: (-<<<-) (Opposite f o) g => (source -> target) -> f (g source) o -> f (g target) o
m -<<<-- x = (-||--) @(<--) @(<--) @(<--) (Opposite m) =- x

(--<<<--) :: (-<<<-) (Straight f o) g => (source -> target) -> f o (g source) -> f o (g target)
m --<<<-- x = (--||--) @(<--) @(<--) @(<--) (Opposite m) =- x

(-/>>-)
	:: Bindable Functor f (-->)
	=> (source -> f target) -> f source -> f target
m -/>>- x = component @(-->) @(-->) @(FG_ _ _) =- FG_ (m ->>- x)

(-/>>>-)
	:: Bindable Functor g (-->)
	=> Functor (-->) (-->) f
	=> (source -> g target) -> f (g source) -> f (g target)
m -/>>>- x = (m -/>>-) ->>- x

(-/>>/-) :: Traversable Functor f g (-->)
	=> (source -> g target) -> f source -> g (f target)
m -/>>/- x = (=-) ...: component @(-->) @(-->) @(FG_ _ _) @(GF_ _ _) =- FG_ (m ->>- x)

(-/>>>/-)
	:: Traversable Functor g h (-->)
	=> Traversable Functor f h (-->)
	=> (source -> h target) -> f (g source) -> h (f (g target))
m -/>>>/- x = (m -/>>/-) -/>>/- x

(--/>>/--)
	:: Functor (-->) (-->) h
	=> Traversable Functor g h (-->)
	=> Traversable Functor (Straight f o) h (-->)
	=> (source -> h target) -> f o source -> h (f o target)
m --/>>/-- x = (=-) ->>- (m -/>>/- Straight x)

(-/>>/--)
	:: Covariant Straight Functor h (->) (->)
	=> Traversable Functor g h (-->)
	=> Traversable Functor (Opposite f o) h (-->)
	=> (source -> h target) -> f source o -> h (f target o)
m -/>>/-- x = (=-) ->>- (m -/>>/- Opposite x)

(--/>>>/--)
	:: Covariant Straight Functor h (->) (->)
	=> Traversable Functor g h (-->)
	=> Traversable Functor (Straight f o) h (-->)
	=> (source -> h target) -> f o (g source) -> h (f o (g target))
m --/>>>/-- x = (=-) ->>- ((m -/>>/-) -/>>/- Straight x)

(-/>>>/--)
	:: Covariant Straight Functor h (->) (->)
	=> Traversable Functor g h (-->)
	=> Traversable Functor (Opposite f o) h (-->)
	=> (source -> h target) -> f (g source) o -> h (f (g target) o)
m -/>>>/-- x = (=-) ->>- ((m -/>>/-) -/>>/- Opposite x)

(|*|-|) :: forall f l r o
	. Semimonoidal Functor (:*:) (:*:) (-->) (-->) (-->) f
	=> (l :*: r -> o) -> (f l :*: f r) -> f o
tensor |*|-| x = component @(-->) @(-->) =- Day x (Straight tensor)

(|+|) :: forall f l r o
	. Semimonoidal Functor (:+:) (:+:) (-->) (-->) (-->) f
	=> (l -> o) -> (r -> o) -> (f l :+: f r) -> f o
l |+| r = \lr -> component @(-->) @(-->) =- Day lr
	(Straight .: \case { This lo -> l lo; That ro -> r ro })

point :: Monoidal Functor (:*:) (:*:) (-->) (-->) (-->) f => o -> f o
point x = component @(-->) @(-->) @((-->) (Neutral (:*:))) =- (Straight .: \Unit -> x)

extract :: Monoidal Functor (:*:) (:*:) (<--) (<--) (-->) f => f o -> o
extract x = component @(<--) @(<--) @((-->) (Neutral (:*:))) =- x =- Unit

empty :: Monoidal Functor (:*:) (:+:) (-->) (-->) (-->) f => f o
empty = component @(-->) @(-->) @((-->) (Neutral (:+:))) =- Straight absurd

join :: Transformation .: (-->) .: (-->) .: FG_ f f .: f => f (f o) -> f o
join x = component @(-->) @(-->) =- FG_ x

return :: forall to f o
	. Transformation .: to .: to .: Identity .: f
	=> Casting to Identity
	=> to .: o .: f o
return = component @to @to . (-=) @to @Identity

-- TODO: merge `point` and `return` in `intro` method

(=-=) :: forall m f source target . (Semigroupoid m, Casting m f)
	=> m .: Casted f source .: Casted f target -> m .: f source .: f target
(=-=) m = (-=) @m . m . (=-) @m

(-=-) :: forall m f source target . (Semigroupoid m, Casting m f)
	=> m .: f source .: f target -> m .: Casted f source .: Casted f target
(-=-) m = (=-) @m . m . (-=) @m

(=--) :: forall m f g o
	. Semigroupoid m
	=> Casting m f
	=> Casting m g
	=> g o ~ Casted f o
	=> m .: f o .: Casted g o
(=--) = (=-) @m . (=-) @m

(=---) :: forall m f g h o
	. Semigroupoid m
	=> Casting m f
	=> Casting m g
	=> Casting m h
	=> g o ~ Casted f o
	=> h o ~ Casted g o
	=> m .: f o .: Casted h o
(=---) = (=-) @m . (=-) @m . (=-) @m

(=----) :: forall m f g h i o
	. Semigroupoid m
	=> Casting m f
	=> Casting m g
	=> Casting m h
	=> Casting m i
	=> g o ~ Casted f o
	=> h o ~ Casted g o
	=> i o ~ Casted h o
	=> m .: f o .: Casted i o
(=----) = (=-) @m . (=-) @m . (=-) @m . (=-) @m

(->>>=)
	:: Covariant Straight Functor f (->) (->)
	=> (Casting (->) f', Casted f' source ~ f source)
	=> (source -> target) -> f' source -> f target
m ->>>= x = map @(-->) @(-->) (Straight m) =- ((=-) x)

(-/>>>/=)
	:: Traversable Functor f h (-->)
	=> Traversable Functor g h (-->)
	=> (Casting (->) f', Casted f' source ~ f (g source))
	=> (source -> h target) -> f' source -> h (f (g target))
m -/>>>/= x = (m -/>>/-) -/>>/- ((=-) x)

instance
	( Functor between to f
	, Functor from between g
	, Casting to (f =!?= g)
	) => Functor from to (f =!?= g) where
	map m = (=-=) ((-||-) @from @between @to @f @g m)

instance {-# OVERLAPS #-}
	(f ->>>- g) -???- (f -<><- g) -??- (f -><>- g) -?- (f -<<<- g)
	=> Functor (-->) (-->) (f =!?= g) where
	map (Straight m) = Straight . (=-=) .: ((<-||-) @f @g m)

instance
	( Functor between to g
	, Functor from between f
	, Casting to (f =?!= g)
	) => Functor from to (f =?!= g) where
	map m = (=-=) ((-||-) @from @between @to @g @f m)

instance {-# OVERLAPS #-}
	(g ->>>- f) -???- (g -<><- f) -??- (g -><>- f) -?- (g -<<<- f)
	=> Functor (-->) (-->) (f =?!= g) where
	map (Straight m) = Straight . (=-=) .: ((<-||-) @g @f m)

instance
	( Transformation (-->) (-->) (Day (-->) f f (:*:) (:*:)) f
	, Transformation (-->) (-->) (Day (-->) g g (:*:) (:*:)) g
	) => Transformation (-->) (-->) (Day (-->) (f =!?= g) (f =!?= g) (:*:) (:*:)) (f =!?= g) where
	transformation (Straight morphism) =
		 Straight .: \(Day (FG_ l :*: FG_ r) (Straight tensor)) ->
			FG_ ....: (morphism . tensor |*|-|)
				<-|- (identity |*|-| l :*: r)

instance (->>>-) f g
	=> Transformation (-->) (-->) (Day (-->) (f =!?= g) Identity (:*:) (:*:)) (f =!?= g) where
	transformation (Straight morphism) = Straight .: \(Day (FG_ l :*: Identity r) tensor) ->
		-- TODO: looks like an adjunction
		FG_ .....: (Straight morphism . tensor =-) . (:*: r) ->>>- l

instance (->>>-) f g
	=> Transformation (-->) (-->) (Day (-->) Identity (f =!?= g) (:*:) (:*:)) (f =!?= g) where
	transformation (Straight morphism) = Straight .: \(Day (Identity l :*: FG_ r) tensor) ->
		FG_ .....: (Straight morphism . tensor =-) . (l :*:) ->>>- r

instance
	( Monoidal Functor (:*:) (:*:) (-->) (-->) (-->) f
	, Monoidal Functor (:*:) (:*:) (-->) (-->) (-->) g
	) => Transformation (-->) (-->) ((-->) Unit) (f =!?= g) where
	transformation (Straight morphism) = Straight .: \(Straight tensor)
		-> FG_ . point . point . morphism .: tensor Unit

instance
	( Functor (-->) (-->) f, Functor (-->) (-->) g, Functor (-->) (-->) h
	, Transformation (-->) (-->) (f =!?= h) (f =?!= h)
	, Transformation (-->) (-->) (g =!?= h) (g =?!= h)
	) => Transformation (-->) (-->) ((f =!?= g) =!?= h) ((f =!?= g) =?!= h) where
	transformation morphism = Straight .: \case
		-- TODO: simplify this
		FG_ (FG_ xs) -> GF_ ....:
			FG_ ->>- ((=-) . (transformation @(-->) @(-->) @(f =!?= h) @(f =?!= h) identity =-)
			. FG_ .: ((=-) . (transformation @(-->) @(-->) @(g =!?= h) @(g =?!= h) morphism =-) . FG_ ->>- xs))

instance
	( Functor from between f'
	, Functor between between' g
	, Functor between' to f
	, Casting to ((=!?!=) f g f')
	) => Functor from to ((=!?!=) f g f') where
	map m = (=-=) ((-|||-) @from @between @between' @to @f @g @f' m)

instance
	( Functor from between h
	, Functor from between g
	, forall o . Functor between to (Straight f .: g o)
	, forall o . Functor between to (Opposite f .: h o)
	, forall o . Casting to (Straight f .: g o)
	, forall o . Casting to (Opposite f .: h o)
	, Casting to ((=!!??=) f g h)
	) => Functor from to ((=!!??=) f g h) where
	map m = (=-=) @to @((=!!??=) f g h)
		.: (-||--) @from @between @to @f @g m
		. (--||--) @from @between @to @f @h m

instance {-# OVERLAPS #-}
	( forall o . (Opposite f o ->>>- g) -???- (Opposite f o -<><- g) -??- (Opposite f o -><>- g) -?- (Opposite f o -<<<- g)
	, forall o . (Straight f o ->>>- h) -???- (Straight f o -<><- h) -??- (Straight f o -><>- h) -?- (Straight f o -<<<- h)
	) => Functor (-->) (-->) ((=!!??=) f g h) where
	map (Straight m) = Straight . (=-=)
		.: (<-||--) @f @g m
		. (<--||--) @f @h m

instance
	( forall o . Functor (-->) (-->) (Opposite f o)
	, forall o . Functor (-->) (-->) (Straight f o)
	, Semimonoidal Functor f f (-->) (-->) (-->) i
	, Functor (-->) (-->) g, Functor (-->) (-->) h, Functor (-->) (-->) i
	, Transformation (-->) (-->) (g =!?= i) (g =?!= i)
	, Transformation (-->) (-->) (h =!?= i) (h =?!= i)
	) => Transformation (-->) (-->) ((=!!??=) f g h =!?= i) ((=!!??=) f g h =?!= i) where
		-- TODO: simplify this
	transformation morphism = Straight .: \case
		FG_ (FFGH_ xs) -> GF_ ....: FFGH_ ->>-
			(\x -> component @(-->) @(-->) @(Day (-->) i i f f) @i =- Day x identity)
				((=-) . (transformation @(-->) @(-->) @(h =!?= i) @(h =?!= i) morphism =-) . FG_ -->>--
				(=-) . (transformation @(-->) @(-->) @(g =!?= i) @(g =?!= i) morphism =-) . FG_ ->>-- xs)

instance Casting (->) f => Casting (-->) f where
	(=-) = Straight (=-)
	(-=) = Straight (-=)

instance Casting (->) f => Casting (<--) f where
	(=-) = Opposite (-=)
	(-=) = Opposite (=-)

(<-|-)
	:: Covariant Straight Functor f (->) (->)
	=> (source -> target) -> f source -> f target
(<-|-) = (->>-)

type (->>-) f = Functor (-->) (-->) f
type (-<<-) f = Functor (<--) (<--) f

type (->>>-) f g = (Functor (-->) (-->) g, Functor (-->) (-->) f)
type (-<><-) f g = (Functor (<--) (-->) g, Functor (-->) (<--) f)
type (-<>>-) f g = (Functor (<--) (-->) g, Functor (-->) (-->) f)
type (-<<<-) f g = (Functor (<--) (<--) g, Functor (<--) (<--) f)
type (-><<-) f g = (Functor (-->) (<--) g, Functor (<--) (<--) f)
type (->><-) f g = (Functor (-->) (-->) g, Functor (-->) (<--) f)
type (-<<>-) f g = (Functor (<--) (<--) g, Functor (<--) (-->) f)
type (-><>-) f g = (Functor (-->) (<--) g, Functor (<--) (-->) f)

class c -?- d where (-?-) :: (c => r) -> (d => r) -> r
class c -??- d where (-??-) :: (c => r) -> (d => r) -> r
class c -???- d where (-???-) :: (c => r) -> (d => r) -> r

instance {-# OVERLAPPABLE #-} (f ->>>- g) => ((f ->>>- g) -???- d) where (-???-) = \r _ -> r
instance d => ((((<--) o) ->>>- ((<--) o)) -???- d) where (-???-) = \_ r -> r

instance {-# OVERLAPPABLE #-} (f -<><- g) => ((f -<><- g) -??- d) where (-??-) = \r _ -> r
instance d => ((((-->) i) -<><- ((-->) i)) -??- d) where (-??-) = \_ r -> r

instance {-# OVERLAPPABLE #-} (f -><>- g) => ((f -><>- g) -?- d) where (-?-) = \r _ -> r
instance d => ((((<--) i) -><>- ((<--) i)) -?- d) where (-?-) = \_ r -> r

(<-||-) :: forall f g source target
	. (f ->>>- g) -???- (f -<><- g) -??- (f -><>- g) -?- (f -<<<- g)
	=> (source -> target) -> f (g source) -> f (g target)
(<-||-) = (-???-) @(f ->>>- g) @((f -<><- g) -??- (f -><>- g) -?- (f -<<<- g)) (->>>-)
	((-??-) @(f -<><- g) @((f -><>- g) -?- (f -<<<- g)) (-<><-)
		((-?-) @(f -><>- g) @(f -<<<- g) (-><>-) (-<<<-)))

(<-||--) :: forall f g o source target
	. (Opposite f o ->>>- g) -???- (Opposite f o -<><- g)
		-??- (Opposite f o -><>- g) -?- (Opposite f o -<<<- g)
	=> (source -> target) -> f (g source) o -> f (g target) o
(<-||--) = (-???-) @(Opposite f o ->>>- g) @((Opposite f o -<><- g) -??- (Opposite f o -><>- g) -?- (Opposite f o -<<<- g)) (->>>--)
	((-??-) @(Opposite f o -<><- g) @((Opposite f o -><>- g) -?- (Opposite f o -<<<- g)) (-<><--)
		((-?-) @(Opposite f o -><>- g) @(Opposite f o -<<<- g) (-><>--) (-<<<--)))

(<--||--) :: forall f g o source target
	. (Straight f o ->>>- g) -???- (Straight f o -<><- g)
		-??- (Straight f o -><>- g) -?- (Straight f o -<<<- g)
	=> (source -> target) -> f o (g source) -> f o (g target)
(<--||--) = (-???-) @(Straight f o ->>>- g) @((Straight f o -<><- g) -??- (Straight f o -><>- g) -?- (Straight f o -<<<- g)) (-->>>--)
	((-??-) @(Straight f o -<><- g) @((Straight f o -><>- g) -?- (Straight f o -<<<- g)) (--<><--)
		((-?-) @(Straight f o -><>- g) @(Straight f o -<<<- g) (--><>--) (--<<<--)))
