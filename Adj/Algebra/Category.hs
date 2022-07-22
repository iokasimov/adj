{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Adj.Algebra.Category where

import Adj.Auxiliary (type (.:), type (=!?=), FG (FG), type (=!?!=), type (=!!??=), Casted, Casting ((-=), (=-)))
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
infixr 7 <--, -->

infixr 8 <:*:, :*:>
infixr 8 <:+:, :+:>

infixl 3 --|||--
infixl 4 -|||--, --||--
infixl 5 -|||-, -||--, --|--
infixl 6 -||-, -|--
infixl 7 -|-

infixl 5 =----
infixl 6 =---
infixl 7 =-=, -=-, =--

infixl 2 --/>>/--
infixl 3 --/>/--, -/>>/--
infixl 4 -/>/--, -/>>/-, -->>--, -/>>/=
infixl 5 ->>>-, -->--, ->>-- -- , -/>>-, -/>/-
infixl 6 ->>-, -><-, -<>-, ->-- -- , -/>-
infixl 7 ->-, -<-, ->=

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
	( Monad f (Straight to)
	, Transformation (Straight to) (Straight to) Identity f
	, Functor (Kleisli f (Straight to)) (Straight to) f
	, Casting (Straight to) Identity
	) => Category (Kleisli f (Straight to)) where
	identity = Kleisli .: return

type family Covariant m functor f from to where
	Covariant m Functor functor from to
		= Functor (m from) (m to) functor

type family Endo m functor f to where
	Endo m Functor f to = Functor (m to) (m to) f

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
		Transformation .: from .: to .: Day tensor f f source target .: f

type family Monoidal x source target from to tensor f where
	Monoidal Functor source target from to tensor f =
		( Transformation .: from .: to .: Day tensor f f source target .: f
		, Transformation .: from .: to .: Day tensor Identity f source target .: f
		, Transformation .: from .: to .: Day tensor f Identity source target .: f
		, Transformation .: from .: to .: tensor (Neutral target) .: f
		)

type Monad f to =
	( Transformation .: Straight to .: Straight to .: FG f f .: f
	, Transformation .: Straight to .: Straight to .: Identity .: f
	)

type Comonad f to =
	( Transformation .: Opposite to .: Opposite to .: FG f f .: f
	, Transformation .: Opposite to .: Opposite to .: Identity .: f
	)

-- TODO: we need to add laws here
-- TODO: turn into a typeclass
type family Traversable x source target g f where
	Traversable Functor source target g f =
		Functor .: Kleisli g (Straight source) .: Kleisli g (Straight target) .: f

type family Adjunction f g from to where
	Adjunction f g from to =
		( Transformation .: to .: from .: FG f g .: Identity
		, Transformation .: from .: to .: Identity .: FG g f
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

-- TODO: use Transformation instead of Component
-- instance Component (-->) Identity Identity
	-- => Functor ((-/->) Identity) (-->) Identity where
	-- map (Kleisli (Straight m)) = Straight .: \case
		-- Identity x -> m x

-- instance
	-- ( Covariant Straight Functor g (->) (->)
	-- , Bindable Functor (->) (->) g
	-- ) => Functor ((-/->) g) ((-/->) g) Identity where
	-- map (Kleisli (Straight m)) = Kleisli . Straight .: \case
		-- Identity x -> (-|-) @_ @(-->) (Straight Identity) =- m x

type (:*:>) = Straight (:*:)

instance Functor (-->) (-->) ((:*:>) l) where
	map (Straight m) = Straight .: \case
		Straight (l :*: r) -> Straight (l :*: m r)

instance Functor (<--) (<--) ((:*:>) l) where
	map (Opposite m) = Opposite .: \case
		Straight (l :*: r) -> Straight (l :*: m r)

-- TODO: use Transformation instead of Component
-- instance
	-- ( Bindable Functor (->) (->) ((:*:>) l)
	-- , Component (-->) Identity ((:*:>) l)
	-- ) => Functor ((-/->) ((:*:>) l)) (-->) ((:*:>) l) where
	-- map (Kleisli (Straight m)) = Straight .: \case
		-- Straight (_ :*: r) -> m r

-- instance
	-- ( Covariant Straight Functor f (->) (->)
	-- , Bindable Functor (->) (->) f
	-- ) => Functor ((-/->) f) ((-/->) f) ((:*:>) l) where
	-- map (Kleisli (Straight m)) = Kleisli . Straight .: \case
		-- Straight (l :*: r) -> Straight . (l :*:) ->- m r

type (:+:>) = Straight (:+:)

instance Functor (-->) (-->) ((:+:>) l) where
	map (Straight m) = Straight .: \case
		Straight (This l) -> Straight .: This l
		Straight (That r) -> Straight . That .: m r

instance Functor (<--) (<--) ((:+:>) l) where
	map (Opposite m) = Opposite .: \case
		Straight (This l) -> Straight .: This l
		Straight (That r) -> Straight . That .: m r

-- TODO: use Transformation instead of Component
-- instance
	-- ( Bindable Functor (->) (->) ((:+:>) l)
	-- , Component (-->) Identity ((:+:>) l)
	-- ) => Functor ((-/->) ((:+:>) l)) (-->) ((:+:>) l) where
	-- map (Kleisli (Straight m)) = Straight .: \case
		-- Straight (This l) -> Straight .: This l
		-- Straight (That r) -> m r

-- TODO: use Transformation instead of Component
-- instance
	-- ( Covariant Straight Functor f (->) (->)
	-- , Bindable Functor (->) (->) f
	-- , Monoidal Functor (:*:) (:*:) (-->) (-->) f
	-- ) => Functor ((-/->) f) ((-/->) f) ((:+:>) l) where
		-- map (Kleisli (Straight m)) = Kleisli . Straight .: \case
			-- Straight (That r) -> Straight . That ->- m r
			-- Straight (This l) -> point . Straight . This .: l

type (<:*:) = Opposite (:*:)

instance Functor (-->) (-->) ((<:*:) r) where
	map (Straight m) = Straight . (=-=) .: \case
		l :*: r -> m l :*: r

instance Functor (<--) (<--) ((<:*:) r) where
	map (Opposite m) = Opposite . (=-=) .: \case
		l :*: r -> m l :*: r

-- TODO: use Transformation instead of Component
-- instance
	-- ( Component (-->) Identity ((<:*:) r)
	-- , Bindable Functor (->) (->) ((<:*:) r)
	-- ) => Functor ((-/->) ((<:*:) r)) (-->) ((<:*:) r) where
	-- map (Kleisli (Straight m)) = Straight .: \case
		-- Opposite (l :*: _) -> m l

-- TODO: return back after changing Bindable type family
-- instance
	-- ( Covariant Straight Functor f (->) (->)
	-- , Bindable Functor (->) (->) f
	-- ) => Functor ((-/->) f) ((-/->) f) ((<:*:) r) where
	-- map (Kleisli (Straight m)) = Kleisli . Straight .: \case
		-- Opposite (l :*: r) -> Opposite . (:*: r) ->- m l

type (<:+:) = Opposite (:+:)

instance Functor (-->) (-->) ((<:+:) r) where
	map (Straight m) = Straight . (=-=) .: \case
		This l -> This .: m l
		That r -> That r

instance Functor (<--) (<--) ((<:+:) r) where
	map (Opposite m) = Opposite . (=-=) .: \case
		This l -> This .: m l
		That r -> That r

-- TODO: use Transformation instead of Component
-- instance Component (-->) Identity ((<:+:) r)
	-- => Functor ((-/->) ((<:+:) r)) (-->) ((<:+:) r) where
	-- map (Kleisli (Straight m)) = Straight .: \case
		-- Opposite (This l) -> m l
		-- Opposite (That r) -> Opposite .: That r

-- TODO: use Transformation instead of Component
-- instance
	-- ( Covariant Straight Functor f (->) (->)
	-- , Bindable Functor (->) (->) f
	-- , Monoidal Functor (:*:) (:*:) (-->) (-->) f
	-- ) => Functor ((-/->) f) ((-/->) f) ((<:+:) r) where
		-- map (Kleisli (Straight m)) = Kleisli . Straight .: \case
			-- Opposite (This l) -> Opposite . This ->- m l
			-- -- Opposite (That r) -> point . Opposite . That .: r

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

-- TODO: amgibous intermediate category for =!?= Functor instance
-- instance Transformation (-->) (-->) ((:*:>) s =!?= (-->) s) Identity where
	-- transformation (Straight morphism) = Straight .: \case
		-- FG (Straight (s :*: Straight ms)) -> Identity . morphism .: ms s

-- TODO: amgibous intermediate category for =!?= Functor instance
-- instance Transformation (-->) (-->) Identity ((-->) s =!?= (:*:>) s) where
	-- transformation (Straight morphism) = Straight .: \case
		-- Identity x -> FG . Straight .: \s -> Straight ...: s :*: morphism x

(->-)
	:: Covariant Straight Functor f (->) (->)
	=> (source -> target) -> f source -> f target
m ->- x = map @(-->) @(-->) (Straight m) =- x

(-<-)
	:: Contravariant Straight Functor f (->) (->)
	=> (source -> target) -> f target -> f source
m -<- x = map @(-->) @(<--) (Straight m) =- x

(->>-)
	:: Covariant Straight Functor f (->) (->)
	=> Covariant Straight Functor g (->) (->)
	=> (source -> target) -> f (g source) -> f (g target)
m ->>- x = (-||-) @(-->) @(-->) @(-->) (Straight m) =- x

(-><-)
	:: Contravariant Straight Functor f (->) (->)
	=> Covariant Straight Functor g (->) (->)
	=> (source -> target) -> f (g target) -> f (g source)
m -><- x = (-||-) @(-->) @(-->) @(<--) (Straight m) =- x

(-<>-)
	:: Covariant Straight Functor f (->) (->)
	=> Contravariant Opposite Functor g (->) (->)
	=> (source -> target) -> f (g target) -> f (g source)
m -<>- x = (-||-) @(<--) @(-->) @(-->) (Opposite m) =- x

(-<<-)
	:: Contravariant Straight Functor f (->) (->)
	=> Contravariant Opposite Functor g (->) (->)
	=> (source -> target) -> f (g source) -> f (g target)
m -<<- x = (-||-) @(<--) @(-->) @(<--) (Opposite m) =- x

(->>>-)
	:: Covariant Straight Functor f (->) (->)
	=> Covariant Straight Functor g (->) (->)
	=> Covariant Straight Functor h (->) (->)
	=> (source -> target) -> f (g (h source)) -> f (g (h target))
m ->>>- x = (-|||-) @(-->) @(-->) @(-->) @(-->) (Straight m) =- x

(->--)
	:: Covariant Straight Functor (Opposite f o) (->) (->)
	=> (source -> target) -> f source o -> f target o
m ->-- x = (-|--) @(-->) @(-->) (Straight m) =- x

(-->--)
	:: Covariant Straight Functor (Straight f o) (->) (->)
	=> (source -> target) -> f o source -> f o target
m -->-- x = (--|--) @(-->) @(-->) (Straight m) =- x

(->>--)
	:: Covariant Straight Functor (Opposite f o) (->) (->)
	=> Covariant Straight Functor g (->) (->)
	=> (source -> target) -> f (g source) o -> f (g target) o
m ->>-- x = (-||--) @(-->) @(-->) @(-->) (Straight m) =- x

(-->>--)
	:: Covariant Straight Functor (Straight f o) (->) (->)
	=> Covariant Straight Functor g (->) (->)
	=> (source -> target) -> f o (g source) -> f o (g target)
m -->>-- x = (--||--) @(-->) @(-->) @(-->) (Straight m) =- x

-- TOOD: define -<<<-, -><<-, -><>-, -<<>-, -<>>-, -<><-

-- TODO: return back after changing Bindable type family
-- (-/>-) :: forall f source target
	-- . Bindable Functor (->) (->) f
	-- => (source -> f target) -> f source -> f target
-- m -/>- x = map @((-/->) f) @(-->) (Kleisli (Straight m)) =- x

-- TODO: return back after changing Bindable type family
-- (-/>>-)
	-- :: Covariant Straight Functor f (->) (->)
	-- => Bindable Functor (->) (->) g
	-- => (source -> g target) -> f (g source) -> f (g target)
-- m -/>>- x = (m -/>-) ->- x

(-/>/-) :: Traversable Functor (->) (->) g f
	=> (source -> g target) -> f source -> g (f target)
m -/>/- x = map @((-/->) _) @((-/->) _) .: Kleisli (Straight m) =- x

(-/>>/-)
	:: Traversable Functor (->) (->) h f
	=> Traversable Functor (->) (->) h g
	=> (source -> h target) -> f (g source) -> h (f (g target))
m -/>>/- x = (m -/>/-) -/>/- x

(--/>/--)
	:: Traversable Functor (->) (->) h (Straight f o)
	=> Traversable Functor (->) (->) h g
	=> Covariant Straight Functor h (->) (->)
	=> (source -> h target) -> f o source -> h (f o target)
m --/>/-- x = (=-) ->- (m -/>/- Straight x)

(-/>/--)
	:: Traversable Functor (->) (->) h (Opposite f o)
	=> Traversable Functor (->) (->) h g
	=> Covariant Straight Functor h (->) (->)
	=> (source -> h target) -> f source o -> h (f target o)
m -/>/-- x = (=-) ->- (m -/>/- Opposite x)

(--/>>/--)
	:: Traversable Functor (->) (->) h (Straight f o)
	=> Traversable Functor (->) (->) h g
	=> Covariant Straight Functor h (->) (->)
	=> (source -> h target) -> f o (g source) -> h (f o (g target))
m --/>>/-- x = (=-) ->- ((m -/>/-) -/>/- Straight x)

(-/>>/--)
	:: Traversable Functor (->) (->) h (Opposite f o)
	=> Traversable Functor (->) (->) h g
	=> Covariant Straight Functor h (->) (->)
	=> (source -> h target) -> f (g source) o -> h (f (g target) o)
m -/>>/-- x = (=-) ->- ((m -/>/-) -/>/- Opposite x)

(|*|) :: forall f l r o
	. Semimonoidal Functor (:*:) (:*:) (-->) (-->) (-->) f
	=> f l -> f r -> (l -> r -> o) -> f o
l |*| r = \tensor -> component @(-->) @(-->) =- Day (l :*: r)
	(Straight .: \(lo :*: ro) -> tensor lo ro)

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

join :: Transformation .: (-->) .: (-->) .: FG f f .: f => f (f o) -> f o
join x = component @(-->) @(-->) =- FG x

return :: forall to f o
	. Transformation .: to .: to .: Identity .: f
	=> Casting to Identity
	=> to .: o .: f o
return = component @to @to . (-=) @to @Identity

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

(->=)
	:: Covariant Straight Functor f (->) (->)
	=> (Casting (->) f', Casted f' source ~ f source)
	=> (source -> target) -> f' source -> f target
m ->= x = map @(-->) @(-->) (Straight m) =- ((=-) x)

(-/>>/=)
	:: Traversable Functor (->) (->) h f
	=> Traversable Functor (->) (->) h g
	=> (Casting (->) f', Casted f' source ~ f (g source))
	=> (source -> h target) -> f' source -> h (f (g target))
m -/>>/= x = (m -/>/-) -/>/- ((=-) x)

instance
	( Functor between to f
	, Functor from between g
	, Casting to (f =!?= g)
	) => Functor from to (f =!?= g) where
	map m = (=-=) ((-||-) @from @between @to @f @g m)

-- TODO: ambigous intermediate category for =!?= Functor instance
-- instance
	-- ( Component (-->) (Day (-->) f f (:*:) (:*:)) f
	-- , Component (-->) (Day (-->) g g (:*:) (:*:)) g
	-- , Covariant Straight Functor f (->) (->)
	-- ) => Transformation (-->) (-->) (Day (-->) (f =!?= g) (f =!?= g) (:*:) (:*:)) (f =!?= g) where
	-- transformation (Straight morphism) = Straight .: \(Day (FG l :*: FG r) tensor) ->
	-- TODO: find a way to simplify this instance
		-- FG ...: (=-) (component @(-->) @(Day (-->) g g (:*:) (:*:)) @g) . (\x -> Day x (Straight morphism . tensor))
			-- ->- (=-) (component @(-->) @(Day (-->) f f (:*:) (:*:)) @f) (Day (l :*: r) identity)

-- TODO: ambigous intermediate category for =!?= Functor instance
-- instance
	-- ( Covariant Straight Functor f (->) (->)
	-- , Covariant Straight Functor g (->) (->)
	-- ) => Transformation (-->) (-->) (Day (-->) (f =!?= g) Identity (:*:) (:*:)) (f =!?= g) where
	-- transformation (Straight morphism) = Straight .: \(Day (FG l :*: Identity r) tensor) ->
		-- -- TODO: looks like an adjunction
		-- FG ....: (Straight morphism . tensor =-) . (:*: r) ->>- l

-- TODO: ambigous intermediate category for =!?= Functor instance
-- instance
	-- ( Covariant Straight Functor f (->) (->)
	-- , Covariant Straight Functor g (->) (->)
	-- ) => Transformation (-->) (-->) (Day (-->) Identity (f =!?= g) (:*:) (:*:)) (f =!?= g) where
	-- transformation (Straight morphism) = Straight .: \(Day (Identity l :*: FG r) tensor) ->
		-- FG ....: (Straight morphism . tensor =-) . (l :*:) ->>- r

-- TODO: ambigous intermediate category for =!?= Functor instance
-- instance
	-- ( Monoidal Functor (:*:) (:*:) (-->) (-->) f
	-- , Monoidal Functor (:*:) (:*:) (-->) (-->) g
	-- ) => Transformation (-->) (-->) ((-->) Unit) (f =!?= g) where
	-- transformation (Straight morphism) = Straight .: \(Straight tensor)
		-- -> FG . point @f . point @g . morphism .: tensor Unit

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

instance Casting (->) f => Casting (-->) f where
	(=-) = Straight (=-)
	(-=) = Straight (-=)

-- instance
	-- ( Casting (->) f
	-- , Monoidal Functor (:*:) (:*:) (-->) (-->) g
	-- ) => Casting ((-/->) g) f where
	-- (=-) = Kleisli . Straight .: point . (=-)
	-- (-=) = Kleisli . Straight .: point . (-=)
