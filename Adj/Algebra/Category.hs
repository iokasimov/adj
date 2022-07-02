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

infixr 7 <--, -->

infixr 8 <:*:, :*:>
infixr 8 <:+:, :+:>

infixl 5 -|||-
infixl 6 -||-
infixl 7 -|-

infixl 4 -|||--
infixl 5 -||--
infixl 6 -|--

infixl 3 --|||--
infixl 4 --||--
infixl 5 --|--

infixl 5 =----
infixl 6 =---
infixl 7 =-=, -=-, =--

infixl 4 -|||->
infixl 5 -||->
infixl 6 -|->

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

type family Betwixt from to = btw | btw -> from to where
	Betwixt category category = category

data Variance = Co | Contra

{- |
> * Identity preserving: map identity ≡ identity
> * Composition preserving: map (f . g) ≡ map f . map g
-}

class (Category from, Category to) => Functor from to f where
	map :: from source target -> to .: f source .: f target

(-|-) :: forall from to f source target . Functor from to f
	=> from source target -> to .: f source .: f target
(-|-) = map @from @to

(-||-) :: forall from to f g source target
	.  Functor .: Betwixt from to .: to .: f
	=> Functor .: from .: Betwixt from to .: g
	=> from source target -> to .: f (g source) .: f (g target)
(-||-) m
	= map @(Betwixt from to) @to
	. map @from @(Betwixt from to)
	.: m

(-|||-) :: forall from to f g h source target
	.  Functor .: from .: Betwixt from (Betwixt from to) .: h
	=> Functor .: Betwixt from (Betwixt from to) .: Betwixt (Betwixt from to) to .: g
	=> Functor .: Betwixt (Betwixt from to) to .: to .: f
	=> from source target -> to .: f (g (h source)) .: f (g (h target))
(-|||-) m
	= map @(Betwixt (Betwixt from to) to) @to
	. map @(Betwixt from (Betwixt from to)) @(Betwixt (Betwixt from to) to)
	. map @from @(Betwixt from (Betwixt from to))
	.: m

(-|--) :: forall from to f source target o
	. (Category to, Functor from to ((Dual f) o), Casting to (Dual f o))
	=> from source target -> to .: f source o .: f target o
(-|--) m = (-=-) ((-|-) @from @to @((Dual f) o) m)

(-||--) :: forall from to f g source target o .
	( Category to, Casting to (Dual f o)
	, Functor (Betwixt from to) to ((Dual f) o)
	, Functor from (Betwixt from to) g
	) => from source target -> to .: f (g source) o .: f (g target) o
(-||--) m = (-=-) ((-||-) @from @to @((Dual f) o) m)

(-|||--) :: forall from to f g h source target o .
	( Category to, Casting to (Dual f o)
	, Functor (Betwixt (Betwixt from to) to) to ((Dual f) o)
	, Functor (Betwixt from (Betwixt from to)) (Betwixt (Betwixt from to) to) g
	, Functor from (Betwixt from (Betwixt from to)) h
	) => from source target -> to .: f (g (h source)) o .: f (g (h target)) o
(-|||--) m = (-=-) ((-|||-) @from @to @((Dual f) o) m)

(--|--) :: forall from to f source target o
	. (Category to, Functor from to ((Flat f) o), Casting to (Flat f o))
	=> from source target -> to .: f o source .: f o target
(--|--) m = (-=-) ((-|-) @from @to @((Flat f) o) m)

(--||--) :: forall from to f g source target o .
	( Category to, Casting to (Flat f o)
	, Functor (Betwixt from to) to ((Flat f) o)
	, Functor from (Betwixt from to) g
	) => from source target -> to .: f o (g source) .: f o (g target)
(--||--) m = (-=-) ((-||-) @from @to @((Flat f) o) m)

(--|||--) :: forall from to f g h source target o .
	( Category to, Casting to (Flat f o)
	, Functor (Betwixt (Betwixt from to) to) to ((Flat f) o)
	, Functor (Betwixt from (Betwixt from to)) (Betwixt (Betwixt from to) to) g
	, Functor from (Betwixt from (Betwixt from to)) h
	) => from source target -> to .: f o (g (h source)) .: f o (g (h target))
(--|||--) m = (-=-) ((-|||-) @from @to @((Flat f) o) m)

class Component m f g where
	component :: m .: f object .: g object

{- |
> * Associativity: (-|) m . component = component . (-|) m
-}

class (Functor from to f, Functor from to g) => Transformation from to f g where
	transformation :: from source target -> to .: f source .: g target

newtype Flat m source target = Flat (m source target)

type instance Casted (Flat m source) target = m source target

instance Casting (->) (Flat m source) where
	(=-) (Flat m) = m
	(-=) m = Flat m

instance Semigroupoid morhism => Semigroupoid (Flat morhism) where
	Flat g . Flat f = Flat .: g . f

instance Category morhism => Category (Flat morhism) where
	identity = Flat identity

newtype Dual m source target = Dual (m target source)

type instance Casted (Dual m target) source = m source target

instance Casting (->) (Dual m target) where
	(=-) (Dual m) = m
	(-=) m = Dual m

instance Semigroupoid morhism => Semigroupoid (Dual morhism) where
	Dual g . Dual f = Dual .: f . g

instance Category morhism => Category (Dual morhism) where
	identity = Dual identity

newtype Kleisli f m source target =
	Kleisli (m source .: f target)

type instance Casted (Kleisli f (->) source) target = source -> f target

instance Casting (->) (Kleisli f (->) source) where
	(=-) (Kleisli m) = m
	(-=) m = Kleisli m

instance (Functor .: Kleisli f target .: target .: f, Semigroupoid target)
	=> Semigroupoid (Kleisli f target) where
		g . Kleisli f = Kleisli .: map g . f

instance (Category target, Functor (Kleisli f target) target f, Component target Identity f, Casting target Identity) => Category (Kleisli f target) where
	identity = Kleisli .: component @_ @Identity @f . (-=) @_ . identity

type family Covariant x source target f where
	Covariant Functor source target f =
		(Category source, Category target, Functor .: Flat source .: Flat target .: f)

type family Contravariant x source target f where
	Contravariant Functor source target f =
		Functor .: Flat source .: Dual target .: f

type family Semimonoidal x source target from to f where
	Semimonoidal Functor source target from to f =
		Component .: from .: Day to f f source target .: f

type family Monoidal x source target from to f where
	Monoidal Functor source target from to f =
		( Component .: from .: Day to f f source target .: f
		, Component .: from .: Day to Identity f source target .: f
		, Component .: from .: Day to f Identity source target .: f
		, Component .: from .: to (Neutral target) .: f
		)

type family Bindable x source target f where
	Bindable Functor source target f =
		Functor .: Kleisli f (Flat source) .: Flat target .: f

type family Traversable x source target g f where
	Traversable Functor source target g f =
		Functor .: Kleisli g (Flat source) .: Kleisli g (Flat target) .: f

-- TODO: not really sure about morphisms in conponents
type family Adjunction source target f g where
	Adjunction source target f g =
		( Functor target source f
		, Functor source target g
		, Component .: Flat source .: (f =!?= g) .: Identity
		, Component .: Flat target .: Identity .: (g =!?= f)
		)

type (-->) = Flat (->)

type (<--) = Dual (->)

type (:*:>) = Flat (:*:)

type (<:*:) = Dual (:*:)

type (:+:>) = Flat (:+:)

type (<:+:) = Dual (:+:)

instance Semigroupoid (->) where
	g . f = \x -> g (f x)

instance Category (->) where
	identity = \x -> x

newtype Identity o = Identity o

type instance Casted Identity o = o

instance Casting (->) Identity where
	(=-) (Identity x) = x
	(-=) x = Identity x

instance Functor (-->) (-->) Identity where
	map (Flat m) = Flat .: \case
		Identity x -> Identity .: m x

instance (Component (-->) Identity Identity, Casting (-->) Identity) => Functor (Kleisli Identity (-->)) (-->) Identity where
	map (Kleisli (Flat m)) = Flat .: \case
		Identity x -> m x

instance (Covariant Functor (->) (->) g, Bindable Functor (->) (->) g) => Functor (Kleisli g (-->)) (Kleisli g (-->)) Identity where
	map (Kleisli (Flat m)) = Kleisli . Flat .: \case
		Identity x -> (-|-) @_ @(-->) (Flat Identity) =- m x

data Day m f g from to result where
	Day :: from (f l) (g r)
		-> m (to l r) result
		-> Day m f g from to result

instance Functor (-->) (-->) (Day (-->) f g from to) where
	map m = Flat .: \case
		Day from to -> Day from .: m . to

instance Functor (-->) (-->) ((:*:>) l) where
	map (Flat m) = Flat .: \case
		Flat (l :*: r) -> Flat (l :*: m r)

instance 
	( Bindable Functor (->) (->) ((:*:>) l)
	, Component (-->) Identity ((:*:>) l)
	, Casting (-->) Identity
	) => Functor (Kleisli ((:*:>) l) (-->)) (-->) ((:*:>) l) where
	map (Kleisli (Flat m)) = Flat .: \case
		Flat (_ :*: r) -> m r

instance Functor (-->) (-->) ((:+:>) l) where
	map (Flat m) = Flat .: \case
		Flat (This l) -> Flat .: This l
		Flat (That r) -> Flat . That .: m r

instance
	( Bindable Functor (->) (->) ((:+:>) l)
	, Component (-->) Identity ((:+:>) l)
	, Casting (-->) Identity
	) => Functor (Kleisli ((:+:>) l) (-->)) (-->) ((:+:>) l) where
	map (Kleisli (Flat m)) = Flat .: \case
		Flat (This l) -> Flat .: This l
		Flat (That r) -> m r

instance Functor (-->) (-->) ((<:*:) r) where
	map (Flat m) = Flat .: \case
		Dual (l :*: r) -> Dual (m l :*: r)

instance Functor (-->) (-->) ((<:+:) r) where
	map (Flat m) = Flat .: \case
		Dual (This l) -> Dual . This .: m l
		Dual (That r) -> Dual .: That r

instance
	( Component (-->) Identity ((<:+:) r)
	, Casting (-->) Identity
	) => Functor (Kleisli ((<:+:) r) (-->)) (-->) ((<:+:) r) where
	map (Kleisli (Flat m)) = Flat .: \case
		Dual (This l) -> m l
		Dual (That r) -> Dual .: That r

instance
	( Component (-->) Identity ((<:*:) r)
	, Bindable Functor (->) (->) ((<:*:) r)
	, Casting (-->) Identity
	) => Functor (Kleisli ((<:*:) r) (-->)) (-->) ((<:*:) r) where
	map (Kleisli (Flat m)) = Flat .: \case
		Dual (l :*: _) -> m l

instance (Covariant Functor (->) (->) f, Bindable Functor (->) (->) f) => Functor (Kleisli f (-->)) (Kleisli f (-->)) ((:*:>) l) where
	map (Kleisli (Flat m)) = Kleisli . Flat .: \case
		Flat (l :*: r) -> m r -|-> Flat . (l :*:)

instance (Covariant Functor (->) (->) f, Bindable Functor (->) (->) f) => Functor (Kleisli f (-->)) (Kleisli f (-->)) ((<:*:) r) where
	map (Kleisli (Flat m)) = Kleisli . Flat .: \case
		Dual (l :*: r) -> m l -|-> Dual . (:*: r)

instance (Covariant Functor (->) (->) f, Bindable Functor (->) (->) f, Monoidal Functor (:*:) (:*:) (-->) (-->) f)
	=> Functor (Kleisli f (-->)) (Kleisli f (-->)) ((:+:>) l) where
		map (Kleisli (Flat m)) = Kleisli . Flat .: \case
			Flat (That r) -> m r -|-> Flat . That
			Flat (This l) -> point . Flat . This .: l

instance (Covariant Functor (->) (->) f, Bindable Functor (->) (->) f, Monoidal Functor (:*:) (:*:) (-->) (-->) f)
	=> Functor (Kleisli f (-->)) (Kleisli f (-->)) ((<:+:) r) where
		map (Kleisli (Flat m)) = Kleisli . Flat .: \case
			Dual (This l) -> m l -|-> Dual . This
			Dual (That r) -> point . Dual . That .: r

instance Component (-->) (Day (-->) Identity Identity (:*:) (:*:)) Identity where
	component = Flat .: \case
		Day (Identity l :*: Identity r) (Flat m) -> Identity .: m (l :*: r)

instance Component (-->) (Day (-->) ((:+:>) l) ((:+:>) l) (:*:) (:*:)) ((:+:>) l) where
	component = Flat .: \case
		Day (Flat (That l) :*: Flat (That r)) (Flat m) -> Flat . That .: m (l :*: r)
		Day (Flat (This l) :*: _) _ -> Flat . This .: l
		Day (_ :*: Flat (This r)) _ -> Flat . This .: r

instance Component (-->) (Day (-->) ((:+:>) l) Identity (:*:) (:*:)) ((:+:>) l) where
	component = Flat .: \case
		Day (Flat (That l) :*: Identity r) (Flat m) -> Flat . That .: m (l :*: r)
		Day (Flat (This l) :*: _) _ -> Flat . This .: l

instance Component (-->) (Day (-->) Identity ((:+:>) l) (:*:) (:*:)) ((:+:>) l) where
	component = Flat .: \case
		Day (Identity l :*: Flat (That r)) (Flat m) -> Flat . That .: m (l :*: r)
		Day (_ :*: Flat (This r)) _ -> Flat . This .: r

instance Component (-->) (Day (-->) Identity Identity (:*:) (:*:)) ((:+:>) l) where
	component = Flat .: \case
		Day (Identity l :*: Identity r) (Flat m) -> Flat . That .: m (l :*: r)

instance Component (-->) (Day (-->) ((<:+:) r) ((<:+:) r) (:*:) (:*:)) ((<:+:) r) where
	component = Flat .: \case
		Day (Dual (This l) :*: Dual (This r)) (Flat m) -> Dual . This .: m (l :*: r)
		Day (Dual (That l) :*: _) _ -> Dual . That .: l
		Day (_ :*: Dual (That r)) _ -> Dual . That .: r

instance Component (-->) (Day (-->) ((<:+:) r) Identity (:*:) (:*:)) ((<:+:) r) where
	component = Flat .: \case
		Day (Dual (This l) :*: Identity r) (Flat m) -> Dual . This .: m (l :*: r)
		Day (Dual (That l) :*: _) _ -> Dual . That .: l

instance Component (-->) (Day (-->) Identity ((<:+:) r) (:*:) (:*:)) ((<:+:) r) where
	component = Flat .: \case
		Day (Identity l :*: Dual (This r)) (Flat m) -> Dual . This .: m (l :*: r)
		Day (_ :*: Dual (That r)) _ -> Dual . That .: r

instance Component (-->) (Day (-->) Identity Identity (:*:) (:*:)) ((<:+:) r) where
	component = Flat .: \case
		Day (Identity l :*: Identity r) (Flat m) -> Dual . This .: m (l :*: r)

instance Component (<--) (Day (-->) ((<:*:) r) ((<:*:) r) (:*:) (:*:)) ((<:*:) r) where
	component = Dual .: \case
		Dual (l :*: r) -> Day (Dual (l :*: r) :*: Dual (l :*: r)) (Flat .: \(o :*: _) -> o)

instance Component (<--) (Day (-->) ((<:*:) r) Identity (:*:) (:*:)) ((<:*:) r) where
	component = Dual .: \case
		Dual (l :*: r) -> Day (Dual (l :*: r) :*: Identity l) (Flat .: \(o :*: _) -> o)

instance Component (<--) (Day (-->) Identity ((<:*:) r) (:*:) (:*:)) ((<:*:) r) where
	component = Dual .: \case
		Dual (l :*: r) -> Day (Identity l :*: Dual (l :*: r)) (Flat .: \(o :*: _) -> o)

instance Component (-->) ((-->) Unit) Identity where
	component = Flat .: \case
		Flat m -> Identity .: m Unit

instance Component (-->) ((-->) Unit) ((:+:>) l) where
	component = Flat .: \case
		Flat m -> Flat . That .: m Unit

instance Component (-->) ((-->) Unit) ((<:+:) r) where
	component = Flat .: \case
		Flat m -> Dual . This .: m Unit

instance Component (<--) ((-->) Unit) (Flat (:*:) l) where
	component = Dual .: \case
		Flat (_ :*: r) -> Flat .: \_ -> r

instance Component (<--) ((-->) Unit) (Dual (:*:) r) where
	component = Dual .: \case
		Dual (l :*: _) -> Flat .: \_ -> l

instance Component (-->) ((:*:>) s =!?= (-->) s) Identity where
	component = Flat .: \case
		FG (Flat (s :*: Flat ms)) -> Identity .: ms s

instance Component (-->) Identity ((-->) s =!?= (:*:>) s) where
	component = Flat .: \case
		Identity x -> FG . Flat .: \s -> Flat ...: s :*: x

(-|->)
	:: Covariant Functor (->) (->) f
	=> f source -> (source -> target) -> f target
x -|-> m = map @(-->) @(-->) (Flat m) =- x

(-||->)
	:: Covariant Functor (->) (->) f
	=> Covariant Functor (->) (->) g
	=> f (g source) -> (source -> target) -> f (g target)
x -||-> m = (-||-) @(-->) @(-->) (Flat m) =- x

(-|||->)
	:: Covariant Functor (->) (->) f
	=> Covariant Functor (->) (->) g
	=> Covariant Functor (->) (->) h
	=> f (g (h source)) -> (source -> target) -> f (g (h target))
x -|||-> m = (-|||-) @(-->) @(-->) (Flat m) =- x

(-|-/->)
	:: Bindable Functor (->) (->) f
	=> f source -> (source -> f target) -> f target
x -|-/-> m = map @_ @(-->) (Kleisli (Flat m)) =- x

(-|-|-/->)
	:: Covariant Functor (->) (->) f
	=> Bindable Functor (->) (->) g
	=> f (g source) -> (source -> g target) -> f (g target)
x -|-|-/-> m = x -|-> (-|-/-> m)

(-|-/-/>)
	:: forall f g source target . Traversable Functor (->) (->) g f
	=> f source -> (source -> g target) -> g (f target)
x -|-/-/> m = case map @(Kleisli g (-->)) @(Kleisli g (-->)) (Kleisli (Flat m)) of
	Kleisli (Flat m') -> m' x

(-|-/-/-/>)
	:: forall f g h source target
	. (Traversable Functor (->) (->) g h, Traversable Functor (->) (->) g f)
	=> f (h source) -> (source -> g target) -> g (f (h target))
x -|-/-/-/> m = case (map @(Kleisli g (-->)) @(Kleisli g (-->)) . map @(Kleisli g (-->)) @(Kleisli g (-->))) (Kleisli (Flat m)) of
	Kleisli (Flat m') -> m' x

point :: Monoidal Functor (:*:) (:*:) (-->) (-->) f => o -> f o
point x = component @(-->) @((-->) (Neutral (:*:))) =- (Flat .: \Unit -> x)

extract :: Monoidal Functor (:*:) (:*:) (<--) (-->) f => f o -> o
extract x = component @(<--) @((-->) (Neutral (:*:))) =- x =- Unit

empty :: Monoidal Functor (:*:) (:+:) (-->) (-->) f => f o
empty = component @(-->) @((-->) (Neutral (:+:))) =- Flat absurd

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

instance
	( Category m
	, Functor m m f
	, Functor m m g
	, Casting m (f =!?= g)
	) => Functor m m (f =!?= g) where
	map m = (=-=) ((-||-) @m @m @f @g m)

instance
	( Category m
	, Functor m m f
	, Functor m m g
	, Functor m m f'
	, Casting m ((=!?!=) f g f')
	) => Functor m m ((=!?!=) f g f') where
	map m = (=-=) ((-|||-) @m @m @f @g @f' m)

instance
	( Category m
	, Functor m m g
	, Functor m m h
	, Casting m ((=!!??=) f g h)
	, forall l . Casting m (Flat f .: g l)
	, forall r . Casting m (Dual f .: h r)
	, forall r . Functor m m ((Flat f) r)
	, forall l . Functor m m ((Dual f) l)
	) => Functor m m ((=!!??=) f g h) where
	map m = (=-=) ((-||--) @m @m @f m . (--||--) @m @m @f m)

instance Casting (->) f => Casting (-->) f where
	(=-) = Flat (=-)
	(-=) = Flat (-=)

instance (Casting (->) f, Monoidal Functor (:*:) (:*:) (-->) (-->) g) => Casting (Kleisli g (-->)) f where
	(=-) = Kleisli . Flat .: point . (=-)
	(-=) = Kleisli . Flat .: point . (-=)
