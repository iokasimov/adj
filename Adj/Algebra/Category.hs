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

infixl 2 --/>>/--
infixl 3 --/>/--, -/>>/--
infixl 4 -/>/--, -/>>/-, -->>--
infixl 5 ->>>-, -->--, ->>--, -/>>-, -/>/-
infixl 6 ->>-, -><-, -<>-, ->--, -/>-
infixl 7 ->-, -<-

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
	. (Category to, Functor from to ((Dual f) o), Casting to (Dual f o))
	=> from source target -> to .: f source o .: f target o
(-|--) m = (-=-) ((-|-) @from @to @((Dual f) o) m)

(-||--) :: forall from between to f g source target o .
	( Casting to (Dual f o)
	, Functor between to ((Dual f) o)
	, Functor from between g
	) => from source target -> to .: f (g source) o .: f (g target) o
(-||--) m = (-=-) @to ((-||-) @from @between @to @((Dual f) o) @g @source @target m)

(-|||--) :: forall from between between' to f g h source target o .
	( Casting to (Dual f o)
	, Functor .: from .: between .: h
	, Functor .: between .: between' .: g
	, Functor .: between' .: to .: Dual f o
	) => from source target -> to .: f (g (h source)) o .: f (g (h target)) o
(-|||--) m = (-=-) ((-|||-) @from @between @between' @to @((Dual f) o) m)

(--|--) :: forall from to f source target o
	. (Category to, Functor from to ((Flat f) o), Casting to (Flat f o))
	=> from source target -> to .: f o source .: f o target
(--|--) m = (-=-) ((-|-) @from @to @((Flat f) o) m)

(--||--) :: forall from between to f g source target o .
	( Category to, Casting to (Flat f o)
	, Functor from between g
	, Functor between to ((Flat f) o)
	) => from source target -> to .: f o (g source) .: f o (g target)
(--||--) m = (-=-) ((-||-) @from @between @to @((Flat f) o) m)

(--|||--) :: forall from between between' to f g h source target o .
	( Category to, Casting to (Flat f o)
	, Functor .: from .: between .: h
	, Functor .: between .: between' .: g
	, Functor .: between' .: to .: Flat f o
	) => from source target -> to .: f o (g (h source)) .: f o (g (h target))
(--|||--) m = (-=-) ((-|||-) @from @between @between' @to @((Flat f) o) m)

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

type instance Casted (Kleisli f (-->) source) target = source -> f target

instance Casting (->) (Kleisli f (-->) source) where
	(=-) (Kleisli (Flat m)) = m
	(-=) m = Kleisli .: Flat m

instance (Functor .: Kleisli f target .: target .: f, Semigroupoid target)
	=> Semigroupoid (Kleisli f target) where
		g . Kleisli f = Kleisli .: map g . f

instance
	( Category target
	, Functor (Kleisli f target) target f
	, Component target Identity f
	, Casting target Identity
	) => Category (Kleisli f target) where
	identity = Kleisli .: component @_ @Identity @f . (-=) @_ . identity

data Functoriality = Natural | Opposite

type family Covariant functoriality functor source target where
	Covariant Natural functor source target = Functor .: Flat source .: Flat source
	Covariant Opposite functor source target = Functor .: Dual source .: Dual source

type family Contravariant functoriality functor source target where
	Contravariant Natural functor source target = Functor .: Flat source .: Dual source
	Contravariant Opposite functor source target = Functor .: Dual source .: Flat source

type family OP direction where
	OP (Flat category) = Dual category
	OP (Dual category) = Flat category
	OP (Kleisli f (Flat category)) = Kleisli f (Dual category)
	OP (Kleisli f (Dual category)) = Kleisli f (Flat category)

type family Semimonoidal x source target from to f where
	Semimonoidal Functor source target from to f =
		( Functor from to f
		, Component .: from .: Day to f f source target .: f
		)

-- TODO: need to add a Functor constraint
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

type (-/->) f = Kleisli f (-->)

type (<-\-) f = Kleisli f (<--)

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

instance (Component (-->) Identity Identity, Casting (-->) Identity) => Functor ((-/->) Identity) (-->) Identity where
	map (Kleisli (Flat m)) = Flat .: \case
		Identity x -> m x

instance (Covariant Natural Functor (->) (->) g, Bindable Functor (->) (->) g) => Functor ((-/->) g) ((-/->) g) Identity where
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
	) => Functor ((-/->) ((:*:>) l)) (-->) ((:*:>) l) where
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
	) => Functor ((-/->) ((:+:>) l)) (-->) ((:+:>) l) where
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
	) => Functor ((-/->) ((<:+:) r)) (-->) ((<:+:) r) where
	map (Kleisli (Flat m)) = Flat .: \case
		Dual (This l) -> m l
		Dual (That r) -> Dual .: That r

instance
	( Component (-->) Identity ((<:*:) r)
	, Bindable Functor (->) (->) ((<:*:) r)
	, Casting (-->) Identity
	) => Functor ((-/->) ((<:*:) r)) (-->) ((<:*:) r) where
	map (Kleisli (Flat m)) = Flat .: \case
		Dual (l :*: _) -> m l

instance (Covariant Natural Functor (->) (->) f, Bindable Functor (->) (->) f) => Functor ((-/->) f) ((-/->) f) ((:*:>) l) where
	map (Kleisli (Flat m)) = Kleisli . Flat .: \case
		Flat (l :*: r) -> Flat . (l :*:) ->- m r

instance (Covariant Natural Functor (->) (->) f, Bindable Functor (->) (->) f) => Functor ((-/->) f) ((-/->) f) ((<:*:) r) where
	map (Kleisli (Flat m)) = Kleisli . Flat .: \case
		Dual (l :*: r) -> Dual . (:*: r) ->- m l

instance (Covariant Natural Functor (->) (->) f, Bindable Functor (->) (->) f, Monoidal Functor (:*:) (:*:) (-->) (-->) f)
	=> Functor ((-/->) f) ((-/->) f) ((:+:>) l) where
		map (Kleisli (Flat m)) = Kleisli . Flat .: \case
			Flat (That r) -> Flat . That ->- m r
			Flat (This l) -> point . Flat . This .: l

instance (Covariant Natural Functor (->) (->) f, Bindable Functor (->) (->) f, Monoidal Functor (:*:) (:*:) (-->) (-->) f)
	=> Functor ((-/->) f) ((-/->) f) ((<:+:) r) where
		map (Kleisli (Flat m)) = Kleisli . Flat .: \case
			Dual (This l) -> Dual . This ->- m l
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

(->-)
	:: Covariant Natural Functor (->) (->) f
	=> (source -> target) -> f source -> f target
m ->- x = map @(-->) @(-->) (Flat m) =- x

(-<-)
	:: Contravariant Natural Functor (->) (->) f
	=> (source -> target) -> f target -> f source
m -<- x = map @(-->) @(<--) (Flat m) =- x

(->>-)
	:: Covariant Natural Functor (->) (->) f
	=> Covariant Natural Functor (->) (->) g
	=> (source -> target) -> f (g source) -> f (g target)
m ->>- x = (-||-) @(-->) @(-->) @(-->) (Flat m) =- x

(-><-)
	:: Contravariant Natural Functor (->) (->) f
	=> Covariant Natural Functor (->) (->) g
	=> (source -> target) -> f (g target) -> f (g source)
m -><- x = (-||-) @(-->) @(-->) @(<--) (Flat m) =- x

(-<>-)
	:: Covariant Natural Functor (->) (->) f
	=> Contravariant Opposite Functor (->) (->) g
	=> (source -> target) -> f (g target) -> f (g source)
m -<>- x = (-||-) @(<--) @(-->) @(-->) (Dual m) =- x

(-<<-)
	:: Contravariant Natural Functor (->) (->) f
	=> Contravariant Opposite Functor (->) (->) g
	=> (source -> target) -> f (g source) -> f (g target)
m -<<- x = (-||-) @(<--) @(-->) @(<--) (Dual m) =- x

(->>>-)
	:: Covariant Natural Functor (->) (->) f
	=> Covariant Natural Functor (->) (->) g
	=> Covariant Natural Functor (->) (->) h
	=> (source -> target) -> f (g (h source)) -> f (g (h target))
m ->>>- x = (-|||-) @(-->) @(-->) @(-->) @(-->) (Flat m) =- x

(->--)
	:: Covariant Natural Functor (->) (->) (Dual f o)
	=> (source -> target) -> f source o -> f target o
m ->-- x = (-|--) @(-->) @(-->) (Flat m) =- x

(-->--)
	:: Covariant Natural Functor (->) (->) (Flat f o)
	=> (source -> target) -> f o source -> f o target
m -->-- x = (--|--) @(-->) @(-->) (Flat m) =- x

(->>--)
	:: Covariant Natural Functor (->) (->) (Dual f o)
	=> Covariant Natural Functor (->) (->) g
	=> (source -> target) -> f (g source) o -> f (g target) o
m ->>-- x = (-||--) @(-->) @(-->) @(-->) (Flat m) =- x

(-->>--)
	:: Covariant Natural Functor (->) (->) (Flat f o)
	=> Covariant Natural Functor (->) (->) g
	=> (source -> target) -> f o (g source) -> f o (g target)
m -->>-- x = (--||--) @(-->) @(-->) @(-->) (Flat m) =- x

-- TOOD: define -<<<-, -><<-, -><>-, -<<>-, -<>>-, -<><-

(-/>-) :: forall f source target
	. Bindable Functor (->) (->) f
	=> (source -> f target) -> f source -> f target
m -/>- x = map @((-/->) f) @(-->) (Kleisli (Flat m)) =- x

(-/>>-)
	:: Covariant Natural Functor (->) (->) f
	=> Bindable Functor (->) (->) g
	=> (source -> g target) -> f (g source) -> f (g target)
m -/>>- x = (m -/>-) ->- x

(-/>/-) :: Traversable Functor (->) (->) g f
	=> (source -> g target) -> f source -> g (f target)
m -/>/- x = map @((-/->) _) @((-/->) _) .: Kleisli (Flat m) =- x

(-/>>/-)
	:: Traversable Functor (->) (->) h f
	=> Traversable Functor (->) (->) h g
	=> (source -> h target) -> f (g source) -> h (f (g target))
m -/>>/- x = (m -/>/-) -/>/- x

(--/>/--)
	:: Traversable Functor (->) (->) h (Flat f o)
	=> Traversable Functor (->) (->) h g
	=> Covariant Natural Functor (->) (->) h
	=> (source -> h target) -> f o source -> h (f o target)
m --/>/-- x = (=-) ->- (m -/>/- Flat x)

(-/>/--)
	:: Traversable Functor (->) (->) h (Dual f o)
	=> Traversable Functor (->) (->) h g
	=> Covariant Natural Functor (->) (->) h
	=> (source -> h target) -> f source o -> h (f target o)
m -/>/-- x = (=-) ->- (m -/>/- Dual x)

(--/>>/--)
	:: Traversable Functor (->) (->) h (Flat f o)
	=> Traversable Functor (->) (->) h g
	=> Covariant Natural Functor (->) (->) h
	=> (source -> h target) -> f o (g source) -> h (f o (g target))
m --/>>/-- x = (=-) ->- ((m -/>/-) -/>/- Flat x)

(-/>>/--)
	:: Traversable Functor (->) (->) h (Dual f o)
	=> Traversable Functor (->) (->) h g
	=> Covariant Natural Functor (->) (->) h
	=> (source -> h target) -> f (g source) o -> h (f (g target) o)
m -/>>/-- x = (=-) ->- ((m -/>/-) -/>/- Dual x)

(|*|) :: forall f l r o
	. Semimonoidal Functor (:*:) (:*:) (-->) (-->) f
	=> f l -> f r -> (l -> r -> o) -> f o
l |*| r = \m -> component @(-->) @(Day (-->) _ _ _ _)
	=- Day (l :*: r) (Flat .: \(l' :*: r') -> m l' r')

(|+|) :: forall f l r o
	. Semimonoidal Functor (:+:) (:+:) (-->) (-->) f
	=> (l -> o) -> (r -> o) -> (f l :+: f r) -> f o
l |+| r = \lr -> component @(-->) @(Day (-->) _ _ _ _)
	=- Day lr (Flat .: \case { This l' -> l l'; That r' -> r r' })

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
	( Functor between to f
	, Functor from between g
	, Casting to (f =!?= g)
	) => Functor from to (f =!?= g) where
	map m = (=-=) ((-||-) @from @between @to @f @g m)

instance
	( Component (-->) (Day (-->) f f (:*:) (:*:)) f
	, Component (-->) (Day (-->) g g (:*:) (:*:)) g
	, Covariant Natural Functor (->) (->) f
	) => Component (-->) (Day (-->) (f =!?= g) (f =!?= g) (:*:) (:*:)) (f =!?= g) where
	component = Flat .: \(Day (FG l :*: FG r) m) ->
	-- TODO: find a way to simplify this instance
		FG ...: (=-) (component @(-->) @(Day (-->) g g (:*:) (:*:)) @g) . (\x -> Day x m)
			->- (=-) (component @(-->) @(Day (-->) f f (:*:) (:*:)) @f) (Day (l :*: r) identity)

instance
	( Covariant Natural Functor (->) (->) f
	, Covariant Natural Functor (->) (->) g
	) => Component (-->) (Day (-->) (f =!?= g) Identity (:*:) (:*:)) (f =!?= g) where
	component = Flat .: \(Day (FG l :*: Identity r) m) ->
		FG ....: (m =-) . (:*: r) ->>- l

instance
	( Covariant Natural Functor (->) (->) f
	, Covariant Natural Functor (->) (->) g
	) => Component (-->) (Day (-->) Identity (f =!?= g) (:*:) (:*:)) (f =!?= g) where
	component = Flat .: \(Day (Identity l :*: FG r) m) ->
		FG ....: (m =-) . (l :*:) ->>- r

instance
	( Monoidal Functor (:*:) (:*:) (-->) (-->) f
	, Monoidal Functor (:*:) (:*:) (-->) (-->) g
	) => Component (-->) ((-->) Unit) (f =!?= g) where
	component = Flat .: \(Flat m) -> FG . point @f . point @g .: m Unit

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
 	, forall o . Functor between to (Flat f .: g o)
 	, forall o . Functor between to (Dual f .: h o)
 	, forall o . Casting to (Flat f .: g o)
 	, forall o . Casting to (Dual f .: h o)
 	, Casting to ((=!!??=) f g h)
 	) => Functor from to ((=!!??=) f g h) where
 	map m = (=-=) @to @((=!!??=) f g h)
		.: (-||--) @from @between @to @f @g m
		. (--||--) @from @between @to @f @h m

instance Casting (->) f => Casting (-->) f where
	(=-) = Flat (=-)
	(-=) = Flat (-=)

instance (Casting (->) f, Monoidal Functor (:*:) (:*:) (-->) (-->) g) => Casting ((-/->) g) f where
	(=-) = Kleisli . Flat .: point . (=-)
	(-=) = Kleisli . Flat .: point . (-=)
