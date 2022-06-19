module Adj.Program.Generation where

import Adj.Auxiliary (Casting (Primary, (=-), (-=)))
import Adj.Algebra ((.:), (.), Functor (map), (|->), (|-|-|->), (:*:), (:+:), type (-->), Flat (Flat), Dual, (-=-))

newtype Generation p t a = Generation (p a (t (Generation p t a)))

instance Casting (->) (Generation p t) where
	type Primary (Generation p t) a = p a (t (Generation p t a))
	(=-) (Generation m) = m
	(-=) m = Generation m

instance 
	( Functor (-->) (-->) t
	, forall b . Functor (-->) (-->) ((Flat p) b)
	, forall a . Functor (-->) (-->) ((Dual p) a)
	) => Functor (-->) (-->) (Generation p t) where
		map (Flat m) = Flat .: \(Generation xxs) -> Generation
			. (-=-) @(->) @((Dual p) _) (|-> m) 
			. (-=-) @(->) @((Flat p) _) (|-|-|-> m)
			.: xxs

type Construction = Generation (:*:)

type Instruction = Generation (:+:)
