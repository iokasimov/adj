module Adj.Program.Instruction where

import Adj.Auxiliary (Casting (Primary, (=-), (-=)))
import Adj.Algebra.Category ((.:), Functor (map), (|-|->), (:+:) (This, That), type (-->), Flat (Flat))

newtype Instruction t a = Instruction (a :+: t (Instruction t a))

instance Casting (Instruction t) where
	type Primary (Instruction t) a = a :+: t (Instruction t a)
	(=-) (Instruction m) = m
	(-=) m = Instruction m

instance Functor (-->) (-->) t => Functor (-->) (-->) (Instruction t) where
	map (Flat m) = Flat .: \(Instruction i) -> Instruction .: case i of
		That xs -> That (xs |-|-> m)
		This x -> This .: m x
