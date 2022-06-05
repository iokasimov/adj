module Adj.Program.Instruction where

import Adj.Algebra.Category ((.:), Functor (map), (|-|->), (:+:) (Option, Adoption), type (-->), Flat (Flat))
import Adj.Program.Disbandable (Disbandable (Primary, (=-), (-=)))

newtype Instruction t a = Instruction (a :+: t (Instruction t a))

instance Disbandable (Instruction t) where
	type Primary (Instruction t) a = a :+: t (Instruction t a)
	(=-) (Instruction m) = m
	(-=) m = Instruction m

instance Functor (-->) (-->) t => Functor (-->) (-->) (Instruction t) where
	map (Flat m) = Flat .: \(Instruction i) -> Instruction .: case i of
		Adoption xs -> Adoption (xs |-|-> m)
		Option x -> Option .: m x
