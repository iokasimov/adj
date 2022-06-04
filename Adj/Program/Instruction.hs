module Adj.Program.Instruction where

import Adj.Algebra.Morphism.Flat (type (-->), Flat (Flat))
import Adj.Algebra.Semigroupoid ((.))
import Adj.Algebra.Category ((.:))
import Adj.Algebra.Functor (Functor (map))
import Adj.Algebra.Sum ((:+:) (Option, Adoption))

newtype Instruction t a = Instruction (a :+: t (Instruction t a))

instance Functor (-->) (-->) t => Functor (-->) (-->) (Instruction t) where
	map (Flat m) = Flat .: \(Instruction i) -> Instruction .: case i of
		Adoption xs -> Adoption .: let Flat m' = map @(-->) @(-->) . map @(-->) @(-->) .: Flat m in m' xs
		Option x -> Option .: m x
