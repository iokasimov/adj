module Adj.Program.Instruction where

import Adj.Algebra.Sum ((:+:))

newtype Instruction t a = Instruction (a :+: t (Instruction t a))

-- instance Functor (-->) (-->) t => Functor (-->) (-->) (Instruction t) where
-- 	map (Flat m) = Flat (\(Instruction i) -> Instruction (case i of
-- 		Adoption xs -> Adoption (let Flat m' = (map @(-->) @(-->) . map @(-->) @(-->)) (Flat m) in m' xs)
-- 		Option x -> m x
-- 		Construction (m x :*: m' xs))
