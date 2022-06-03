module Adj.Program.Instruction where

import Adj.Algebra.Sum ((:+:))

newtype Instruction t a = Instruction (a :+: t (Instruction t a))
