module Adj.Program.Controlflow.Implementation.State where

import Adj.Algebra.Category (type (:*:))
import Adj.Auxiliary (type (.:), type (..:), Casting (Primary, (-=), (=-)))

newtype State state o = State ((->) state .: (:*:) state ..: o)

instance Casting (->) (State state) where
	type Primary (State state) o = (->) state .: (:*:) state ..: o
	(=-) (State s) = s
	(-=) s = State s
