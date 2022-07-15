module Adj.Program.Datastructure.Implementation.Tree where

import Adj.Algebra.Set (type (=:*:=))
import Adj.Program.Primitive.Maybe (Maybe)
import Adj.Program.Primitive.Generation (Construction)

type Tree = Construction

-- TODO: Alternative representation:
-- Tree (Identity =:+*:= Identity)
type family Binary tree where
	Binary Tree = Tree (Maybe =:*:= Maybe)

type family Ternary tree where
	Ternary Tree = Tree (Maybe =:*:= Maybe =:*:= Maybe)
