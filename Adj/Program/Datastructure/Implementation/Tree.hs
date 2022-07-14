module Adj.Program.Datastructure.Implementation.Tree where

import Adj.Algebra.Set (type (=:*:=))
import Adj.Program.Primitive.Maybe (Maybe)
import Adj.Program.Primitive.Generation (Construction)

type Tree = Construction

type Binary tree = Tree (Maybe =:*:= Maybe)

type Ternary tree = Tree (Maybe =:*:= Maybe =:*:= Maybe)
