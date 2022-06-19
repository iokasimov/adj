module Adj.Program.Datastructure.Implementation.List where

import Adj.Auxiliary (type (|.:|))
import Adj.Program.Generation (Construction)
import Adj.Program.Option (Option)

type List = Option |.:| Construction Option
