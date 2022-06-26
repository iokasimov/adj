module Adj.Program.Controlflow.Implementation.Optics where

import Adj.Auxiliary (type (=!!??=))
import Adj.Algebra.Category (type (-->), Identity)
import Adj.Program.Controlflow.Implementation.Store (Store)

type Lens avaliable = (=!!??=) (-->) Identity (Store avaliable)
