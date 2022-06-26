module Adj.Program.Controlflow.Implementation.Optics where

import Adj.Auxiliary ((=-))
import Adj.Algebra.Category (type (-->), (..:))
import Adj.Program.Controlflow.Implementation.Store (Store, position)

type Lens avaliable source target = source --> Store (avaliable target) source

view :: Lens avaliable source target -> source -> avaliable target
view lens source = position ..: lens =- source
