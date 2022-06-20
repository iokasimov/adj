module Adj.Program.Controlflow.Implementation.State where

import Adj.Algebra.Category (type (:*:))
import Adj.Auxiliary (type (=!?=))

type State state = (->) state =!?= (:*:) state
