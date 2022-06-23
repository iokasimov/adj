module Adj.Program.Controlflow.Implementation.State where

import Adj.Algebra.Category ((.:), (:*:) ((:*:)))
import Adj.Auxiliary (type (=!?=), FG (FG))

type State state = (->) state =!?= (:*:) state

current :: State state state
current = FG .: \state -> state :*: state
