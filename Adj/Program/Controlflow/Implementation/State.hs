module Adj.Program.Controlflow.Implementation.State where

import Adj.Algebra.Category ((.), (.:), type (-->), Flat (Flat), (:*:) ((:*:)), type (:*:>))
import Adj.Auxiliary (type (=!?=), FG (FG))

type State state = (-->) state =!?= (:*:>) state

current :: State state state
current = FG . Flat .: \state -> Flat (state :*: state)

modify :: (state -> state) -> State state state
modify m = FG . Flat .: \state -> Flat (m state :*: state)
