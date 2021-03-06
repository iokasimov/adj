module Adj.Program.Controlflow.Implementation.State where

import Adj.Algebra.Category ((.), (.:), type (-->), Straight (Straight), type (:*:>))
import Adj.Algebra.Set ((:*:) ((:*:)))
import Adj.Auxiliary (type (=!?=), FG_ (FG_))

type State state = (-->) state =!?= (:*:>) state

current :: State state state
current = FG_ . Straight .: \state -> Straight (state :*: state)

modify :: (state -> state) -> State state state
modify m = FG_ . Straight .: \state -> Straight (m state :*: state)
