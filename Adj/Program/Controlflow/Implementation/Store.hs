module Adj.Program.Controlflow.Implementation.Store where

import Adj.Algebra.Category ((:*:) ((:*:)), (...:))
import Adj.Auxiliary (type (=!?=), FG (FG))

type Store store = (:*:) store =!?= (->) store

position :: Store store o -> store
position (FG (store :*: _)) = store

retrofit :: (store -> store) -> Store store store -> Store store store
retrofit g (FG (store :*: f)) = FG ...: g store :*: f
