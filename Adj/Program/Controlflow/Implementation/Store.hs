module Adj.Program.Controlflow.Implementation.Store where

import Adj.Algebra.Category (type (-->), type (:*:>), (.), (:*:) ((:*:)), Flat (Flat), (...:))
import Adj.Auxiliary (type (=!?=), FG (FG))

type Store store = (:*:>) store =!?= (-->) store

position :: Store store o -> store
position (FG (Flat (store :*: _))) = store

retrofit :: (store -> store) -> Store store store -> Store store store
retrofit g (FG (Flat (store :*: f))) = FG . Flat ...: g store :*: f
