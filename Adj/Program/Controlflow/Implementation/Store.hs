module Adj.Program.Controlflow.Implementation.Store where

import Adj.Algebra.Category (type (:*:))
import Adj.Auxiliary (type (=!?=))

type Store store = (:*:) store =!?= (->) store
