module Adj.Program.Controlflow.Implementation.Store where

import Adj.Algebra.Category (type (-->), type (:*:>))
import Adj.Auxiliary (type (=!?=), FFGHHI__)

type Store queried required = FFGHHI__ (:*:>) queried (-->) required
