module Adj.Program.Controlflow.Implementation.Optics where

import Adj.Auxiliary ((=-), type (=!?=))
import Adj.Algebra.Category (type (-->), type (:*:>), (.), (..:), Dual (Dual), extract)

type Lens queried required source target =
	source --> (((:*:>) (queried target) =!?= (-->) (required target)) source)

view :: Lens queried required source target -> source -> queried target
view lens source = extract . Dual . (=-) . (=-) ..: lens =- source
