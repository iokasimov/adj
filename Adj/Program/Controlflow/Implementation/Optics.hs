module Adj.Program.Controlflow.Implementation.Optics where

import Adj.Auxiliary ((=-), type (=!?=), FG (FG))
import Adj.Algebra.Category (type (<--), type (-->), type (:*:>), type (:+:>), (.), (..:), Dual (Dual), Flat (Flat), (:+:) (This, That), extract)

type Lens queried required source target =
	source --> (((:*:>) (queried target) =!?= (-->) (required target)) source)

view :: Lens queried required source target -> source -> queried target
view lens source = extract . Dual . (=-) . (=-) ..: lens =- source

type Prism available set subset =
	set --> (((:+:>) (available subset) =!?= (<--) (available subset)) set)

review :: Prism available set subset -> set -> available subset
review prism set = case prism =- set of
	FG (Flat (This subset)) -> subset
	FG (Flat (That m)) -> m =- set

-- TODO: think about composition between different type of optics
-- TODO: Lens and Prism types looks the same so maybe we can just generalize them somehow
-- TODO: think about cardinality in a target of Lens
