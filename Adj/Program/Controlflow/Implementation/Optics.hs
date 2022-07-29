module Adj.Program.Controlflow.Implementation.Optics where

import Adj.Auxiliary ((=-), type (=!?=), FG_ (FG_))
import Adj.Algebra.Category (type (<--), type (-->), type (:*:>), type (:+:>), (.), (..:), Opposite (Opposite), Straight (Straight), extract)
import Adj.Algebra.Set ((:+:) (This, That), (:*:) ((:*:)))

-- TODO: to use it as natural transformation
-- I should hide source and target parameters
type Lens queried required source target =
	source --> (((:*:>) (queried target) =!?= (-->) (required target)) source)

view :: Lens queried required source target -> source -> queried target
view lens source = extract . Opposite . (=-) . (=-) ..: lens =- source

change :: Lens queried required source target
	-> (queried target -> required target) -> source -> source
change lens f source = let (q :*: r) = (=-) . (=-) ..: lens =- source in r =- f q

type Prism available set subset =
	set --> (((:+:>) (available subset) =!?= (<--) (available subset)) set)

review :: Prism available set subset -> set -> available subset
review prism set = case prism =- set of
	FG_ (Straight (This subset)) -> subset
	FG_ (Straight (That m)) -> m =- set

-- TODO: think about composition between different type of optics
-- TODO: Lens and Prism types looks the same so maybe we can just generalize them somehow
-- TODO: think about cardinality in a target of Lens
