module Adj.Program.Controlflow.Implementation.Optics where

import Adj.Auxiliary ((=-), type (=!?=), FG_ (FG_), FFGHH__ (FFGHH__), FFGHHI__ (FFGHHI__))
import Adj.Algebra.Category (type (<--), type (-->), type (:+:>), (.), (.:), Opposite (Opposite), Straight (Straight), Identity (Identity), extract)
import Adj.Algebra.Set ((:+:) (This, That), (:*:) ((:*:)))
import Adj.Program.Controlflow.Implementation.Store (Store)

type Lens queried required = FFGHH__ (-->)
	Identity (Opposite (Store queried required))

view :: Lens queried required source target -> source -> queried target
view (FFGHH__ lens) source =
	let (Opposite (FFGHHI__ store)) = lens =- Identity source
	in extract . Opposite . (=-) . (=-) .: store

change :: Lens queried required source target
	-> (queried target -> required target) -> source -> source
change (FFGHH__ lens) f source =
	let (Opposite (FFGHHI__ store)) = lens =- Identity source in
	let (q :*: r) = (=-) . (=-) .: store in
	r =- f q

type Prism available set subset =
	set --> (((:+:>) (available subset) =!?= (<--) (available subset)) set)

review :: Prism available set subset -> set -> available subset
review prism set = case prism =- set of
	FG_ (Straight (This subset)) -> subset
	FG_ (Straight (That m)) -> m =- set

-- TODO: think about composition between different type of optics
-- TODO: Lens and Prism types looks the same so maybe we can just generalize them somehow
-- TODO: think about cardinality in a target of Lens
