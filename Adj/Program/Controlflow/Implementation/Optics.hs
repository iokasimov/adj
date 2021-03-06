{-# OPTIONS_GHC -fno-warn-orphans #-}

module Adj.Program.Controlflow.Implementation.Optics where

import Adj.Auxiliary ((=-), type (=!?=), FG_ (FG_), FFGHH__ (FFGHH__), FFGHHI__ (FFGHHI__))
import Adj.Algebra.Category (Semigroupoid ((.)), Category (identity), type (<--), type (-->), type (:+:>), (.), (.:), Opposite (Opposite), Straight (Straight), Identity (Identity), (->>-), extract)
import Adj.Algebra.Set ((:+:) (This, That), (:*:) ((:*:)))
import Adj.Program.Primitive.Maybe (Maybe, pattern Some, pattern None)
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

-- TODO: simplify, it looks awful
instance Semigroupoid (Lens Maybe Identity) where
	FFGHH__ to . FFGHH__ from = FFGHH__ . Straight .: \case
		Identity source -> case from =- Identity source of
			Opposite (FFGHHI__ (FG_ (Straight (Some between :*: Straight mb)))) ->
				let (Opposite (FFGHHI__ (FG_ (Straight (target :*: Straight mt))))) = to =- Identity between in
				Opposite (FFGHHI__ (FG_ (Straight (target :*: Straight (mb . Identity . mt)))))
			Opposite (FFGHHI__ (FG_ (Straight (_ :*: _)))) ->
				Opposite (FFGHHI__ (FG_ (Straight (None :*: (Straight .: \_ -> source)))))

instance Category (Lens Maybe Identity) where
	identity = FFGHH__ . Straight .: \(Identity source) -> Opposite
		-- TODO: replace =- with extract
		(FFGHHI__ (FG_ (Straight (Some source :*: Straight .: (=-) . identity))))

-- TODO: to proceed with this instance we should explore Store capabilities more
-- instance Functor (-->) (-->) f => Functor (Lens Maybe Identity) (Lens Maybe Identity) f where
	-- map (FFGHH__ lens) = FFGHH__ . Straight .: \(Identity fs) ->
		-- let f_lens :: f (Store Maybe Identity target source) = (=-) lens . Identity ->>- fs in

type Prism available set subset =
	set --> (((:+:>) (available subset) =!?= (<--) (available subset)) set)

review :: Prism available set subset -> set -> available subset
review prism set = case prism =- set of
	FG_ (Straight (This subset)) -> subset
	FG_ (Straight (That m)) -> m =- set

-- TODO: think about composition between different type of optics
-- TODO: Lens and Prism types looks the same so maybe we can just generalize them somehow
-- TODO: think about cardinality in a target of Lens
