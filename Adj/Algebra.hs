{-# OPTIONS_GHC -fno-warn-orphans #-}
module Adj.Algebra (module Exports, Covariant) where

import Adj.Algebra.Semigroupoid as Exports
import Adj.Algebra.Category as Exports
import Adj.Algebra.Functor as Exports
import Adj.Algebra.Morphism as Exports
import Adj.Algebra.Product as Exports
import Adj.Algebra.Sum as Exports
import Adj.Algebra.Initial as Exports
import Adj.Algebra.Terminal as Exports
import Adj.Algebra.Unit as Exports

type family Covariant x source target functor where
	Covariant Functor source target functor = 
		Functor (Flat source) (Flat target) functor 

type family Contravariant x source target functor where
	Contravariant Functor source target functor = 
		Functor (Flat source) (Dual target) functor 

instance Functor (-->) (-->) ((Flat (:*:)) left) where
	map (Flat m) = Flat .: \case
		Flat (left :*: right) -> Flat (left :*: m right)

instance Functor (-->) (-->) ((Flat (:+:)) left) where
	map (Flat m) = Flat .: \case
		Flat (Option left) -> Flat (Option left)
		Flat (Adoption right) -> Flat (Adoption .: m right)

instance Functor (-->) (-->) ((Dual (:*:)) right) where
	map (Flat m) = Flat .: \case
		Dual (left :*: right) -> Dual (m left :*: right)

instance Functor (-->) (-->) ((Dual (:+:)) right) where
	map (Flat m) = Flat .: \case
		Dual (Option left) -> Dual (Option .: m left)
		Dual (Adoption right) -> Dual (Adoption right)
