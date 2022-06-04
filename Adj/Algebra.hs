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
