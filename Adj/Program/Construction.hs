module Adj.Program.Construction where

import Adj.Algebra.Morphism.Flat (type (-->), Flat (Flat))
import Adj.Algebra.Semigroupoid ((.))
import Adj.Algebra.Functor (Functor (map))
import Adj.Algebra.Product ((:*:) ((:*:)))

newtype Construction t a = Construction (a :*: t (Construction t a))

instance Functor (-->) (-->) t => Functor (-->) (-->) (Construction t) where
	map (Flat m) = Flat (\(Construction (x :*: xs)) ->
		let Flat m' = (map @(-->) @(-->) . map @(-->) @(-->)) (Flat m) in
		Construction (m x :*: m' xs))
