module Adj.Program.Construction where

import Adj.Algebra.Category ((.), (.:), Functor (map), (:*:) ((:*:)), type (-->), Flat (Flat))

newtype Construction t a = Construction (a :*: t (Construction t a))

instance Functor (-->) (-->) t => Functor (-->) (-->) (Construction t) where
	map (Flat m) = Flat .: \(Construction (x :*: xs)) ->
		let Flat m' = map @(-->) @(-->) . map @(-->) @(-->) .: Flat m in
		Construction (m x :*: m' xs)
