module Adj.Program.Construction where

import Adj.Algebra ((.), (.:), Functor (map), (:*:) ((:*:)), type (-->), Flat (Flat))
import Adj.Program.Disbandable (Disbandable (Primary, (=-), (-=)))

newtype Construction t a = Construction (a :*: t (Construction t a))

instance Disbandable (Construction t) where
	type Primary (Construction t) a = a :*: t (Construction t a)
	(=-) (Construction m) = m
	(-=) m = Construction m

instance Functor (-->) (-->) t => Functor (-->) (-->) (Construction t) where
	map m = Flat .: \(Construction (x :*: xs)) ->
		Construction (m =- x :*: map @(-->) @(-->) . map @(-->) @(-->) .: m =- xs)
