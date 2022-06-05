module Adj.Program.Construction where

import Adj.Algebra ((.), (.:), Functor (map), (:*:) ((:*:)), type (-->), Flat (Flat))
import Adj.Program.Disbandable ((=-))

newtype Construction t a = Construction (a :*: t (Construction t a))

instance Functor (-->) (-->) t => Functor (-->) (-->) (Construction t) where
	map m = Flat .: \(Construction (x :*: xs)) ->
		Construction (m =- x :*: map @(-->) @(-->) . map @(-->) @(-->) .: m =- xs)
