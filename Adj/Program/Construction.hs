module Adj.Program.Construction where

import Adj.Algebra.Product ((:*:))

newtype Construction t a = Construction (a :*: t (Construction t a))
