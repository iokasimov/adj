module Adj.Algebra.Unit where

type family Unit (p :: * -> * -> *) = r | r -> p
