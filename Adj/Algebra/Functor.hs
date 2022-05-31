module Adj.Algebra.Functor where

import Adj.Algebra.Category (Category)

{- |
> * Identity preserving: map identity ≡ identity
> * Composition preserving: map (f . g) ≡ map f . map g
-}

class (Category source, Category target) => Functor source target t where
	map :: source a b -> target (t a) (t b)
