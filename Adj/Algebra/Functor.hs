module Adj.Algebra.Functor where

import Adj.Algebra.Category (Category)

{- |
> * Identity preserving: map identity ≡ identity
> * Composition preserving: map (f . g) ≡ map f . map g
-}

class (Category from, Category to) => Functor from to functor where
	map :: from source target -> to (functor source) (functor target)
