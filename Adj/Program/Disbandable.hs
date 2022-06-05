module Adj.Program.Disbandable where

class Disbandable t where
	{-# MINIMAL (=-), (-=) #-}
	type Primary t a :: *
	(=-) :: t a -> Primary t a
	(-=) :: Primary t a -> t a
