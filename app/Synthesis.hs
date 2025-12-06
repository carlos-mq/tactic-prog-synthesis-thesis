module Synthesis where

import AST

-- Idea: have a general ExprZipper (for the atomic steps),
-- and a specific HoleZipper that we're keeping track of.

data SynthState = SynthState {
  zipper :: HoleZipper
  localContext :: Context
  nextId :: Int
}

type Tactic = Context -> Type -> Maybe Expression

intro :: 