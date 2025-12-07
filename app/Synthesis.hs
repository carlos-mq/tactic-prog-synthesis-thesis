module Synthesis where

import AST

-- Idea: a Tactic Tempalte 

data SynthState = SynthState {
  zipper :: HoleZipper
  localContext :: Context
  nextId :: Int
}

type Tactic = Context -> Type -> Maybe Expression

intro :: 