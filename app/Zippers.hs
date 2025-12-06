module Zippers where

import AST


{-
======================================================
|                EXPRESSION NAVIGATION               |
======================================================
-}

class TreeZipper z d where
  -- Traverse the tree
  goUp :: z -> Maybe z
  goDown :: z -> Maybe z
  goLeft :: z -> Maybe z
  goDown :: z -> Maybe z
  -- Gets the data stored at the current 'node'
  getData :: z -> d

data PathChoice = PathChoice {
  leftSiblings :: [Expression],
  parentData :: ExpressionData,
  rightSiblings :: [Expression]
}

type Location = [PathChoice]

data ExprZipper = ExprZipper {
  subexpr :: Expression,
  location :: Location
}

instance TreeZipper ExprZipper ExpressionData where
  goUp z =
    case location z of
      [] -> Nothing
      lastChoice : choices -> Just ExprZipper {
        subexpr = 
          Expr (parentData lastChoice) (leftSiblings lastChoice ++ (subexpr z : rightSiblings lastChoice)),
        location = choices
      }
  -- Goes to the leftmost subexpression by default.
  goDown z =
    case subexpr z of
      Expr _ [] -> Nothing
      Expr exprData (lExpr : exprs) ->
        Just ExprZipper {
          subexpr = lExpr,
          location = PathChoice {
            leftSiblings = [],
            parentData = exprData,
            rightSiblings = exprs
          } : location z
        }
  goLeft z =
    case location z of
      [] -> Nothing
      lastChoice : choices ->
        case leftSiblings lastChoice of
          [] -> Nothing
          l : ls ->
            Just ExprZipper {
              subexpr = l,
              location = PathChoice {
                leftSiblings = ls,
                parentData = parentData lastChoice,
                rightSiblings = subexpr z : rightSiblings lastChoice
              } : choices
            }
  goRight z =
    case location z of
      [] -> Nothing
      lastChoice : choices ->
        case rightSiblings lastChoice of
          [] -> Nothing
          r : rs ->
            Just ExprZipper {
              subexpr = r,
              location = PathChoice {
                leftSiblings = subexpr z : leftSiblings lastChoice,
                parentData = parentData lastChoice,
                rightSiblings = rs
              } : choices
            }
  getData z =
    case subexpr z of
      Expression d _ -> d

-- Goes to the top and shows the expression.
instance Show ExprZipper where
  show z =
    case goUp z of
      Nothing -> show (subexpr z)
      Just z' -> show z'


{-
======================================================
|                HOLE-SPECIFIC ZIPPERS               |
======================================================
-}

{-
If there are no holes to track, holeTracked is Nothing and
the HoleZipper tracks the top of the program.
-}
data HoleZipper = HoleZipper {
  zipper :: ExprZipper,
  global :: Context,
  local :: Context
}

{-
Both get a piece of expression data, and if it
represents an abstraction (either top-level or lambda),
adds to the context or removes accordingly.
-}
addToContext :: ExpressionData -> Context -> Context
addToContext d =
  case d of
  
-- WE NEED: Solidification of Types!

instance TreeZipper HoleZipper where
  goLeft HoleZipper{zipper = z, context = ctxt } = do
    z' <- goLeft z
    return HoleZipper{zipper = z', context = ctxt }
  goRight HoleZipper{zipper = z, context = ctxt } = do
    z' <- goRight z
    return HoleZipper{zipper = z', context = ctxt }
  goUp HoleZipper{zipper = z, context = ctxt } = do
    z' <- goUp z
    return HoleZipper{zipper = z', context = ctxt }
  goDown HoleZipper{zipper = z, context = ctxt } = do
    z' <- goDown z
    return HoleZipper{zipper = z', context = ctxt }



-- Attempts to find a hole below the zipper to track.
trackHole :: Context -> ExprZipper -> Maybe HoleZipper 
trackHole ctxt ez =
  case subexpr ez of
    Expr (IDHole id t) [] -> Just HoleZipper {
      zipper = ez,
      context = ctxt,
      holeTracked = Just id
    }
    Expr (Lambda )

--
nextHole :: HoleZipper -> HoleZipper
