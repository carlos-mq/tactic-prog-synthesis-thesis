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

-- Zipper Auxiliaries

atRoot :: ExprZipper -> Bool
atRoot z = null (location z)

atLeaf :: ExprZipper -> Bool
atLeaf z =
  case subexpr z of
    Expr _ [] -> True
    _ -> False

atTopLevel :: ExprZipper -> Bool
atTopLevel z =
  case subexpr z of
    Expr (Let _ _) _ -> True
    Expr (LetRec _ _) -> True
    _ -> False

atLambda :: ExprZipper -> Bool
atLambda z =
  case subexpr z of
    Expr (Lambda _ _) _ -> True
    _ -> False

-- If pointing at a variable, top-level, or lambda, obtains its data.
getData :: ExprZipper -> Maybe (String, Type)
getData z =
  case subexpr z of
    Expr (Var s t) _ -> Just (s, t)
    Expr (Let s t) _ -> Just (s, t)
    Expr (LetRec s t) _ -> Just (s, t)
    Expr (Lambda s t) _ -> Just (s, t)
    _ -> Nothing


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
|                CONTEXT UPDATING                    |
======================================================
Ideas:
1. Try to always keep track of a global context and an
_usable_ global context.
2. In particular, the global context is only changed by
definitions;
3. On the other hand, the _usable_ global context will consist of
  the global context minus the current top-level.
4. Therefore, it suffices to have an unchangeable global context
(only changeable by definitions) and a tracker of the current top-level.

The top-level:
Only changes with goLeft or goRight whenever the parent
is Program. In all other cases it doesn't change.
-}

-- If we are positioned at a top-level, gets its name.
getTopLevelName :: HoleZipper -> Maybe String
getTopLevelName hz
  | atTopLevel (zipper hz) =
    case getData (zipper hz) of
      Just (name, _) -> name
      _ -> Nothing
  | otherwise = Nothing 

-- If we are positioned at a lambda, gets its data.
getLambdaName :: HoleZipper -> Maybe (String, Type)
getLambdaName hz
  | atLambda (zipper hz) = getData (zipper hz)
  | otherwise = Nothing


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
  topLevel :: String,
  local :: Context
}
  
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

-- In each step until the top, try trackHole again.
-- If the top is reached, stay there.
nextHole :: HoleZipper -> HoleZipper
