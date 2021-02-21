{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
module FOL.Connection where

import Control.Applicative
import FOL.Tableau
import FOL.Search
import FOL.CNF
import FOL.Unification
import Control.Arrow (second)
import Text.PrettyPrint.HughesPJ hiding ((<>),empty,first)

-- This is a prolog-style search. We keep a list of "goals" to fulfill (this is the 1st branch)
-- Example 1:
--  the (first) branch is f(x) ∨ g(y)
-- We know that we must refute f(x)
-- Say we find a clause like this:
--  ¬h(y) ∨ f(y)   (ie. h(z) -> f(y))
-- Then we have the unification: x = y
-- and h(z) ∨ g(y) is added as a new goal.

-- Say we find a clause like this:
--  ¬h(y) ∨ f(y) ∨ i(Z)   (ie. (h(z) ∧ ¬i(Z))  -> f(y))
-- Then we have the unification: x = y
-- we have now two goals:
-- h(z) ∨ g(z) and i(Z) ∨ g(z) 


-- | Choose a clause, and allocate new variables for it so they don't
-- clash with those in the tableau. The returned tableau takes this
-- into account, having more free variables.
chooseAndAllocateClause :: [Clause] -> Tableau -> Search (NakedClause,Tableau)
chooseAndAllocateClause cls (fvs,branches) = do
  (cFvs,c) <- choose cls
  return (clauseShiftVars fvs c,(fvs+cFvs,branches))
  

-- | Try to close the 1st term of the 1st branch in the tableau.
connection :: [Clause] -> Tableau -> Search (Operation,Tableau)
connection cls t0@(_fvs, branches) = do 
  let ((l0:_) : _otherBranches) = branches      -- first literal of the first branch (we do other branches later)
  (c,t) <- chooseAndAllocateClause cls t0                  -- try any clause
  (l, cRest) <- choose (select' c) -- try any literal in the clause
  unifier <- try $ unifyTop (l0, l)   -- try to unify l0 and l
  let t' = applyS unifier t
      c' = applyS unifier <$> cRest
  -- Unifier succeds;
  return (Connection c l0 unifier c', extendUsingClause c' t')

select' :: [b] -> [(b,[b])]
select' [] = []
select' (x:xs) = (x,xs): map (second (x:)) (select' xs)

-- >>> select' "abcde"
-- [('a',"bcde"),('b',"acde"),('c',"abde"),('d',"abce"),('e',"abcd")]

select :: (a, [b]) -> [(b,(a, [b]))]
select (fvs,ls) = map (second (fvs,)) (select' ls)

refuteD :: [Clause] -> Tableau -> Search [(Tableau,Operation)]
refuteD cls t
  | finished t = return []
  | otherwise = do
      (op, t') <- connection cls t
      (\ops -> (t,op):(t',Close):ops) <$> (deeper $ refuteD (rotate cls) $ filterClosed t')

-- Question : Do we have to apply the normal closure rule (now called reduction) for completeness?

-- refute depth initialClause clauseSet
refute :: Int -> [Clause] -> Maybe [(Tableau,Operation)]
refute d cs = runSearchAt d $ do
  (c,t) <- chooseAndAllocateClause cs initialTableau -- any of the clause may yield a contradiction but
                 -- some will be just neutral, so we need to try them
                 -- all
  refuteD cs (extendUsingClause c t)

data Operation = Connection NakedClause SimpleTerm Substitution NakedClause | Close

prettyOp :: Operation -> Doc
prettyOp = \case
  Close -> text "Close"
  Connection cl t s cl' -> hang (text "Connect") 2 $
                            cat [prettyClause cl <> text " and ", prettySimpleTerm t <> text " with ", prettySubst s <> text " yielding ", prettyClause cl']

prettyTrace :: [(Tableau, Operation)] -> Doc
prettyTrace trace = vcat $ concat [[hang (text "Goals") 2 (prettyTabl t),
                                    prettyOp op] | (t,op)  <- trace]
