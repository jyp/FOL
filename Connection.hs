module FOL.Connection where

import Control.Applicative
import FOL.Tableau
import FOL.Search
import FOL.CNF
import FOL.Unification

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

-- | Try to close the 1st term of the 1st branch in the tableau.
connection :: (Monad m, Alternative m)
           => [Clause] -> Tableau -> m (Substitution, Tableau)
connection cl t@(_fvs, branches) = do 
  let ((l0:_) : _otherBranches) = branches      -- first literal of the first branch
  c@(_fvs, ls) <- choose cl       -- try any clause
  (i, l) <- choose (zip [0..] ls) -- try any literal in the clause
  unifier <- try $ unifyTop (l0, l)   -- try to unify l0 and l
  let t' = applyS unifier t
      c' = applyS unifier <$> (c `without` i)
  -- Unifier succeds;
  return (unifier, extendUsingClause c' t')

-- | Remove the ith literal from a clause
without :: (a, [b]) -> Int -> (a, [b])
without (fvs,ls) i = (fvs, help ls i)
 where help [] _ = []
       help (_:xs) 0 = xs
       help (x:xs) n = x : help xs (n - 1)

-- >>> ('z',"abcde") `without` 3
-- ('z',"abce")

refuteD :: [Clause] -> Tableau -> Search Substitution
refuteD cls t
  | finished t = return idSubst
  | otherwise = do
      (mgu, t') <- connection cls t
      (`after` mgu) <$> (deeper $ refuteD (rotate cls) $ filterClosed t')

-- Question : Do we have to apply the normal closure rule (now called reduction) for completeness?

-- refute depth initialClause clauseSet
refute :: Int -> Clause -> [Clause] -> Maybe Substitution
refute d c cs = case runSearch (refuteD
                                cs
                                t0) d of
                  [] -> Nothing
                  (x:_) -> Just x
    where t0 = extendUsingClause c initialTableau




