{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module FOL.Tableau where

import FOL.Search
import FOL.CNF
import FOL.Unification
import Control.Applicative
import Data.Tree
import Data.Maybe
import Control.Arrow (second)

type Tableau = (Int, [Branch]) -- (freeVars, openBranches)  loss of sharing possible. (we have to refute all the branches)
type Branch = [SimpleTerm] -- interpreted as a conjunction (which we have to refute)

-- | All pairs in a list
pairs :: [a] -> [(a, a)]
pairs (x:xs) = map (\y -> (x, y)) xs ++ pairs xs
pairs [] = []

-- | is a branch closed?
isClosed :: Branch -> Bool
isClosed = any opposed . pairs

-- | Two terms directly incompatible?
opposed :: (SimpleTerm, SimpleTerm) -> Bool
opposed ((tru1, t1), (tru2, t2)) = tru1 /= tru2 && t1 == t2

-- | All the MGUs able to close a branch
branchClosingMGUs :: Branch -> [Substitution]
branchClosingMGUs = catMaybes . map unifyTop . pairs

---------------------------------------------------
-- Tableau queries

finished :: Tableau -> Bool
finished = null . snd

-- | All the MGU able to close any branch
possibleMGUs :: Tableau -> [Substitution]
possibleMGUs (_, bs) = concatMap branchClosingMGUs bs

------------------------------
-- Tableau combinators

initialTableau :: Tableau
initialTableau = (0, [[]])

-- | remove all closed branches
filterClosed :: Tableau -> Tableau
filterClosed (fv, bs) = (fv, filter (not . isClosed) bs)

-- | apply an MGU to the whole tableau
applySubstTabl :: Substitution -> Tableau -> Tableau
applySubstTabl s (fv, t) = (fv, map (map (second (applySubst s))) t) 

instance Substable Tableau where
  applyS = applySubstTabl

-- | Extend the 1st branch using a given clause c = l1 ∨ l2 ... ∨ ln.
-- The clause is split into literals l_i. We add each of the l_i to the branch,
-- creating a new branch for each.
-- (If we're able to refute every case of the disjuction then we'd be done).
extendUsingClause :: Clause -> Tableau -> Tableau
extendUsingClause (clausFreeVars, conjuncts) (tablFreeVars,(b:branches))
  = (tablFreeVars + clausFreeVars, [ l:b |
                                     l <- clauseShiftVars tablFreeVars conjuncts
                                     -- use fresh variables.
                                         ] ++ branches)

---------------------------------------------
-- Depth-bounded search with backtracking

-- There will be at most one branch in this kind of tableau.

-- Assume a list of true clauses.
-- Pick one of the clauses, add it to the branch.
-- Stop when there is a contradiction.

refuteSimpleD :: [Clause] -> Tableau -> Search [Substitution]
refuteSimpleD cs@(c:cs') t
   | finished t = return []
   | otherwise
   =   do deeper $ refuteSimpleD cs' -- keep going using the rest of the clauses
                   (extendUsingClause c t) -- try the 1st clause
  <|>  do mgu <- choose (possibleMGUs t) -- see if we can close any branch
          (mgu:) <$> refuteSimpleD cs (filterClosed $ applySubstTabl mgu t) -- go ahead


refute :: Int -> [Clause] -> Maybe [Substitution]
refute d cs = listToMaybe $
                    runSearch (refuteSimpleD
                               (cycle cs) -- infinite supply of facts (try those in round-robin)
                                initialTableau) d

-------------------------------------
--  "Incomplete" utilities.

-- | Close the 1st branch using the 1st mgu.
close1 :: Tableau -> Tableau
close1 (fv, b:bs) = filterClosed $ applySubstTabl mgu (fv, b:bs)
    where (mgu:_) = branchClosingMGUs b

rotateBranches :: Tableau -> Tableau
rotateBranches (t, bs) = (t, rotate bs)

rotate :: [a] -> [a]
rotate (x:xs) = xs ++ [x]
