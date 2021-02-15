{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Regularity where

import Control.Applicative
import Search
import Connection (without)
import Unification
import CNF
import Tableau
import qualified Data.Map as M
import Control.Arrow (first)

newtype Constraint = Constraint (Maybe Substitution)
-- Nothing --> No substitution, the constraint can never be satisfied
-- Just x --> all variables need to be substituted to the corresponding literals.

instance Substable Constraint where
  applyS s (Constraint Nothing) = Constraint Nothing -- TODO: clear these constraints
  applyS s (Constraint (Just u))
    = Constraint (unifyAll (both (applyS s)
                            <$> [ (SVar x, t) | (x, t) <- M.assocs u ]))

constraintSatisfied :: Constraint -> Bool
constraintSatisfied (Constraint (Just u)) = M.null u
constraintSatisfied (Constraint Nothing)  = False

-- A regular tableau is one that never contains the same literal
-- twice.  Rather than checking equality explicitly at every point, we
-- remember a bunch of constraints on literals, which, if any of them
-- is satisfied, mean that some literals in the branch are equal.
type RegTableau = (Tableau, [Constraint])

instance Substable RegTableau where
  applyS s (t, cs) = (applyS s t, applyS s cs)

-- | Extend the 1st branch using given clause.
extendUsingClauseReg :: Clause -> RegTableau -> RegTableau
extendUsingClauseReg (clausFreeVars, conjuncts) ((tablFreeVars, (b:branches)), constrs)
  = ((tablFreeVars + clausFreeVars,
      [ l:b |  l <- clause'] ++ branches), -- add the clause as normal
      [Constraint (unifyEq (l, l')) -- record constraint
      | l <- b, -- for every literal in the branch
        l' <- clause' ] ++ constrs -- for every literal in the  clause
     -- Idea. If a literal is found twice exactly the same on a
     -- branch, then we are wasting our time: see below.
     -- Implementation: Whenever a literal (l) is added to a branch
     -- (b), record equations that would yield variable equality.
    )
  where clause' = clauseShiftVars tablFreeVars conjuncts
  -- use fresh variables.

-- | If B a branch containing a literal L and C is a clause whose
-- expansion violates regularity, then C contains L. In order to close
-- the tableau, one needs to expand and close, among others, the
-- branch where B − L, where L occurs twice. However, the formulae in
-- this branch are exactly the same as the formulae of B alone. As a
-- result, the same expansion steps that close B − L also close
-- B. This means that expanding C was unnecessary; moreover, if C
-- contained other literals, its expansion generated other leaves that
-- needed to be closed. In the propositional case, the expansion
-- needed to close these leaves are completely useless; in the
-- first-order case, they may only affect the rest of the tableau
-- because of some unifications; these can however be combined to the
-- substitutions used to close the rest of the tableau.

-- | Read and understand Connection.hs before looking at this.
regularConnection :: (Monad m, Alternative m) => [Clause] -> RegTableau -> m (Substitution, RegTableau)
regularConnection cl t@((_fvs, branches), _constrs) = do
   let ((l0:_) : _) = branches      -- consider the 1st branch
   c@(_fvs, ls) <- choose cl       -- try any clause
   (i, l) <- choose (zip [0..] ls) -- try any literal in the clause
   unifier <- try $ unifyTop (l0, l)
   -- Unifier succeeds;
   let t' = applyS unifier t
       c' = applyS unifier <$> (c `without` i)
   return (unifier, applyS unifier $ extendUsingClauseReg (c' `without` i) $ t')

refuteD :: [Clause] -> RegTableau -> Search [Substitution]
refuteD cls t@((_fvs, branches), constrs)
  | any constraintSatisfied constrs = empty -- Backtrack if any constraint has been met.
  | null branches = return [] -- nothing left to refute
  | otherwise = do
      (unifier, t') <- regularConnection cls t
      (unifier:) <$> (deeper $ refuteD (rotate cls) $ first filterClosed t')

-- | Question : Do we have to apply the normal closure rule (now called
-- reduction) for completeness?

-- refute depth initialClause clauseSet
refute :: Int -> Clause -> [Clause] -> Maybe [Substitution]
refute d c cs = case runSearch (refuteD
                                cs
                                t0) d of
                  [] -> Nothing
                  (x:_) -> Just x
  where t0 = (extendUsingClause c initialTableau, [])

