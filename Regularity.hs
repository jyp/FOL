{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module FOL.Regularity where
 
import Control.Applicative
import FOL.Connection (select', Operation(..),prettyOp,chooseAndAllocateClause)
import FOL.Unification
import FOL.CNF
import FOL.Tableau
import FOL.Search
import qualified Data.Map as M
import Control.Arrow (first)
import Text.PrettyPrint.HughesPJ hiding ((<>),empty,first)

newtype Constraint = Constraint {fromConstraint :: (Maybe Substitution)} deriving Show
-- Nothing --> No substitution, the constraint can never be satisfied
-- Just x --> all variables need to be substituted to the corresponding literals.

instance Substable Constraint where
  applyS _ (Constraint Nothing) = Constraint Nothing
  applyS s (Constraint (Just (Subst u)))
    = Constraint (unifyAll (both (applyS s)
                            <$> [ (SVar x, t) | (x, t) <- M.assocs u ]))

sweepConstraints :: [Constraint] -> [Constraint]
sweepConstraints = filter (not . unsatisfiable)

unsatisfiable :: Constraint -> Bool
unsatisfiable = \case Constraint Nothing -> True
                      _ -> False

constraintSatisfied :: Constraint -> Bool
constraintSatisfied (Constraint (Just (Subst u))) = M.null u
constraintSatisfied (Constraint Nothing)  = False

-- A regular tableau is one that never contains the same literal
-- twice.  Rather than checking equality explicitly at every point, we
-- remember a bunch of constraints on literals, which, if any of them
-- is satisfied, mean that some literals in the branch are equal.
type RegTableau = (Tableau, [Constraint])

instance Substable RegTableau where
  applyS s (t, cs) = (applyS s t, sweepConstraints (applyS s cs))

-- | Extend the 1st branch using given clause.
extendUsingClauseReg :: NakedClause -> RegTableau -> RegTableau
extendUsingClauseReg clause' ((fvs,b:branches), constrs)
  = ((fvs,
      [ l:b |  l <- clause'] -- each conjunct in the new clause generates a new goal, together with the rest of the disjuncts of the branch
      ++ branches  -- all the old goals remain
     ),
      sweepConstraints [Constraint (unifyEq (l, l')) -- record constraint
                       | l <- b, -- for every literal in the branch
                         l' <- clause' ] ++ constrs -- for every literal in the clause
     -- Idea. If a literal is found twice exactly the same on a
     -- branch, then we are wasting our time. We should have proven
     -- the first literal immediately instead of proving a copy of
     -- it. See also below.  Implementation: Whenever a literal (l) is
     -- added to a branch (b), record equations that would yield
     -- variable equality.  If we ever make those equal, backtrack.
    )
  -- use fresh variables.

-- If B is a branch containing a literal L and C is a clause whose
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

-- Read and understand Connection.hs before looking at this.
regularConnection :: [Clause] -> RegTableau -> Search (Operation, RegTableau)
regularConnection cls (t0@(_, branches), constrs) = do
  let ((l0:_) : _) = branches     -- Try to refute the 1st literal of the 1st branch.
  (c,t) <- chooseAndAllocateClause cls t0 -- try any clause
  (l, cRest) <- choose (select' c) -- try any literal in the clause
  unifier <- try $ unifyTop (l0, l)
  -- Unifier succeeds;
  let t' = applyS unifier t
      c' = applyS unifier <$> cRest
  return (Connection c l0 unifier c',
          (extendUsingClauseReg c' (t',constrs)))



refuteD :: [Clause] -> RegTableau -> Search [(RegTableau,Operation)]
refuteD cls t@((_fvs, branches), constrs)
  | any constraintSatisfied constrs = empty -- Backtrack if any constraint has been met.
  | null branches = return [] -- nothing left to refute
  | otherwise = do
      (op, t') <- regularConnection cls t
      let closed_t' = first filterClosed t'
      (\ops -> (t,op):(t',Close):ops) <$> (deeper $ refuteD (rotate cls) closed_t')

-- refute depth initialClause clauseSet
refute :: Int -> [Clause] -> Maybe [(RegTableau,Operation)]
refute d cs = runSearchAt d $ do
          (c,t) <- chooseAndAllocateClause cs initialTableau -- any of the clause may yield a
                         -- contradiction but some will be just
                         -- neutral, so we need to try them all
          refuteD cs (extendUsingClause c t, [])


prettyRegTabl :: RegTableau -> Doc
prettyRegTabl (t,cs) = vcat [hang (text "Goals") 2 (prettyTabl t),
                             hang (text "Constraints") 2 (vcat $ fmap prettyConstraint cs)]

prettyTrace :: [(RegTableau, Operation)] -> Doc
prettyTrace trace = vcat $ concat [[prettyRegTabl t, prettyOp op] | (t,op)  <- trace]

prettyConstraint :: Constraint -> Doc
prettyConstraint (Constraint Nothing) = text "Unsat"
prettyConstraint (Constraint (Just s)) = prettySubst s
