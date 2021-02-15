{-# LANGUAGE
    LambdaCase #-}

module FOL.CNF where

import FOL.FOL

import Data.Char
import Control.Arrow (first, second)
import Control.Monad.State

------------------------------------------------------------------------------------

-- | negation normal form step
nnfStep :: Term a -> Maybe (Term a)
nnfStep (Not Fal) = Just Tru
nnfStep (Not Tru) = Just Fal
nnfStep (Not (Not t)) = Just t
nnfStep (Not (All t)) = Just $ Exi (Not t)
nnfStep (Not (Exi t)) = Just $ All (Not t)
nnfStep (Not (Or t u)) = Just $ And (Not t) (Not u)
nnfStep (Not (And t u)) = Just $ Or (Not t) (Not u)
nnfStep _ = Nothing

toNNF :: Term a -> Term a
toNNF = topDown nnfStep


skolem :: [Term a] -> Term a -> State [String] (Term a)
skolem vs = \case
  (All t) -> All <$> skolem (Var Nothing:(wk <$> vs)) t
  (Exi t) -> do
    fs <- get
    let f:_ = fs
    modify tail
    t' <- skolem (wk <$> vs) t
    return (subst0 t' (App f vs))
  (Not x) -> Not <$> skolem vs x
  Or x y -> Or <$> skolem vs x <*> skolem vs y
  And x y -> And <$> skolem vs x <*> skolem vs y
  App f xs -> App f <$> traverse (skolem vs) xs
  Var x -> return (Var x)
  Tru -> pure Tru
  Fal -> pure Fal

-- | Skolemization
skolemize :: Term a -> Term a
skolemize t = fst $ runState (skolem  [] t) (map (map toUpper) varNames)

-- | Pull uniersal quantifiers to the top
pullQuantStep :: Term a -> Maybe (Term a)
pullQuantStep (Or  (All f) t) = Just $ All (Or (f) (wk t))
pullQuantStep (Or  t (All f)) = Just $ All (Or (wk t) (f))
pullQuantStep (And (All f) t) = Just $ All (And (f) (wk t))
pullQuantStep (And t (All f)) = Just $ All (And (wk t) (f))
pullQuantStep _ = Nothing

pullQuantifiers :: Term a -> Term a
pullQuantifiers = bottomUp pullQuantStep 

toCNF :: Term Int -> [Clause]
toCNF = map (mkClause . -- turn "Or" into lists
             forgetQuantifiers) . -- remote the (top-level Foralls)
        mkConjuncts . -- distribute all operator over conjuctions (so we optain conjucts)
        pullQuantifiers . -- pull Forall to the top
        skolemize . -- remove Exists
        toNNF  -- push negation down to terms

-- | Replace quantifiers at the top-level by universal variables
forgetQuantifiers :: Term Int -> Term Int
forgetQuantifiers (All t) = forgetQuantifiers (inc <$> t)
  where inc Nothing = 0
        inc (Just x) = 1 + x 
forgetQuantifiers x = x


mkConjuncts :: Term a -> [Term a]
mkConjuncts Tru = []
mkConjuncts (And x y) = mkConjuncts x ++ mkConjuncts y
mkConjuncts (Or x y)  = [Or t u | t <- mkConjuncts x, u <- mkConjuncts y]
mkConjuncts (All x)   = [All t | t <- mkConjuncts x]
mkConjuncts x = [x]



mkNakedClause :: Term Int -> NakedClause
mkNakedClause Fal = []
mkNakedClause (Or x y) = mkNakedClause x ++ mkNakedClause y
mkNakedClause x = [mkSimpleTerm x]

mkClause :: Term Int -> Clause
mkClause t = (1 + foldr max (-1) t, mkNakedClause t)

mkSimpleTerm :: Term Int -> SimpleTerm
mkSimpleTerm (Not x) = (False, mkLit x)
mkSimpleTerm x = (True, mkLit x)

mkLit :: Term Int -> Literal
mkLit (Var x) = SVar x
mkLit (App f xs) = SApp f (map mkLit xs) 
mkLit (Not x) = error "Inner 'Not' is unsupported in mkLit; negation normal form expected in mkConjuncts"
mkLit x = error ("mkLit: not supported: " ++ show x)

----------------------------------------------------------------------------------------
{-
-}

type SimpleTerm = (Bool, Literal)

data Literal
  = SVar Int
  | SApp String [Literal]
  deriving Eq

-- | Understood as a disjuction
type NakedClause = [SimpleTerm]

-- | First component is the number of (free) variables
type Clause = (Int, NakedClause)

shiftVars :: Int -> Literal -> Literal
shiftVars i (SVar x) = SVar (x + i)
shiftVars i (SApp s ls) = SApp s (map (shiftVars i) ls)

-- | "Rename" variables so they do not clash with anything below 'i'.
clauseShiftVars :: Int -> NakedClause -> NakedClause
clauseShiftVars i = map (second (shiftVars i))

varsOf :: Literal -> ([Int] -> [Int])
varsOf (SVar x) = (x:)
varsOf (SApp _ xs) = foldr (.) id $ map varsOf xs

instance Show Literal where
  show = show . litToTerm

showCNF :: [Clause] -> Term Int
showCNF = cnfToTerm

-- q1 :: Term (Either Int a) -> Term a
-- q1 t = case sequenceA t of
--     Right u -> u
--     Left _ -> All (q1 (dec <$> t))
--   where dec (Left 0) = Right Nothing
--         dec (Left n) = Left (n-1)
--         dec (Right x) = Right (Just x)
--         t' = dec <$> t

-- quantify :: Term Int -> Term Void
-- quantify t = q1 (Left <$> t)

cnfToTerm :: [Clause] -> Term Int
cnfToTerm = foldr1 And . map clauseToTerm
  where clauseToTerm (vs, t) = (foldr1 Or . map simpToTerm $ t)
        simpToTerm (b, t) = (if not b then Not else id) (litToTerm t)

litToTerm :: Literal -> Term Int
litToTerm (SApp s args) = App s (map litToTerm args)
litToTerm (SVar i) = Var i


