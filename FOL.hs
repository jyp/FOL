{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
module FOL.FOL where

import Text.PrettyPrint.HughesPJ hiding ((<>))

import Numeric
import Control.Monad (ap)
import Data.Function (on)

-- Nested abstract syntax
data Term a
  = App String [Term a]
  | Var a
  | All (Term (Maybe a))
  | Exi (Term (Maybe a))
  | Not (Term a)
  | And (Term a) (Term a)
  | Or  (Term a) (Term a)
  | Tru 
  | Fal
  deriving (Functor, Traversable, Foldable, Eq)

instance Applicative Term where
  pure = Var
  (<*>) = ap
instance Monad Term where
  t >>= s = case t of
    Var x -> s x
    Tru -> Tru
    Fal -> Fal
    App f xs -> App f ((>>= s) <$> xs)
    Or u v -> Or (u >>= s) (v >>= s)
    And u v -> And (u >>= s) (v >>= s)
    Not u -> Not (u >>= s)
    All u -> All (u >>= liftSubst s)
    Exi u -> Exi (u >>= liftSubst s)

liftSubst :: (a -> Term b) -> (Maybe a -> Term (Maybe b))
liftSubst f = \case
  Nothing -> Var Nothing
  Just t -> wk (f t)


wk :: Term a -> Term (Maybe a)
wk = fmap Just

subst0 :: Term (Maybe a) -> Term a -> Term a
subst0 s t = s >>= \case
  Nothing -> t
  Just x -> Var x
  
data Value 
  = Free Int -- argument is deBruijn *level* of the variable
  | VApp String [Value]
  | VAll (Value -> Value)
  | VExi (Value -> Value)
  | VNot Value
  | VAnd Value Value
  | VOr  Value Value
  | VTru
  | VFal

instance Eq Value where
  (==) = (==) `on` doQuote

(⟶) :: Value -> Value -> Value
x ⟶ y = VNot x `VOr` y

(∨), (∧) :: Value -> Value -> Value
(∨) = VOr
(∧) = VAnd

class DeBruijn a where
  toDB :: Int -> a

data Void

magic :: Void -> Int
magic = \case

instance DeBruijn Void where
  toDB = error "toDB: oops"

instance DeBruijn a => DeBruijn (Maybe a) where
  toDB 0 = Nothing
  toDB n = Just (toDB (n - 1))

doQuote :: Value -> Term Int
doQuote v = fmap magic (quote @Void 0 v)

-- | Value to Terms. 1st argument is current depth.
quote :: DeBruijn a => Int -> Value -> Term a
quote d (Free i) = Var (toDB (d - i - 1)) -- deBruijn index = current depth - deBruijn level - 1
quote d (VApp s vs) = App s (map (quote d) vs)
quote d (VAnd v u) = And (quote d v) (quote d u)
quote d (VOr v u) = Or (quote d v) (quote d u)
quote d (VNot v) = Not (quote d v)
quote _ (VTru) = Tru
quote _ (VFal) = Fal
quote d (VExi f) = Exi (quote (d + 1) (f (Free d))) 
quote d (VAll f) = All (quote (d + 1) (f (Free d)))

onSubTerms :: (forall a. Term a -> Term a) -> Term a -> Term a
onSubTerms r value = case value of
                       App s ts -> App s (map r ts)
                       All t    -> All (r (t))
                       Exi t    -> Exi (r (t))
                       Not t    -> Not (r t)
                       Or  t u  -> Or (r t) (r u)
                       And t u  -> And (r t) (r u)
                       x -> x

bottomUp :: (forall a. Term a -> Maybe (Term a)) -> Term a  -> Term a
bottomUp f t = case f t' of
                 Nothing -> t'
                 Just t'' -> bottomUp f t''
  where t' = onSubTerms (bottomUp f) t

topDown :: (forall a. Term a  -> Maybe (Term a)) -> Term a  -> Term a
topDown f t = case f t of
                Just t' -> topDown f t'
                Nothing -> onSubTerms (topDown f) t

data Nat = Z | S Nat

smallShow :: Int -> String
smallShow x = showIntAtBase 10 (\i -> "₀₁₂₃₄₅₆₇₈₉" !! i) x []

infnames :: [Char] -> [[Char]]
infnames basenames = [ v ++ n | n <- "" : map smallShow [1..], v <- map (:[]) $ basenames ]

varNames :: [[Char]]
varNames = infnames "xyzvw"

freeVarsNames :: [[Char]]
freeVarsNames = infnames "αβγδηεικλμνπρσφψξζω"

commas :: [Doc] -> Doc
commas = cat . punctuate comma

prec :: Ord a => a -> a -> Doc -> Doc
prec p n = if p < n then parens else id

-- Precedence levels:
-- 0: atoms
-- 1: not
-- 2: ∧
-- 3: ∨
-- 4: ∃, ∀

-- showVar Nothing  (x:xs) = x
-- showVar (Just i) (x:xs) = showVar i xs

nothing :: a -> Maybe a -> a
nothing x Nothing = x
nothing _ (Just x) = x

-- | p: precedence of context; vs: not yet allocated variable names
pretty :: Int -> [String] -> Term Doc -> Doc
pretty p vs term = case term of
                     Tru -> text "⊤"
                     Fal -> text "⊥"
                     Not t -> prec p 1 $ text "¬" <> pretty 1 vs t 
                     App c [] -> text c
                     App c ts -> text c <> parens (commas (map (pretty 3 vs) ts))
                     Var (d) -> d
                     Or t u -> op 3 " ∨ " t u
                     And t u -> op 2 " ∧ " t u
                     All t -> quant "∀" t
                     Exi t -> quant "∃" t
  where quant s t = prec p 4 $ text s <> text v <> text ". " <> pretty 4 vs' (fmap (nothing (text v)) t)
        (v:vs') = vs
        op n s t u = prec p n $ pretty n vs t <> text s <> pretty n vs u

prettyTerm :: Term Int -> Doc
prettyTerm term = pretty 5 varNames ((\i -> text (freeVarsNames !! i)) <$> term)

instance Show (Term Int) where
    show t = show $ prettyTerm t

exampleNaturals :: Term Int
exampleNaturals = doQuote $ foldr1 VAnd [
  nat zero,
  VAll $ \x -> nat x ⟶ nat (suc x)
 ]
 where nat x = VApp "N" [x]
       zero = VApp "Z" []
       suc x  = VApp "S" [x]

var0 = Var (Nothing)
var1 = Var ((Just Nothing))
var2 = Var ((Just (Just (Nothing))))

term1 :: Term a
term1 = All (Not (App "P" [var0]))

-- >>> term1 :: Term Int
-- ∀x. ¬P(x)

term2 :: Term a
term2 = Not (Not (Exi (Not (App "P" [var0]))))

-- >>> term2 :: Term Int
-- ¬¬(∃x. ¬P(x))

term3 :: Term a
term3 = Or term1 term2

-- >>> term3 :: Term Int
-- (∀x. ¬P(x)) ∨ ¬¬(∃x. ¬P(x))

term4 :: Term a
term4 = All $ And (var0) (Or (var0) (term3))

-- >>> term4 :: Term Int
-- ∀x. x ∧ (x ∨ (∀y. ¬P(y)) ∨ ¬¬(∃y. ¬P(y)))

term5 :: Term a
term5 = All $ Exi $ Exi $ App "p" [var2, var1, var0]

-- >>> term5 :: Term Int
-- ∀x. ∃y. ∃z. p(x,y,z)







