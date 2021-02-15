{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module FOL.Unification where

import FOL.FOL (prettyTerm,freeVarsNames)
import FOL.CNF
import qualified Data.Map as M
import Data.Map (Map)
import Control.Arrow (second)
import Text.PrettyPrint.HughesPJ hiding ((<>))

newtype Substitution = Subst (Map Int Literal)

class Substable t where
  applyS :: Substitution -> t -> t

instance Substable a => Substable [a] where
  applyS s = fmap (applyS s)

idSubst :: Substitution
idSubst = Subst M.empty

-- | Add an "assignment" to a substitution
(+>) :: Substitution -> (Int, Literal) -> Substitution
Subst s +> (x, t) = Subst (M.insert x t (M.map (applySubst (x ==> t)) s))

-- | Single literal substitution
(==>) :: Int -> Literal -> Substitution
x ==> t = Subst (M.singleton x t)

instance Substable Literal where
  applyS = applySubst

instance Substable Substitution where
  applyS s (Subst t) = Subst (fmap (applySubst s) t)

after :: Substable t => Substitution -> t -> t
t `after` s = applyS t s

applySubst :: Substitution -> Literal -> Literal
applySubst (Subst f) (SVar i) = case M.lookup i f of
                                  Nothing -> SVar i
                                  Just t -> t
applySubst f (SApp c xs) = SApp c (map (applySubst f) xs)

instance Substable SimpleTerm where
  applyS = applySubst'

applySubst' :: Substitution -> SimpleTerm -> SimpleTerm
applySubst' s = second (applyS s)

occursIn :: Int -> Literal -> Bool
occursIn x t = x `elem` varsOf t []

both :: (t -> b) -> (t, t) -> (b, b)
both f (a, b) = (f a, f b)

-- | Unify two terms only if they are equal
unifyEq :: (SimpleTerm, SimpleTerm) -> Maybe Substitution
unifyEq ((tru1, t1), (tru2, t2)) | tru1 /= tru2 = Nothing
                                 | otherwise = unifyAll [(t1, t2)]

-- | Unify two terms only if they are the negation of each other.
unifyTop :: (SimpleTerm, SimpleTerm) -> Maybe Substitution
unifyTop ((tru1, t1), (tru2, t2)) | tru1 == tru2 = Nothing
                                  | otherwise = unifyAll [(t1, t2)]

unifyAll :: [(Literal, Literal)] -> Maybe Substitution
unifyAll us = unify us idSubst

-- Implementation of MGU algorithm given on slide 29.
unify :: [(Literal, Literal)] -> Substitution -> Maybe Substitution
unify [] s = Just s -- base
unify ((t1, t2) : ts) s 
  | t1 == t2 = unify ts s -- Trivial
unify ((SApp c xs, SApp d ys) : ts) s
  | c == d    = unify (zip xs ys ++ ts) s -- Decompose
  | otherwise = Nothing -- Clash
unify ((SVar x, t) : ts) s 
  | x `occursIn` t = Nothing -- Occurs check
  | otherwise      = unify (map (both (applySubst (x ==> t))) ts) (s +> (x, t))
unify ((t, SVar i) : ts) s = unify ((SVar i, t) : ts) s -- Orient

mgu :: SimpleTerm -> SimpleTerm -> Maybe Substitution
mgu t u = unifyTop (t, u)

-- example slide 31
sterm1 :: Literal
sterm1 = SApp "f" [SApp "g" [SVar 0, SVar 1], SVar 1]

sterm2 :: Literal
sterm2 = SApp "f" [SVar 2, SApp "h" [SVar 3]]

exampleSlide31 :: Maybe Substitution
exampleSlide31 = unify [(sterm1, sterm2)] idSubst

prettySubst :: Substitution -> Doc
prettySubst (Subst s) = braces $ cat $ [text (freeVarsNames !! i) <> text " ↦ " <> (prettyTerm . litToTerm) t <> text "," | (i,t) <- M.assocs s]

instance Show Substitution where
  show = show . prettySubst

-- >>> exampleSlide31
-- Just {β ↦ h(δ),γ ↦ g(α,h(δ)),}

