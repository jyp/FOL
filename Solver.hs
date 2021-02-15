module FOL.Solver where

import FOL.Regularity
import FOL.FOL
import FOL.CNF
import FOL.Unification

solver :: Foldable t => Int -> t Value -> Maybe [Substitution]
solver maxSteps input = refute maxSteps (xs !! 0) xs
  where xs = toCNF $ doQuote $ foldr1 VAnd input

contradicts :: Int -> [Value] -> Value -> Maybe [Substitution]
contradicts d gamma phi = solver d (phi:gamma)

entails :: Int -> [Value] -> Value -> Maybe [Substitution]
entails d gamma phi = contradicts d gamma (VNot phi)

data Status = Entailment | Contradiction | Neutral deriving (Show, Eq)

tryProve :: Int -> [Value] -> Value -> Status
tryProve d gamma phi = case entails d gamma phi of
  Nothing -> case contradicts d gamma phi of
    Nothing -> Neutral
    _ -> Contradiction
  _ -> Entailment
  