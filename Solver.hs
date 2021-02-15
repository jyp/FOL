module FOL.Solver where

-- import FOL.Connection
import FOL.Regularity
import FOL.FOL
import FOL.CNF

prepare :: Foldable t => t Value -> [Clause]
prepare  = toCNF . doQuote . foldr1 VAnd

-- solveCNF :: Int -> [Clause] -> Maybe Substitution
solveCNF maxSteps xs = refute maxSteps xs

-- solver :: Foldable t => Int -> t Value -> Maybe Substitution
solver maxSteps = refute maxSteps . prepare

-- contradicts :: Int -> [Value] -> Value -> Maybe Substitution
contradicts d gamma phi = solver d (phi:gamma)

-- entails :: Int -> [Value] -> Value -> Maybe Substitution
entails d gamma phi = contradicts d gamma (VNot phi)

data Status = Entailment | Contradiction | Neutral deriving (Show, Eq)

tryProve :: Int -> [Value] -> Value -> Status
tryProve d gamma phi = case entails d gamma phi of
  Nothing -> case contradicts d gamma phi of
    Nothing -> Neutral
    _ -> Contradiction
  _ -> Entailment
  
