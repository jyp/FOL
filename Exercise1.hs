module FOL.Exercise1 where

import Data.Maybe
import FOL.Tableau
import FOL.CNF
import Text.Groom
import FOL.FOL
import FOL.Regularity
import FOL.Connection
import FOL.Solver

(-->) :: Value -> Value -> Value
p --> q = VNot p ∨ q

test = 
         VNot (
        good matt
        ) : [ VExi $ \x -> good x,
              VAll $ \x -> good x  --> good x ]
       
    where good x = VApp "good" [x]
          matt =  VApp "matt" []


-- >>> solver 10 test
-- Nothing


cls = prepare test

-- >>> putGroom (rotate cls)
-- [(0, [(True, good (X))]),
--  (1, [(False, good (α)), (True, good (α))]),
--  (0, [(False, good (matt))])]

t0 = extendUsingClause (head cls) (10,[[]])

-- >>> t0
-- (10,[[(False,good(matt))]])

t1 :: [Tableau]
t1 = map snd $ connection ((cls)) t0

-- >>> t1
-- [(11,[[(False,good(matt)),(False,good(matt))]])]


t2 :: [Tableau]
t2 = map snd $ connection (cls) (head t1)

-- >>> putGroom t2
-- [(12,
--   [[(False, good (matt)), (False, good (matt)),
--     (False, good (matt))]])]

t3 :: [Tableau]
t3 = map snd $ connection (cls) (head t2)

-- >>> putGroom t3
-- [(13,
--   [[(False, good (matt)), (False, good (matt)), (False, good (matt)),
--     (False, good (matt))]])]


test' :: [Clause]
test' = prepare $

         VNot ((VExi $ \x -> gin x ∧ drink x ash)
         ∧ 
        (VExi julian)
        -- ∧ (good matt)
        ) : [ VExi $ \x -> gin x ∧ good x,
              (VExi julian),
              VAll $ \x -> good x  --> (good x ∧ drink x ash) ]
       
    where gin x = VApp "gin" [x]
          good x = VApp "good" [x]
          julian x = VApp "julian" [x]
          drink a b = VApp "drink" [a,b]
          ash =  VApp "ash" []
          matt =  VApp "matt" []

-- >>> print $ prettyClauses test'
-- ¬gin(γ) ∨ ¬drink(γ,ash) ∨ ¬julian(β)
-- gin(X)
-- good(X)
-- julian(Y)
-- ¬good(α) ∨ good(α)
-- ¬good(α) ∨ drink(α,ash)

-- >>> print $ prettyTrace $ fromJust $ solveCNF 10 test'
-- Tableau
--   branch ¬gin(γ)
--   branch ¬drink(γ,ash)
--   branch ¬julian(β)
-- Constraints
-- Connect gin(X) and ¬gin(γ) with {γ ↦ X,} yielding ⊥
-- Tableau
--   branch ¬drink(X,ash)
--   branch ¬julian(β)
-- Constraints
-- Close
-- Tableau
--   branch ¬drink(X,ash)
--   branch ¬julian(β)
-- Constraints
-- Connect
--   ¬good(α) ∨ drink(α,ash) and 
--   ¬drink(X,ash) with 
--   {α ↦ X,} yielding 
--   ¬good(X)
-- Tableau
--   branch ¬good(X) ∨ ¬drink(X,ash)
--   branch ¬julian(β)
-- Constraints Unsat
-- Close
-- Tableau
--   branch ¬good(X) ∨ ¬drink(X,ash)
--   branch ¬julian(β)
-- Constraints Unsat
-- Connect good(X) and ¬good(X) with {} yielding ⊥
-- Tableau branch ¬julian(β)
-- Constraints
-- Close
-- Tableau branch ¬julian(β)
-- Constraints
-- Connect julian(Y) and ¬julian(β) with {β ↦ Y,} yielding ⊥
-- Tableau
-- Constraints
-- Close

exx = VNot ((VExi $ \x -> gin (x) ∨ good x) `VAnd`
        (VExi julian)) : [ VNot $ VAll $ \x -> gin x,
                           VAll $ \x -> good x  --> drink x ash ]
    where gin x = VApp "gin" [x]
          good x = VApp "good" [x]
          julian x = VApp "julian" [x]
          drink a b = VApp "drink" [a,b]
          ash =  VApp "ash" []
       
-- >>> pullQuantifiers $ skolemize $ toNNF $ doQuote (foldr1 VAnd exx)
-- ∀x. ∀y. ∀z. (¬gin(x) ∧ ¬good(x) ∨ ¬julian(y)) ∧ ¬gin(X) ∧ (¬good(z) ∨ drink(z,
--                                                                             ash))

-- ex3 = [VAll $ \x -> drink x ash ∧ gin x, ,
--        VExi $ \x -> gin (x) ∨ good x
--       ]
--     where gin x = VApp "gin" [x]
--           julian x = VApp "julian" [x]
--           good x = VApp "good" [x]
--           drink a b = VApp "drink" [a,b]
--           ash =  VApp "ash" []


-- >>> putGroom julianEx
-- [(0, [(False, gin (X))]),
--  (1, [(False, good (α)), (True, drink (α, ash))]),
--  (0, [(True, gin (Y)), (True, good (Y))])]


exercise1' = toCNF $ doQuote $ foldr1 VAnd 
               [ VAll $ \x -> g (x,a) ∨ g (f x, x),
                 VAll $ \x -> g (x,a) ∨ g (x, f x),
                 VAll $ \x -> VAll $ \y -> g (x,y) ⟶ g (y, f y),
                 VAll $ \x -> VAll $ \y -> g (x,y) ⟶ g (f y, y),
                 VAll $ \x -> VAll $ \y -> VNot (g (x,y) ∧ g (y, a))]
    where a = VApp "a" []
          g (t,u) = VApp "g" [t,u]
          f t = VApp "f" [t]
          

-- >>> prettyClauses exercise1'
-- g(κ,a) ∨ g(f(κ),κ)
-- g(ι,a) ∨ g(ι,f(ι))
-- ¬g(ε,η) ∨ g(η,f(η))
-- ¬g(δ,γ) ∨ g(f(γ),γ)
-- ¬g(β,α) ∨ ¬g(α,a)


exercise1 :: [Clause]
exercise1 = [ (1,[ ok (g (x,a)) ,ok (g (f x, x))]),
              (1,[ ok (g (x,a)) ,ok (g (x, f x))]),
              (2,[ nk (g (x,y)) ,ok (g (y, f y))]),
              (2,[ nk (g (x,y)) ,ok (g (f y, y))]),
              (2,[ nk (g (x,y)) ,nk (g (y,   a))])
            ]
    where x = SVar 0
          y = SVar 1
          a = SApp "a" []
          g (t,u) = SApp "g" [t,u]
          f t = SApp "f" [t]
          ok x = (True, x)
          nk x = (False, x)

-- >>> prettyClauses exercise1'
-- g(κ,a) ∨ g(f(κ),κ)
-- g(ι,a) ∨ g(ι,f(ι))
-- ¬g(ε,η) ∨ g(η,f(η))
-- ¬g(δ,γ) ∨ g(f(γ),γ)
-- ¬g(β,α) ∨ ¬g(α,a)

solution1 :: Tableau
solution1 =
    close1 $
    close1 $
    rotateBranches $
    extendUsingClause (c 4) $
    close1 $
    close1 $
    extendUsingClause (c 4) $
    extendUsingClause (c 1) $
    close1 $
    close1 $
    extendUsingClause (c 4) $
    close1 $
    extendUsingClause (c 3) $
    extendUsingClause (c 0) $
    initialTableau
    where c i = exercise1 !! i

-- >>> solution1
-- (10,[])

putGroom :: Show a => a -> IO ()
putGroom a = putStrLn $ groom a

testSimple :: IO ()
testSimple = print $ FOL.Tableau.refute 9 exercise1 -- never finds a solution

testConn :: IO ()
testConn = putGroom $ FOL.Connection.refute 9 (exercise1 !! 0) exercise1

-- >>> testConn
-- Just
--   [fromList [(1, a)], fromList [(0, a), (1, f (a))],
--    fromList [(0, f (f (a))), (1, f (a))],
--    fromList [(0, f (f (a))), (1, f (a))],
--    fromList [(0, f (f (a))), (1, f (a))], fromList [(0, a)],
--    fromList [(0, a), (1, a)], fromList [(0, f (a)), (1, a)],
--    fromList [(0, a), (1, f (a))]]

main =  print $ prettyTrace $ fromJust $ FOL.Regularity.refute 9 (exercise1 !! 0) exercise1

-- >>> main
-- Goals
--   > g(α,a)
--   > g(f(α),α)
-- Constraints
-- Connect
--   ¬g(α,β) ∨ g(β,f(β)) and g(α,a) with {β ↦ a,} yielding g(a,f(a))
-- Goals
--   > g(a,f(a)) ∨ g(α,a)
--   > g(f(α),α)
-- Constraints Unsat
-- Close
-- Goals
--   > g(a,f(a)) ∨ g(α,a)
--   > g(f(α),α)
-- Constraints Unsat
-- Connect
--   ¬g(α,β) ∨ g(f(β),β) and 
--   g(a,f(a)) with 
--   {α ↦ a,β ↦ f(a),} yielding 
--   g(f(f(a)),f(a))
-- Goals
--   > g(f(f(a)),f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Constraints
--   Unsat
--   Unsat
-- Close
-- Goals
--   > g(f(f(a)),f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Constraints
--   Unsat
--   Unsat
-- Connect
--   ¬g(α,β) ∨ ¬g(β,a) and 
--   g(f(f(a)),f(a)) with 
--   {α ↦ f(f(a)),β ↦ f(a),} yielding 
--   ¬g(f(a),a)
-- Goals
--   > ¬g(f(a),a) ∨ g(f(f(a)),f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Constraints
--   Unsat
--   Unsat
--   Unsat
-- Close
-- Goals
--   > ¬g(f(a),a) ∨ g(f(f(a)),f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Constraints
--   Unsat
--   Unsat
--   Unsat
-- Connect
--   ¬g(α,β) ∨ g(f(β),β) and ¬g(f(a),a) with {β ↦ a,} yielding ¬g(α,a)
-- Goals
--   > ¬g(κ,a) ∨ ¬g(f(a),a) ∨ g(f(f(a)),f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Constraints
--   {κ ↦ f(a),}
--   Unsat
--   Unsat
--   Unsat
-- Close
-- Goals
--   > ¬g(κ,a) ∨ ¬g(f(a),a) ∨ g(f(f(a)),f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Constraints
--   {κ ↦ f(a),}
--   Unsat
--   Unsat
--   Unsat
-- Connect
--   g(α,a) ∨ g(f(α),α) and ¬g(κ,a) with {κ ↦ α,} yielding g(f(α),α)
-- Goals
--   > g(f(μ),μ) ∨ ¬g(α,a) ∨ ¬g(f(a),a) ∨ g(f(f(a)),f(a)) ∨ g(a,
--                                                            f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Constraints
--   Unsat
--   Unsat
--   {μ ↦ f(a),}
--   Unsat
--   Unsat
--   {α ↦ f(a),}
-- Close
-- Goals
--   > g(f(μ),μ) ∨ ¬g(α,a) ∨ ¬g(f(a),a) ∨ g(f(f(a)),f(a)) ∨ g(a,
--                                                            f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Constraints
--   Unsat
--   Unsat
--   {μ ↦ f(a),}
--   Unsat
--   Unsat
--   {α ↦ f(a),}
-- Connect
--   ¬g(α,β) ∨ ¬g(β,a) and 
--   g(f(μ),μ) with 
--   {β ↦ f(a),μ ↦ a,} yielding 
--   ¬g(α,f(a))
-- Goals
--   > ¬g(ν,f(a)) ∨ g(f(a),a) ∨ ¬g(α,a) ∨ ¬g(f(a),a) ∨ g(f(f(a)),
--                                                       f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Constraints
--   Unsat
--   Unsat
--   Unsat
--   Unsat
--   Unsat
--   Unsat
--   {α ↦ f(a),}
-- Close
-- Goals > g(f(a),a)
-- Constraints
--   Unsat
--   Unsat
--   Unsat
--   Unsat
--   Unsat
--   Unsat
--   {α ↦ f(a),}
-- Connect
--   ¬g(α,β) ∨ ¬g(β,a) and 
--   g(f(a),a) with 
--   {β ↦ f(a),} yielding 
--   ¬g(α,f(a))
-- Goals > ¬g(ρ,f(a)) ∨ g(f(a),a)
-- Constraints
--   Unsat
--   {α ↦ f(a),}
-- Close
-- Goals > ¬g(ρ,f(a)) ∨ g(f(a),a)
-- Constraints
--   Unsat
--   {α ↦ f(a),}
-- Connect
--   ¬g(α,β) ∨ g(β,f(β)) and 
--   ¬g(ρ,f(a)) with 
--   {β ↦ a,ρ ↦ a,} yielding 
--   ¬g(α,a)
-- Goals > ¬g(φ,a) ∨ ¬g(a,f(a)) ∨ g(f(a),a)
-- Constraints
--   Unsat
--   Unsat
--   {α ↦ f(a),}
-- Close
-- Goals > ¬g(φ,a) ∨ ¬g(a,f(a)) ∨ g(f(a),a)
-- Constraints
--   Unsat
--   Unsat
--   {α ↦ f(a),}
-- Connect
--   ¬g(α,β) ∨ g(f(β),β) and 
--   ¬g(φ,a) with 
--   {β ↦ a,φ ↦ f(a),} yielding 
--   ¬g(α,a)
-- Goals > ¬g(ξ,a) ∨ ¬g(f(a),a) ∨ ¬g(a,f(a)) ∨ g(f(a),a)
-- Constraints
--   {ξ ↦ f(a),}
--   Unsat
--   Unsat
--   {α ↦ f(a),}
-- Close


