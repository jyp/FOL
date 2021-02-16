module FOL.Exercise1 where

import Data.Maybe
import FOL.Tableau
import FOL.CNF
import Text.Groom
import FOL.FOL
import FOL.Regularity
import qualified FOL.Connection
import FOL.Connection (connection)
import FOL.Solver

(-->) :: Value -> Value -> Value
p --> q = VNot p ∨ q

emacsEx :: [Clause]
emacsEx = prepare  [p1,p2, VNot  (p1 --> p2)]
    where command x = VApp "command" [x]
          prepared x = VApp "prepared" [x]
          wait(x,y) =  VApp "wait" [x,y]
          emacs = VApp "emacs" []
          p1 = (VAll $ \x -> VNot (VExi $ \y -> wait(y,x)) ∨ (VExi $ \y -> wait(y, x) ∧ prepared(x)))
          p2 = (VExi $ \x -> command (x) ∧ wait (x,emacs))


-- >>> prettyClauses emacsEx
-- ¬wait(δ,η) ∨ wait(X(η),η)
-- ¬wait(δ,η) ∨ prepared(η)
-- command(Y)
-- wait(Y,emacs)
-- ¬wait(β,γ) ∨ wait(Z(γ),γ)
-- ¬wait(β,γ) ∨ prepared(γ)
-- ¬command(α) ∨ ¬wait(α,emacs)


test :: [Clause]
test = prepare $ 
         VNot (
        good matt
        ) : [ VExi $ \x -> good x,
              VAll $ \x -> good x  --> good x ]
       
    where good x = VApp "good" [x]
          matt =  VApp "matt" []

-- >>> prettyClauses test
-- ¬good(matt)
-- good(X)
-- ¬good(α) ∨ good(α)

-- >>> isJust $ solveCNF 10 test
-- False

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

-- >>> prettyClauses test'
-- ¬gin(γ) ∨ ¬drink(γ,ash) ∨ ¬julian(β)
-- gin(X)
-- good(X)
-- julian(Y)
-- ¬good(α) ∨ good(α)
-- ¬good(α) ∨ drink(α,ash)

-- >>> print $ prettyTrace $ fromJust $ solveCNF 10 $ test'
-- Goals
--   > ¬gin(γ)
--   > ¬drink(γ,ash)
--   > ¬julian(β)
-- Constraints
-- Connect gin(X) and ¬gin(γ) with {γ ↦ X,} yielding ⊥
-- Goals
--   > ¬drink(X,ash)
--   > ¬julian(β)
-- Constraints
-- Close
-- Goals
--   > ¬drink(X,ash)
--   > ¬julian(β)
-- Constraints
-- Connect
--   ¬good(δ) ∨ drink(δ,ash) and 
--   ¬drink(X,ash) with 
--   {δ ↦ X,} yielding 
--   ¬good(X)
-- Goals
--   > ¬good(X) ∨ ¬drink(X,ash)
--   > ¬julian(β)
-- Constraints
-- Close
-- Goals
--   > ¬good(X) ∨ ¬drink(X,ash)
--   > ¬julian(β)
-- Constraints
-- Connect good(X) and ¬good(X) with {} yielding ⊥
-- Goals > ¬julian(β)
-- Constraints
-- Close
-- Goals > ¬julian(β)
-- Constraints
-- Connect julian(Y) and ¬julian(β) with {β ↦ Y,} yielding ⊥
-- Goals
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

-- solution1 :: Tableau
-- solution1 =
--     close1 $
--     close1 $
--     rotateBranches $
--     extendUsingClause (c 4) $
--     close1 $
--     close1 $
--     extendUsingClause (c 4) $
--     extendUsingClause (c 1) $
--     close1 $
--     close1 $
--     extendUsingClause (c 4) $
--     close1 $
--     extendUsingClause (c 3) $
--     extendUsingClause (c 0) $
--     initialTableau
--     where c i = exercise1 !! i

-- >>> solution1
-- (10,[])

putGroom :: Show a => a -> IO ()
putGroom a = putStrLn $ groom a

testSimple :: IO ()
testSimple = print $ FOL.Tableau.refute 9 exercise1 -- never finds a solution

testConn :: IO ()
testConn = print $ FOL.Connection.prettyTrace $ fromJust $ FOL.Connection.refute 9  exercise1

-- >>> testConn
-- Goals
--   > g(α,a)
--   > g(f(α),α)
-- Connect
--   ¬g(α,β) ∨ g(β,f(β)) and g(α,a) with {β ↦ a,} yielding g(a,f(a))
-- Goals
--   > g(a,f(a)) ∨ g(α,a)
--   > g(f(α),α)
-- Close
-- Goals
--   > g(a,f(a)) ∨ g(α,a)
--   > g(f(α),α)
-- Connect
--   ¬g(α,β) ∨ g(f(β),β) and 
--   g(a,f(a)) with 
--   {α ↦ a,β ↦ f(a),} yielding 
--   g(f(f(a)),f(a))
-- Goals
--   > g(f(f(a)),f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Close
-- Goals
--   > g(f(f(a)),f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Connect
--   ¬g(α,β) ∨ g(f(β),β) and 
--   g(f(f(a)),f(a)) with 
--   {α ↦ f(f(a)),β ↦ f(a),} yielding 
--   g(f(f(a)),f(a))
-- Goals
--   > g(f(f(a)),f(a)) ∨ g(f(f(a)),f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Close
-- Goals
--   > g(f(f(a)),f(a)) ∨ g(f(f(a)),f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Connect
--   ¬g(α,β) ∨ g(f(β),β) and 
--   g(f(f(a)),f(a)) with 
--   {α ↦ f(f(a)),β ↦ f(a),} yielding 
--   g(f(f(a)),f(a))
-- Goals
--   > g(f(f(a)),f(a)) ∨ g(f(f(a)),f(a)) ∨ g(f(f(a)),f(a)) ∨ g(a,
--                                                             f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Close
-- Goals
--   > g(f(f(a)),f(a)) ∨ g(f(f(a)),f(a)) ∨ g(f(f(a)),f(a)) ∨ g(a,
--                                                             f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Connect
--   ¬g(α,β) ∨ ¬g(β,a) and 
--   g(f(f(a)),f(a)) with 
--   {α ↦ f(f(a)),β ↦ f(a),} yielding 
--   ¬g(f(a),a)
-- Goals
--   > ¬g(f(a),a) ∨ g(f(f(a)),f(a)) ∨ g(f(f(a)),f(a)) ∨ g(f(f(a)),
--                                                        f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Close
-- Goals
--   > ¬g(f(a),a) ∨ g(f(f(a)),f(a)) ∨ g(f(f(a)),f(a)) ∨ g(f(f(a)),
--                                                        f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Connect
--   g(α,a) ∨ g(f(α),α) and ¬g(f(a),a) with {α ↦ a,} yielding g(a,a)
-- Goals
--   > g(a,a) ∨ ¬g(f(a),a) ∨ g(f(f(a)),f(a)) ∨ g(f(f(a)),
--                                               f(a)) ∨ g(f(f(a)),f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Close
-- Goals
--   > g(a,a) ∨ ¬g(f(a),a) ∨ g(f(f(a)),f(a)) ∨ g(f(f(a)),
--                                               f(a)) ∨ g(f(f(a)),f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Connect
--   ¬g(α,β) ∨ g(f(β),β) and 
--   g(a,a) with 
--   {α ↦ a,β ↦ a,} yielding 
--   g(f(a),a)
-- Goals
--   > g(f(a),a) ∨ g(a,a) ∨ ¬g(f(a),a) ∨ g(f(f(a)),f(a)) ∨ g(f(f(a)),
--                                                           f(a)) ∨ g(f(f(a)),f(a)) ∨ g(a,f(a)) ∨ g(a,
--                                                                                                   a)
--   > g(f(a),a)
-- Close
-- Goals > g(f(a),a)
-- Connect
--   ¬g(α,β) ∨ g(β,f(β)) and 
--   g(f(a),a) with 
--   {α ↦ f(a),β ↦ a,} yielding 
--   g(a,f(a))
-- Goals > g(a,f(a)) ∨ g(f(a),a)
-- Close
-- Goals > g(a,f(a)) ∨ g(f(a),a)
-- Connect
--   ¬g(α,β) ∨ ¬g(β,a) and 
--   g(a,f(a)) with 
--   {α ↦ a,β ↦ f(a),} yielding 
--   ¬g(f(a),a)
-- Goals > ¬g(f(a),a) ∨ g(a,f(a)) ∨ g(f(a),a)
-- Close

-- main =  print $ prettyTrace $ fromJust $ FOL.Regularity.refute 9 (exercise1 !! 0) exercise1

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
-- Constraints
-- Close
-- Goals
--   > g(a,f(a)) ∨ g(α,a)
--   > g(f(α),α)
-- Constraints
-- Connect
--   ¬g(α,β) ∨ g(f(β),β) and 
--   g(a,f(a)) with 
--   {α ↦ a,β ↦ f(a),} yielding 
--   g(f(f(a)),f(a))
-- Goals
--   > g(f(f(a)),f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Constraints
-- Close
-- Goals
--   > g(f(f(a)),f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Constraints
-- Connect
--   ¬g(α,β) ∨ ¬g(β,a) and 
--   g(f(f(a)),f(a)) with 
--   {α ↦ f(f(a)),β ↦ f(a),} yielding 
--   ¬g(f(a),a)
-- Goals
--   > ¬g(f(a),a) ∨ g(f(f(a)),f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Constraints
-- Close
-- Goals
--   > ¬g(f(a),a) ∨ g(f(f(a)),f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Constraints
-- Connect
--   ¬g(α,β) ∨ g(f(β),β) and ¬g(f(a),a) with {β ↦ a,} yielding ¬g(α,a)
-- Goals
--   > ¬g(κ,a) ∨ ¬g(f(a),a) ∨ g(f(f(a)),f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Constraints {κ ↦ f(a),}
-- Close
-- Goals
--   > ¬g(κ,a) ∨ ¬g(f(a),a) ∨ g(f(f(a)),f(a)) ∨ g(a,f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Constraints {κ ↦ f(a),}
-- Connect
--   g(α,a) ∨ g(f(α),α) and ¬g(κ,a) with {κ ↦ α,} yielding g(f(α),α)
-- Goals
--   > g(f(μ),μ) ∨ ¬g(α,a) ∨ ¬g(f(a),a) ∨ g(f(f(a)),f(a)) ∨ g(a,
--                                                            f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Constraints
--   {μ ↦ f(a),}
--   {α ↦ f(a),}
-- Close
-- Goals
--   > g(f(μ),μ) ∨ ¬g(α,a) ∨ ¬g(f(a),a) ∨ g(f(f(a)),f(a)) ∨ g(a,
--                                                            f(a)) ∨ g(a,a)
--   > g(f(a),a)
-- Constraints
--   {μ ↦ f(a),}
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
-- Constraints {α ↦ f(a),}
-- Close
-- Goals > g(f(a),a)
-- Constraints {α ↦ f(a),}
-- Connect
--   ¬g(α,β) ∨ ¬g(β,a) and 
--   g(f(a),a) with 
--   {β ↦ f(a),} yielding 
--   ¬g(α,f(a))
-- Goals > ¬g(ρ,f(a)) ∨ g(f(a),a)
-- Constraints {α ↦ f(a),}
-- Close
-- Goals > ¬g(ρ,f(a)) ∨ g(f(a),a)
-- Constraints {α ↦ f(a),}
-- Connect
--   ¬g(α,β) ∨ g(β,f(β)) and 
--   ¬g(ρ,f(a)) with 
--   {β ↦ a,ρ ↦ a,} yielding 
--   ¬g(α,a)
-- Goals > ¬g(φ,a) ∨ ¬g(a,f(a)) ∨ g(f(a),a)
-- Constraints {α ↦ f(a),}
-- Close
-- Goals > ¬g(φ,a) ∨ ¬g(a,f(a)) ∨ g(f(a),a)
-- Constraints {α ↦ f(a),}
-- Connect
--   ¬g(α,β) ∨ g(f(β),β) and 
--   ¬g(φ,a) with 
--   {β ↦ a,φ ↦ f(a),} yielding 
--   ¬g(α,a)
-- Goals > ¬g(ξ,a) ∨ ¬g(f(a),a) ∨ ¬g(a,f(a)) ∨ g(f(a),a)
-- Constraints
--   {ξ ↦ f(a),}
--   {α ↦ f(a),}
-- Close


