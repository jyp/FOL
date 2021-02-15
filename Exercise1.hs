module FOL.Exercise1 where

import FOL.Tableau
import FOL.CNF
import FOL.Unification
import FOL.Text.Groom
import FOL.FOL
import FOL.Regularity
import FOL.Connection
import FOL.Solver

(-->) :: Value -> Value -> Value
p --> q = VNot p ∨ q

julianEx = toCNF $ doQuote  $ foldr1 VAnd
           [ VNot $ VAll $ \x -> gin x,
             VAll $ \x -> good x --> drink x ash,
             VExi $ \x -> gin (x) ∨ good x]
    where gin x = VApp "gin" [x]
          good x = VApp "good" [x]
          drink a b = VApp "drink" [a,b]
          ash =  VApp "ash" []

testX = solver 10 $

         VNot (

       (VExi $ \x -> gin x ∧ drink x ash)
         ∧ 
        good matt
        ) : [ VExi $ \x -> gin x ∧ good x,
              VAll $ \x -> good x  --> (good x ∧ drink x ash) ]
       
    where gin x = VApp "gin" [x]
          good x = VApp "good" [x]
          drink a b = VApp "drink" [a,b]
          ash =  VApp "ash" []
          matt =  VApp "matt" []

-- >>> testX
-- Nothing

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

-- >>> t2
-- [(12,[[(False,good(matt)),(False,good(matt)),(False,good(matt))]])]

t3 :: [Tableau]
t3 = map snd $ connection (cls) (head t2)

-- >>> t3
-- [(13,[[(False,good(matt)),(False,good(matt)),(False,good(matt)),(False,good(matt))]])]


test' = putGroom $ toCNF $ doQuote $ foldr1 VAnd $

         VNot ((VExi $ \x -> gin x ∧ drink x ash)
        --  ∧ 
        -- (VExi julian)
        ∧
        (good matt)
        ) : [ VExi $ \x -> gin x ∧ good x,
                     VAll $ \x -> good x  --> (good x ∧ drink x ash) ]
       
    where gin x = VApp "gin" [x]
          good x = VApp "good" [x]
          julian x = VApp "julian" [x]
          drink a b = VApp "drink" [a,b]
          ash =  VApp "ash" []
          matt =  VApp "matt" []


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
          



-- >>> putGroom exercise1'
-- [(1, [(True, g (α, a)), (True, g (f (α), α))]),
--  (1, [(True, g (α, a)), (True, g (α, f (α)))]),
--  (2, [(False, g (β, α)), (True, g (α, f (α)))]),
--  (2, [(False, g (β, α)), (True, g (f (α), α))]),
--  (2, [(False, g (β, α)), (False, g (α, a))])]

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
testSimple = print $ Tableau.refute 9 exercise1 -- never finds a solution

testConn :: IO ()
testConn = putGroom $ Connection.refute 9 (exercise1 !! 0) exercise1

-- >>> testConn
-- [fromList [(1, a)], fromList [(1, f (α)), (2, α)],
--  fromList [(1, f (α)), (4, α)], fromList [(1, f (α)), (6, α)],
--  fromList [(0, f (β)), (8, β)], fromList [(1, a), (10, f (a))],
--  fromList [(0, f (f (a))), (1, f (a))],
--  fromList [(0, f (β)), (14, β)], fromList [(1, a), (16, f (a))]]

main = putGroom $ Regularity.refute 9 (exercise1 !! 0) exercise1

-- >>> main
-- [fromList [(1, a)], fromList [(1, f (α)), (2, α)],
--  fromList [(0, f (β)), (4, β)], fromList [(1, f (α)), (6, α)],
--  fromList [(0, f (β)), (8, β)], fromList [(1, a), (10, f (a))],
--  fromList [(0, f (f (f (f (a))))), (1, f (f (f (a))))],
--  fromList [(0, f (β)), (14, β)], fromList [(1, a), (16, f (a))]]


main' = putGroom $ Regularity.refute 9 (julianEx !! 0) julianEx


-- >>> main'
-- *** Exception: no solution found
-- CallStack (from HasCallStack):
--   error, called at ./Regularity.hs:93:25 in main:Regularity
