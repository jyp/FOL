module Exercise1 where

import FOL.Tableau
import FOL.CNF
-- import FOL.Unification
-- import FOL.Text.Groom
import FOL.FOL
import FOL.Regularity
import FOL.Connection
import FOL.Solver

(-->) :: Value -> Value -> Value
p --> q = VNot p ∨ q

julianEx :: [Clause]
julianEx = toCNF $ doQuote  $ foldr1 VAnd
           [VNot $ VAll $ \x -> gin x,
            VAll $ \x -> good x --> drink x ash,
            VExi $ \x -> gin (x) ∨ good x]
    where gin x = VApp "gin" [x]
          good x = VApp "good" [x]
          drink a b = VApp "drink" [a, b]
          ash =  VApp "ash" []

test = solver 10 $

         VNot (

       (VExi $ \x -> gin x ∧ drink x ash)
         ∧ 
        good matt
        ) : [ VExi $ \x -> gin x ∧ good x,
              VAll $ \x -> good x  --> (good x ∧ drink x ash) ]
       
    where gin x = VApp "gin" [x]
          good x = VApp "good" [x]
          drink a b = VApp "drink" [a, b]
          ash =  VApp "ash" []
          matt =  VApp "matt" []

-- >>> test
-- Just [fromList [(1,X)],fromList [(0,X)],fromList [(2,X)],fromList [(0,matt)],fromList [(3,X)]]
 

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
testSimple = print $ refuteSimple 9 exercise1 -- never finds a solution

testConn :: IO ()
testConn = putGroom $ FOL.Connection.refute 9 (exercise1 !! 0) exercise1

-- >>> testConn
-- [fromList [(1, a)], fromList [(1, f (α)), (2, α)],
--  fromList [(1, f (α)), (4, α)], fromList [(1, f (α)), (6, α)],
--  fromList [(0, f (β)), (8, β)], fromList [(1, a), (10, f (a))],
--  fromList [(0, f (f (a))), (1, f (a))],
--  fromList [(0, f (β)), (14, β)], fromList [(1, a), (16, f (a))]]

main = putGroom $ FOL.Regularity.refute 9 (exercise1 !! 0) exercise1

-- >>> main
-- <interactive>:69:2-5: error:
--     • Variable not in scope: main
--     • Perhaps you meant ‘min’ (imported from Prelude)
