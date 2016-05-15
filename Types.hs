{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}


module Types where

-- Type level Nats
data Nat = S Nat | Z

-- Value Nats
data SNat (a :: Nat) where
    SZ :: SNat Z
    SS :: SNat m -> SNat (S m)

-- Type level addition
type family Add (n :: Nat) (m :: Nat) :: Nat
type instance Add Z      m = m
type instance Add (S m)  n = S (Add m n)

-- Value level addition
add :: SNat m -> SNat n -> SNat (Add m n)
add SZ m     = m
add (SS n) m = SS (add n m)

-- Time Secure ints. We track how many operations it takes to do
-- something. Hence the type is dependent on the number of operations
-- to construct it
data SecInt (pc :: Nat) where
    SecLit  :: Int -> SecInt Z
    SecAdd  :: SecInt m -> SecInt n -> SecInt (S (Add m n))
    SecEq   :: SecInt m -> SecInt n -> SecBool (S (Add m n))

    -- Semantics of performing an operation m times and returning SecInt t
    SecSkip :: SecInt t -> SNat m -> SecInt (Add t m)
    -- Many more

data SecBool (pc :: Nat) where
    BoolLit :: Bool -> SecBool Z

    BoolAnd :: 
    ...

data SecList a where
    Cons :: a -> SecList a -> SecList a
    Nil  :: SecList a  

data SecControl where
    Cond :: ...
    Map  :: SecList a -> Func a b -> SecList b
    Fold :: SecList a -> b -> (b -> a -> b) -> b
    Zip  ::

-- Tests on conditionals

data Box = X (SecInt Z) | Y (SecInt (S Z))
data List a = Cons a (List a) | Nil

testFails :: Bool -> Box
testFails True  = X (SecLit 0)
testFails False = Y (SecAdd (SecLit 10) (SecLit 1000))

testSuccess ::  Bool -> SecInt (S Z)
testSuccess True  = (SecSkip (SecLit 0) (SS SZ))
testSuccess False = SecAdd (SecLit 10) (SecLit 1000)



-- How to circumvent:

data SomeThing = 
      A (SecInt (S Z))
    | B (SecInt (S (S Z)))
someFunc :: Bool -> SomeThing
someFunc True = A (SecAdd (SecLit 10) (SecLit 10))
someFunc False = B (SecAdd (SecAdd (SecLit 10) (SecLit 10)) (SecLit 10))

-- This works because we box the output


--instance Num (SecInt t) where
--    a + b = SecAdd a b
--    Pair (a,b) * Pair (c,d) = Pair (a*c,b*d)
--    Pair (a,b) - Pair (c,d) = Pair (a-c,b-d)
--    abs    (Pair (a,b)) = Pair (abs a,    abs b) 
--    signum (Pair (a,b)) = Pair (signum a, signum b) 
--    fromInteger i = Pair (fromInteger i, fromInteger i)

{-
-- Value level Nats
data SNat (a :: Nat) where
    SZ :: SNat Z
    SS :: SNat n -> SNat (S n)

data SecLang (time :: Nat) a where
    -- Literals
    LFunc :: Var (SecLang n) a -> SecLang (S n) a 
    LInt  :: Int -> SecLang Z Int
    -- Bool :: Bool -> SecLang Z Bool
    Cond :: SecLang t1 Bool -> SecLang t2 a -> SecLang t3 a -> SecLang (Add t1 (højeste t2, t3)) a

    -- Build-in Operations
    --App  :: SecLang t1 (b) ->  SecLang t2 b -> SecLang (Add t1 t2 ) b
    Add :: SecLang t1 Int -> SecLang t2 Int -> SecLang (Add t1 t2) Int
    -- Mult
    -- Sub

    Lt  :: SecLang t1 Int -> SecLang t2 Int -> SecLang (Add t1 t2) Bool
    Eq  ::

    And :: SecLang ..
    Or  ::
    


let test = App (Func ...) (LInt 4)

secureEvaluation :: SecLang n a -> ...
secureEvaluation Func var

-}