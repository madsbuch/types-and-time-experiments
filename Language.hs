{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}


module Language where

-- Type level natural
data Nat = Z | S Nat

-- Type level addition
type family Add (n :: Nat) (m :: Nat) :: Nat
type instance Add Z      m = m
type instance Add (S m)  n = S (Add m n)

-- Type level Multiplication
type family Mult (n :: Nat) (m :: Nat) :: Nat
type instance Mult Z     m = Z
type instance Mult (S m) n = (Add n (Mult m n))

-- List type, Size is the only thing we leak
infixr 4 :::
data List a (size :: Nat) where
    Nill :: List a Z
    (:::) :: a -> List a m -> List a (S m)

-- Define the lagnuage
data CoreLang t (s :: Nat) where
    -- Literals
    LBool :: Bool -> CoreLang Bool Z
    LInt  :: Int  -> CoreLang Int Z 
    LList :: List a s -> CoreLang (List a s) s

    -- Booleans
    And  :: CoreLang Bool m -> CoreLang Bool n -> CoreLang Bool (S (Add m n))
    Or   :: CoreLang Bool m -> CoreLang Bool n -> CoreLang Bool (S (Add m n))
    Not  :: CoreLang Bool m -> CoreLang Bool (S m)

    -- Integer
    Plus  :: CoreLang Int m -> CoreLang Int n -> CoreLang Int (S (Add m n))
    Minus :: CoreLang Int m -> CoreLang Int n -> CoreLang Int (S (Add m n))
    Time  :: CoreLang Int m -> CoreLang Int n -> CoreLang Int (S (Add m n))
    Div   :: CoreLang Int m -> CoreLang Int n -> CoreLang Int (S (Add m n))
    IEq   :: CoreLang Int m -> CoreLang Int n -> CoreLang Bool (S (Add m n))

    -- List operations
    Map  :: CoreLang (List (CoreLang a m) s) n 
        -> (CoreLang a m -> CoreLang b n) 
        -> CoreLang (List (CoreLang b n) s) (Mult n s)
    Fold :: (CoreLang a Z -> CoreLang a Z -> CoreLang a (S Z)) -- function, only constant operations time on literals
        -> CoreLang a Z -- Neutral element, only constants
        -> CoreLang (List (CoreLang a Z) s) s --list to fold over, s-sized list of constant values
        -> CoreLang a s

    -- Misc - actually, the relevant stuff
    -- Conditional
    If   :: CoreLang Bool m1 -> CoreLang a m2 -> CoreLang a m2 -> CoreLang a (S (Add m1 m2))
    -- parallell computations
    -- Par ...

instance Show a => Show (List a s) where
    show (x ::: xs) = (show x) ++ " ::: " ++ (show xs)
    show (Nill)     = "Nill" 

instance Show t => Show (CoreLang t s) where
    show (LBool b) = show b
    show (LInt i)  = show i
    show (LList l) = show l
    show (Fold f i l) = "(Fold f " ++ show i ++ " " ++ show l ++ ")"

--An interpreter
interpret :: CoreLang t m -> t
interpret (LBool a)    = a
interpret (LInt i)     = i
interpret (LList l)    = l
interpret (Fold f z (LList l)) = interpret $ unfold f z l
  where
    unfold f z Nill         = z
    unfold f z (x ::: xs)   = f x (unfold f z xs)

{- Some Applications -}

-- Secure login, User
userList = LList (LInt 133 ::: LInt 3434 ::: LInt 23234 ::: LInt 3434 ::: Nill)
userCheckTrue  = (LInt 133)
userCheckFalse = (LInt 323)


{-
This first example generates a program which can check if a user exists in a list
-}
-- Note that we can force literals in the type
--checkUser :: CoreLang Int Z 
--    -> CoreLang (List (CoreLang Int Z) s) (S (Add Z Z)) 
--    -> CoreLang Bool (Add (Mult s (S Z)) Z)

elementEquals x xs = (Map xs (\y -> (IEq y x)))

doOr :: CoreLang Bool m -> CoreLang Bool n -> CoreLang Bool (S (Add m n))
doOr a b = (Or a b)

false :: CoreLang Bool Z
false = (LBool False)


listBools = LList (LBool False ::: LBool False ::: LBool True ::: LBool False ::: Nill)

foldOr :: CoreLang (List (CoreLang Bool Z) s) s -> CoreLang Bool s
foldOr xs = (Fold doOr false xs)

--    Fold :: (CoreLang a m1 -> CoreLang a m2 -> CoreLang a (S (Add m1 m2))) -- function, only constant operations time
--        -> CoreLang a n0 -- Neutral element
--        -> CoreLang (List (CoreLang a n1) s) n2 --list to fold over
--        -> CoreLang a (Add (Mult s (S (Add m1 m2))) n0)

-- checkUser user uList         = 

-- Generate expression for execution
--cuExp = checkUser (LInt 133) userList


-- Safe multi threading (relate to the presented paper)

{-

# Problems doing this:

## Fold

* Functions used to fold has to be dependent, so we can statically infer running time

-}