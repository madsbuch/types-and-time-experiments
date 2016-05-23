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
    LList :: List a s -> CoreLang (List a s) Z

    -- Booleans
    And  :: CoreLang Bool m -> CoreLang Bool n -> CoreLang Bool (S (Add m n))
    Or   :: CoreLang Bool m -> CoreLang Bool n -> CoreLang Bool (S (Add m n))
    Not  :: CoreLang Bool m -> CoreLang Bool (S m)


    -- Integer
    Plus  :: CoreLang Int m -> CoreLang Int n -> CoreLang Int (S (Add m n))
    Minus :: CoreLang Int m -> CoreLang Int n -> CoreLang Int (S (Add m n))
    Time  :: CoreLang Int m -> CoreLang Int n -> CoreLang Int (S (Add m n))
    Div   :: CoreLang Int m -> CoreLang Int n -> CoreLang Int (S (Add m n))
    IEq   :: CoreLang Int m -> CoreLang Int n -> CoreLang Bool (S (Add m1 m2))

    -- List operations
    Map  :: CoreLang (List (CoreLang a m) s) n 
        -> (CoreLang a m -> CoreLang b n) 
        -> CoreLang (List (CoreLang b n) s) (Mult n s)
    Fold :: (CoreLang a m1 -> CoreLang a m2 -> CoreLang a m3) -- function
        -> CoreLang a n0 -- Neutral element
        -> CoreLang (List (CoreLang a n1) s) n2
        -> CoreLang a (Add (Mult s m3) n0)

    -- Misc
    If   :: CoreLang Bool m1 -> CoreLang a m2 -> CoreLang a m2 -> CoreLang a (S (Add m1 m2))


instance Show a => Show (List a s) where
    show (x ::: xs) = (show x) ++ " ::: " ++ (show xs)
    show (Nill)     = "Nill" 

instance Show t => Show (CoreLang t s) where
    show (LBool b) = show b
    show (LInt i)  = show i
    show (LList l) = show l

--An interpreter
interpret :: CoreLang t m -> t
interpret (LBool a) = a
interpret (LInt i)  = i
interpret (LList l) = l


{- Some Applications -}

-- Secure login, User
userList = LList (LInt 133 ::: LInt 3434 ::: Nill)

{-
This first example generates a program which can check if a user exists in a list
-}
-- Note that we can force literals in the type
checkUser :: CoreLang Int Z -> CoreLang (List (CoreLang Int m2) s) m3 -> CoreLang Bool a --(Add (Mult s (S (Add ))) n0)
checkUser user uList         = (Fold 
                                (\(a) (b) -> (Or a b))
                                (LBool False)
                                (Map uList (\u -> (IEq u user)) ))

-- Generate expression for execution
--cuExp = checkUser (LInt 133) userList


-- Safe multi threading (relate to the presented paper)
