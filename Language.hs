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
data List a (size :: Nat) where
    Nill :: List a Z
    Cons :: a -> List a m -> List a (S m)

-- Define the lagnuage
data CoreLang t (s :: Nat) where
    -- Literals
    LBool :: Bool -> CoreLang Bool Z
    Lint  :: Int  -> CoreLang Int Z 
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

    -- List operations
    Map  :: CoreLang (List (CoreLang a m) s) n -> (CoreLang a m -> CoreLang b n) -> CoreLang (List (CoreLang b n) s) (Add n s)
    Fold :: (CoreLang a m1 -> CoreLang a m2 -> CoreLang a m3) -- function
        -> CoreLang a n0 -- Neutral element
        -> List (CoreLang a n1) s
        -> CoreLang a (Add (Mult s m3) n0)

    -- Misc
    If   :: CoreLang Bool m1 -> CoreLang a m2 -> CoreLang a m2 -> CoreLang a (S (Add m1 m2))

--An interpreter
interpret :: CoreLang t m -> t
interpret = error "implement"