{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}


module Language where

-- Type level natural
data Nat = Z | S Nat

-- Type level addition
type family Add (n :: Nat) (m :: Nat) :: Nat
type instance Add Z      m = m
type instance Add (S m)  n = S (Add m n)

-- Secret Type
data STypes where
    BBool :: Boolean -> STypes
    BInt  :: Integer -> STypes
    BChar :: Char    -> STypes

-- Public type
data PType where
    Nil  :: PType
    Cons :: STypes -> PType -> PType

-- Define the lagnuage
data CoreLang t (s :: Nat) where
    -- Literals
    LBool :: Bool -> CoreLang Bool Z

    -- Booleans
    And  :: CoreLang Bool m -> CoreLang Bool n -> CoreLang Bool (S (Add m n))
    Or   :: CoreLang Bool m -> CoreLang Bool n -> CoreLang Bool (S (Add m n))
    Not  :: CoreLang Bool m -> CoreLang Bool (S m)

    -- Integer
    Plus  :: CoreLang Int m -> CoreLang Int n -> CoreLang Int (S (Add m n))
    Minus :: CoreLang Int m -> CoreLang Int n -> CoreLang Int (S (Add m n))
    Mult  :: CoreLang Int m -> CoreLang Int n -> CoreLang Int (S (Add m n))
    Div   :: CoreLang Int m -> CoreLang Int n -> CoreLang Int (S (Add m n))

    -- Control Structures
    If   :: BBool -> CoreLang m -> CoreLang m -> CoreLang (S m)

--An interpreter
interpret :: CoreLang t m -> t
interpret = error "implement"