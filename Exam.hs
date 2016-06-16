{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Exam where

import Language
import UserAuthentication
import Auction
import GHC.Exts (Constraint)

-- introducing the language

{- Some Data -}
intList = L (I 1 ::: I 2 ::: I 3 ::: I 4 ::: Nill )
plusFold l = Fold (Lit l) (Lit (I 0)) (\a b -> (Plus a b))

-- User authentication



-- Auction

-- Constant time multiplication

-- A litle easter egg: Our investigations allow that we can limit how many ticks
-- programs can take. This is done as follows:

-- Value level naturals
data SNat (a :: Nat) where
  SZ :: SNat Z
  SS :: SNat a -> SNat (S a)

-- A class, not important..
class ConstraintSatisfied (a :: Nat) where
instance ConstraintSatisfied Z where
instance ConstraintSatisfied (S t) where

-- Alright, this is tricky. We _only_ create a constraint iff n <= m. This results
-- in an ugly compile time error if it is not the case. 
type family Leq (n :: Nat) (m :: Nat) :: Constraint
type instance Leq Z     m      = ConstraintSatisfied m
type instance Leq (S m) (S n)  = (Leq m n)

-- A bound that ensures that they are within 50% of each others.
type family Bound (a :: Nat) (m :: Nat) :: Constraint
type instance a b  = (Leq a (Mult b (S(S(Z)))))
type instance a b  = (Leq b (Mult a (S(S(Z)))))

limitRuntimeInterpreter :: Leq t limit => SNat limit -> CoreLang a t -> (a, Integer)
limitRuntimeInterpreter _ exp = interpret exp

boundExeTimeInterpreter :: 

{- Play with compile til runtime constraints -}

--fails = limitRuntimeInterpreter (SS $ SZ) (plusFold intList)
works = limitRuntimeInterpreter (SS $ SS $ SS $ SS $ SS $ SS $ SS $ SS $ SS $ SS $ SS $ SZ) (plusFold intList)