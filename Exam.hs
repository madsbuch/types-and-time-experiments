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

data SNat (a :: Nat) where
  SZ :: SNat Z
  SS :: SNat a -> SNat (S a)

class IsLeq (a :: Nat) where

instance IsLeq Z where
instance IsLeq (S t) where

type family Leq (n :: Nat) (m :: Nat) :: Constraint
type instance Leq Z     m      = IsLeq m
type instance Leq (S m) (S n)  = (Leq m n)

limitRuntimeInterpreter :: Leq t limit => SNat limit -> CoreLang a t -> (a, Integer)
limitRuntimeInterpreter _ exp = interpret exp

{- Some Data -}
intList = Lit $ L (I 1 ::: I 2 ::: I 3 ::: I 4 ::: Nill )

plusFold l = Fold l (Lit (I 0)) (\a b -> (Plus a b))

{- Play with compile til runtime constraints -}

--fails = limitRuntimeInterpreter (SS $ SZ) (plusFold intList)
works = limitRuntimeInterpreter (SS $ SS $ SS $ SS $ SS $ SS $ SS $ SS $ SS $ SS $ SS $ SZ) (plusFold intList)