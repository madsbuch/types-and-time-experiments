{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Test where


instance Show ( a -> b ) where
    show f = "diller"

data Test a where
    T :: (a -> b) -> a -> Test b


data TLang a where
    TLit :: a -> TLang a
    TMap ::  (a -> b) ->  TLang [a] -> TLang [b]



eval :: TLang a -> a
eval (TLit a)   = a
eval (TMap f l) = (map f (eval l))
