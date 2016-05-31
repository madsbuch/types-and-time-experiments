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

data TypePack a where
    B :: Bool     -> TypePack Bool
    L :: List a s -> TypePack (List a s)
    I :: Int      -> TypePack Int
    P :: a -> b -> TypePack (a, b)

-- Define the lagnuage
data CoreLang t (s :: Nat) where
    -- Literals
    Lit   :: TypePack a -> CoreLang (TypePack a) Z

    -- Booleans
    And  :: CoreLang (TypePack Bool) m -> CoreLang (TypePack Bool) n -> CoreLang (TypePack Bool) (S (Add m n))
    Or   :: CoreLang (TypePack Bool) m -> CoreLang (TypePack Bool) n -> CoreLang (TypePack Bool) (S (Add m n))
    --Not  :: CoreLang Bool m -> CoreLang Bool (S m)

    -- Pairs
    Fst  :: CoreLang (TypePack (TypePack a, TypePack b)) n -> CoreLang (TypePack a) (S n)
    Scn  :: CoreLang (TypePack (TypePack a, TypePack b)) n -> CoreLang (TypePack b) (S n)
    Pair :: CoreLang (TypePack a) n -> CoreLang (TypePack b) m -> CoreLang (TypePack (TypePack a, TypePack b)) (S (Add n m))

    -- Integer
    --Plus  :: CoreLang Int m -> CoreLang Int n -> CoreLang Int  (S (Add m n))
    --Minus :: CoreLang Int m -> CoreLang Int n -> CoreLang Int  (S (Add m n))
    --Time  :: CoreLang Int m -> CoreLang Int n -> CoreLang Int  (S (Add m n))
    --Div   :: CoreLang Int m -> CoreLang Int n -> CoreLang Int  (S (Add m n))
    --IEq   :: CoreLang Int m -> CoreLang Int n -> CoreLang Bool (S (Add m n))

    -- List operations
    Map  :: CoreLang (TypePack (List (TypePack a) s)) n
        -> (CoreLang (TypePack Int) Z -> CoreLang (TypePack a) Z -> CoreLang (TypePack b) fTime)
        -> CoreLang (TypePack (List (TypePack b) s)) (Add n (Mult fTime s))

    Fold  :: CoreLang (TypePack (List (TypePack a) s)) n
        -> CoreLang (TypePack b) n0 -- accumulator
        -> (CoreLang (TypePack Int) Z -> CoreLang (TypePack a) Z -> CoreLang (TypePack b) Z -> CoreLang (TypePack b) fTime)
        -> CoreLang (TypePack b) (Add n (Add n0 (Mult fTime s)))

    -- Misc - actually, the relevant stuff
    -- Conditional
    If   :: CoreLang (TypePack Bool) m1 -> CoreLang (TypePack a) m2 -> CoreLang (TypePack a) m2 -> CoreLang (TypePack a) (S (Add m1 m2))
    -- parallell computations
    -- Par  

instance Show a => Show (List a s) where
    show (x ::: xs) = (show x) ++ " ::: " ++ (show xs)
    show (Nill)     = "Nill" 

instance Show a => Show (TypePack a) where
    show (B b) = "(B " ++ show b ++ ")"
    show (I i) = "(I " ++ show i ++ ")"
    show (L l) = "(L " ++ show l ++ ")"

instance Show t => Show (CoreLang t s) where
    show (Lit l) = (show l)
--    show (Fold f i l) = "(Fold f " ++ show i ++ " " ++ show l ++ ")"


typeUnpack :: TypePack a -> a
typeUnpack (I i)    = i
typeUnpack (B b)    = b
typeUnpack (L l)    = l

--An interpreter
interpret :: CoreLang t m -> t
interpret (Lit l)  = l

interpret (Or a b) = let
                        a'@(B a'') = interpret a
                        b'@(B b'') = interpret b
                    in 
                        B (a'' || b'')

interpret (And a b) = let
                        a'@(B a'') = interpret a
                        b'@(B b'') = interpret b
                    in 
                        B (a'' && b'')

interpret (Fst p) = case (interpret p) of
                      (P a b) -> a

interpret (Scn p) = case (interpret p) of
                    (P a b) -> b

interpret (Pair a b) = (P (interpret a) (interpret b))

interpret (Map list f) = doMap (interpret list) f 0
  where
    doMap :: TypePack (List (TypePack a) s) -> (CoreLang (TypePack Int) Z -> CoreLang (TypePack a) Z -> CoreLang (TypePack b) fTime) -> Int -> TypePack (List (TypePack b) s)
    doMap (L Nill) f count          = (L Nill)
    doMap (L (x ::: xs)) f count    = case (doMap (L xs) f (count + 1)) of
                                           (L e) -> (L ((interpret (f (Lit (I count)) (Lit x))) ::: e))

interpret (Fold list n f) = doFold (interpret list) f (interpret n) 0
  where
    doFold :: TypePack (List (TypePack a) s) -> (CoreLang (TypePack Int) Z -> CoreLang (TypePack a) Z -> CoreLang (TypePack b) Z -> CoreLang (TypePack b) fTime) -> TypePack b -> Int -> (TypePack b)
    doFold (L Nill) f n count          = n
    doFold (L (x ::: xs)) f n count    = doFold (L xs) (f) (interpret (f (Lit (I count)) (Lit x) (Lit n))) (count + 1)


interpret (If cond tBranch fBranch) = let 
                                        cond'@(B cond'') = interpret cond
                                        tBranch' = interpret tBranch
                                        fBranch' = interpret fBranch
                                    in
                                        if cond'' then tBranch' else fBranch'

listBools = Lit $ L (B False ::: B False ::: B True ::: B False ::: Nill)


{-
user1Name = L (I 119 ::: I 101 ::: I 98 ::: I 98 ::: I 105 ::: I 101 ::: I 115 ::: Nill) -- "webbies"
user1Pass = L (I 104 ::: I 117 ::: I 110 ::: I 116 ::: I 101 ::: I 114 ::: I 50  ::: Nill) -- "hunter2"
user1 = Lit $ L (user1Name ::: user1Pass ::: Nill)

user2Name = L (I 119 ::: I 97 ::: I 114 ::: I 108 ::: I 105 ::: I 122 ::: I 122 ::: I 97 ::: I 114 ::: I 100 ::: Nill) -- "warlizard"
user2Pass = L (I 112 ::: I 97 ::: I 115 ::: I 115 ::: I 119 ::: I 111 ::: I 114 ::: I 100 ::: Nill ) -- "password"
user2 = Lit $ L (user2Name ::: user2Pass ::: Nill)

user3Name = L (I 82 ::: I 97 ::: I 110 ::: I 100 ::: I 97 ::: I 108 ::: I 108 ::: Nill) -- "Randall"
user3Pass = L (I 99 ::: I 111 ::: I 109 ::: I 109 ::: I 111 ::: I 110 ::: I 32 ::: I 104 ::: I 111 ::: I 114 ::: I 115 ::: I 101 ::: I 32 ::: I 98 ::: I 97 ::: I 116 ::: I 116 ::: I 101 ::: I 114 ::: I 121 ::: I 32 ::: I 115 ::: I 116 ::: I 97 ::: I 112 ::: I 108 ::: I 101 ::: Nill) -- "common horse battery staple"

-}


listUsers = Lit $ L (I 34 ::: Nill)


mapTest list = (Map list (\_ b -> (And
    (And (Lit (B True)) b)) (Lit (B True)) ))

-- Does not typecheck!!!
--noTypeCheckTest = If 
--                (Lit (B True)) 
--                (Lit (B False)) 
--                (Or (Lit (B True)) (Lit (B False)))

-- Does type check
doesTypeCheckTest = If 
                (Lit (B True)) 
                (And (Lit (B True)) (Lit (B False)))
                (Or (Lit (B True)) (Lit (B False)))

{- Some Applications -}

-- Secure login, User

-- ordinary Haskell
--checkUser us ul = foldl (||) False (map (==us) ul)

--userList = LList (LInt 133 ::: LInt 3434 ::: LInt 23234 ::: LInt 3434 ::: Nill)
--userCheckTrue  = (LInt 133)
--userCheckFalse = (LInt 323)


{-
This first example generates a program which can check if a user exists in a list
-}
-- Note that we can force literals in the type
--checkUser :: CoreLang Int Z 
--    -> CoreLang (List (CoreLang Int Z) s) (S (Add Z Z)) 
--    -> CoreLang Bool (Add (Mult s (S Z)) Z)

--elementEquals x xs = (Map xs (\y -> (IEq y x)))
{-
doOr :: CoreLang Bool m -> CoreLang Bool n -> CoreLang Bool (S (Add m n))
doOr a b = (Or a b)

false :: CoreLang Bool Z
false = (Lit $ B False)


--foldOr :: CoreLang (List Bool s) s -> CoreLang Bool s
--foldOr xs = (Fold doOr false xs)

--    Fold :: (CoreLang a m1 -> CoreLang a m2 -> CoreLang a (S (Add m1 m2))) -- function, only constant operations time
--        -> CoreLang a n0 -- Neutral element
--        -> CoreLang (List (CoreLang a n1) s) n2 --list to fold over
--        -> CoreLang a (Add (Mult s (S (Add m1 m2))) n0)

-- checkUser user uList         = 
-}
-- Generate expression for execution
--cuExp = checkUser (LInt 133) userList


-- Safe multi threading (relate to the presented paper)

{-

# Problems doing this:

## Fold

* Functions used to fold has to be dependent, so we can statically infer running time

-}