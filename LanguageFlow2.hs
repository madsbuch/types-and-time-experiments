{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}


module Language where

import Data.Bits
import Control.Concurrent (threadDelay)
import System.CPUTime
import Control.DeepSeq

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

data Label = Public | Secret

type family LabelLub (a :: Label) (b :: Label) :: Label
type instance LabelLub Public Public = Public
type instance LabelLub Public Secret = Secret
type instance LabelLub Secret Public = Secret
type instance LabelLub Secret Secret = Secret

type family LabelLub3 (a :: Label) (b :: Label) (c :: Label) :: Label
type instance LabelLub3 a b c = (LabelLub (LabelLub a b) c)

data Time = Dependent Label | Constant Nat

type family TimeLub (a :: Time) (b :: Time) :: Time
type instance TimeLub (Dependent l1) (Dependent l2) = Dependent (LabelLub l1 l2)
type instance TimeLub (Dependent l1) (Constant t1) = Dependent l1
type instance TimeLub (Constant t1) (Dependent l1) = Dependent l1
type instance TimeLub (Constant t1) (Constant t2) = Constant (Add t1 t2)

type family TimeLub3 (a :: Time) (b :: Time) (c :: Time) :: Time
type instance TimeLub3 a b c = TimeLub (TimeLub a b) c

type family TimeLub4 (a :: Time) (b :: Time) (c :: Time) (d :: Time) :: Time
type instance TimeLub4 a b c d = TimeLub (TimeLub3 a b c) d

type family TimeMult (a :: Time) (b :: Nat) :: Time
type instance TimeMult (Dependent l1) b = Dependent l1
type instance TimeMult (Constant t1) b = Constant (Mult t1 b)

-- List type, Size is the only thing we leak
infixr 4 :::
data List a (size :: Nat) where
    Nill :: List a Z
    (:::) :: a -> List a m -> List a (S m)

data SumType a b = InL a | InR b

data SecLevel (l :: Label) where
    Pub :: SecLevel Public
    Sec :: SecLevel Secret

data TypePack a (l :: Label) where
    B :: SecLevel l -> Bool       -> TypePack Bool l
    L :: SecLevel l -> List a s   -> TypePack (List a s) l
    I :: SecLevel l -> Int        -> TypePack Int l
    U :: SecLevel l ->               TypePack () l
    P :: SecLevel l -> a -> b     -> TypePack (a, b) l
    E :: SecLevel l -> SumType a b-> TypePack (SumType a b) l

type ThirtyTwo = (S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( Z)))))))))))))))))))))))))))))))))


-- Define the lagnuage
data CoreLang t (s :: Time) where
    -- Literals
    Lit   :: TypePack a l -> CoreLang (TypePack a l) (Constant Z)
    
    -- Let 
    Let   :: CoreLang (TypePack a l1) t1 -> (CoreLang (TypePack a l1) (Constant Z) -> CoreLang (TypePack b l2) t2) -> CoreLang (TypePack b l2) (TimeLub3 t1 t2 (Constant (S Z)))
    
    -- Skip
    Skip    :: CoreLang (TypePack a l) t -> CoreLang (TypePack a l) (TimeLub t (Constant (S Z)))
    SkipSeq :: CoreLang (TypePack a l1) t1 -> CoreLang (TypePack b l2) t2 -> CoreLang (TypePack b l2) (TimeLub3 t1 t2 (Constant (S Z)))

    -- Booleans
    And  :: CoreLang (TypePack Bool l1) t1 -> CoreLang (TypePack Bool l2) t2 -> CoreLang (TypePack Bool (LabelLub l1 l2)) (TimeLub3 (Constant (S Z)) t1 t2)
    Or   :: CoreLang (TypePack Bool l1) t1 -> CoreLang (TypePack Bool l2) t2 -> CoreLang (TypePack Bool (LabelLub l1 l2)) (TimeLub3 (Constant (S Z)) t1 t2)
    Not  :: CoreLang (TypePack Bool l1) t1 -> CoreLang (TypePack Bool l1) (TimeLub t1 (Constant (S Z)))
    
    -- If
    If      :: CoreLang (TypePack Bool l1) t1 -> 
               CoreLang (TypePack a l2) t2 -> 
               CoreLang (TypePack a l3) t3 -> 
               CoreLang (TypePack a (LabelLub3 l1 l2 l3)) (TimeLub4 t1 t2 t3 (Dependent l1))
               
    IfConst :: CoreLang (TypePack Bool l1) t1 -> 
               CoreLang (TypePack a l2) (Constant t2) -> 
               CoreLang (TypePack a l3) (Constant t2) -> 
               CoreLang (TypePack a (LabelLub3 l1 l2 l3)) (TimeLub t1 (Constant t2))
    

    -- Pairs
    Fst  :: CoreLang (TypePack (TypePack a l1, TypePack b l2) l)  t -> CoreLang (TypePack a (LabelLub l1 l)) (TimeLub t (Constant (S Z)))
    Scn  :: CoreLang (TypePack (TypePack a l1, TypePack b l2) l)  t -> CoreLang (TypePack b (LabelLub l2 l)) (TimeLub t (Constant (S Z)))
    Pair :: CoreLang (TypePack a l1) t1 -> CoreLang (TypePack b l2) t2 -> CoreLang (TypePack (TypePack a l1, TypePack b l2) (LabelLub l1 l2)) (TimeLub3 t1 t2 (Constant (S Z)))

    {- SumL  :: CoreLang (TypePack a l) t -> CoreLang (TypePack (SumType (TypePack a) (TypePack b)) l) (TimeLub t (Constant (S Z)))
    SumR  :: CoreLang (TypePack b l) t -> CoreLang (TypePack (SumType (TypePack a) (TypePack b)) l)  (TimeLub t (Constant (S Z)))
    Case  :: CoreLang (TypePack (SumType (TypePack a) (TypePack b)) l1) t1
          -> (CoreLang (TypePack a l1) (Constant Z) -> CoreLang (TypePack c l2) t2) -- In Left
          -> (CoreLang (TypePack b l1) (Constant Z) -> CoreLang (TypePack c l3) t3) -- In Right
          -> CoreLang (TypePack c (LabelLub3 l1 l2 l3)) (TimeLub4 (Dependent l1) t1 t2 t3) 
          
    CaseConst  :: CoreLang (TypePack (SumType (TypePack a) (TypePack b))) l1 t1
               -> (CoreLang (TypePack a) l1 (Constant Z) -> CoreLang (TypePack c) l2 (Constant t2)) -- In Left
               -> (CoreLang (TypePack b) l1 (Constant Z) -> CoreLang (TypePack c) l3 (Constant t2)) -- In Right
               -> CoreLang (TypePack c) (LabelLub3 l1 l2 l3) (TimeLub t1 (Constant (S t2)))      -}

    -- Integer
    Plus  :: CoreLang (TypePack Int l1) t1 -> CoreLang (TypePack Int l2) t2 -> CoreLang (TypePack Int (LabelLub l1 l2)) (TimeLub3 t1 t2 (Constant (S Z)))
    Minus :: CoreLang (TypePack Int l1) t1 -> CoreLang (TypePack Int l2) t2 -> CoreLang (TypePack Int (LabelLub l1 l2)) (TimeLub3 t1 t2 (Constant (S Z)))
    Time  :: CoreLang (TypePack Int l1) t1 -> CoreLang (TypePack Int l2) t2 -> CoreLang (TypePack Int (LabelLub l1 l2)) (TimeLub3 t1 t2 (Constant (S Z)))
    Div   :: CoreLang (TypePack Int l1) t1 -> CoreLang (TypePack Int l2) t2 -> CoreLang (TypePack Int (LabelLub l1 l2)) (TimeLub3 t1 t2 (Constant (S Z)))
    IEq   :: CoreLang (TypePack Int l1) t1 -> CoreLang (TypePack Int l2) t2 -> CoreLang (TypePack Bool (LabelLub l1 l2)) (TimeLub3 t1 t2 (Constant (S Z)))
    ILt   :: CoreLang (TypePack Int l1) t1 -> CoreLang (TypePack Int l2) t2 -> CoreLang (TypePack Bool (LabelLub l1 l2)) (TimeLub3 t1 t2 (Constant (S Z)))
    IGt   :: CoreLang (TypePack Int l1) t1 -> CoreLang (TypePack Int l2) t2 -> CoreLang (TypePack Bool (LabelLub l1 l2)) (TimeLub3 t1 t2 (Constant (S Z)))

    -- Explode :: CoreLang (TypePack Int) l t -> CoreLang (TypePack (List (TypePack Bool) ThirtyTwo)) l (TimeLub t (Constant (S Z)))
    
    -- List operations
    Cons :: CoreLang (TypePack (List (TypePack a elementLabel1) s) listLabel) t1 ->
            CoreLang (TypePack a elementLabel2) t2 ->
            CoreLang (TypePack (List (TypePack a (LabelLub elementLabel1 elementLabel2)) (S s)) listLabel) (TimeLub3 t1 t2 (Constant (S Z)))
            
    -- Security downgrade operations
    {-TimeToPublic :: CoreLang (TypePack a) l1 (Constant t1) -> CoreLang (TypePack a) l1 (TimeLub t1 (Dependent Public))
    TimeToSecret :: CoreLang (TypePack a) l1 t1 -> CoreLang (TypePack a) l1 (TimeLub t1 (Dependent Secret))
    
    LabelToSecret :: CoreLang (TypePack a) l1 t1 -> CoreLang (TypePack a) Secret t1-}
    
    Map  :: CoreLang (TypePack (List (TypePack a el) s) ll) t1
         -> (CoreLang (TypePack a el) (Constant Z) -> CoreLang (TypePack b el2) fTime)
         -> CoreLang (TypePack (List (TypePack b el2) s) l1) (TimeLub3 t1 (Constant (S Z)) (TimeMult fTime s))

    {-Fold  :: CoreLang (TypePack (List (TypePack a) s)) l1 t1
          -> CoreLang (TypePack b) l2 t2
          -> (CoreLang (TypePack a) l1 (Constant Z) -> CoreLang (TypePack b) l2 (Constant Z) -> CoreLang (TypePack b) l2 fTime)
          -> CoreLang (TypePack b) l2 (TimeLub4 (Constant (S Z)) t1 t2 (TimeMult fTime s))

    Zip :: CoreLang (TypePack (List (TypePack a) s)) l1 t1
        -> CoreLang (TypePack (List (TypePack b) s)) l2 t2
        -> CoreLang (TypePack (List (TypePack ((TypePack a), (TypePack b))) s)) (LabelLub l1 l2) (TimeLub4 (Constant (S Z)) t1 t2 (Constant s))
        
-}


instance Show a => Show (List a s) where
    show (x ::: xs) = (show x) ++ " ::: " ++ (show xs)
    show (Nill)     = "Nill" 
    

instance (Show a, Show b) => Show (SumType a b) where
    show (InL a) = "(InL " ++ show a ++ ")"
    show (InR a) = "(InR " ++ show a ++ ")"

instance Show a => Show (TypePack a l) where
    show (B r b)      = "(B " ++ show b ++ ")"
    show (I r i)      = "(I " ++ show i ++ ")"
    show (L r l)      = "(L " ++ show l ++ ")"
    show (U r)        = "()"
    show (E r a)      = "(E " ++ show a ++ ")"

--instance (Show a, Show b) => Show (TypePack (a, b)) where
--    show (P a b)    = "(" ++ show a ++ ", " ++ show b ++ ")"

instance Show t => Show (CoreLang t s) where
    show (Lit l) = (show l)
--    show (Fold f i l) = "(Fold f " ++ show i ++ " " ++ show l ++ ")"




--getBit a n = if (not $ 0 == ((.&.) (2^n) a)) then (B True) else (B False) 
--explodeInt a = L $ (getBit a 0) ::: (getBit a 1) ::: (getBit a 2) ::: (getBit a 3) ::: (getBit a 4) ::: (getBit a 5) ::: (getBit a 6) ::: (getBit a 7) ::: (getBit a 8) ::: (getBit a 9) ::: (getBit a 10) ::: (getBit a 11) ::: (getBit a 12) ::: (getBit a 13) ::: (getBit a 14) ::: (getBit a 15) ::: (getBit a 16) ::: (getBit a 17) ::: (getBit a 18) ::: (getBit a 19) ::: (getBit a 20) ::: (getBit a 21) ::: (getBit a 22) ::: (getBit a 23) ::: (getBit a 24) ::: (getBit a 25) ::: (getBit a 26) ::: (getBit a 27) ::: (getBit a 28) ::: (getBit a 29) ::: (getBit a 30) ::: (getBit a 31) ::: Nill

interpretLub :: SecLevel l1 -> SecLevel l2 -> SecLevel (LabelLub l1 l2)
interpretLub Pub Pub = Pub
interpretLub Pub Sec = Sec
interpretLub Sec Pub = Sec
interpretLub Sec Sec = Sec

getLabel :: TypePack a l -> SecLevel l
getLabel (B l b) = l
getLabel (I l i) = l
getLabel (L l i) = l
getLabel (U l) = l
getLabel (P l a b) = l
getLabel (E l e) = l

setLabel :: TypePack a l1 -> SecLevel l2 -> TypePack a l2
setLabel (B l b) l2 = B l2 b
setLabel (I l i) l2 = (I l2 i)
setLabel (L l i) l2 = (L l2 i)
setLabel (U l) l2 = (U l2)
setLabel (P l a b) l2 = (P l2 a b) 
setLabel (E l e) l2 = (E l2 e)


--An interpreter
interpret :: CoreLang t m -> t

-- Basic operations
interpret (Lit l)  = l

interpret (Let a f) = let
                        a' = interpret a
                        b' = interpret (f (Lit a'))
                     in
                        b'

interpret (Skip a) = interpret a

interpret (SkipSeq a b) = let
                             a' = interpret a
                             b' = interpret b
                          in
                             b'
                        
{-interpret (Explode a) = let 
                          (I a') = interpret a
                        in 
                          explodeInt a'-}
                                                
                       

interpret (Or a b) = let
                        (B l1 a') = interpret a
                        (B l2 b') = interpret b
                    in 
                        B (interpretLub l1 l2) (a' || b')

interpret (And a b) = let
                        (B l1 a') = interpret a
                        (B l2 b') = interpret b
                    in 
                        B (interpretLub l1 l2) (a' && b')

interpret (Not a) = let
                        (B l a') = interpret a
                    in
                        B l (not a')

interpret (Plus a b) = let
                          (I l1 a') = interpret a
                          (I l2 b') = interpret b
                       in
                          I (interpretLub l1 l2) (a' + b')

interpret (Minus a b) = let
                          (I l1 a') = interpret a
                          (I l2 b') = interpret b
                      in
                          I (interpretLub l1 l2) (a' - b')

interpret (Time a b) = let
                          (I l1 a') = interpret a
                          (I l2 b') = interpret b
                      in
                          I (interpretLub l1 l2) (a' * b')

interpret (Div a b) = let
                          (I l1 a') = interpret a
                          (I l2 b') = interpret b
                      in
                          I (interpretLub l1 l2) (div a' b')

interpret (IEq a b) = let
                          (I l1 a') = interpret a
                          (I l2 b') = interpret b
                      in
                          B (interpretLub l1 l2) (a' == b')
                          
interpret (ILt a b) = let
                          (I l1 a') = interpret a
                          (I l2 b') = interpret b
                      in
                          B (interpretLub l1 l2) (a' < b')
                          
interpret (IGt a b) = let
                          (I l1 a') = interpret a
                          (I l2 b') = interpret b
                      in
                          B (interpretLub l1 l2) (a' > b')
                          
interpret (If cond tBranch fBranch) = let 
                                        (B l1 cond') = interpret cond
                                        tBranch' = interpret tBranch
                                        l2 = getLabel tBranch'
                                        fBranch' = interpret fBranch
                                        l3 = getLabel fBranch'
                                        label = interpretLub (interpretLub l1 l2) l3
                                    in
                                        if cond' then setLabel tBranch' label else setLabel fBranch' label

interpret (IfConst cond tBranch fBranch) = let 
                                        (B l1 cond') = interpret cond
                                        tBranch' = interpret tBranch
                                        l2 = getLabel tBranch'
                                        fBranch' = interpret fBranch
                                        l3 = getLabel fBranch'
                                        label = interpretLub (interpretLub l1 l2) l3
                                    in
                                        if cond' then setLabel tBranch' label else setLabel fBranch' label

{-
-- Sum types
{-interpret (SumL a) = let
                        a' = interpret a
                     in
                        E (InL a')
interpret (SumR a) = let
                        a' = interpret a
                     in
                        E (InR a')

interpret (Case a f g) = (case (interpret a) of
                           (E (InL b)) -> interpret (f (Lit b))
                           (E (InR c)) -> interpret (g (Lit c)))
                           
interpret (CaseConst a f g) = (case (interpret a) of
                           (E (InL b)) -> interpret (f (Lit b))
                           (E (InR c)) -> interpret (g (Lit c)))

-- Product types
interpret (Fst p) = case (interpret p) of
                       (P a b) -> a

interpret (Scn p) = case (interpret p) of
                       (P a b) -> b

interpret (Pair a b) = let
                        a' = interpret a
                        b' = interpret b
                       in
                        P (a') (b')

-- List operations

interpret (Cons list e) = let
                            l' = interpret list
                            e' = interpret e
                          in 
                            case l' of 
                                (L l'') -> L (e' ::: l'')

interpret (Map list f) = let
                            a' = interpret list
                            b' = doMap a' f
                         in
                            b'
  where
    doMap :: TypePack (List (TypePack a) s) -> (CoreLang (TypePack a) l1 (Constant Z) -> CoreLang (TypePack b) l2 fTime) -> TypePack (List (TypePack b) s)
    doMap (L Nill) f          = (L Nill)
    doMap (L (x ::: xs)) f    = case (doMap (L xs) f) of
                                           (L e) -> case (interpret (f (Lit x))) of
                                                i -> (L (i ::: e))


{-interpret (Fold list n f) = let
                                l' = interpret list
                                n' = interpret n
                                d' = doFold l' f n'
                            in
                                d'
  where
    doFold :: TypePack (List (TypePack a) s) -> (CoreLang (TypePack a) l1 (Constant Z) -> CoreLang (TypePack b) l2 (Constant Z) -> CoreLang (TypePack b) l2 fTime) -> TypePack b -> TypePack b
    doFold (L Nill) f n          = n
    doFold (L (x ::: xs)) f n    = let
                                    i' = interpret (f (Lit x) (Lit n))
                                    g' = doFold (L xs) f i'
                                   in
                                    g'

interpret (Zip xs ys) = let
                            a'  = interpret xs
                            b'  = interpret ys
                            dz' = doZip a' b'
                        in
                            dz'
  where
    doZip :: TypePack (List (TypePack a) s) -> TypePack (List (TypePack b) s) -> TypePack (List (TypePack ((TypePack a), (TypePack b))) s)
    doZip (L Nill) (L Nill) = L Nill
    doZip (L (x ::: xs)) (L (y ::: ys)) = case (doZip (L xs) (L ys)) of
                                            (L e) -> L(P x y ::: e) -}

-}-}


                                        
                                        
                                        
pInt = Lit (I Pub 1) 
pInt2 = Lit (I Pub 3) 
sInt = Lit (I Sec 2)

foo = If (IEq pInt sInt) (Plus pInt pInt) (pInt)

bar = IfConst (IEq pInt sInt) pInt pInt2

