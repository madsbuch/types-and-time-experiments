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

type family Max (n :: Nat) (m :: Nat) :: Nat
type instance Max Z Z     = Z
type instance Max Z (S n) = S n
type instance Max (S n) Z = S n
type instance Max (S n) (S m) = S (Max n m)

-- List type, Size is the only thing we leak
infixr 4 :::
data List a (size :: Nat) where
    Nill :: List a Z
    (:::) :: a -> List a m -> List a (S m)

data SumType a b = InL a | InR b

data TypePack a where
    B :: Bool       -> TypePack Bool
    L :: List a s   -> TypePack (List a s)
    I :: Int        -> TypePack Int
    U ::               TypePack ()
    P :: a -> b     -> TypePack (a, b)
    E :: SumType a b-> TypePack (SumType a b)

data BoolT = FalseT | TrueT

type ThirtyTwo = (S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( S ( Z)))))))))))))))))))))))))))))))))

-- Define the lagnuage
data CoreLang t (s :: Nat) where
    -- Literals
    Lit   :: TypePack a -> CoreLang (TypePack a) Z

    -- Let 
    Let   :: CoreLang (TypePack a) n -> (CoreLang (TypePack a) Z -> CoreLang (TypePack b) m) -> CoreLang (TypePack b) (S (Add n m))
    
    -- Skip
    Skip    :: CoreLang (TypePack a) n -> CoreLang (TypePack a) (S n)
    SkipSeq :: CoreLang (TypePack a) n -> CoreLang (TypePack b) m -> CoreLang (TypePack b) (S (Add n m))

    -- Booleans
    And  :: CoreLang (TypePack Bool) m -> CoreLang (TypePack Bool) n -> CoreLang (TypePack Bool) (S (Add m n))
    Or   :: CoreLang (TypePack Bool) m -> CoreLang (TypePack Bool) n -> CoreLang (TypePack Bool) (S (Add m n))
    Not  :: CoreLang (TypePack Bool) m -> CoreLang (TypePack Bool) (S m)

    -- Pairs
    Fst  :: CoreLang (TypePack (TypePack a, TypePack b)) n -> CoreLang (TypePack a) (S n)
    Scn  :: CoreLang (TypePack (TypePack a, TypePack b)) n -> CoreLang (TypePack b) (S n)
    Pair :: CoreLang (TypePack a) n -> CoreLang (TypePack b) m -> CoreLang (TypePack (TypePack a, TypePack b)) (S (Add n m))

    SumL  :: CoreLang (TypePack a) n -> CoreLang (TypePack (SumType (TypePack a) (TypePack b))) (S n)
    SumR  :: CoreLang (TypePack b) n -> CoreLang (TypePack (SumType (TypePack a) (TypePack b))) (S n)
    Case  :: CoreLang (TypePack (SumType (TypePack a) (TypePack b))) n
          -> (CoreLang (TypePack a) Z -> CoreLang (TypePack c) m) -- In Left
          -> (CoreLang (TypePack b) Z -> CoreLang (TypePack c) m) -- In Right
          -> CoreLang (TypePack c) (S (S (Add n m)))

    -- Integer
    Plus  :: CoreLang (TypePack Int) m -> CoreLang (TypePack Int) n -> CoreLang (TypePack Int)  (S (Add m n))
    Minus :: CoreLang (TypePack Int) m -> CoreLang (TypePack Int) n -> CoreLang (TypePack Int)  (S (Add m n))
    Time  :: CoreLang (TypePack Int) m -> CoreLang (TypePack Int) n -> CoreLang (TypePack Int)  (S (Add m n))
    Div   :: CoreLang (TypePack Int) m -> CoreLang (TypePack Int) n -> CoreLang (TypePack Int)  (S (Add m n))
    IEq   :: CoreLang (TypePack Int) m -> CoreLang (TypePack Int) n -> CoreLang (TypePack Bool) (S (Add m n))
    ILt   :: CoreLang (TypePack Int) m -> CoreLang (TypePack Int) n -> CoreLang (TypePack Bool) (S (Add m n))
    IGt   :: CoreLang (TypePack Int) m -> CoreLang (TypePack Int) n -> CoreLang (TypePack Bool) (S (Add m n))

    Explode :: CoreLang (TypePack Int) m -> CoreLang (TypePack (List (TypePack Bool) ThirtyTwo)) (S m)
    
    -- List operations
    
    Cons :: CoreLang (TypePack (List (TypePack a) s)) n ->
            CoreLang (TypePack a) m ->
            CoreLang (TypePack (List (TypePack a) (S s))) (S (Add n m))
    
    Map  :: CoreLang (TypePack (List (TypePack a) s)) n
         -> (CoreLang (TypePack a) Z -> CoreLang (TypePack b) fTime)
         -> CoreLang (TypePack (List (TypePack b) s)) (S (Add n (Mult (S fTime) s)))

    Fold  :: CoreLang (TypePack (List (TypePack a) s)) n
          -> CoreLang (TypePack b) n0 -- accumulator
          -> (CoreLang (TypePack a) Z -> CoreLang (TypePack b) Z -> CoreLang (TypePack b) fTime)
          -> CoreLang (TypePack b) (S (Add n (Add n0 (Mult (S fTime) s))))

    Zip :: CoreLang (TypePack (List (TypePack a) s)) n
        -> CoreLang (TypePack (List (TypePack b) s)) m
        -> CoreLang (TypePack (List (TypePack ((TypePack a), (TypePack b))) s)) (S (Add n (Add m s)))


    -- Misc - actually, the relevant stuff
    -- Conditional
    If   :: CoreLang (TypePack Bool) m1 -> CoreLang (TypePack a) m2 -> CoreLang (TypePack a) m2 -> CoreLang (TypePack a) (S (Add m1 m2))

instance Show a => Show (List a s) where
    show (x ::: xs) = (show x) ++ " ::: " ++ (show xs)
    show (Nill)     = "Nill" 

instance (Show a, Show b) => Show (SumType a b) where
    show (InL a) = "(InL " ++ show a ++ ")"
    show (InR a) = "(InR " ++ show a ++ ")"

instance Show a => Show (TypePack a) where
    show (B b)      = "(B " ++ show b ++ ")"
    show (I i)      = "(I " ++ show i ++ ")"
    show (L l)      = "(L " ++ show l ++ ")"
    show (U)        = "()"
    show (E a)      = "(E " ++ show a ++ ")"

--instance (Show a, Show b) => Show (TypePack (a, b)) where
--    show (P a b)    = "(" ++ show a ++ ", " ++ show b ++ ")"

instance Show t => Show (CoreLang t s) where
    show (Lit l) = (show l)
--    show (Fold f i l) = "(Fold f " ++ show i ++ " " ++ show l ++ ")"


getBit a n = if (not $ 0 == ((.&.) (2^n) a)) then (B True) else (B False) 
explodeInt a = L $ (getBit a 0) ::: (getBit a 1) ::: (getBit a 2) ::: (getBit a 3) ::: (getBit a 4) ::: (getBit a 5) ::: (getBit a 6) ::: (getBit a 7) ::: (getBit a 8) ::: (getBit a 9) ::: (getBit a 10) ::: (getBit a 11) ::: (getBit a 12) ::: (getBit a 13) ::: (getBit a 14) ::: (getBit a 15) ::: (getBit a 16) ::: (getBit a 17) ::: (getBit a 18) ::: (getBit a 19) ::: (getBit a 20) ::: (getBit a 21) ::: (getBit a 22) ::: (getBit a 23) ::: (getBit a 24) ::: (getBit a 25) ::: (getBit a 26) ::: (getBit a 27) ::: (getBit a 28) ::: (getBit a 29) ::: (getBit a 30) ::: (getBit a 31) ::: Nill

--An interpreter
interpret :: CoreLang t m -> (t, Integer)

-- Basic operations
interpret (Lit l)  = (l, 0)
interpret (Skip a) = let
                        (a', t) = interpret a
                     in
                        (a', t+1)
                        
interpret (SkipSeq a b) = let
                        (a', t1) = interpret a
                        (b', t2) = interpret b
                     in
                        (b', t1 + t2 + 1)
                        
interpret (Explode a) = let 
                          (I a', t) = interpret a
                        in 
                          (explodeInt a', t+1)
                        
interpret (Let a f) = let
                        (a', t1) = interpret a
                        (b', t2) = interpret (f (Lit a'))
                     in
                        (b', t1+t2+1)
                       
                        
interpret (Or a b) = let
                        a'@(B a'', t1) = interpret a
                        b'@(B b'', t2) = interpret b
                    in 
                        (B (a'' || b''), t1+t2+1)

interpret (And a b) = let
                        a'@(B a'', t1) = interpret a
                        b'@(B b'', t2) = interpret b
                    in 
                        (B (a'' && b''), t1+t2+1)

interpret (Not a) = let
                        a'@(B a'', t) = interpret a
                    in
                        (B (not a''), t+1)

interpret (Plus a b) = let
                          a'@(I a'', t1) = interpret a
                          b'@(I b'', t2) = interpret b
                       in
                          (I (a'' + b''), t1+t2+1)

interpret (Minus a b) = let
                          a'@(I a'', t1) = interpret a
                          b'@(I b'', t2) = interpret b
                      in
                          (I (a'' - b''), t1+t2+1)

interpret (Time a b) = let
                          a'@(I a'', t1) = interpret a
                          b'@(I b'', t2) = interpret b
                      in
                          (I (a'' * b''), t1+t2+1)

interpret (Div a b) = let
                          a'@(I a'', t1) = interpret a
                          b'@(I b'', t2) = interpret b
                      in
                          (I (div a''  b''), t1+t2+1)

interpret (IEq a b) = let
                          a'@(I a'', t1) = interpret a
                          b'@(I b'', t2) = interpret b
                      in
                          (B (a'' == b''), t1+t2+1)
                          
interpret (ILt a b) = let
                          a'@(I a'', t1) = interpret a
                          b'@(I b'', t2) = interpret b
                      in
                          (B (a'' < b''), t1+t2+1)
                          
interpret (IGt a b) = let
                          a'@(I a'', t1) = interpret a
                          b'@(I b'', t2) = interpret b
                      in
                          (B (a'' > b''), t1+t2+1)


-- Sum types
interpret (SumL a) = let
                        a'@(a'', t) = interpret a
                     in
                        ((E (InL a'')), t+1)
interpret (SumR a) = let
                        a'@(a'', t) = interpret a
                     in
                        (E (InR a''), t+1)

interpret (Case a f g) = (case (interpret a) of
                           (E (InL b), t) -> pack t (interpret (f (Lit b)))
                           (E (InR c), t) -> pack t (interpret (g (Lit c))))
  where
    pack t1 (a, t2) = (a, t1+t2+2)

-- Product types
interpret (Fst p) = case (interpret p) of
                       ((P a b), t) -> (a, t+1)

interpret (Scn p) = case (interpret p) of
                       ((P a b), t) -> (b, t+1)

interpret (Pair a b) = let
                        a'@(a'', t1) = interpret a
                        b'@(b'', t2) = interpret b
                       in
                        (P (a'') (b''), t1+t2+1)

-- List operations

interpret (Cons list e) = let
                            (l', t1) = interpret list
                            (e', t2) = interpret e
                          in 
                            case l' of 
                                (L l'') -> ((L (e' ::: l'')), t1+t2+1)

interpret (Map list f) = let
                            a@(a', t1) = interpret list
                            b@(b', t2) = doMap a' f
                         in
                            (b', t1+t2+1)
  where
    doMap :: TypePack (List (TypePack a) s) -> (CoreLang (TypePack a) Z -> CoreLang (TypePack b) fTime) -> (TypePack (List (TypePack b) s), Integer)
    doMap (L Nill) f          = ((L Nill), 0)
    doMap (L (x ::: xs)) f    = case (doMap (L xs) f) of
                                           ((L e), t1) -> case (interpret (f (Lit x))) of
                                                (i, t2) -> ((L (i ::: e)), t1+t2 + 1)


interpret (Fold list n f) = let
                                l'@(l'', t1) = (interpret list)
                                n'@(n'', t2) = (interpret n)
                                d'@(d'', t3) = doFold l'' f n''
                            in
                                (d'', t1+t2+t3+1)                                
  where
    doFold :: TypePack (List (TypePack a) s) -> (CoreLang (TypePack a) Z -> CoreLang (TypePack b) Z -> CoreLang (TypePack b) fTime) -> TypePack b -> (TypePack b, Integer)
    doFold (L Nill) f n          = (n, 0)
    doFold (L (x ::: xs)) f n    = let
                                    i@(i', t1) = interpret (f (Lit x) (Lit n))
                                    g@(g', t2) = doFold (L xs) f i'
                                   in
                                    (g', t1+t2 + 1)

interpret (Zip xs ys) = let
                            a'@(a'', t1)  = interpret xs
                            b'@(b'', t2)  = interpret ys
                            dz@(dz'', t3) = doZip a'' b''
                        in
                            (dz'', t1+t2+t3+1)
  where
    doZip :: TypePack (List (TypePack a) s) -> TypePack (List (TypePack b) s) -> (TypePack (List (TypePack ((TypePack a), (TypePack b))) s), Integer)
    doZip (L Nill) (L Nill) = (L Nill, 0)
    doZip (L (x ::: xs)) (L (y ::: ys)) = case (doZip (L xs) (L ys)) of
                                            ((L e), t) -> (L(P x y ::: e), t+1)


-- If
interpret (If cond tBranch fBranch) = let 
                                        cond'@(B cond'', t1) = interpret cond
                                        tb@(tBranch', tt) = interpret tBranch
                                        fb@(fBranch', tf) = interpret fBranch
                                    in
                                        if cond'' then (tBranch', t1+tt+1) else (fBranch', t1+tf+1)


------------- END INTERPRETER -------------

timedInterpret :: CoreLang (TypePack a) t -> IO (TypePack a)
timedInterpret exp = do
    start <- getCPUTime
    let (r, cMilli) = (interpret exp)
    let c = cMilli * 1000
    end <- r `deepseq` getCPUTime
    let ellapsed = (div ((fromIntegral end) - (fromIntegral start)) 1000000)
    let sleepTime = ((fromIntegral c) - ellapsed)
    threadDelay sleepTime -- from picosecond (10^-12) to mikrosecond (10^-6)
    return r

instance NFData (TypePack a) where 
    rnf (B a) = rnf a
    rnf (I a) = rnf a
    rnf (U)   = rnf ()


-- A couple of basic tests

testList = Lit $ L (B True ::: B True ::: B False ::: B False ::: Nill )

mapTest list = (Map list (\b -> (And
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

-- Standard operations
         
equalIntList xs ys = Fold (Map (Zip xs ys) (\p -> IEq (Fst p) (Scn p))) (Lit (B True)) (\a b -> And a b)


list = Lit $ L (I 119 ::: I 101 ::: I 98 ::: Nill)




-- Statically limit execution time
{-
type family Sub (n :: Nat) (m :: Nat) :: Nat
type instance Sub Z     m      = m
type instance Sub (S m) (S n)  = (Sub m n)

class Sub a b => Leq a b where
-}
{-

data Refl a b = Refl a a
data Leq  (x :: Nat) (y :: Nat) where
  Leq :: SNat x -> SNat y -> Leq (Sub x y) x

satisfies_limit :: SNat limit -> CoreLang a time -> Leq time limit 
satisfies_limit l e = Leq l l

-}

{-
data SNat a where
  SZero :: SNat Z
  SSucc :: SNat a -> SNat (S a)

sNatToInt :: SNat m -> Int
sNatToInt SZero       = 0
sNatToInt (SSucc t)   = (sNatToInt t) + 1

constructList ::  SNat s -> TypePack (List (TypePack Int) s)
constructList SZero         = L Nill
constructList (SSucc r)     = case (constructList r) of
                                (L list) -> (L ((I (sNatToInt r) ) ::: list))

theList a = foldr (:::) Nill [if (not $ 0 == ((.&.) (2^n) a)) then 1 else 0 | n<-[0..31]]
-}

-- Constant time multiplication
buildList a1 = Let (Plus a1 a1) (\a2 -> Let (Plus a2 a2) (\a3 -> Let (Plus a3 a3) (\a4 -> Let (Plus a4 a4) (\a5 -> Let (Plus a5 a5) (\a6 -> Let (Plus a6 a6) (\a7 -> Let (Plus a7 a7) (\a8 -> Let (Plus a8 a8) (\a9 -> Let (Plus a9 a9) (\a10 -> Let (Plus a10 a10) (\a11 -> Let (Plus a11 a11) (\a12 -> Let (Plus a12 a12) (\a13 -> Let (Plus a13 a13) (\a14 -> Let (Plus a14 a14) (\a15 -> Let (Plus a15 a15) (\a16 -> Let (Plus a16 a16) (\a17 -> Let (Plus a17 a17) (\a18 -> Let (Plus a18 a18) (\a19 -> Let (Plus a19 a19) (\a20 -> Let (Plus a20 a20) (\a21 -> Let (Plus a21 a21) (\a22 -> Let (Plus a22 a22) (\a23 -> Let (Plus a23 a23) (\a24 -> Let (Plus a24 a24) (\a25 -> Let (Plus a25 a25) (\a26 -> Let (Plus a26 a26) (\a27 -> Let (Plus a27 a27) (\a28 -> Let (Plus a28 a28) (\a29 -> Let (Plus a29 a29) (\a30 -> Let (Plus a30 a30) (\a31 -> Let (Plus a31 a31) (\a32 -> 
                    (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Cons (Lit (L Nill)) a32) a31) a30) a29) a28) a27) a26) a25) a24) a23) a22) a21) a20) a19) a18) a17) a16) a15) a14) a13) a12) a11) a10) a9) a8) a7) a6) a5) a4) a3) a2) a1)
               )))))))))))))))))))))))))))))))

mult a b = Fold (Map (Zip (buildList a) (Explode b)) (\p -> If (Scn p) (Fst p) (Skip (Lit (I 0))))) (Lit (I 0)) (\a b -> Plus a b)
        
test a b = timedInterpret (mult (Lit (I a)) (Lit (I b)))         
