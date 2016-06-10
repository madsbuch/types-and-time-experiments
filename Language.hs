{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}


module Language where


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

-- Define the lagnuage
data CoreLang t (s :: Nat) where
    -- Literals
    Lit   :: TypePack a -> CoreLang (TypePack a) Z

    -- Skip
    Skip   :: CoreLang (TypePack a) n -> CoreLang (TypePack a) (S n)

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
    show (B b)    = "(B " ++ show b ++ ")"
    show (I i)    = "(I " ++ show i ++ ")"
    show (L l)    = "(L " ++ show l ++ ")"
    show (U)      = "()"
    --show (P a)  = "(" ++ show a ++ ", " ++ show b ++ ")"
    show (E a)    = "(E " ++ show a ++ ")"

instance Show t => Show (CoreLang t s) where
    show (Lit l) = (show l)
--    show (Fold f i l) = "(Fold f " ++ show i ++ " " ++ show l ++ ")"


--An interpreter
interpret :: CoreLang t m -> (t, Integer)

-- Basic operations
interpret (Lit l)  = (l, 0)
interpret (Skip a) = let
                        a'@(a'', t) = interpret a
                     in
                        (a'', t+1)
                        
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
                
equalIntList xs ys = Fold (Map (Zip xs ys) (\p -> IEq (Fst p) (Scn p))) (Lit (B True)) (\a b -> And a b)


list = Lit $ L (I 119 ::: I 101 ::: I 98 ::: Nill)

foo e acc = If (And (IEq (Plus e acc) (Lit (I 10)))  (equalIntList list list))
                (Lit (I 0)) 
                (Lit (I 1))

bar = foo (Lit $ I 0) (Lit $ I 2)

test = Fold list (Lit (I 0)) (\e acc -> foo e acc)
