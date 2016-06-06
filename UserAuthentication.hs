{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}


module UserAuthentication where

import Language 

{-
User authentication example.

First we deine a list of users, then we generate a function for
testing if a user is in that list
-}

-- First, letS make some type aliases so we can type annotate everything, this makes
-- it easier for us to see what goes on

-- We use the fixed-length integer string a whole let. There fore we make a type for it
type Thirty = (S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S Z))))))))))))))))))))))))))))))
type String30 = TypePack (List (TypePack Int) Thirty)

-- UserName Is a fixed-length list of integers
type Username = String30
type Password = String30

type User = TypePack ((TypePack (Username, (TypePack Int))), Password)
type HashedUser = TypePack ((TypePack (Username, (TypePack Int))), (TypePack Int))

type UserList s = TypePack (List User s)

-- An example of a password hashing mechanism
hash pass = let
              multList = (Map pass (\char -> Time char (Time char char)))
              folded = Fold multList (Lit (I 0)) (\a b -> Plus a b)
            in
              folded

-- Then we make some users

-- First we completely annotate the variables.
user1Name :: Username -- "webbies"
user1Name = L (I 119 ::: I 101 ::: I 98 ::: I 98 ::: I 105 ::: I 101 ::: I 115 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: Nill)
user1Pass :: Password-- "hunter2"
user1Pass = L (I 104 ::: I 117 ::: I 110 ::: I 116 ::: I 101 ::: I 114 ::: I 50 ::: I 0  ::: I 0  ::: I 0  ::: I 0  ::: I 0  ::: I 0  ::: I 0  ::: I 0  ::: I 0  ::: I 0  ::: I 0  ::: I 0  ::: I 0  ::: I 0  ::: I 0  ::: I 0  ::: I 0  ::: I 0  ::: I 0  ::: I 0  ::: I 0  ::: I 0  ::: I 0  ::: Nill)
user1 :: User
user1 = (P (P user1Name (I 0)) user1Pass)

-- Secondly we show, that our types actually can be inferred by Haskell. Two other users are defined here:
 -- "warlizard"
user2Name = L (I 119 ::: I 97 ::: I 114 ::: I 108 ::: I 105 ::: I 122 ::: I 122 ::: I 97 ::: I 114 ::: I 100 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: Nill)
 -- "password"
user2Pass = L (I 112 ::: I 97 ::: I 115 ::: I 115 ::: I 119 ::: I 111 ::: I 114 ::: I 100 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: Nill )
user2 = (P (P user2Name (I 1)) user2Pass)

 -- "Randall"
user3Name = L (I 82 ::: I 97 ::: I 110 ::: I 100 ::: I 97 ::: I 108 ::: I 108 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: I 0 ::: Nill)
 -- "common horse battery staple"
user3Pass = L (I 99 ::: I 111 ::: I 109 ::: I 109 ::: I 111 ::: I 110 ::: I 32 ::: I 104 ::: I 111 ::: I 114 ::: I 115 ::: I 101 ::: I 32 ::: I 98 ::: I 97 ::: I 116 ::: I 116 ::: I 101 ::: I 114 ::: I 121 ::: I 32 ::: I 115 ::: I 116 ::: I 97 ::: I 112 ::: I 108 ::: I 101 ::: I 0 ::: I 0 ::: I 0 ::: Nill)
user3 = (P (P user3Name (I 2)) user3Pass)


-- List of users (3 users)
userList :: UserList (S (S (S Z)))
userList = L (user1 ::: user2 ::: user3 ::: Nill)

--hashUser :: User -> CoreLang HashedUser ('S ('S (Add Z ('S (Add (Add Z (Add Thirty (Add Thirty 'Z))) (Add Thirty 'Z))))))
hashUser user = Pair (Fst user) (hash (Scn user))

hashedUsers = Map (Lit $ L (user1 ::: user2 ::: user3 ::: Nill)) (\user -> hashUser user)

equalIntList xs ys = Fold (Map (Zip xs ys) (\p -> IEq (Fst p) (Scn p))) (Lit (B True)) (\a b -> And a b)

testUser user name password = And (equalIntList (Fst (Fst user)) name) (IEq (Scn user) password)

--getUserId :: UserList s -> Username -> Password -> TypePack Int
getUserId users uName pWord = let
                                        username = uName
                                        password = pWord
                                    in
                                        Fold users (SumL (Lit U)) (\candidate acc ->
                                            (Case acc 
                                                (\_ -> (If (testUser candidate username password) -- InL case
                                                    (SumR (Scn (Fst candidate))) -- Candidate Match
                                                    (Skip (Skip (SumL (Lit U)))) -- No Match
                                                     ))
                                                (\_ -> (If (testUser candidate username password) -- InR case, c/p for convenience
                                                    (Skip (Skip (Skip (acc)))) -- Candidate Match
                                                    (Skip (Skip (Skip (acc)))) -- No Match
                                                     )))
                                        )

-- Tests

-- Should return (B True)
testTestUser = testUser (hashUser (Lit user1)) (Lit user1Name) (hash (Lit user1Pass)) 

test = getUserId hashedUsers (Lit user1Name) (hash (Lit user1Pass))





testHashUser = hashUser (Lit user1)

--test1 = interpret (getUserId userList user1 user1Pass)