{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}


module Auction where

import Language 

--- START AUCTION MODULE --- 

-- Library functions
atIndex list index = Fold list (SumL (Lit (I 0))) (\e acc -> (
                    Case acc 
                        (\n -> 
                            If (IEq n index)
                                (Skip (SumR (e)))
                                (SumL (Plus n (Lit (I 1))))
                        )
                        (\_ ->  
                            (Skip (Skip (Skip (Skip (acc)))))
                        )
                 ))
                 
atIndexWithDefault list index def = Case (atIndex list index) (\_ -> def) (\x -> x)
                 
atIndexTest = interpret (atIndex (Lit $ L ((I 0) ::: (I 3) ::: Nill)) (Lit (I 1))) -- Little test 


-- Items: 
-- 0: Chicken. Normal price: 30
-- 1: Cow. Normal price: 5000
-- 2: Cricket. Normal price: 2
-- 3: Salmon. Normal price 300

{-
CoreLang (TypePack (List (TypePack Int) s1)) n1
     -> CoreLang
          (TypePack
             (TypePack Int,
              TypePack (List (TypePack (TypePack Bool, TypePack Int)) s)))
          n

-}


--                  [ID, Quantity, price pr. item]
type AuctionOffer = TypePack (List (TypePack Int) (S (S (S Z))))
--  ID, [(quantityGt?, quantityTest), (priceGt?, priceTest)] -- 
type AuctionOfferCondition = TypePack ((TypePack Int), (TypePack (List (TypePack (TypePack Bool, TypePack Int)) (S (S Z)))))
type AuctionOfferConditions size = TypePack (List AuctionOfferCondition size)



testNumber isGt number test = If isGt 
                                (IGt number test)
                                (ILt number test) 

-- An example of just how expressive the language is. 
isConditionSatisfied offer condition = let
                                        offerId = atIndexWithDefault offer (Lit (I 0)) (Lit (I (-1)))
                                        offerQuantity = atIndexWithDefault offer (Lit (I 1)) (Lit (I (-1)))
                                        offerPrice = atIndexWithDefault offer (Lit (I 2)) (Lit (I (-1)))
                                        conditionId = Fst condition
                                        conditionQuantityGt = Fst (atIndexWithDefault (Scn condition) (Lit (I 0)) (Lit (P (B True) (I (-1)))))
                                        conditionQuantity =  Scn (atIndexWithDefault (Scn condition) (Lit (I 0)) (Lit (P (B True) (I (-1)))))
                                        conditionPriceGt =  Fst (atIndexWithDefault (Scn condition) (Lit (I 1)) (Lit (P (B True) (I (-1)))))
                                        conditionPrice =  Scn (atIndexWithDefault (Scn condition) (Lit (I 1)) (Lit (P (B True) (I (-1)))))
                                     in 
                                        And (IEq offerId conditionId) 
                                            (And
                                                (testNumber conditionQuantityGt offerQuantity conditionQuantity)
                                                (testNumber conditionPriceGt offerPrice conditionPrice)
                                            )

                          

                          
auctionBuyer1Conditions :: AuctionOfferConditions (S (S Z))
auctionBuyer1Conditions = L (
                            -- Wants to buy chicken for under 20, any quantity
                            (P (I 0) (L (((P (B True) (I 0))) ::: (P (B False) (I 20)) ::: Nill))) ::: 
                            -- Wants at most 5 salmon, any price
                            (P (I 3) (L (((P (B False) (I 6))) ::: (P (B True) (I (-1))) ::: Nill))) ::: 
                            Nill
                          )

isOfferAccepted offer conditions = Fold (Map conditions (\cond -> isConditionSatisfied offer cond)) (Lit (B False)) (\a b -> Or a b)

offer1 :: AuctionOffer
offer1 = L ((I 0) ::: (I 10) ::: (I 25) ::: Nill)

marchant1 = \offer -> (isOfferAccepted offer (Lit auctionBuyer1Conditions))

interpMerchant marchant offer = fst (interpret (marchant (Lit offer)))

-- Marchant 2, wants to buy crickets, ALL the crickets. 
marchant2 = \offer -> IEq (atIndexWithDefault offer (Lit (I 0)) (Lit (I (-1)))) (Lit (I 2))

marchants = [interpMerchant marchant1, interpMerchant marchant2]

acceptedOffer1 = map (\marchant -> marchant offer1) marchants 
