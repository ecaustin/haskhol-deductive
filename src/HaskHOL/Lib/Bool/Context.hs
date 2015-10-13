{-# LANGUAGE DataKinds, EmptyDataDecls, TypeOperators, UndecidableInstances #-}
{-|
  Module:    HaskHOL.Lib.Bool.Context
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown

  This module extends the 'ctxtBase' context with the 'loadBoolLib' computation.
  It exports the theory context, quasi-quoter, and compile-time proof methods
  for the Boolean logic library.
-}
module HaskHOL.Lib.Bool.Context
    ( -- * Theory Context
       -- $ThryCtxt
      BoolType
    , BoolThry
    , BoolCtxt
    , ctxtBool
    ) where

import HaskHOL.Core

-- New Theory Type and Constraint
data BoolThry
type instance BoolThry == BoolThry = 'True

instance CtxtName BoolThry where
    ctxtName _ = "BoolCtxt"

type instance PolyTheory BoolType b = BoolCtxt b

type family BoolCtxt a :: Constraint where
    BoolCtxt a = (Typeable a, BaseCtxt a, BoolContext a ~ 'True)

-- Assert Theory Hierarchy
type BoolType = ExtThry BoolThry BaseThry

type family BoolContext a :: Bool where
    BoolContext BaseThry = 'False
    BoolContext (ExtThry a b) = BoolContext b || (a == BoolThry)   

-- Build Context
ctxtBool :: TheoryPath BoolType
ctxtBool = extendTheory ctxtBase $(thisModule') $
    do parseAsPrefix "~"
       mapM_ parseAsInfix [ ("==>", (4, "right"))
                          , ("\\/", (6, "right"))
                          , ("/\\", (8, "right"))
                          , ("<=>", (2, "right")) ]
       mapM_ parseAsBinder ["!", "?", "?!"]
       mapM_ parseAsTyBinder ["!!", "??"]
       overrideInterface "<=>" [str| (=):bool->bool->bool |]
       mapM_ newBasicDefinition
         [ ("T", [str| T = ((\ p:bool . p) = (\ p:bool . p)) |])
         , ("/\\", [str| (/\) = \ p q . (\ f:bool->bool->bool . f p q) = 
                                        (\ f . f T T) |])
         , ("==>", [str| (==>) = \ p q . p /\ q <=> p |])
         , ("!", [str| (!) = \ P:A->bool . P = \ x . T |])
         , ("?", [str| (?) = \ P:A->bool . ! q . (! x . P x ==> q) ==> q |])
         , ("\\/", [str| (\/) = \ p q . ! r . (p ==> r) ==> (q ==> r)  ==> r |])
         , ("F", [str| F = ! p:bool . p |])
         , ("_FALSITY_", [str| _FALSITY_ = F |])
         , ("~", [str| (~) = \ p . p ==> F |])
         , ("?!", [str| (?!) = \ P:A->bool. ((?) P) /\ 
                                            (!x y. P x /\ P y ==> x = y) |])
         , ("!!", [str| (!!) = \ P : (% 'A. bool). P = (\\ 'A. T) |])
         , ("??", [str| (??) = \ P : (% 'A. bool). ~(P = (\\ 'A . F)) |])
         ]
