{-# LANGUAGE DataKinds, EmptyDataDecls, TypeOperators, UndecidableInstances #-}
module HaskHOL.Lib.Classic.Context
    ( ClassicType
    , ClassicThry
    , ClassicCtxt
    , ctxtClassic
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Simp
import HaskHOL.Lib.IndDefs

import HaskHOL.Lib.IndDefs.Context
import HaskHOL.Lib.Classic.Base

-- New Theory Type and Constraint
data ClassicThry
type instance ClassicThry == ClassicThry = 'True

instance CtxtName ClassicThry where
    ctxtName _ = "ClassicCtxt"

type instance PolyTheory ClassicType b = ClassicCtxt b

type family ClassicCtxt a :: Constraint where
    ClassicCtxt a = (Typeable a, IndDefsCtxt a, ClassicContext a ~ 'True)

-- Assert Theory Hierarchy
type ClassicType = ExtThry ClassicThry IndDefsType

type family ClassicContext a :: Bool where
    ClassicContext BaseThry = 'False
    ClassicContext (ExtThry a b) = ClassicContext b || (a == ClassicThry)

ctxtClassic :: TheoryPath ClassicType
ctxtClassic = extendTheory ctxtIndDefs $(thisModule') $
-- stage1
    do parseAsBinder "@"
       newConstant "@" "(A->bool)->A"
       sequence_ [axETA', axSELECT']
       void defCOND'
-- stage2
       rewr1 <- thmSELECT_REFL'
       extendBasicRewrites [rewr1]
-- stage3
       rewr2 <- thmNOT_CLAUSE'
       rewr3 <- thmCOND_CLAUSES'
       extendBasicRewrites [rewr2, rewr3]
-- stage4
       mthm <- thmMONO_COND'
       addMonoThm mthm
       cth <- thmCOND_CONG'
       extendBasicCongs [cth]
       rth <- thmCOND_EQ_CLAUSE'
       extendBasicRewrites [rth]
       boolTh1 <- inductBool'
       boolTh2 <- recursionBool'
       addIndDefs [("bool", (2, boolTh1, boolTh2))]
