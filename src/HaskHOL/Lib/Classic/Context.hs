{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TypeSynonymInstances,
             UndecidableInstances #-}
module HaskHOL.Lib.Classic.Context
    ( ClassicType
    , ClassicCtxt
    , ctxtClassic
    , classic
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Simp
import HaskHOL.Lib.IndDefs

import HaskHOL.Lib.Classic.C.Context
import HaskHOL.Lib.Classic.Base

templateTypes ctxtClassicC "Classic"

ctxtClassic :: TheoryPath ClassicType
ctxtClassic = extendTheory ctxtClassicC $
    do mthm <- thmMONO_COND
       addMonoThm mthm
       cth <- thmCOND_CONG
       extendBasicCongs [cth]
       rth <- thmCOND_EQ_CLAUSE
       extendBasicRewrites [rth]
       boolTh1 <- inductBool
       boolTh2 <- recursionBool
       addIndDefs [("bool", (2, boolTh1, boolTh2))]

templateProvers 'ctxtClassic

-- have to manually write this, for now
type family ClassicCtxt a where
    ClassicCtxt a = (ClassicCCtxt a, ClassicContext a ~ 'True)

type instance PolyTheory ClassicType b = ClassicCtxt b

instance BasicConvs ClassicType where
    basicConvs _ = []
