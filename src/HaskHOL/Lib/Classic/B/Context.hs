{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TypeSynonymInstances,
             UndecidableInstances #-}
module HaskHOL.Lib.Classic.B.Context
    ( ClassicBType
    , ClassicBThry
    , ClassicBCtxt
    , ctxtClassicB
    , classicB
    ) where

import HaskHOL.Core
import HaskHOL.Lib.Simp

import HaskHOL.Lib.Classic.A.Context
import HaskHOL.Lib.Classic.B.Base

templateTypes ctxtClassicA "ClassicB"

ctxtClassicB :: TheoryPath ClassicBType
ctxtClassicB = extendTheory ctxtClassicA $(thisModule') $
    extendBasicRewrites =<< sequence [ thmSELECT_REFL ]

templateProvers 'ctxtClassicB

-- have to manually write this, for now
type family ClassicBCtxt a where
    ClassicBCtxt a = (ClassicACtxt a, ClassicBContext a ~ 'True)

type instance PolyTheory ClassicBType b = ClassicBCtxt b
