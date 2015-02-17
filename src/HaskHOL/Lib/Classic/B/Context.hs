{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TypeSynonymInstances,
             UndecidableInstances #-}
module HaskHOL.Lib.Classic.B.Context
    ( ClassicBType
    , ClassicBCtxt
    , ctxtClassicB
    , classicB
    ) where

import HaskHOL.Core
import HaskHOL.Lib.Simp

import HaskHOL.Lib.Classic.A.Context
import HaskHOL.Lib.Classic.B.Base

-- generate template types
extendTheory ctxtClassicA "ClassicB" $
    extendBasicRewrites =<< sequence [ thmSELECT_REFL ]

templateProvers 'ctxtClassicB

-- have to manually write this, for now
type family ClassicBCtxt a where
    ClassicBCtxt a = (ClassicACtxt a, ClassicBContext a ~ 'True)

type instance PolyTheory ClassicBType b = ClassicBCtxt b

instance BasicConvs ClassicBType where
    basicConvs _ = []
