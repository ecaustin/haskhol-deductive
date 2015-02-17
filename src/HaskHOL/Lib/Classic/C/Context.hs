{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TemplateHaskell, 
             TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
module HaskHOL.Lib.Classic.C.Context
    ( ClassicCType
    , ClassicCCtxt
    , ctxtClassicC
    , classicC
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Bool
import HaskHOL.Lib.Simp

import HaskHOL.Lib.Classic.B
import HaskHOL.Lib.Classic.C.Base

-- generate template types
extendTheory ctxtClassicB "ClassicC" $
    extendBasicRewrites =<< 
      sequence [ruleCONJUNCT1 thmNOT_CLAUSES, thmCOND_CLAUSES]

templateProvers 'ctxtClassicC

-- have to manually write this, for now
type family ClassicCCtxt a where
    ClassicCCtxt a = (ClassicBCtxt a, ClassicCContext a ~ 'True)

type instance PolyTheory ClassicCType b = ClassicCCtxt b

instance BasicConvs ClassicCType where
    basicConvs _ = []
