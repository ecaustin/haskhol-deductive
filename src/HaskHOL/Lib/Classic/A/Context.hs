{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TypeSynonymInstances,
             UndecidableInstances #-}
module HaskHOL.Lib.Classic.A.Context
    ( ClassicAType
    , ClassicACtxt
    , ctxtClassicA
    , classicA
    ) where

import HaskHOL.Core
import HaskHOL.Lib.Simp

import HaskHOL.Lib.IndDefs.Context
import HaskHOL.Lib.Classic.A.Base

templateTypes ctxtIndDefs "ClassicA"

ctxtClassicA :: TheoryPath ClassicAType
ctxtClassicA = extendTheory ctxtIndDefs $
    do parseAsBinder "@"
       newConstant "@" "(A->bool)->A"
       sequence_ [axETA', axSELECT']
       void defCOND'

templateProvers 'ctxtClassicA

-- have to manually write this, for now
type family ClassicACtxt a where
    ClassicACtxt a = (IndDefsCtxt a, ClassicAContext a ~ 'True)

type instance PolyTheory ClassicAType b = ClassicACtxt b

instance BasicConvs ClassicAType where
    basicConvs _ = []
