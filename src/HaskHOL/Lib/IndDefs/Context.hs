{-# LANGUAGE DataKinds, EmptyDataDecls, TypeOperators, UndecidableInstances #-}
module HaskHOL.Lib.IndDefs.Context
    ( IndDefsType
    , IndDefsThry
    , IndDefsCtxt
    , ctxtIndDefs
    ) where

import HaskHOL.Core
import HaskHOL.Lib.Theorems

import HaskHOL.Lib.Theorems.Context
import HaskHOL.Lib.IndDefs.Base

-- New Theory Type and Constraint
data IndDefsThry
type instance IndDefsThry == IndDefsThry = 'True

instance CtxtName IndDefsThry where
    ctxtName _ = "IndDefsCtxt"

type instance PolyTheory IndDefsType b = IndDefsCtxt b

type family IndDefsCtxt a :: Constraint where
    IndDefsCtxt a = (Typeable a, TheoremsCtxt a, IndDefsContext a ~ 'True)

-- Assert Theory Hierarchy
type IndDefsType = ExtThry IndDefsThry TheoremsType

type family IndDefsContext a :: Bool where
    IndDefsContext BaseThry = 'False
    IndDefsContext (ExtThry a b) = IndDefsContext b || (a == IndDefsThry)

ctxtIndDefs :: TheoryPath IndDefsType
ctxtIndDefs = extendTheory ctxtTheorems $(thisModule') $
    mapM_ addMonoThm [ thmMONO_AND, thmMONO_OR, thmMONO_IMP
                     , thmMONO_NOT, thmMONO_EXISTS, thmMONO_FORALL ]
