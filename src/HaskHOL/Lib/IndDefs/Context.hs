{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TypeSynonymInstances,
             UndecidableInstances #-}
module HaskHOL.Lib.IndDefs.Context
    ( IndDefsType
    , IndDefsCtxt
    , ctxtIndDefs
    , indDefs
    ) where

import HaskHOL.Core
import HaskHOL.Lib.Theorems
import HaskHOL.Lib.Simp

import HaskHOL.Lib.Theorems.Context
import HaskHOL.Lib.IndDefs.Base

extendTheory ctxtTheorems "IndDefs" $
    mapM_ addMonoThm [ thmMONO_AND, thmMONO_OR, thmMONO_IMP
                     , thmMONO_NOT, thmMONO_EXISTS, thmMONO_FORALL ]

templateProvers 'ctxtIndDefs

-- have to manually write this, for now
type family IndDefsCtxt a where
    IndDefsCtxt a = (TheoremsCtxt a, IndDefsContext a ~ 'True)

type instance PolyTheory IndDefsType b = IndDefsCtxt b

instance BasicConvs IndDefsType where
    basicConvs _ = []
