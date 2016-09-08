{-# LANGUAGE DataKinds, EmptyDataDecls, TypeOperators, UndecidableInstances #-}
module HaskHOL.Lib.Theorems.Context
    ( TheoremsType
    , TheoremsThry
    , TheoremsCtxt
    , ctxtTheorems
    ) where

import HaskHOL.Core
import HaskHOL.Lib.Simp

import HaskHOL.Lib.Bool.Context
import HaskHOL.Lib.Theorems.Base

-- New Theory Type and Constraint
data TheoremsThry
type instance TheoremsThry == TheoremsThry = 'True

instance CtxtName TheoremsThry where
    ctxtName _ = "TheoremsCtxt"

type instance PolyTheory TheoremsType b = TheoremsCtxt b

type family TheoremsCtxt a :: Constraint where
    TheoremsCtxt a = (Typeable a, BoolCtxt a, TheoremsContext a ~ 'True)

-- Assert Theory Hierarchy
type TheoremsType = ExtThry TheoremsThry BoolType

type family TheoremsContext a :: Bool where
    TheoremsContext UnsafeThry = 'True
    TheoremsContext BaseThry = 'False
    TheoremsContext (ExtThry a b) = TheoremsContext b || (a == TheoremsThry) 

ctxtTheorems :: TheoryPath TheoremsType
ctxtTheorems = extendTheory ctxtBool $(thisModule') $
    do extendBasicRewrites [ thmREFL_CLAUSE
                           , thmEQ_CLAUSES
                           , thmNOT_CLAUSES_WEAK
                           , thmAND_CLAUSES
                           , thmOR_CLAUSES
                           , thmIMP_CLAUSES
                           , thmFORALL_SIMP
                           , thmEXISTS_SIMP
                           , thmBETA
                           , thmIMP_EQ_CLAUSE
                           ]
       extendBasicCongs [ thmBASIC_CONG ]
