{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TypeSynonymInstances,
             UndecidableInstances #-}
module HaskHOL.Lib.Theorems.Context
    ( TheoremsType
    , TheoremsCtxt
    , ctxtTheorems
    , theorems
    ) where

import HaskHOL.Core
import HaskHOL.Lib.Simp

import HaskHOL.Lib.Bool.Context
import HaskHOL.Lib.Theorems.Base


extendTheory ctxtBool "Theorems" $
    do extendBasicRewrites =<< sequence [ thmREFL_CLAUSE
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
       extendBasicCongs =<< sequence [ thmBASIC_CONG ]

templateProvers 'ctxtTheorems

-- have to manually write this, for now
type family TheoremsCtxt a :: Constraint where
    TheoremsCtxt a = (BoolCtxt a, TheoremsContext a ~ 'True)

type instance PolyTheory TheoremsType b = TheoremsCtxt b

instance BasicConvs TheoremsType where
    basicConvs _ = []
