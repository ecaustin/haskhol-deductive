{-# LANGUAGE DataKinds, EmptyDataDecls, UndecidableInstances #-}
{-|
  Module:    HaskHOL.Lib.Bool.Context
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown

  This module extends the 'ctxtBase' context with the 'loadBoolLib' computation.
  It exports the theory context, quasi-quoter, and compile-time proof methods
  for the Boolean logic library.
-}
module HaskHOL.Lib.Bool.Context
    ( BoolType
    , BoolThry
    , BoolCtxt
    , ctxtBool
    , bool
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Bool.Base

templateTypes ctxtBase "Bool"

ctxtBool :: TheoryPath BoolType
ctxtBool = extendTheory ctxtBase $
    do parseAsPrefix "~"
       mapM_ parseAsInfix [ ("==>", (4, "right"))
                          , ("\\/", (6, "right"))
                          , ("/\\", (8, "right"))
                          , ("<=>", (2, "right")) ]
       mapM_ parseAsBinder ["!", "?", "?!"]
       mapM_ parseAsTyBinder ["!!", "??"]
       overrideInterface "<=>" [str| (=):bool->bool->bool |]
       sequence_ [ defT'
                 , defAND'
                 , defIMP'
                 , defFORALL'
                 , defEXISTS'
                 , defOR'
                 , defFALSE'
                 , def_FALSITY_'
                 , defNOT'
                 , defEXISTS_UNIQUE'
                 , defTY_FORALL'
                 , defTY_EXISTS'
                 ]

templateProvers 'ctxtBool

-- have to manually write this, for now
-- we bake in ctxtname to clean stuff up later
type family BoolCtxt a :: Constraint where
    BoolCtxt a = (CtxtName a, BaseCtxt a, BoolContext a ~ 'True)

type instance PolyTheory BoolType b = BoolCtxt b
