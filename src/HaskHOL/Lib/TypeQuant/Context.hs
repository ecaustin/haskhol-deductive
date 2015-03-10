{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TypeSynonymInstances,
             UndecidableInstances #-}
module HaskHOL.Lib.TypeQuant.Context
    ( TypeQuantType
    , TypeQuantThry
    , TypeQuantCtxt
    , ctxtTypeQuant
    , typeQuant
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Simp

import HaskHOL.Lib.Trivia.Context

templateTypes ctxtTrivia "TypeQuant"

ctxtTypeQuant :: TheoryPath TypeQuantType
ctxtTypeQuant = extendTheory ctxtTrivia $ 
    do tm <- toHTm [str| ((\\ 'B. t):(% 'B. C)) [: 'A] |]
       extendBasicConvs 
         ("tybeta", (tm, ("convTYBETA", ["HaskHOL.Lib.TypeQuant"])))

templateProvers 'ctxtTypeQuant

-- have to manually write this, for now
type family TypeQuantCtxt a where
    TypeQuantCtxt a = (TriviaCtxt a, TypeQuantContext a ~ 'True)

type instance PolyTheory TypeQuantType b = TypeQuantCtxt b
