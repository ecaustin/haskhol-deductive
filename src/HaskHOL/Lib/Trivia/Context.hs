{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TypeSynonymInstances,
             UndecidableInstances #-}
module HaskHOL.Lib.Trivia.Context
    ( TriviaType
    , TriviaCtxt
    , ctxtTrivia
    , trivia
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Classic
import HaskHOL.Lib.Simp

import HaskHOL.Lib.Trivia.A.Context
import HaskHOL.Lib.Trivia.Base

-- generate template types
extendTheory ctxtTriviaA "Trivia" $
    do iTh <- induct_one
       rTh <- recursion_one
       addIndDefs [("1", (1, iTh, rTh))]

templateProvers 'ctxtTrivia

-- have to manually write this, for now
type family TriviaCtxt a where
    TriviaCtxt a = (TriviaACtxt a, TriviaContext a ~ 'True)

type instance PolyTheory TriviaType b = TriviaCtxt b

instance BasicConvs TriviaType where
    basicConvs _ = []
