{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TypeSynonymInstances,
             UndecidableInstances #-}
module HaskHOL.Lib.Trivia.A.Context
    ( TriviaAType
    , TriviaACtxt
    , ctxtTriviaA
    , triviaA
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Simp

import HaskHOL.Lib.Classic.Context
import HaskHOL.Lib.Trivia.A.Base

templateTypes ctxtClassic "TriviaA"

ctxtTriviaA :: TheoryPath TriviaAType
ctxtTriviaA = extendTheory ctxtClassic $
    do parseAsInfix ("o", (26, "right"))
       sequence_ [defO', defI']
       void tyDefOne'
       void defONE'

templateProvers 'ctxtTriviaA

-- have to manually write this, for now
type family TriviaACtxt a where
    TriviaACtxt a = (ClassicCtxt a, TriviaAContext a ~ 'True)

type instance PolyTheory TriviaAType b = TriviaACtxt b

instance BasicConvs TriviaAType where
    basicConvs _ = []
