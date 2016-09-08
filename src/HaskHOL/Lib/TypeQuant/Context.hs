{-# LANGUAGE DataKinds, EmptyDataDecls, TypeOperators, UndecidableInstances #-}
module HaskHOL.Lib.TypeQuant.Context
    ( TypeQuantType
    , TypeQuantThry
    , TypeQuantCtxt
    , ctxtTypeQuant
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Simp

import HaskHOL.Lib.Trivia.Context

-- New Theory Type and Constraint
data TypeQuantThry
type instance TypeQuantThry == TypeQuantThry = 'True

instance CtxtName TypeQuantThry where
    ctxtName _ = "TypeQuantCtxt"

type instance PolyTheory TypeQuantType b = TypeQuantCtxt b

type family TypeQuantCtxt a :: Constraint where
    TypeQuantCtxt a = (Typeable a, TriviaCtxt a, TypeQuantContext a ~ 'True)

-- Assert Theory Hierarchy
type TypeQuantType = ExtThry TypeQuantThry TriviaType

type family TypeQuantContext a :: Bool where
    TypeQuantContext UnsafeThry = 'True
    TypeQuantContext BaseThry = 'False
    TypeQuantContext (ExtThry a b) = TypeQuantContext b || (a == TypeQuantThry)

ctxtTypeQuant :: TheoryPath TypeQuantType
ctxtTypeQuant = extendTheory ctxtTrivia $(thisModule') $ 
    extendBasicConvs 
      [("convTYBETA", 
        ([txt| ((\\ 'B. t):(% 'B. C)) [: 'A] |], "HaskHOL.Lib.TypeQuant"))]

