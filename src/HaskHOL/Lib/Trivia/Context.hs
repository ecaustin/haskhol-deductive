{-# LANGUAGE DataKinds, EmptyDataDecls, TypeOperators, UndecidableInstances #-}
module HaskHOL.Lib.Trivia.Context
    ( TriviaType
    , TriviaThry
    , TriviaCtxt
    , ctxtTrivia
    ) where

import HaskHOL.Core

import HaskHOL.Lib.DRule
import HaskHOL.Lib.Classic

import HaskHOL.Lib.Classic.Context
import HaskHOL.Lib.Trivia.Base

-- New Theory Type and Constraint
data TriviaThry
type instance TriviaThry == TriviaThry = 'True

instance CtxtName TriviaThry where
    ctxtName _ = "TriviaCtxt"

type instance PolyTheory TriviaType b = TriviaCtxt b

type family TriviaCtxt a :: Constraint where
    TriviaCtxt a = (Typeable a, ClassicCtxt a, TriviaContext a ~ 'True)

-- Assert Theory Hierarchy
type TriviaType = ExtThry TriviaThry ClassicType

type family TriviaContext a :: Bool where
    TriviaContext UnsafeThry = 'True
    TriviaContext BaseThry = 'False
    TriviaContext (ExtThry a b) = TriviaContext b || (a == TriviaThry)

ctxtTrivia :: TheoryPath TriviaType
ctxtTrivia = extendTheory ctxtClassic ($thisModule') $
-- Stage 1
    do parseAsInfix ("o", (26, "right"))
       mapM_ newDefinition
         [ ("o", [txt| (o) (f:B->C) g = \x:A. f(g(x)) |])
         , ("I", [txt| I = \x:A. x |])
         ]
       void $ newTypeDefinition "1" "one_ABS" "one_REP" thmEXISTS_ONE_REP
       void $ newDefinition ("one", [txt| one = @x:1. T |])
-- Stage 2
       addIndDef ("1", (1, induct_one, recursion_one))
