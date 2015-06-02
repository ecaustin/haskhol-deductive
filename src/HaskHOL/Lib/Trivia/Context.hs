{-# LANGUAGE DataKinds, EmptyDataDecls, TypeOperators, UndecidableInstances #-}
module HaskHOL.Lib.Trivia.Context
    ( TriviaType
    , TriviaThry
    , TriviaCtxt
    , ctxtTrivia
    ) where

import HaskHOL.Core

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
    TriviaContext BaseThry = 'False
    TriviaContext (ExtThry a b) = TriviaContext b || (a == TriviaThry)

ctxtTrivia :: TheoryPath TriviaType
ctxtTrivia = extendTheory ctxtClassic ($thisModule') $
-- Stage 1
    do parseAsInfix ("o", (26, "right"))
       sequence_ [defO', defI']
       void tyDefOne'
       void defONE'
-- Stage 2
       iTh <- induct_one'
       rTh <- recursion_one'
       addIndDefs [("1", (1, iTh, rTh))]
