{-# LANGUAGE DataKinds, EmptyDataDecls, TypeOperators, UndecidableInstances #-}
module HaskHOL.Lib.Classic.Context
    ( ClassicType
    , ClassicThry
    , ClassicCtxt
    , ctxtClassic
    ) where

import HaskHOL.Core

import HaskHOL.Lib.DRule
import HaskHOL.Lib.Simp
import HaskHOL.Lib.IndDefs

import HaskHOL.Lib.IndDefs.Context
import HaskHOL.Lib.Classic.Base

-- New Theory Type and Constraint
data ClassicThry
type instance ClassicThry == ClassicThry = 'True

instance CtxtName ClassicThry where
    ctxtName _ = "ClassicCtxt"

type instance PolyTheory ClassicType b = ClassicCtxt b

type family ClassicCtxt a :: Constraint where
    ClassicCtxt a = (Typeable a, IndDefsCtxt a, ClassicContext a ~ 'True)

-- Assert Theory Hierarchy
type ClassicType = ExtThry ClassicThry IndDefsType

type family ClassicContext a :: Bool where
    ClassicContext BaseThry = 'False
    ClassicContext (ExtThry a b) = ClassicContext b || (a == ClassicThry)

ctxtClassic :: TheoryPath ClassicType
ctxtClassic = extendTheory ctxtIndDefs $(thisModule') $
-- stage1
    do parseAsBinder "@"
       newConstant ("@", [txt| (A->bool)->A |])
       mapM_ newAxiom 
         [ ("axETA", [txt| !t:A->B. (\x. t x) = t |])
         , ("axSELECT", [txt| !P (x:A). P x ==> P((@) P) |])
         ]
       void $ newDefinition 
         ("COND", [txt| COND = \t t1 t2. @x:A. ((t <=> T) ==> (x = t1)) /\ 
                                               ((t <=> F) ==> (x = t2)) |])
-- stage2
       extendBasicRewrites [thmSELECT_REFL, thmNOT_CLAUSE, thmCOND_CLAUSES]
-- stage3
       addMonoThm thmMONO_COND
       extendBasicCongs [thmCOND_CONG]
       extendBasicRewrites [thmCOND_EQ_CLAUSE]
       addIndDef ("bool", (2, inductBool, recursionBool))
