{-|
  Module:    HaskHOL.Lib.Trivia
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Trivia
    ( TriviaCtxt
    , ctxtTrivia
    , trivia
    , defI
    , defO
    , tyDef1
    , thmI
    , thm_one
    , def_one
    , induct_one
    , recursion_one
    ) where

import HaskHOL.Core

import HaskHOL.Lib.DRule
import HaskHOL.Lib.Simp
import HaskHOL.Lib.Tactics
import HaskHOL.Lib.Classic

import HaskHOL.Lib.Trivia.Base
import HaskHOL.Lib.Trivia.Context
import HaskHOL.Lib.Trivia.PQ

defO :: TriviaCtxt thry => HOL cls thry HOLThm
defO = cacheProof "defO" ctxtTrivia $ getDefinition "o"

defI :: TriviaCtxt thry => HOL cls thry HOLThm
defI = cacheProof "defI" ctxtTrivia $ getDefinition "I"

tyDef1 :: TriviaCtxt thry => HOL cls thry HOLThm
tyDef1 = cacheProof "ty1" ctxtTrivia $ getTypeDefinition "1"

def_one :: TriviaCtxt thry => HOL cls thry HOLThm
def_one = cacheProof "def_one" ctxtTrivia $ getDefinition "one"

thm_one :: TriviaCtxt thry => HOL cls thry HOLThm
thm_one = cacheProof "thm_one" ctxtTrivia thm_one'

induct_one :: TriviaCtxt thry => HOL cls thry HOLThm
induct_one = cacheProof "induct_one" ctxtTrivia induct_one'

recursion_one :: TriviaCtxt thry => HOL cls thry HOLThm
recursion_one = cacheProof "recursion_one" ctxtTrivia recursion_one'

thmI :: TriviaCtxt thry => HOL cls thry HOLThm
thmI = cacheProof "thmI" ctxtTrivia $
    prove "!x:A. I x = x" $ tacREWRITE [defI]
