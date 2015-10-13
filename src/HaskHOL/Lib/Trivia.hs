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

import qualified HaskHOL.Lib.Trivia.Base as Base
import HaskHOL.Lib.Trivia.Context
import HaskHOL.Lib.Trivia.PQ

defO :: TriviaCtxt thry => HOL cls thry HOLThm
defO = cacheProof "defO" ctxtTrivia $ getDefinition "o"

defI :: TriviaCtxt thry => HOL cls thry HOLThm
defI = cacheProof "defI" ctxtTrivia $ getDefinition "I"

tyDef1 :: TriviaCtxt thry => HOL cls thry HOLThm
tyDef1 = Base.tyDef1

def_one :: TriviaCtxt thry => HOL cls thry HOLThm
def_one = cacheProof "def_one" ctxtTrivia $ getDefinition "one"

thm_one :: TriviaCtxt thry => HOL cls thry HOLThm
thm_one = Base.thm_one

induct_one :: TriviaCtxt thry => HOL cls thry HOLThm
induct_one = Base.induct_one

recursion_one :: TriviaCtxt thry => HOL cls thry HOLThm
recursion_one = Base.recursion_one

thmI :: TriviaCtxt thry => HOL cls thry HOLThm
thmI = cacheProof "thmI" ctxtTrivia $
    prove "!x:A. I x = x" $ tacREWRITE [defI]
