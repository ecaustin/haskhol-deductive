{-|
  Module:    HaskHOL.Lib.Trivia
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Trivia
    ( TriviaType
    , TriviaCtxt
    , defI
    , defO
    , thmI
    , thm_one
    , def_one
    , induct_one
    , recursion_one
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Simp
import HaskHOL.Lib.Tactics

import HaskHOL.Lib.Trivia.Base
import HaskHOL.Lib.Trivia.Context

thmI :: TriviaCtxt thry => HOL cls thry HOLThm
thmI = cacheProof "thmI" ctxtTrivia $
    prove "!x:A. I x = x" $ tacREWRITE [defI]
