{-|
  Module:    HaskHOL.Lib.Misc
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Misc where

import HaskHOL.Core

import HaskHOL.Lib.Bool
import HaskHOL.Lib.Tactics
import HaskHOL.Lib.Simp

tacASSUM_MATCH_ACCEPT :: BoolCtxt thry => Tactic cls thry
tacASSUM_MATCH_ACCEPT = _FIRST_ASSUM tacMATCH_ACCEPT

tacASSUM_REWRITE :: (BasicConvs thry, BoolCtxt thry) 
                 => (HOLThm -> HOL cls thry HOLThm) -> Tactic cls thry
tacASSUM_REWRITE rl =
    _FIRST_X_ASSUM (\ thm gl ->
                      do th <- ruleREWRITE_NIL =<< rl thm
                         tacASSUME th gl)
