{-|
  Module:    HaskHOL.Deductive
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown

  This module is the one to import for users looking to include the entirety of
  the deductive reasoning engine of the HaskHOL proof system.  It re-exports all
  of the deductive sub-modules; additionally, it exports aliases to a theory 
  context, quasi-quoter, and compile-time proof methods for users who are
  working only with these libraries.
-}
module HaskHOL.Deductive
    ( -- * Theory Context
       -- $ThryCtxt
      DeductiveType
    , DeductiveCtxt
    , ctxtDeductive
    , deductive
      -- * Re-exported Modules
    , module HaskHOL.Lib.Equal
    , module HaskHOL.Lib.Bool
    , module HaskHOL.Lib.DRule
    , module HaskHOL.Lib.Tactics
    , module HaskHOL.Lib.Itab
    , module HaskHOL.Lib.Simp
    , module HaskHOL.Lib.Theorems
    , module HaskHOL.Lib.IndDefs
    , module HaskHOL.Lib.Classic
    , module HaskHOL.Lib.Trivia
    , module HaskHOL.Lib.Canon
    , module HaskHOL.Lib.Meson
    , module HaskHOL.Lib.Quot
    , module HaskHOL.Lib.Misc
    , module HaskHOL.Lib.TypeQuant
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Equal
import HaskHOL.Lib.Bool
import HaskHOL.Lib.DRule
import HaskHOL.Lib.Tactics
import HaskHOL.Lib.Itab
import HaskHOL.Lib.Simp
import HaskHOL.Lib.Theorems
import HaskHOL.Lib.IndDefs
import HaskHOL.Lib.Classic
import HaskHOL.Lib.Trivia
import HaskHOL.Lib.Canon
import HaskHOL.Lib.Meson
import HaskHOL.Lib.Quot
import HaskHOL.Lib.Misc
import HaskHOL.Lib.TypeQuant

import HaskHOL.Lib.TypeQuant.Context

{- $ThryCtxt
  See 'extendCtxt' in the "HaskHOL.Core.Ext" module for more information.
-}

{-| 
  The theory context type for the deductive libraries.  
  An alias to 'TypeQuantType'.
-}
type DeductiveType = TypeQuantType
type DeductiveCtxt a = TypeQuantCtxt a

{-| 
  The theory context for the deductive libraries.  
  An alias to 'ctxtTypeQuant'.
-}
{-# NOINLINE ctxtDeductive #-}
ctxtDeductive :: TheoryPath DeductiveType
ctxtDeductive = ctxtTypeQuant

-- | The quasi-quoter for the deductive libraries.  An alias to 'typeQuant'.
deductive :: QuasiQuoter
deductive = typeQuant
