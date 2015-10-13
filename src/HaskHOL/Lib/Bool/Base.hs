{-|
  Module:    HaskHOL.Lib.Bool.Base
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown

  This module defines the theory context extensions for the Boolean logic
  library, including parser extensions and term definitions.
-}
module HaskHOL.Lib.Bool.Base where

import HaskHOL.Core
 
defT' :: HOL Theory thry HOLThm
defT' = newBasicDefinition "T"
  

defAND' :: HOL Theory thry HOLThm
defAND' = newBasicDefinition "/\\"
  

defIMP' :: HOL Theory thry HOLThm
defIMP' = newBasicDefinition "==>"
  

defFORALL' :: HOL Theory thry HOLThm
defFORALL' = newBasicDefinition "!"
  

defEXISTS' :: HOL Theory thry HOLThm
defEXISTS' = newBasicDefinition "?"
  

defOR' :: HOL Theory thry HOLThm
defOR' = newBasicDefinition "\\/"
  

defFALSE' :: HOL Theory thry HOLThm
defFALSE' = newBasicDefinition "F" 
  

def_FALSITY_' :: HOL Theory thry HOLThm
def_FALSITY_' = newBasicDefinition "_FALSITY_"
  

defNOT' :: HOL Theory thry HOLThm
defNOT' = newBasicDefinition "~"
  

defEXISTS_UNIQUE' :: HOL Theory thry HOLThm
defEXISTS_UNIQUE' = newBasicDefinition "?!"
  

defTY_FORALL' :: HOL Theory thry HOLThm
defTY_FORALL' = newBasicDefinition "!!"
  

defTY_EXISTS' :: HOL Theory thry HOLThm
defTY_EXISTS' = newBasicDefinition "??"
  
