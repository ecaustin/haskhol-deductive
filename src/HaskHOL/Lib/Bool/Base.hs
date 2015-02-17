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
  [str| T = ((\ p:bool . p) = (\ p:bool . p)) |]

defAND' :: HOL Theory thry HOLThm
defAND' = newBasicDefinition "/\\"
  [str| (/\) = \ p q . (\ f:bool->bool->bool . f p q) = (\ f . f T T) |]

defIMP' :: HOL Theory thry HOLThm
defIMP' = newBasicDefinition "==>"
  [str| (==>) = \ p q . p /\ q <=> p |]

defFORALL' :: HOL Theory thry HOLThm
defFORALL' = newBasicDefinition "!"
  [str| (!) = \ P:A->bool . P = \ x . T |]

defEXISTS' :: HOL Theory thry HOLThm
defEXISTS' = newBasicDefinition "?"
  [str| (?) = \ P:A->bool . ! q . (! x . P x ==> q) ==> q |]

defOR' :: HOL Theory thry HOLThm
defOR' = newBasicDefinition "\\/"
  [str| (\/) = \ p q . ! r . (p ==> r) ==> (q ==> r)  ==> r |]

defFALSE' :: HOL Theory thry HOLThm
defFALSE' = newBasicDefinition "F" 
  [str| F = ! p:bool . p |]

def_FALSITY_' :: HOL Theory thry HOLThm
def_FALSITY_' = newBasicDefinition "_FALSITY_"
  [str| _FALSITY_ = F |]

defNOT' :: HOL Theory thry HOLThm
defNOT' = newBasicDefinition "~"
  [str| (~) = \ p . p ==> F |]

defEXISTS_UNIQUE' :: HOL Theory thry HOLThm
defEXISTS_UNIQUE' = newBasicDefinition "?!"
  [str| (?!) = \ P:A->bool. ((?) P) /\ (!x y. P x /\ P y ==> x = y) |]

defTY_FORALL' :: HOL Theory thry HOLThm
defTY_FORALL' = newBasicDefinition "!!"
  [str| (!!) = \ P : (% 'A. bool). P = (\\ 'A. T) |]

defTY_EXISTS' :: HOL Theory thry HOLThm
defTY_EXISTS' = newBasicDefinition "??"
  [str| (??) = \ P : (% 'A. bool). ~(P = (\\ 'A . F)) |]
