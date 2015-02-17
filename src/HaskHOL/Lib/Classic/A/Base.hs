module HaskHOL.Lib.Classic.A.Base where

import HaskHOL.Core

import HaskHOL.Lib.Bool
import HaskHOL.Lib.DRule

-- eta conv stuff
axETA' :: HOL Theory thry HOLThm
axETA' = newAxiom "axETA" [str| !t:A->B. (\x. t x) = t |]


axSELECT' :: HOL Theory thry HOLThm
axSELECT' = newAxiom "axSELECT" "!P (x:A). P x ==> P((@) P)"

-- conditionals
defCOND' :: BoolCtxt thry => HOL Theory thry HOLThm
defCOND' = newDefinition "COND"
    [str| COND = \t t1 t2. @x:A. ((t <=> T) ==> (x = t1)) /\ 
                                 ((t <=> F) ==> (x = t2)) |]
