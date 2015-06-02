module HaskHOL.Lib.Trivia.Base where

import HaskHOL.Core

import HaskHOL.Lib.Equal
import HaskHOL.Lib.DRule
import HaskHOL.Lib.Bool
import HaskHOL.Lib.Tactics
import HaskHOL.Lib.Simp
import HaskHOL.Lib.Classic

thmEXISTS_ONE_REP :: ClassicCtxt thry => HOL cls thry HOLThm
thmEXISTS_ONE_REP = cacheProof "thmEXISTS_ONE_REP" ctxtClassic $
    prove "?b:bool . b" $
      tacEXISTS "T" `_THEN`
      tacBETA `_THEN`
      tacACCEPT thmTRUTH

defO' :: BoolCtxt thry => HOL Theory thry HOLThm
defO' = newDefinition "o"
    [str| (o) (f:B->C) g = \x:A. f(g(x)) |]

defI' :: BoolCtxt thry => HOL Theory thry HOLThm
defI' = newDefinition "I"
    [str| I = \x:A. x |]

tyDefOne' :: ClassicCtxt thry => HOL Theory thry HOLThm
tyDefOne' = newTypeDefinition "1" "one_ABS" "one_REP" thmEXISTS_ONE_REP

defONE' :: BoolCtxt thry => HOL Theory thry HOLThm
defONE' = newDefinition "one" "one = @x:1. T" 

-- Stage 2
thm_one' :: BoolCtxt thry => HOL cls thry HOLThm
thm_one' =
    do th <- ruleCONJUNCT1 $ getTypeDefinition "1"
       prove "!v:1. v = one" $
         tacMP (ruleGEN_ALL =<< ruleSPEC "one_REP a" =<< 
                ruleCONJUNCT2 (getTypeDefinition "1")) `_THEN`
         tacREWRITE [th] `_THEN`
         tacDISCH `_THEN`
         tacONCE_REWRITE [ruleGSYM th] `_THEN`
         tacASM_REWRITE_NIL

induct_one' :: BoolCtxt thry => HOL cls thry HOLThm
induct_one' =
    prove "!P. P one ==> !x. P x" $
      tacONCE_REWRITE [thm_one'] `_THEN` tacREWRITE_NIL

recursion_one' :: BoolCtxt thry => HOL cls thry HOLThm
recursion_one' =
    prove "!e:A. ?fn. fn one = e" $
      tacGEN `_THEN`
      tacEXISTS [str| \x:1. e:A |]  `_THEN`
      tacBETA `_THEN`
      tacREFL
 
