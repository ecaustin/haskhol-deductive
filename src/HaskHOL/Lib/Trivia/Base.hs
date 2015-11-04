module HaskHOL.Lib.Trivia.Base where

import HaskHOL.Core

import HaskHOL.Lib.Equal
import HaskHOL.Lib.Bool
import HaskHOL.Lib.Tactics
import HaskHOL.Lib.Simp
import HaskHOL.Lib.Classic

thmEXISTS_ONE_REP :: ClassicCtxt thry => HOL cls thry HOLThm
thmEXISTS_ONE_REP = cacheProof "thmEXISTS_ONE_REP" ctxtClassic .
    prove [txt| ?b:bool . b |] $
      tacEXISTS [txt| T |] `_THEN`
      tacBETA `_THEN`
      tacACCEPT thmTRUTH

-- Stage 2
tyDef1 :: HOL cls thry HOLThm
tyDef1 = unsafeCacheProof "tyDef1" $ getTypeDefinition "1"

thm_one :: BoolCtxt thry => HOL cls thry HOLThm
thm_one = unsafeCacheProof "thm_one" $
    do th <- ruleCONJUNCT1 tyDef1
       prove [txt| !v:1. v = one |] $
         tacMP (ruleGEN_ALL . ruleSPEC [txt| one_REP a |] $ 
                ruleCONJUNCT2 tyDef1) `_THEN`
         tacREWRITE [th] `_THEN`
         tacDISCH `_THEN`
         tacONCE_REWRITE [ruleGSYM th] `_THEN`
         tacASM_REWRITE_NIL

induct_one :: BoolCtxt thry => HOL cls thry HOLThm
induct_one = unsafeCacheProof "induct_one" .
    prove [txt| !P. P one ==> !x. P x |] $
      tacONCE_REWRITE [thm_one] `_THEN` tacREWRITE_NIL

recursion_one :: BoolCtxt thry => HOL cls thry HOLThm
recursion_one = unsafeCacheProof "recursion_one" .
    prove [txt| !e:A. ?fn. fn one = e |] $
      tacGEN `_THEN`
      tacEXISTS [txt| \x:1. e:A |]  `_THEN`
      tacBETA `_THEN`
      tacREFL
 
