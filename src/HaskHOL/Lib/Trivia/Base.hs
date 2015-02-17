module HaskHOL.Lib.Trivia.Base where

import HaskHOL.Core

import HaskHOL.Lib.Equal
import HaskHOL.Lib.DRule
import HaskHOL.Lib.Bool
import HaskHOL.Lib.Tactics
import HaskHOL.Lib.Simp
import HaskHOL.Lib.Classic

import HaskHOL.Lib.Trivia.A

-- guarded definitions from TriviaA
defO :: TriviaACtxt thry => HOL cls thry HOLThm
defO = cacheProof "defO" ctxtTriviaA $ getDefinition "o"

defI :: TriviaACtxt thry => HOL cls thry HOLThm
defI = cacheProof "defI" ctxtTriviaA $ getDefinition "I"

ty1 :: TriviaACtxt thry => HOL cls thry HOLThm
ty1 = cacheProof "ty1" ctxtTriviaA $ getTypeDefinition "1"

def_one :: TriviaACtxt thry => HOL cls thry HOLThm
def_one = cacheProof "def_one" ctxtTriviaA $ getDefinition "one"

thm_one :: (BasicConvs thry, TriviaACtxt thry) => HOL cls thry HOLThm
thm_one = cacheProof "thm_one" ctxtTriviaA $
    do th <- ruleCONJUNCT1 ty1
       prove "!v:1. v = one" $
         tacMP (ruleGEN_ALL =<< ruleSPEC "one_REP a" =<< 
                ruleCONJUNCT2 ty1) `_THEN`
         tacREWRITE [th] `_THEN`
         tacDISCH `_THEN`
         tacONCE_REWRITE [ruleGSYM th] `_THEN`
         tacASM_REWRITE_NIL

induct_one :: (BasicConvs thry, TriviaACtxt thry) => HOL cls thry HOLThm
induct_one = cacheProof "induct_one" ctxtTriviaA $
    prove "!P. P one ==> !x. P x" $
      tacONCE_REWRITE [thm_one] `_THEN` tacREWRITE_NIL

recursion_one :: TriviaACtxt thry => HOL cls thry HOLThm
recursion_one = cacheProof "recursion_one" ctxtTriviaA $
    prove "!e:A. ?fn. fn one = e" $
      tacGEN `_THEN`
      tacEXISTS [str| \x:1. e:A |]  `_THEN`
      tacBETA `_THEN`
      tacREFL
 
