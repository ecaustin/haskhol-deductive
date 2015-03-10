{-|
  Module:    HaskHOL.Lib.Theorems
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Theorems
    ( TheoremsCtxt
    , ctxtTheorems
    , theorems
    , thmEQ_REFL_T
    , thmEQ_SYM
    , thmEQ_SYM_EQ
    , thmEQ_TRANS
    , thmREFL_CLAUSE
    , convAC
    , thmBETA
    , thmCONJ_ASSOC
    , thmCONJ_SYM
    , thmCONJ_ACI
    , thmDISJ_ASSOC
    , thmDISJ_SYM
    , thmDISJ_ACI
    , thmIMP_CONJ
    , thmIMP_IMP
    , thmFORALL_SIMP
    , thmEXISTS_SIMP
    , thmEQ_IMP
    , thmEQ_CLAUSES
    , thmNOT_CLAUSES_WEAK
    , thmAND_CLAUSES
    , thmOR_CLAUSES
    , thmIMP_EQ_CLAUSE
    , thmSWAP_FORALL
    , thmSWAP_EXISTS
    , thmFORALL_AND
    , thmAND_FORALL
    , thmLEFT_AND_FORALL
    , thmRIGHT_AND_FORALL
    , thmEXISTS_OR
    , thmOR_EXISTS
    , thmLEFT_OR_EXISTS
    , thmRIGHT_OR_EXISTS
    , thmLEFT_EXISTS_AND
    , thmRIGHT_EXISTS_AND
    , thmLEFT_AND_EXISTS
    , thmRIGHT_AND_EXISTS
    , thmLEFT_IMP_EXISTS
    , thmLEFT_FORALL_IMP
    , thmEXISTS_REFL
    , thmEXISTS_UNIQUE
    , thmEXISTS_UNIQUE_ALT
    , thmEXISTS_UNIQUE_REFL
    , thmUNWIND1
    , thmUNWIND2
    , thmMONO_AND
    , thmMONO_OR
    , thmMONO_IMP
    , thmMONO_NOT
    , thmMONO_FORALL
    , thmMONO_EXISTS
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Bool
import HaskHOL.Lib.Equal
import HaskHOL.Lib.Itab
import HaskHOL.Lib.Simp
import HaskHOL.Lib.Tactics

import HaskHOL.Lib.Theorems.Base
import HaskHOL.Lib.Theorems.Context

thmEQ_IMP :: TheoremsCtxt thry => HOL cls thry HOLThm
thmEQ_IMP = cacheProof "thmEQ_IMP" ctxtTheorems $
    ruleITAUT "(a <=> b) ==> a ==> b"

-- basic equality proofs
thmEQ_REFL_T :: TheoremsCtxt thry => HOL cls thry HOLThm
thmEQ_REFL_T = cacheProof "thmEQ_REFL_T" ctxtTheorems $
    do th <- ruleEQT_INTRO =<< ruleSPEC_ALL thmEQ_REFL
       prove "!x:A. (x = x) <=> T" $
         tacGEN `_THEN` 
         tacMATCH_ACCEPT th

thmEQ_SYM :: TheoremsCtxt thry => HOL cls thry HOLThm
thmEQ_SYM = cacheProof "thmEQ_SYM" ctxtTheorems $
    prove "!(x:A) y. (x = y) ==> (y = x)" $
      _REPEAT tacGEN `_THEN`
      _DISCH_THEN (tacACCEPT <#< ruleSYM)

thmEQ_SYM_EQ :: TheoremsCtxt thry => HOL cls thry HOLThm
thmEQ_SYM_EQ = cacheProof "thmEQ_SYM_EQ" ctxtTheorems $
    prove "!(x:A) y. (x = y) <=> (y = x)" $
      _REPEAT tacGEN `_THEN`
      tacEQ `_THEN`
      tacMATCH_ACCEPT thmEQ_SYM

thmEQ_TRANS :: TheoremsCtxt thry => HOL cls thry HOLThm
thmEQ_TRANS = cacheProof "thmEQ_TRANS" ctxtTheorems $
    prove [str| !(x:A) y z. (x = y) /\ (y = z) ==> (x = z) |] $
      _REPEAT tacSTRIP `_THEN` tacPURE_ASM_REWRITE_NIL `_THEN` tacREFL

-- common case of ordered rewriting
convAC :: (TheoremsCtxt thry, HOLThmRep thm cls thry) => thm 
       -> Conversion cls thry
convAC acsuite = Conv $ \ tm ->
    do th1 <- toHThm acsuite
       th2 <- thmEQ_REFL_T
       ruleEQT_ELIM =<< runConv (convPURE_REWRITE [th1, th2]) tm

-- intuitionistic tauts
thmCONJ_ASSOC :: TheoremsCtxt thry => HOL cls thry HOLThm
thmCONJ_ASSOC = cacheProof "thmCONJ_ASSOC" ctxtTheorems $
    prove [str| !t1 t2 t3. t1 /\ t2 /\ t3 <=> (t1 /\ t2) /\ t3 |] tacITAUT

thmCONJ_SYM :: TheoremsCtxt thry => HOL cls thry HOLThm
thmCONJ_SYM = cacheProof "thmCONJ_SYM" ctxtTheorems $
    prove [str| !t1 t2. t1 /\ t2 <=> t2 /\ t1 |] tacITAUT

thmCONJ_ACI :: TheoremsCtxt thry => HOL cls thry HOLThm
thmCONJ_ACI = cacheProof "thmCONJ_ACI" ctxtTheorems $
    prove [str| (p /\ q <=> q /\ p) /\
                ((p /\ q) /\ r <=> p /\ (q /\ r)) /\
                (p /\ (q /\ r) <=> q /\ (p /\ r)) /\
                (p /\ p <=> p) /\
                (p /\ (p /\ q) <=> p /\ q) |] tacITAUT

thmDISJ_ASSOC :: TheoremsCtxt thry => HOL cls thry HOLThm
thmDISJ_ASSOC = cacheProof "thmDISJ_ASSOC" ctxtTheorems $
    prove [str| !t1 t2 t3. t1 \/ t2 \/ t3 <=> (t1 \/ t2) \/ t3 |] tacITAUT

thmDISJ_SYM :: TheoremsCtxt thry => HOL cls thry HOLThm
thmDISJ_SYM = cacheProof "thmDISJ_SYM" ctxtTheorems $
    prove [str| !t1 t2. t1 \/ t2 <=> t2 \/ t1 |] tacITAUT

thmDISJ_ACI :: TheoremsCtxt thry => HOL cls thry HOLThm
thmDISJ_ACI = cacheProof "thmDISJ_ACI" ctxtTheorems $
    prove [str| (p \/ q <=> q \/ p) /\
                ((p \/ q) \/ r <=> p \/ (q \/ r)) /\
                (p \/ (q \/ r) <=> q \/ (p \/ r)) /\
                (p \/ p <=> p) /\
                (p \/ (p \/ q) <=> p \/ q) |] tacITAUT

thmIMP_CONJ :: TheoremsCtxt thry => HOL cls thry HOLThm
thmIMP_CONJ = cacheProof "thmIMP_CONJ" ctxtTheorems $
    prove [str| p /\ q ==> r <=> p ==> q ==> r |] tacITAUT

thmIMP_IMP :: TheoremsCtxt thry => HOL cls thry HOLThm
thmIMP_IMP = cacheProof "thmIMP_IMP" ctxtTheorems $
    ruleGSYM thmIMP_CONJ

-- permuting quantifiers
thmSWAP_FORALL :: TheoremsCtxt thry => HOL cls thry HOLThm
thmSWAP_FORALL = cacheProof "thmSWAP_FORALL" ctxtTheorems $
    prove "!P:A->B->bool. (!x y. P x y) <=> (!y x. P x y)" tacITAUT

thmSWAP_EXISTS :: TheoremsCtxt thry => HOL cls thry HOLThm
thmSWAP_EXISTS = cacheProof "thmSWAP_EXISTS" ctxtTheorems $
    prove "!P:A->B->bool. (?x y. P x y) <=> (?y x. P x y)" tacITAUT

-- universal quantifier and conjunction
thmFORALL_AND :: TheoremsCtxt thry => HOL cls thry HOLThm
thmFORALL_AND = cacheProof "thmFORALL_AND" ctxtTheorems $
    prove [str| !P Q. (!x:A. P x /\ Q x) <=> (!x. P x) /\ (!x. Q x) |] 
      tacITAUT

thmAND_FORALL :: TheoremsCtxt thry => HOL cls thry HOLThm
thmAND_FORALL = cacheProof "thmAND_FORALL" ctxtTheorems $
    prove [str| !P Q. (!x. P x) /\ (!x. Q x) <=> 
                      (!x:A. P x /\ Q x) |] tacITAUT

thmLEFT_AND_FORALL :: TheoremsCtxt thry => HOL cls thry HOLThm
thmLEFT_AND_FORALL = cacheProof "thmLEFT_AND_FORALL" ctxtTheorems $
    prove [str| !P Q. (!x:A. P x) /\ Q <=> (!x:A. P x /\ Q) |] tacITAUT

thmRIGHT_AND_FORALL :: TheoremsCtxt thry => HOL cls thry HOLThm
thmRIGHT_AND_FORALL = cacheProof "thmRIGHT_AND_FORALL" ctxtTheorems $
    prove [str| !P Q. P /\ (!x:A. Q x) <=> (!x. P /\ Q x) |] tacITAUT


-- existential quantifier and disjunction
thmEXISTS_OR :: TheoremsCtxt thry => HOL cls thry HOLThm
thmEXISTS_OR = cacheProof "thmEXISTS_OR" ctxtTheorems $
    prove [str| !P Q. (?x:A. P x \/ Q x) <=> 
                      (?x. P x) \/ (?x. Q x) |] tacITAUT

thmOR_EXISTS :: TheoremsCtxt thry => HOL cls thry HOLThm
thmOR_EXISTS = cacheProof "thmOR_EXISTS" ctxtTheorems $
    prove [str| !P Q. (?x. P x) \/ (?x. Q x) <=> 
                      (?x:A. P x \/ Q x) |] tacITAUT

thmLEFT_OR_EXISTS :: TheoremsCtxt thry => HOL cls thry HOLThm
thmLEFT_OR_EXISTS = cacheProof "thmLEFT_OR_EXISTS" ctxtTheorems $
    prove [str| !P Q. (?x. P x) \/ Q <=> (?x:A. P x \/ Q) |] tacITAUT

thmRIGHT_OR_EXISTS :: TheoremsCtxt thry => HOL cls thry HOLThm
thmRIGHT_OR_EXISTS = cacheProof "thmRIGHT_OR_EXISTS" ctxtTheorems $
    prove [str| !P Q. P \/ (?x. Q x) <=> (?x:A. P \/ Q x) |] tacITAUT

-- existential quantification and conjunction
thmLEFT_EXISTS_AND :: TheoremsCtxt thry => HOL cls thry HOLThm
thmLEFT_EXISTS_AND = cacheProof "thmLEFT_EXISTS_AND" ctxtTheorems $
    prove [str| !P Q. (?x:A. P x /\ Q) <=> (?x:A. P x) /\ Q |] tacITAUT

thmRIGHT_EXISTS_AND :: TheoremsCtxt thry => HOL cls thry HOLThm
thmRIGHT_EXISTS_AND = cacheProof "thmRIGHT_EXISTS_AND" ctxtTheorems $
    prove [str| !P Q. (?x:A. P /\ Q x) <=> P /\ (?x:A. Q x) |] tacITAUT

thmLEFT_AND_EXISTS :: TheoremsCtxt thry => HOL cls thry HOLThm
thmLEFT_AND_EXISTS = cacheProof "thmLEFT_AND_EXISTS" ctxtTheorems $
    prove [str| !P Q. (?x:A. P x) /\ Q <=> (?x:A. P x /\ Q) |] tacITAUT

thmRIGHT_AND_EXISTS :: TheoremsCtxt thry => HOL cls thry HOLThm
thmRIGHT_AND_EXISTS = cacheProof "thmRIGHT_AND_EXISTS" ctxtTheorems $
    prove [str| !P Q. P /\ (?x:A. Q x) <=> (?x:A. P /\ Q x) |] tacITAUT

thmLEFT_IMP_EXISTS :: TheoremsCtxt thry => HOL cls thry HOLThm
thmLEFT_IMP_EXISTS = cacheProof "thmLEFT_IMP_EXISTS" ctxtTheorems $
    prove "!P Q. ((?x:A. P x) ==> Q) <=> (!x. P x ==> Q)" tacITAUT 

thmLEFT_FORALL_IMP :: TheoremsCtxt thry => HOL cls thry HOLThm
thmLEFT_FORALL_IMP = cacheProof "thmLEFT_FORALL_IMP" ctxtTheorems $
    prove "!P Q. (!x. P x ==> Q) <=> ((?x:A. P x) ==> Q)" tacITAUT 

thmEXISTS_REFL :: TheoremsCtxt thry => HOL cls thry HOLThm
thmEXISTS_REFL = cacheProof "thmEXISTS_REFL" ctxtTheorems $
    do a <- toHTm "a:A"
       prove "!a:A. ?x. x = a" $
         tacGEN `_THEN`
         tacEXISTS a `_THEN`
         tacREFL

thmEXISTS_UNIQUE :: TheoremsCtxt thry => HOL cls thry HOLThm
thmEXISTS_UNIQUE = cacheProof "thmEXISTS_UNIQUE" ctxtTheorems $
    prove [str| !P. (?!x:A. P x) <=> 
                    (?x. P x) /\ (!x x'. P x /\ P x' ==> (x = x')) |] $
      tacGEN `_THEN` tacREWRITE [defEXISTS_UNIQUE]

thmEXISTS_UNIQUE_REFL :: TheoremsCtxt thry => HOL cls thry HOLThm
thmEXISTS_UNIQUE_REFL = cacheProof "thmEXISTS_UNIQUE_REFL" ctxtTheorems $
    prove "!a:A. ?!x. x = a" $
      tacGEN `_THEN` tacREWRITE [thmEXISTS_UNIQUE] `_THEN`
      _REPEAT (tacEQ `_ORELSE` tacSTRIP) `_THENL`
      [ tacEXISTS "a:A", tacASM_REWRITE_NIL ] `_THEN`
      tacREFL

thmEXISTS_UNIQUE_ALT :: TheoremsCtxt thry => HOL cls thry HOLThm
thmEXISTS_UNIQUE_ALT = cacheProof "thmEXISTS_UNIQUE_ALT" ctxtTheorems $
  do pth <- ruleGSYM thmEXISTS_REFL
     prove "!P:A->bool. (?!x. P x) <=> (?x. !y. P y <=> (x = y))" $
       tacGEN `_THEN` tacREWRITE [thmEXISTS_UNIQUE] `_THEN` tacEQ `_THENL`
       [ _DISCH_THEN (_CONJUNCTS_THEN2 (tacX_CHOOSE "x:A") tacASSUME) `_THEN`
         tacEXISTS "x:A" `_THEN` tacGEN `_THEN` tacEQ `_THENL`
         [ tacDISCH `_THEN` _FIRST_ASSUM tacMATCH_MP `_THEN` 
           tacASM_REWRITE_NIL
         , _DISCH_THEN (\ th -> tacSUBST1 (fromRight $ ruleSYM th)) `_THEN` 
           _FIRST_ASSUM tacMATCH_ACCEPT
         ]
       , _DISCH_THEN (tacX_CHOOSE "x:A") `_THEN`
         tacASM_REWRITE [pth] `_THEN` 
         _REPEAT tacGEN `_THEN`
         _DISCH_THEN (_CONJUNCTS_THEN 
                      (\ th -> tacSUBST1 (fromRight $ ruleSYM th))) `_THEN` 
         tacREFL
       ]

thmUNWIND1 :: TheoremsCtxt thry => HOL cls thry HOLThm
thmUNWIND1 = cacheProof "thmUNWIND1" ctxtTheorems $
    prove [str| !P (a:A). (?x. a = x /\ P x) <=> P a |] $
      _REPEAT tacGEN `_THEN` tacEQ `_THENL`
      [ _DISCH_THEN (_CHOOSE_THEN (_CONJUNCTS_THEN2 tacSUBST1 tacACCEPT))
      , tacDISCH `_THEN` tacEXISTS "a:A" `_THEN`
        tacCONJ `_THEN` _TRY (_FIRST_ASSUM tacMATCH_ACCEPT) `_THEN`
        tacREFL
      ]

thmUNWIND2 :: TheoremsCtxt thry => HOL cls thry HOLThm
thmUNWIND2 = cacheProof "thmUNWIND2" ctxtTheorems $
    prove [str| !P (a:A). (?x. x = a /\ P x) <=> P a |] $
      _REPEAT tacGEN `_THEN` tacCONV (convLAND (convONCE_DEPTH convSYM)) `_THEN`
      tacMATCH_ACCEPT thmUNWIND1

-- monotonicity theorems for inductive definitions
thmMONO_AND :: TheoremsCtxt thry => HOL cls thry HOLThm
thmMONO_AND = cacheProof "thmMONO_AND" ctxtTheorems $
    ruleITAUT [str| (A ==> B) /\ (C ==> D) ==> (A /\ C ==> B /\ D) |]

thmMONO_OR :: TheoremsCtxt thry => HOL cls thry HOLThm
thmMONO_OR = cacheProof "thmMONO_OR" ctxtTheorems $
    ruleITAUT [str| (A ==> B) /\ (C ==> D) ==> (A \/ C ==> B \/ D) |]

thmMONO_IMP :: TheoremsCtxt thry => HOL cls thry HOLThm
thmMONO_IMP = cacheProof "thmMONO_IMP" ctxtTheorems $
    ruleITAUT [str| (B ==> A) /\ (C ==> D) ==> 
                    ((A ==> C) ==> (B ==> D)) |]

thmMONO_NOT :: TheoremsCtxt thry => HOL cls thry HOLThm
thmMONO_NOT = cacheProof "thmMONO_NOT" ctxtTheorems $
    ruleITAUT "(B ==> A) ==> (~A ==> ~B)"

thmMONO_FORALL :: TheoremsCtxt thry => HOL cls thry HOLThm
thmMONO_FORALL = cacheProof "thmMONO_FORALL" ctxtTheorems $
    prove "(!x:A. P x ==> Q x) ==> ((!x. P x) ==> (!x. Q x))" $
      _REPEAT tacSTRIP `_THEN` 
      _FIRST_ASSUM tacMATCH_MP `_THEN`
      tacASM_REWRITE_NIL

thmMONO_EXISTS :: TheoremsCtxt thry => HOL cls thry HOLThm
thmMONO_EXISTS = cacheProof "thmMONO_EXISTS" ctxtTheorems $
    prove "(!x:A. P x ==> Q x) ==> ((?x. P x) ==> (?x. Q x))" $
      tacDISCH `_THEN` 
      _DISCH_THEN (tacX_CHOOSE "x:A") `_THEN`
      tacEXISTS "x:A" `_THEN` 
      _FIRST_ASSUM tacMATCH_MP `_THEN`
      tacASM_REWRITE_NIL
