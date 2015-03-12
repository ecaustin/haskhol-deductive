module HaskHOL.Lib.Theorems.Base where

import HaskHOL.Core

import HaskHOL.Lib.Bool
import HaskHOL.Lib.Tactics
import HaskHOL.Lib.Itab
import HaskHOL.Lib.Simp


-- basic rewrites
thmEQ_CLAUSES :: BoolCtxt thry => HOL cls thry HOLThm
thmEQ_CLAUSES = cacheProof "thmEQ_CLAUSES" ctxtBool $
    prove [str| !t. ((T <=> t) <=> t) /\
                    ((t <=> T) <=> t) /\
                    ((F <=> t) <=> ~t) /\ 
                    ((t <=> F) <=> ~t) |] tacITAUT

thmNOT_CLAUSES_WEAK :: BoolCtxt thry => HOL cls thry HOLThm
thmNOT_CLAUSES_WEAK = cacheProof "thmNOT_CLAUSES_WEAK" ctxtBool $
    prove [str| (~T <=> F) /\ (~F <=> T) |] tacITAUT

thmAND_CLAUSES :: BoolCtxt thry => HOL cls thry HOLThm
thmAND_CLAUSES = cacheProof "thmAND_CLAUSES" ctxtBool $
    prove [str| !t. (T /\ t <=> t) /\ 
                    (t /\ T <=> t) /\ 
                    (F /\ t <=> F) /\
                    (t /\ F <=> F) /\ 
                    (t /\ t <=> t) |] tacITAUT

thmOR_CLAUSES :: BoolCtxt thry => HOL cls thry HOLThm
thmOR_CLAUSES = cacheProof "thmOR_CLAUSES" ctxtBool $
    prove [str| !t. (T \/ t <=> T) /\ 
                    (t \/ T <=> T) /\ 
                    (F \/ t <=> t) /\
                    (t \/ F <=> t) /\ 
                    (t \/ t <=> t) |] tacITAUT

thmREFL_CLAUSE :: BoolCtxt thry => HOL cls thry HOLThm
thmREFL_CLAUSE = cacheProof "thmREFL_CLAUSE" ctxtBool $
    do th <- ruleEQT_INTRO =<< ruleSPEC "x:A" thmEQ_REFL
       prove "!x:A. (x = x) = T" $
         tacGEN `_THEN`
         tacACCEPT th

thmIMP_EQ_CLAUSE :: BoolCtxt thry => HOL cls thry HOLThm
thmIMP_EQ_CLAUSE = cacheProof "thmIMP_EQ_CLAUSE" ctxtBool $
    do th1 <- ruleEQT_INTRO =<< ruleSPEC_ALL thmEQ_REFL
       th2 <- thmIMP_CLAUSES
       prove "((x = x) ==> p) <=> p" $ tacREWRITE [th1, th2]

-- degenerate cases of quantifiers
thmFORALL_SIMP :: BoolCtxt thry => HOL cls thry HOLThm
thmFORALL_SIMP = cacheProof "thmFORALL_SIMP" ctxtBool $
    prove "!t. (!x:A. t) = t" tacITAUT

thmEXISTS_SIMP :: BoolCtxt thry => HOL cls thry HOLThm
thmEXISTS_SIMP = cacheProof "thmEXISTS_SIMP" ctxtBool $
    prove "!t. (?x:A. t) = t" tacITAUT


-- beta reduction stuff
thmBETA :: BoolCtxt thry => HOL cls thry HOLThm
thmBETA = cacheProof "thmBETA" ctxtBool $
    prove [str| !(f:A->B) y. (\x. (f:A->B) x) y = f y |] $
      _REPEAT tacGEN `_THEN` tacBETA `_THEN` tacREFL

-- basic congruence
thmBASIC_CONG :: BoolCtxt thry => HOL cls thry HOLThm
thmBASIC_CONG = cacheProof "thmBASIC_CONG" ctxtBool $
    prove [str| (p <=> p') ==> 
                (p' ==> (q <=> q')) ==> 
                (p ==> q <=> p' ==> q') |]
      tacITAUT
