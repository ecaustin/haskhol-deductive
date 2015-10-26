{-|
  Module:    HaskHOL.Lib.Bool
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown

  This module implements the boolean logic library for HaskHOL.  Computations
  and protected values that are sealed against the boolean theory context are
  guarded with the 'BoolCtxt' type constraint.
-}
module HaskHOL.Lib.Bool
    ( BoolCtxt
    , ctxtBool
    , bool
      -- * General, Derived Rules 
    , pattern T
    , pattern F
    , rulePINST
    , rulePROVE_HYP
      -- * Derived Rules for Truth
    , defT
    , thmTRUTH
    , ruleEQT_ELIM
    , ruleEQT_INTRO
      -- * Derived Rules for Conjunction
    , defAND
    , ruleCONJ
    , ruleCONJUNCT1
    , ruleCONJUNCT2
    , ruleCONJ_PAIR
    , ruleCONJUNCTS
      -- * Derived Rules for Implication
    , defIMP
    , ruleMP         
    , ruleDISCH           
    , ruleDISCH_ALL      
    , ruleUNDISCH       
    , ruleUNDISCH_ALL
    , ruleIMP_ANTISYM   
    , ruleADD_ASSUM
    , ruleEQ_IMP
    , ruleIMP_TRANS
      -- * Derived Syntax and Rules for Universal Quantification
    , defFORALL
    , ruleSPEC 
    , ruleSPECL
    , ruleSPEC_VAR
    , ruleSPEC_ALL
    , ruleISPEC
    , ruleISPECL
    , ruleGEN 
    , ruleGENL
    , ruleGEN_ALL
      -- * Derived Syntax and Rules for Existential Quantification
    , defEXISTS
    , ruleEXISTS
    , ruleSIMPLE_EXISTS
    , ruleCHOOSE
    , ruleSIMPLE_CHOOSE
      -- * Derived Rules for Disjunction
    , defOR
    , ruleDISJ1
    , ruleDISJ2
    , ruleDISJ_CASES
    , ruleSIMPLE_DISJ_CASES
      -- * Derived Rules for Negation and Falsity
    , defFALSE
    , def_FALSITY_
    , defNOT
    , ruleNOT_ELIM
    , ruleNOT_INTRO
    , ruleEQF_INTRO
    , ruleEQF_ELIM
    , ruleCONTR
      -- * Derived Rules for Unique Existence
    , defEXISTS_UNIQUE
    , ruleEXISTENCE 
      -- * Additional Definitions for Type Quantification
    , defTY_FORALL
    , defTY_EXISTS
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Equal

import HaskHOL.Lib.Bool.Context
import HaskHOL.Lib.Bool.PQ

pattern T <- Const "T" _

pattern F <- Const "F" _


tmP, tmQ, tmR, tmT, tmX, tmPred :: BoolCtxt thry => HOL cls thry HOLTerm
tmP = serve [bool| p:bool |]
tmQ = serve [bool| q:bool |]
tmR = serve [bool| r:bool |]
tmT = serve [bool| t:bool |]
tmX = serve [bool| x:A |]
tmPred = serve [bool| P:A->bool |]


--allows easy instantiation for pro forma theorems

{-|@

 [(ty1, tv1), ..., (tyn, tvn)]   [(t1, x1), ..., (tn, xn)]   A |- t             
--------------------------------------------------------------------
   A[ty1, ..., tyn\/tv1, ..., tvn][t1, ..., tn\/x1, ..., xn]
    |- t[ty1, ..., tyn\/tv1, ..., tvn][t1, ..., tn\/x1, ..., xn]
@

  Fails if the provided term substitution environment is ill-formed.
-}
rulePINST :: (Inst a b, HOLTermRep tm1 cls thry, HOLTermRep tm2 cls thry, 
              HOLThmRep thm cls thry) 
          => [(a, b)] -> [(tm1, tm2)] -> thm -> HOL cls thry HOLThm
rulePINST tyenv ptmenv thm =
    do tmenv <- mapM (toHTm `ffCombM` toHTm) ptmenv
       primINST (map (first (inst tyenv)) tmenv) .
         primINST_TYPE tyenv $ toHThm thm

--derived deductive rules

{-|@
  A1 |- t1   A2 |- t2  
------------------------
 (A1 U A2) - t1 |- t2
@

  Never fails.
-}
rulePROVE_HYP :: (HOLThmRep thm1 cls thry, HOLThmRep thm2 cls thry) 
              => thm1 -> thm2 -> HOL cls thry HOLThm
rulePROVE_HYP pthm1 pthm2 =
    do athm@(Thm _ a) <- toHThm pthm1
       bthm@(Thm bs _) <- toHThm pthm2
       if any (aConv a) bs
          then primEQ_MP (primDEDUCT_ANTISYM athm bthm) athm
          else return bthm

-- derived rules for truth
-- | @T = (\ p:bool . p) = (\ p:bool . p)@
defT :: BoolCtxt thry => HOL cls thry HOLThm
defT = cacheProof "defT" ctxtBool $ getBasicDefinition "T"

-- | @|- T@
thmTRUTH :: BoolCtxt thry => HOL cls thry HOLThm
thmTRUTH = cacheProof "thmTRUTH" ctxtBool .
    primEQ_MP (ruleSYM defT) $ primREFL [txt| \p:bool. p |]

{-|@
 A |- t \<=\> T  
----------------
     A |- t         
@

  Throws a 'HOLException' if the conclusion of the provided theorem is not of 
  the form @tm \<=\> T@.
-}
ruleEQT_ELIM :: (BoolCtxt thry, HOLThmRep thm cls thry) 
             => thm -> HOL cls thry HOLThm
ruleEQT_ELIM thm =
    (primEQ_MP (ruleSYM thm) thmTRUTH) <?> "ruleEQT_ELIM"


{-|@
    A |- t     
--------------
 A |- t \<=\> T
@

  Never fails.
-}  
ruleEQT_INTRO :: (BoolCtxt thry, HOLThmRep thm cls thry) 
              => thm -> HOL cls thry HOLThm
ruleEQT_INTRO pthm = 
    do thm@(Thm _ c) <- toHThm pthm
       primEQ_MP (primINST [(tmT, c)] ruleEQT_INTRO_pth) thm
  where ruleEQT_INTRO_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleEQT_INTRO_pth = cacheProof "ruleEQT_INTRO" ctxtBool $
            do th1 <- primASSUME tmT
               th2@(Thm _ tm) <- primDEDUCT_ANTISYM th1 thmTRUTH
               th3 <- ruleEQT_ELIM $ primASSUME tm
               primDEDUCT_ANTISYM th3 th2

-- derived rules for conjunction
-- | @(\/\\) = \\ p q . (\\ f:bool->bool->bool . f p q) = (\\ f . f T T)@
defAND :: BoolCtxt thry => HOL cls thry HOLThm
defAND = cacheProof "defAND" ctxtBool $ getBasicDefinition "/\\"

{-|@
 A1 |- t1      A2 |- t2
------------------------
  A1 U A2 |- t1 \/\\ t2  
@

  Never fails.
-}
ruleCONJ :: (BoolCtxt thry, HOLThmRep thm1 cls thry, HOLThmRep thm2 cls thry) 
         => thm1 -> thm2 -> HOL cls thry HOLThm
ruleCONJ pthm1 pthm2 = 
    do thm1@(Thm _ t1) <- toHThm pthm1
       thm2@(Thm _ t2) <- toHThm pthm2
       rulePROVE_HYP thm2 . rulePROVE_HYP thm1 $
         primINST [(tmP, t1), (tmQ, t2)] ruleCONJ_pth
  where ruleCONJ_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleCONJ_pth = cacheProof "ruleCONJ_pth" ctxtBool $
            do eqpthm <- ruleEQT_INTRO $ primASSUME tmP
               eqqthm <- ruleEQT_INTRO $ primASSUME tmQ
               th0 <- ruleAP_TERM [txt| f:bool->bool->bool |] eqpthm
               th1 <- primABS [txt| f:bool->bool->bool |] $ 
                        primMK_COMB th0 eqqthm
               th1_5 <- ruleAP_THM defAND tmP
               th2 <- ruleBETA $ ruleAP_THM th1_5 tmQ
               primEQ_MP (ruleSYM th2) th1

{-|@
 A |- t1 \/\\ t2
---------------
    A |- t1  
@

  Throws a 'HOLException' if the conclusion of the provided theorem is not a
  conjunction.
-}
ruleCONJUNCT1 :: (BoolCtxt thry, HOLThmRep thm cls thry) 
              => thm -> HOL cls thry HOLThm
ruleCONJUNCT1 pthm = 
    do thm <- toHThm pthm
       case concl thm of
         (l :/\ r) -> 
             rulePROVE_HYP thm $
               primINST [ (tmP, l), (tmQ, r) ] ruleCONJUNCT1_pth
         _ -> fail "ruleCONJUNCT1: conclusion not a conjunction."
  where ruleCONJUNCT1_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleCONJUNCT1_pth = cacheProof "ruleCONJUNCT1_pth" ctxtBool $
            do thm1 <- ruleCONV (convRAND convBETA) $ ruleAP_THM defAND tmP
               thm2 <- ruleCONV (convRAND convBETA) $ ruleAP_THM thm1 tmQ
               thm3 <- primEQ_MP thm2 $ primASSUME [txt| p /\ q |]
               ruleEQT_ELIM . ruleBETA $ 
                 ruleAP_THM thm3 [txt| \(p:bool) (q:bool). p |]

{-|@
 A |- t1 \/\\ t2
---------------
    A |- t2
@

  Throws a 'HOLException' if the conclusion of the provided theorem is not a
  conjunction.
-}
ruleCONJUNCT2 :: (BoolCtxt thry, HOLThmRep thm cls thry) 
              => thm -> HOL cls thry HOLThm
ruleCONJUNCT2 pthm = 
    do thm <- toHThm pthm 
       case concl thm of
         (l :/\ r) ->
             rulePROVE_HYP thm $
               primINST [ (tmP, l), (tmQ, r) ] ruleCONJUNCT2_pth
         _ -> fail "ruleCONJUNCT2: conclusion not a conjunction."
  where ruleCONJUNCT2_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleCONJUNCT2_pth = cacheProof "ruleCONJUNCT2_pth" ctxtBool $
            do thm1 <- ruleCONV (convRAND convBETA) $ ruleAP_THM defAND tmP
               thm2 <- ruleCONV (convRAND convBETA) $ ruleAP_THM thm1 tmQ
               thm3 <- primEQ_MP thm2 $ primASSUME [txt| p /\ q |]
               ruleEQT_ELIM . ruleBETA $ 
                 ruleAP_THM thm3 [txt| \(p:bool) (q:bool). q |]

{-|@
    A |- t1 \/\\ t2   
----------------------
  (A |- t1, A |- t2)
@

  Throws a 'HOLException' if the conclusion of the theorem is not a conjunction.
-}
ruleCONJ_PAIR :: (BoolCtxt thry, HOLThmRep thm cls thry) 
              => thm -> HOL cls thry (HOLThm, HOLThm)
ruleCONJ_PAIR pthm =
    (do th1 <- ruleCONJUNCT1 pthm
        th2 <- ruleCONJUNCT2 pthm
        return (th1, th2))
    <?> "ruleCONJ_PAIR"

{-|@
    A |- t1 \/\\ t2 \/\\ ... \/\\ tn
-----------------------------------
 [A |- t1, A |- t2, ..., A |- tn]
@

  Never fails, but may have no effect.
-}
ruleCONJUNCTS :: (BoolCtxt thry, HOLThmRep thm cls thry) 
              => thm -> HOL cls thry [HOLThm]
ruleCONJUNCTS pthm = 
    do thm <- toHThm pthm
       stripListM ruleCONJ_PAIR thm

--derived rules for implication
-- | @(==>) = \\ p q . p \/\\ q \<=\> p@
defIMP :: BoolCtxt thry => HOL cls thry HOLThm
defIMP = cacheProof "defIMP" ctxtBool $ getBasicDefinition "==>"

{-|@
 A1 |- t1 ==> t2   A2 |- t1
----------------------------
       A1 U A2 |- t2     
@

  Throws a 'HOLException' in the following cases:

  * Conclusion of first provided theorem is not an implication.

  * The antecedent of the implication is not alpha-equivalent to the conclusion
    of the second provided theorem.  
-}
ruleMP :: (BoolCtxt thry, HOLThmRep thm1 cls thry, HOLThmRep thm2 cls thry) 
       => thm1 -> thm2 -> HOL cls thry HOLThm
ruleMP pthm1 pthm2 = note "ruleMP" $
    do ithm <- toHThm pthm1
       thm@(Thm _ t1) <- toHThm pthm2
       case concl ithm of
         (ant :==> con)
             | ant `aConv` t1 ->  
                 rulePROVE_HYP thm . rulePROVE_HYP ithm $ 
                   primINST [ (tmP, ant), (tmQ, con) ] ruleMP_pth
             | otherwise -> fail "theorems do not agree."
         _ -> fail "not an implication."
  where ruleMP_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleMP_pth = cacheProof "ruleMP_pth" ctxtBool $
            do th1 <- ruleAP_THM (ruleAP_THM defIMP tmP) tmQ
               th2 <- ruleBETA th1
               th3 <- ruleSYM . primEQ_MP th2 $ primASSUME [txt| p ==> q |]     
               ruleCONJUNCT2 . primEQ_MP th3 $ primASSUME tmP

{-|@
     u    A |- t     
--------------------
 A - u |- u ==> t
@

  Throws a 'HOLException' if the provided term is not a proposition.
-}
ruleDISCH :: (BoolCtxt thry, HOLTermRep tm cls thry, HOLThmRep thm cls thry) 
          => tm -> thm -> HOL cls thry HOLThm
ruleDISCH ptm pthm =
    (do a <- toHTm ptm
        thm@(Thm _ t) <- toHThm pthm
        th1 <- ruleCONJ (primASSUME a) thm
        th2 <- ruleCONJUNCT1 $ primASSUME (concl th1)
        pth' <- primINST [(tmP, a), (tmQ, t)] ruleDISCH_pth
        primEQ_MP pth' $ primDEDUCT_ANTISYM th1 th2) 
    <?> "ruleDISCH"
  where ruleDISCH_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleDISCH_pth = cacheProof "ruleDISCH_pth" ctxtBool $
            do th1 <- ruleAP_THM defIMP tmP
               ruleSYM . ruleBETA $ ruleAP_THM th1 tmQ

{-|@
      A1, ..., An |- t     
----------------------------
 |- A1 ==> ... ==> An ==> t
@

  Never fails, but may have no effect.
-}
ruleDISCH_ALL :: (BoolCtxt thry, HOLThmRep thm cls thry) 
              => thm -> HOL cls thry HOLThm
ruleDISCH_ALL pthm = 
    do thm <- toHThm pthm
       case hyp thm of
         (a:_) -> ruleDISCH_ALL $ ruleDISCH a thm
         _     -> return thm


{-|@
 A |- t1 ==> t2
----------------
  A, t1 |- t2
@

  Throws a 'HOLException' if the conclusion of the provided theorem is not an
  implication.
-}
ruleUNDISCH :: (BoolCtxt thry, HOLThmRep thm cls thry) 
            => thm -> HOL cls thry HOLThm
ruleUNDISCH pthm = note "ruleUNDISCH" $
    do thm <- toHThm pthm
       case concl thm of
         (tm :==> _) -> ruleMP thm $ primASSUME tm
         _           -> fail "not an implication."

{-|@
 A |- t1 ==> ... ==> tn ==> t
------------------------------
     A, t1, ..., tn |- t
@

  Never fails, but may have no effect.
-}
ruleUNDISCH_ALL :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                => thm -> HOL cls thry HOLThm
ruleUNDISCH_ALL pthm =
    do thm <- toHThm pthm
       case concl thm of
         (:==>){} -> ruleUNDISCH_ALL =<< ruleUNDISCH thm
         _      -> return thm

{-|@
 A1 |- t1 ==> t2     A2 |- t2 ==> t1
-------------------------------------
        A1 U A2 |- t1 \<=\> t2
@

  Throws a 'HOLException' if the conclusions of the provided theorems are not
  complimentary implications.
-}
ruleIMP_ANTISYM :: (BoolCtxt thry, HOLThmRep thm1 cls thry,
                    HOLThmRep thm2 cls thry) 
                => thm1 -> thm2 -> HOL cls thry HOLThm
ruleIMP_ANTISYM thm1 thm2 = 
    (do th1 <- ruleUNDISCH thm1
        th2 <- ruleUNDISCH thm2
        primDEDUCT_ANTISYM th2 th1)
    <?> "ruleIMP_ANTISYM"

{-|@
  s   A |- t
--------------
  A U s |- t
@

  Throws a 'HOLException' if the provided term is not a proposition.
-}
ruleADD_ASSUM :: (BoolCtxt thry, HOLTermRep tm cls thry, HOLThmRep thm cls thry)
              => tm -> thm -> HOL cls thry HOLThm
ruleADD_ASSUM tm thm =
    (do th <- ruleDISCH tm thm
        ruleMP th $ primASSUME tm)
    <?> "ruleADD_ASSUM"

{-|@
           A |- t1 \<=\> t2
-----------------------------------
  (A |- t1 ==> t2, A |- t2 ==> t1)
@

  Throws a 'HOLException' if the conclusion of the theorem is not biconditional.
-}
ruleEQ_IMP :: (BoolCtxt thry, HOLThmRep thm cls thry) 
           => thm -> HOL cls thry (HOLThm, HOLThm)
ruleEQ_IMP pthm = note "ruleEQ_IMP" $
    do thm <- toHThm pthm
       case concl thm of
         (l :<=> r) ->
           let instFun = primINST [ (tmP, l), (tmQ, r) ] in
             do (pth1', pth2') <- pairMapM instFun ( ruleEQ_IMP_pth1
                                                   , ruleEQ_IMP_pth2 )
                pairMapM (flip ruleMP thm) (pth1', pth2')
         _ -> fail "not an equivalence."
  where ruleEQ_IMP_pth1 :: BoolCtxt thry => HOL cls thry HOLThm
        ruleEQ_IMP_pth1 = cacheProof "ruleEQ_IMP_pth1" ctxtBool $
            do th1 <- primASSUME [txt| p <=> q |]
               th2 <- primEQ_MP th1 $ primASSUME tmP
               ruleDISCH [txt| p <=> q |] $ ruleDISCH tmP th2

        ruleEQ_IMP_pth2 :: BoolCtxt thry => HOL cls thry HOLThm
        ruleEQ_IMP_pth2 = cacheProof "ruleEQ_IMP_pth2" ctxtBool $
            do th1 <- ruleSYM $ primASSUME [txt| p <=> q |]
               th2 <- primEQ_MP th1 $ primASSUME tmQ
               ruleDISCH [txt| p <=> q |] $ ruleDISCH tmQ th2 
                 

{-|@
 A1 |- t1 ==> t2   A2 |- t2 ==> t3
-----------------------------------
       A1 U A2 |- t1 ==> t3        
@

  Throws a 'HOLException' in the following cases:

  * The conclusions of the theorems are not implications.

  * The implications are not transitive.
-}
ruleIMP_TRANS :: (BoolCtxt thry, HOLThmRep thm1 cls thry,
                  HOLThmRep thm2 cls thry) 
              => thm1 -> thm2 -> HOL cls thry HOLThm
ruleIMP_TRANS pthm1 pthm2 = note "ruleIMP_TRANS" $
    do thm1 <- toHThm pthm1
       thm2 <- toHThm pthm2
       case (concl thm1, concl thm2) of
         (x :==> y1, y2 :==> z)
             | y1 /= y2 -> fail "implications are not transitive."
             | otherwise ->
                 do pth' <- primINST [ (tmP, x), (tmQ, y1), (tmR, z) 
                                     ] ruleIMP_TRANS_pth
                    ruleMP (ruleMP pth' thm1) thm2
         _ -> fail "not implications."
  where ruleIMP_TRANS_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleIMP_TRANS_pth = cacheProof "ruleIMP_TRANS_pth" ctxtBool $
            do qrth <- primASSUME [txt| q ==> r |]
               pqth <- primASSUME [txt| p ==> q |]
               mpth <- ruleMP qrth . ruleMP pqth $ primASSUME tmP
               foldrM ruleDISCH mpth [ [txt| p ==> q |], [txt| q ==> r |]
                                     , [txt| p:bool |] ]


-- derived rules for forall
-- | @(!) = \\ P:A->bool . P = \\ x . T@
defFORALL :: BoolCtxt thry => HOL cls thry HOLThm
defFORALL = cacheProof "defFORALL" ctxtBool $ getBasicDefinition "!"

{-|@
 u   A |- !x. t
----------------
  A |- t[u\/x]
@

  Throws a 'HOLException' in the following cases:

  * Conclusion of the provided theorem is not universally quantified.

  * The type of the bound variable does not agree with the type of the provided
    term.
-}
ruleSPEC :: (BoolCtxt thry, HOLTermRep tm cls thry, HOLThmRep thm cls thry) 
         => tm -> thm -> HOL cls thry HOLThm
ruleSPEC ptm pthm = note "ruleSPEC" $
    do thm <- toHThm pthm
       case concl thm of
         (Bind' "!" ab@(Abs (Var _ bvty) _)) ->
             do tm <- toHTm ptm
                pth' <- rulePINST [(tyA, bvty)] [ (tmPred, ab), (tmX, tm)
                                                ] ruleSPEC_pth
                (ruleCONV convBETA $ ruleMP pth' thm) <?> "types do not agree."
         _ -> fail "not universally quantified."
  where ruleSPEC_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleSPEC_pth = cacheProof "ruleSPEC_pth" ctxtBool $
            do th1 <- ruleAP_THM defFORALL tmPred
               th1_5 <- primEQ_MP th1 $ primASSUME [txt| (!)(P:A->bool) |]
               th2 <- ruleCONV convBETA th1_5
               th3 <- ruleCONV (convRAND convBETA) $ ruleAP_THM th2 tmX
               ruleDISCH_ALL $ ruleEQT_ELIM th3


{-|@
 [u1, ..., un]    A |- !x1 ... xn. t
---------------------------------------
    A |- t[u1, ..., un\/x1, ..., xn]
@

  Iteratively applies 'ruleSPEC' using a provided list of specialization terms,
  failing accordingly. 
-}
ruleSPECL :: (BoolCtxt thry, HOLTermRep tm cls thry, HOLThmRep thm cls thry) 
          => [tm] -> thm -> HOL cls thry HOLThm
ruleSPECL ptms pthm = 
    (do thm <- toHThm pthm
        foldlM (flip ruleSPEC) thm ptms) <?> "ruleSPECL"
                                 
{-|@
     A |- !x. t       
--------------------
 (x', A |- t[x'\/x])
@
  
  Applies 'ruleSPEC' using a 'variant' of the bound term, failing accordingly.
-}
ruleSPEC_VAR :: (BoolCtxt thry, HOLThmRep thm cls thry) 
             => thm -> HOL cls thry (HOLTerm, HOLThm)
ruleSPEC_VAR pthm =
    (do thm@(Thm _ x) <- toHThm pthm
        v <- bndvar =<< rand x
        let bv = variant (thmFrees thm) v
        thm' <- ruleSPEC bv thm
        return (bv, thm'))
    <?> "ruleSPEC_VAR: conclusion not quantified."

{-|@
        A |- !x1 ... xn. t
----------------------------------
 A |- t[x1', ..., xn'\/x1, ..., xn]
@

  Never fails, but may have no effect.
-}
ruleSPEC_ALL :: (BoolCtxt thry, HOLThmRep thm cls thry) 
             => thm -> HOL cls thry HOLThm
ruleSPEC_ALL thm =
    do thm'@(Thm _ x) <- toHThm thm
       if isForall x
          then do (_, thm'') <- ruleSPEC_VAR thm'
                  ruleSPEC_ALL thm''
          else return thm'

{-|@
  t:ty'   A |- !x:ty.tm
---------------------------
   A[ty'\/ty] |- tm[t\/x]
@

  A type instantiating version of 'ruleSPEC'.
  Throws a 'HOLException' in the following cases:

  * The conclusion of the provided therem is not universally quantified.

  * A matching instantiation for the provided term and the bound term cannot be
    found.
-}
ruleISPEC :: (BoolCtxt thry, HOLTermRep tm cls thry, HOLThmRep thm cls thry) 
          => tm -> thm -> HOL cls thry HOLThm
ruleISPEC ptm pthm = note "ruleISPEC" $
    do thm <- toHThm pthm
       case concl thm of
         (Forall (Var _ ty) _) ->
           do tm <- toHTm ptm
              tyenv <- typeMatch ty (typeOf tm) ([], [], []) <?> 
                         "can't instantiate theorem."
              (ruleSPEC tm (primINST_TYPE_FULL tyenv thm)) <?> 
                "type variable(s) free in assumption list."
         _ -> fail "theorem not universally quantified."

{-|@
 [t1:ty1', ..., tn:tyn']   A |- !x1:ty1 ... xn:tyn.t
-----------------------------------------------------
         A[ty1', ..., tyn'\/ty1, ..., tyn] 
          |- t[t1, ..., tn\/x1, ..., xn]
@

  Throws a 'HOLException' in the following cases:

  * The provided instantiation list is too long.

  * A satisfying instantiation cannot be found.
-}
ruleISPECL :: (BoolCtxt thry, HOLTermRep tm cls thry, HOLThmRep thm cls thry)
           => [tm] -> thm -> HOL cls thry HOLThm
ruleISPECL [] thm = toHThm thm
ruleISPECL ptms pthm = note "ruleISPECL" $
    do tms <- mapM toHTm ptms
       thm@(Thm _ x) <- toHThm pthm
       let (vs, _) = stripForall x
       (avs, _) <- trySplitAt (length tms) vs <?> "instantiation list too long."
       tyenv <- (foldr2M tyFun ([], [], []) avs $ map typeOf tms) <?>
                  "can't instantiate theorem."
       (ruleSPECL tms $ primINST_TYPE_FULL tyenv thm) <?>
         "type variable(s) free in assumption list."
  where tyFun :: HOLTerm -> HOLType -> SubstTrip -> HOL cls thry SubstTrip
        tyFun (Var _ ty1) ty2 acc = typeMatch ty1 ty2 acc
        tyFun _ _ _ = fail "tyFun"

{-|@
 x   A |- t  
------------
 A |- !x. t
@

  Throws a 'HOLException' in the following cases:

  * The provided term is not a variable.

  * The provided term is free in the assumption list of the provided theorem.
-}      
ruleGEN :: (BoolCtxt thry, HOLTermRep tm cls thry, HOLThmRep thm cls thry) 
        => tm -> thm -> HOL cls thry HOLThm
ruleGEN px pthm = note "ruleGEN" $
    do x <- toHTm px
       case x of
         (Var _ tyx) ->
           do qth <- primINST_TYPE [(tyA, tyx)] ruleGEN_pth
              ptm <- rand =<< rand (concl qth)
              th1 <- ruleEQT_INTRO pthm
              th2 <- primABS x th1 <?> "term free in the assumption list."
              phi <- lHand $ concl th2
              qth' <- primINST [(ptm, phi)] qth
              primEQ_MP qth' th2
         _ -> fail "term not a variable."
  where ruleGEN_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleGEN_pth = cacheProof "ruleGEN_pth" ctxtBool .
            ruleSYM . ruleCONV (convRAND convBETA) $ 
              ruleAP_THM defFORALL tmPred


{-|@
 [x1, ..., xn]     A |- t
--------------------------
    A |- !x1 ... xn. t
@

  Throws a 'HOLException' in the following cases:

  * Any of the provided terms are not a variable.

  * Any of the provided terms are free in the assumption list.
-}
ruleGENL :: (BoolCtxt thry, HOLTermRep tm cls thry, HOLThmRep thm cls thry) 
         => [tm] -> thm -> HOL cls thry HOLThm
ruleGENL ptms pthm = 
    (do thm <- toHThm pthm
        foldrM ruleGEN thm ptms) <?> "ruleGENL"

{-|@
       A |- t
--------------------
 A |- !x1 ... xn. t
@

  Never fails, but may have no effect.
-}
ruleGEN_ALL :: (BoolCtxt thry, HOLThmRep thm cls thry) 
            => thm -> HOL cls thry HOLThm
ruleGEN_ALL pthm =
    do thm@(Thm asl c) <- toHThm pthm 
       let vars = frees c \\ catFrees asl
       ruleGENL vars thm


-- derived rules for exists
-- | @(?) = \\ P:A->bool . ! q . (! x . P x ==> q) ==> q@
defEXISTS :: BoolCtxt thry => HOL cls thry HOLThm
defEXISTS = cacheProof "defEXISTS" ctxtBool $ getBasicDefinition "?"

{-|@
 (?x. p)   u   A |- p[u\/x]
---------------------------
         A |- ?x. p
@

  Throws a 'HOLException' in the following cases:

  *  The first provided term is not existentially quantified.

  *  The second provided term is not the witness that matches the conclusion of
     the provided theorem.
-}
ruleEXISTS :: (BoolCtxt thry, HOLTermRep tm1 cls thry, HOLTermRep tm2 cls thry,
               HOLThmRep thm cls thry) 
           => tm1 -> tm2 -> thm -> HOL cls thry HOLThm
ruleEXISTS ptm1 ptm2 thm = 
    (do atm <- toHTm ptm1
        stm <- toHTm ptm2
        ab <- rator atm
        th1 <- runConv convBETA =<< mkComb ab stm
        pth' <- rulePINST [(tyA, typeOf stm)] 
                  [ (tmPred, ab), (tmX, stm) ] ruleEXISTS_pth
        th2 <- primEQ_MP (ruleSYM th1) thm
        rulePROVE_HYP th2 pth')
    <?> "ruleEXISTS"
  where ruleEXISTS_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleEXISTS_pth = cacheProof "ruleEXISTS_pth" ctxtBool $
            do th1 <- ruleCONV (convRAND convBETA) $
                        ruleAP_THM defEXISTS tmPred
               th2 <- ruleSPEC tmX $ primASSUME [txt| !x:A. P x ==> q |]
               th3 <- ruleDISCH [txt| !x:A. P x ==> q |] . ruleMP th2 $ 
                        primASSUME [txt| (P:A->bool) x |]
               th4 <- ruleGEN tmQ th3
               primEQ_MP (ruleSYM th1) th4

{-|@
 u   A |- p   
-------------
 A |- ?u. p
@

  Throws a 'HOLException' if the provided term is not a variable.
-}
ruleSIMPLE_EXISTS :: (BoolCtxt thry, HOLTermRep tm cls thry, 
                      HOLThmRep thm cls thry) 
                  => tm -> thm -> HOL cls thry HOLThm
ruleSIMPLE_EXISTS ptm pthm =
    do thm@(Thm _ p) <- toHThm pthm
       v <- toHTm ptm
       (ruleEXISTS (mkExists v p) v thm) <?> "ruleSIMPLE_EXISTS"

{-|@
  v    A1 |- ?x. s    A2 |- t  
-------------------------------
   A1 U (A2 - s[v\/x]) |- t
@

  Throws a 'HOLException' in the following cases:

  * The provided term is not a variable of appropriate type.

  * The conclusion of the first provided theorem is not existentially quantified
    with a bound variable of same type as the provided term.

  * The provided term would be free in any part of the resultant theorem.
-}
ruleCHOOSE :: (BoolCtxt thry, HOLTermRep tm cls thry, HOLThmRep thm1 cls thry,
               HOLThmRep thm2 cls thry)
           => tm -> thm1 -> thm2 -> HOL cls thry HOLThm
ruleCHOOSE ptm pthm1 pthm2 = note "ruleCHOOSE" $
    do thm1 <- toHThm pthm1
       case concl thm1 of
         (Comb _ ab@(Abs bv bod)) ->
             (do v <- toHTm ptm
                 cmb <- mkComb ab v
                 pat <- varSubst [(bv, v)] bod
                 thm2 <- toHThm pthm2
                 thm3 <- ruleCONV convBETA $ primASSUME cmb
                 thm4 <- ruleGEN v . ruleDISCH cmb $ 
                           ruleMP (ruleDISCH pat thm2) thm3
                 thm5 <- rulePINST [(tyA, typeOf v)] 
                           [ (tmPred, ab), (tmQ, concl thm2) ] ruleCHOOSE_pth
                 ruleMP (ruleMP thm5 thm4) thm1)
             <?> "provided term is free in resultant theorem."
         _ -> fail "conclusion not existentially quantified."
  where ruleCHOOSE_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleCHOOSE_pth = cacheProof "ruleCHOOSE_pth" ctxtBool $
            do th1 <- ruleCONV (convRAND convBETA) $ 
                        ruleAP_THM defEXISTS tmPred
               (th2, _) <- ruleEQ_IMP th1
               th3 <- ruleSPEC tmQ $ ruleUNDISCH th2
               ruleDISCH_ALL . ruleDISCH [txt| (?) (P:A->bool) |] $ 
                 ruleUNDISCH th3

{-|@
  v    [a1, ..., an] |- t  
---------------------------
   [?v. a1 ... an] |- t
@

  Throws a 'HOLException' in the following cases:

  * The provided term is not a variable.

  * The provided term is free in the conclusion of the provided theorem.
-}
ruleSIMPLE_CHOOSE :: (BoolCtxt thry, HOLTermRep tm cls thry, 
                      HOLThmRep thm cls thry) 
                  => tm -> thm -> HOL cls thry HOLThm
ruleSIMPLE_CHOOSE ptm pthm = note "ruleSIMPLE_CHOOSE" $
    do v <- toHTm ptm
       thm@(Thm a c) <- toHThm pthm
       if v `freeIn` c then fail "provided term free in conclusion."
          else do v' <- (mkExists v $ head a) <?> "provided term not variable." 
                  ruleCHOOSE v (primASSUME v') thm

-- derived rules for disjunction
-- | @(\\\/) = \\ p q . ! r . (p ==> r) ==> (q ==> r) ==> r@
defOR :: BoolCtxt thry => HOL cls thry HOLThm
defOR = cacheProof "defOR" ctxtBool $ getBasicDefinition "\\/"

{-|@
  t2   A |- t1   
----------------
 A |- t1 \\/ t2
@

  Throws a 'HOLException' if the provided term is not a proposition.
-}
ruleDISJ1 :: (BoolCtxt thry, HOLThmRep thm cls thry, HOLTermRep tm cls thry) 
          => thm -> tm -> HOL cls thry HOLThm
ruleDISJ1 pthm ptm = 
    (do thm@(Thm _ c) <- toHThm pthm
        tm <- toHTm ptm
        rulePROVE_HYP thm $ primINST [ (tmP, c), (tmQ, tm) ] ruleDISJ1_pth)
        <?> "ruleDISJ1"
  where ruleDISJ1_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleDISJ1_pth = cacheProof "ruleDISJ1_pth" ctxtBool $
            do th1 <- ruleCONV (convRAND convBETA) $ ruleAP_THM defOR tmP
               th2 <- ruleCONV (convRAND convBETA) $ ruleAP_THM th1 tmQ
               th3 <- ruleMP (primASSUME [txt| p ==> t |]) $ primASSUME tmP
               th4 <- ruleGEN tmT . ruleDISCH [txt| p ==> t |] $ 
                        ruleDISCH [txt| q ==> t |] th3
               primEQ_MP (ruleSYM th2) th4

{-|@
  t1   A |- t2   
----------------
 A |- t1 \\/ t2
@

  Throws a 'HOLException' if the provided term is not a proposition.
-}
ruleDISJ2 :: (BoolCtxt thry, HOLTermRep tm cls thry, HOLThmRep thm cls thry) 
          => tm -> thm -> HOL cls thry HOLThm
ruleDISJ2 ptm pthm = 
    (do tm <- toHTm ptm
        thm@(Thm _ c) <- toHThm pthm
        rulePROVE_HYP thm $ primINST [ (tmP, tm), (tmQ, c) ] ruleDISJ2_pth)
    <?> "ruleDISJ2"
  where ruleDISJ2_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleDISJ2_pth = cacheProof "ruleDISJ2_pth" ctxtBool $
            do th1 <- ruleCONV (convRAND convBETA) $ ruleAP_THM defOR tmP
               th2 <- ruleCONV (convRAND convBETA) $ ruleAP_THM th1 tmQ
               th3 <- ruleMP (primASSUME [txt| q ==> t |]) $ primASSUME tmQ
               th4 <- ruleGEN tmT . ruleDISCH [txt| p ==> t |] $ 
                        ruleDISCH [txt| q ==> t |] th3
               primEQ_MP (ruleSYM th2) th4


{-|@
   A |- t1 \\/ t2     A1 |- t      A2 |- t     
---------------------------------------------
      A U (A1 - t1) U (A2 - t2) |- t
@

  Throws a 'HOLException' in the following cases:

  * The conclusion of the first provided theorem is not a disjunction.

  * The conclusions of the last two provided theorems are not alpha-equivalent.
-}
ruleDISJ_CASES :: (BoolCtxt thry, HOLThmRep thm1 cls thry, 
                   HOLThmRep thm2 cls thry, HOLThmRep thm3 cls thry) 
               => thm1 -> thm2 -> thm3 -> HOL cls thry HOLThm
ruleDISJ_CASES pthm1 pthm2 pthm3 = note "ruleDISJ_CASES" $
    do th0 <- toHThm pthm1
       case concl th0 of
         (l0 :\/ r0) ->
             do th1@(Thm _ c1) <- toHThm pthm2
                th2@(Thm _ c2) <- toHThm pthm3
                if not $ c1 `aConv` c2
                   then fail "conclusions not equivalent."
                   else do dth1 <- ruleDISCH r0 th2
                           dth2 <- ruleDISCH l0 th1
                           rulePROVE_HYP dth1 . rulePROVE_HYP dth2 . 
                             rulePROVE_HYP th0 $ primINST 
                               [ (tmP, l0), (tmQ, r0), (tmR, c1) 
                               ] ruleDISJ_CASES_pth
         _ -> fail "theorem not a disjunction."
  where ruleDISJ_CASES_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleDISJ_CASES_pth = cacheProof "ruleDISJ_CASES_pth" ctxtBool $
            do thm1 <- ruleCONV (convRAND convBETA) $ ruleAP_THM defOR tmP
               thm2 <- ruleCONV (convRAND convBETA) $ ruleAP_THM thm1 tmQ
               thm3 <- ruleSPEC tmR . primEQ_MP thm2 $ 
                         primASSUME [txt| p \/ q |]
               ruleUNDISCH $ ruleUNDISCH thm3

{-|@
     [p1, ..., pn] |- r    [q1, ..., qn] |- r       
--------------------------------------------------
 (p1 \\/ q1) U [p2, ..., pn] U [q2, ..., qn] |- r
@

  Throws a 'HOLException' when the conclusions of the provided theorems are
  not alpha-equivalent.
-}
ruleSIMPLE_DISJ_CASES :: (BoolCtxt thry, HOLThmRep thm1 cls thry, 
                          HOLThmRep thm2 cls thry) 
                      => thm1 -> thm2 -> HOL cls thry HOLThm
ruleSIMPLE_DISJ_CASES pthm1 pthm2 =
    (do thm1 <- toHThm pthm1
        thm2 <- toHThm pthm2
        thm3 <- primASSUME $ mkDisj (head $ hyp thm1) (head $ hyp thm2)
        ruleDISJ_CASES thm3 thm1 thm2) 
    <?> "ruleSIMPLE_DISJ_CASES"

-- derived rules for negation
-- | @F = ! p:bool . p@
defFALSE :: BoolCtxt thry => HOL cls thry HOLThm
defFALSE = cacheProof "defFALSE" ctxtBool $ getBasicDefinition "F" 

-- | @_FALSITY_ = F@
def_FALSITY_ :: BoolCtxt thry => HOL cls thry HOLThm
def_FALSITY_ = cacheProof "def_FALSITY_" ctxtBool $ 
    getBasicDefinition "_FALSITY_"

-- | @(~) = \\ p . p ==> F@
defNOT :: BoolCtxt thry => HOL cls thry HOLThm
defNOT = cacheProof "defNOT" ctxtBool $ getBasicDefinition "~"

{-|@
   A |- ~t   
--------------
 A |- t ==> F
@

  Throws a 'HOLException' if the conclusion of the provided theorem is not a
  negated term.
-}
ruleNOT_ELIM :: (BoolCtxt thry, HOLThmRep thm cls thry) 
             => thm -> HOL cls thry HOLThm
ruleNOT_ELIM pthm = note "ruleNOT_ELIM" $
    do thm <- toHThm pthm
       case concl thm of
         (Neg tm) ->
             do pth' <- primINST [(tmP, tm)] ruleNOT_ELIM_pth
                primEQ_MP pth' thm
         _ -> fail "not a negation."
  where ruleNOT_ELIM_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleNOT_ELIM_pth = cacheProof "ruleNOT_ELIM_pth" ctxtBool .
            ruleCONV (convRAND convBETA) $ ruleAP_THM defNOT tmP

{-|@
 A |- t ==> F
--------------
   A |- ~t
@

  Throws a 'HOLException' if the conclusion of the provided theorem is not of
  the form @tm ==> F@.
-}
ruleNOT_INTRO :: (BoolCtxt thry, HOLThmRep thm cls thry) 
              => thm -> HOL cls thry HOLThm
ruleNOT_INTRO pthm = note "ruleNOT_INTRO" $
    do thm <- toHThm pthm
       case concl thm of
         (tm :==> _) ->
             do pth' <- primINST [(tmP, tm)] ruleNOT_INTRO_pth
                primEQ_MP pth' thm
         _ -> fail "not an implication."
  where ruleNOT_INTRO_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleNOT_INTRO_pth = cacheProof "ruleNOT_INTRO_pth" ctxtBool .
            ruleSYM . ruleCONV (convRAND convBETA) $ ruleAP_THM defNOT tmP

{-|@
  A |- ~t
---------------
 A |- t \<=\> F
@

  Throws a 'HOLException' if the conclusion of the provided theorem is not a
  negation.
-}
ruleEQF_INTRO :: (BoolCtxt thry, HOLThmRep thm cls thry) 
              => thm -> HOL cls thry HOLThm
ruleEQF_INTRO pthm = note "ruleEQF_INTRO" $
    do thm <- toHThm pthm
       case concl thm of
         (Neg tm) ->
             do pth' <- primINST [(tmP, tm)] ruleEQF_INTRO_pth
                ruleMP pth' thm
         _ -> fail "not a negation."
  where ruleEQF_INTRO_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleEQF_INTRO_pth = cacheProof "ruleEQF_INTRO_pth" ctxtBool $
            do th1 <- ruleNOT_ELIM $ primASSUME [txt| ~p |]
               th2 <- ruleDISCH [txt| F |] . ruleSPEC tmP .
                        primEQ_MP defFALSE $ primASSUME [txt| F |]
               ruleDISCH_ALL $ ruleIMP_ANTISYM th1 th2

{-|@
 A |- t \<=\> F
---------------
   A |- ~t
@

  Throws a 'HOLException' if the conclusion of the provided theorem is not of 
  the form @tm \<=\> F@.
-}
ruleEQF_ELIM :: (BoolCtxt thry, HOLThmRep thm cls thry) 
             => thm -> HOL cls thry HOLThm
ruleEQF_ELIM pthm = note "ruleEQF_ELIM" $
    do thm <- toHThm pthm
       case concl thm of
         (tm :<=> _) ->
             do pth' <- primINST [(tmP, tm)] ruleEQF_ELIM_pth
                ruleMP pth' thm
         _ -> fail "not an equality."
  where ruleEQF_ELIM_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleEQF_ELIM_pth = cacheProof "ruleEQF_ELIM_pth" ctxtBool $
          do th1 <- primEQ_MP defFALSE . primEQ_MP (primASSUME [txt| p = F |]) $
                      primASSUME tmP
             ruleDISCH_ALL . ruleNOT_INTRO . ruleDISCH tmP $
               ruleSPEC [txt| F |] th1

{-|@
  t   A |- F
-------------
   A |- t
@

  Throws a 'HOLException' in the following cases:

  * The provided term is not a proposition.

  * The conclusion of the provided theorem is not @F@.
-}
ruleCONTR :: (BoolCtxt thry, HOLTermRep tm cls thry, HOLThmRep thm cls thry) 
          => tm -> thm -> HOL cls thry HOLThm
ruleCONTR tm thm =
    (rulePROVE_HYP thm $ 
       primINST [(tmP, tm)] ruleCONTR_pth) <?> "ruleCONTR"
  where ruleCONTR_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleCONTR_pth = cacheProof "ruleCONTR_pth" ctxtBool .
            ruleSPEC tmP . primEQ_MP defFALSE $ primASSUME [txt| F |]

{-|@
  A |- ?!x. p
---------------
  A |- ?x. p
@

  Throws a 'HOLException' when the conclusion of the provided theorem is not
  unique-existentially quantified.
-}
ruleEXISTENCE :: (BoolCtxt thry, HOLThmRep thm cls thry) 
              => thm -> HOL cls thry HOLThm
ruleEXISTENCE pthm = note "ruleEXISTENCE" $
    do thm <- toHThm pthm
       case concl thm of
         (Bind' "?!" ab@(Abs (Var _ ty) _)) ->
             do pth' <- rulePINST [(tyA, ty)] [(tmPred, ab)] ruleEXISTENCE_pth
                ruleMP pth' thm
         _ -> fail "not a unique-existential."
  where ruleEXISTENCE_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleEXISTENCE_pth = cacheProof "ruleEXISTENCE_pth" ctxtBool $
            do th1 <- ruleCONV (convRAND convBETA) $ 
                        ruleAP_THM defEXISTS_UNIQUE tmPred
               th2 <- ruleUNDISCH $ liftM fst (ruleEQ_IMP th1)
               ruleDISCH_ALL $ ruleCONJUNCT1 th2

-- Other definitions
-- | @(?!) = \\ P:A->bool . ((?) P) /\ (! x y . P x /\ P y ==> x = y)@
defEXISTS_UNIQUE :: BoolCtxt thry => HOL cls thry HOLThm
defEXISTS_UNIQUE = cacheProof "defEXISTS_UNIQUE" ctxtBool $ 
    getBasicDefinition "?!"

-- | @(!!) = \ P : (% 'A . bool). P = (\\ 'A . T)@
defTY_FORALL :: BoolCtxt thry => HOL cls thry HOLThm
defTY_FORALL = cacheProof "defTY_FORALL" ctxtBool $ getBasicDefinition "!!"

-- | @(??) = \ P : (% 'A . bool). ~(P = (\\ 'A . F))@
defTY_EXISTS :: BoolCtxt thry => HOL cls thry HOLThm
defTY_EXISTS = cacheProof "defTY_EXISTS" ctxtBool $ getBasicDefinition "??"
