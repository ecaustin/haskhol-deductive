{-# LANGUAGE PatternSynonyms #-}
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
    ( -- * Theory Context
       -- $ThryCtxt
      BoolType
    , BoolThry
    , BoolCtxt
    , ctxtBool
      -- * General, Derived Rules 
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

{- $ThryCtxt
  See 'templateTypes', 'extendCtxt', and 'templateProvers' in the 
  "HaskHOL.Core.Ext" module for more information about these types and values.
-}


--allows easy instantiation for pro forma theorems

{-|@

 [(ty1, tv1), ..., (tyn, tvn)]   [(t1, x1), ..., (tn, xn)]   A |- t             
--------------------------------------------------------------------
   A[ty1, ..., tyn\/tv1, ..., tvn][t1, ..., tn\/x1, ..., xn]
    |- t[ty1, ..., tyn\/tv1, ..., tvn][t1, ..., tn\/x1, ..., xn]
@

  Fails with 'Nothing' if the provided term substitution environment is 
  ill-formed.
-}
rulePINST :: HOLTypeEnv -> HOLTermEnv -> HOLThm -> Maybe HOLThm
rulePINST tyenv tmenv thm =
    primINST (map (first (inst tyenv)) tmenv) $ 
      primINST_TYPE tyenv thm

--derived deductive rules

{-|@
  A1 |- t1   A2 |- t2  
------------------------
 (A1 U A2) - t1 |- t2
@

  Never fails.
-}
rulePROVE_HYP :: HOLThm -> HOLThm -> HOLThm
rulePROVE_HYP athm@(Thm _ a) bthm@(Thm bs _)
    | any (aConv a) bs = 
        fromRight $ primEQ_MP (primDEDUCT_ANTISYM athm bthm) athm
    | otherwise = bthm
rulePROVE_HYP _ _ = error "rulePROVE_HYP: exhaustive warning."

-- derived rules for truth
-- | @T = (\ p:bool . p) = (\ p:bool . p)@
defT :: BoolCtxt thry => HOL cls thry HOLThm
defT = cacheProof "defT" ctxtBool $ getBasicDefinition "T"

-- | @|- T@
thmTRUTH :: BoolCtxt thry => HOL cls thry HOLThm
thmTRUTH = cacheProof "thmTRUTH" ctxtBool $
    do tm <- toHTm [str| \p:bool. p |]
       tdef <- defT
       liftO . liftM1 primEQ_MP (ruleSYM tdef) $ primREFL tm

{-|@
 A |- t \<=\> T  
----------------
     A |- t         
@

  Throws a 'HOLException' if the conclusion of the provided theorem is not of 
  the form @tm \<=\> T@.
-}
ruleEQT_ELIM :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleEQT_ELIM thm =
    do truth <- thmTRUTH
       liftEither "ruleEQT_ELIM" $
         liftM1 primEQ_MP (ruleSYM thm) truth


{-|@
    A |- t     
--------------
 A |- t \<=\> T
@

  Never fails.
-}  
ruleEQT_INTRO :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleEQT_INTRO thm@(Thm _ c) = 
    do t <- serve [bool| t:bool |]
       pth <- ruleEQT_INTRO_pth
       let pth' = fromJust $ primINST [(t, c)] pth
       liftO $ primEQ_MP pth' thm
  where ruleEQT_INTRO_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleEQT_INTRO_pth = cacheProof "ruleEQT_INTRO" ctxtBool $
            do t <- toHTm "t:bool"
               truth <- thmTRUTH
               let th1 = fromRight $ primASSUME t
               let th2@(Thm _ tm) = primDEDUCT_ANTISYM th1 truth
               th3 <- ruleEQT_ELIM #<< primASSUME tm
               return $! primDEDUCT_ANTISYM th3 th2
ruleEQT_INTRO _ = error "exhaustive warning."

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
ruleCONJ :: BoolCtxt thry => HOLThm -> HOLThm -> HOL cls thry HOLThm
ruleCONJ thm1@(Thm _ t1) thm2@(Thm _ t2) = 
    do p <- serve [bool| p:bool |]
       q <- serve [bool| q:bool |]
       pth <- ruleCONJ_pth
       return . rulePROVE_HYP thm2 . rulePROVE_HYP thm1 . fromJust $ 
         primINST [(p, t1), (q, t2)] pth
  where ruleCONJ_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleCONJ_pth = cacheProof "ruleCONJ_pth" ctxtBool $
            do f <- toHTm "f:bool->bool->bool"
               p <- toHTm "p:bool"
               q <- toHTm "q:bool"
               dAnd <- defAND
               eqpthm <- ruleEQT_INTRO #<< primASSUME p
               eqqthm <- ruleEQT_INTRO #<< primASSUME q
               let th1 = fromRight $ primABS f =<< 
                           liftM1 primMK_COMB (ruleAP_TERM f eqpthm) eqqthm
               th2 <- ruleBETA #<< liftM1 ruleAP_THM (ruleAP_THM dAnd p) q
               liftO $ liftM1 primEQ_MP (ruleSYM th2) th1
ruleCONJ _ _ = error "ruleCONJ: exhaustive warning."

{-|@
 A |- t1 \/\\ t2
---------------
    A |- t1  
@

  Throws a 'HOLException' if the conclusion of the provided theorem is not a
  conjunction.
-}
ruleCONJUNCT1 :: (BoolCtxt thry, HOLThmRep thm cls thry) => thm 
              -> HOL cls thry HOLThm
ruleCONJUNCT1 pthm = 
    do p <- serve [bool| P:bool |]
       q <- serve [bool| Q:bool |]
       pth <- ruleCONJUNCT1_pth
       thm <- toHThm pthm
       case destConj $ concl thm of
         Just (l, r) -> 
             return . rulePROVE_HYP thm . fromJust $
               primINST [(p, l), (q, r)] pth
         _ -> fail "ruleCONJUNCT1: conclusion not a conjunction."
  where ruleCONJUNCT1_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleCONJUNCT1_pth = cacheProof "ruleCONJUNCT1_pth" ctxtBool $
            do p <- toHTm "P:bool"
               q <- toHTm "Q:bool"
               pAndQ <- toHTm [str| P /\ Q |]
               sel1 <- toHTm [str| \(p:bool) (q:bool). p |]
               dAnd <- defAND
               thm1 <- ruleCONV (convRAND convBETA) #<< ruleAP_THM dAnd p
               thm2 <- ruleCONV (convRAND convBETA) #<< ruleAP_THM thm1 q
               let thm3 = fromRight $ primEQ_MP thm2 =<< primASSUME pAndQ
               ruleEQT_ELIM =<< ruleBETA #<< ruleAP_THM thm3 sel1

{-|@
 A |- t1 \/\\ t2
---------------
    A |- t2
@

  Throws a 'HOLException' if the conclusion of the provided theorem is not a
  conjunction.
-}
ruleCONJUNCT2 :: (BoolCtxt thry, HOLThmRep thm cls thry) => thm 
              -> HOL cls thry HOLThm
ruleCONJUNCT2 = ruleCONJUNCT2' <=< toHThm
  where ruleCONJUNCT2' :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
        ruleCONJUNCT2' thm = 
            do p <- serve [bool| P:bool |]
               q <- serve [bool| Q:bool |]
               pth <- ruleCONJUNCT2_pth
               case destConj $ concl thm of
                 Just (l, r) ->
                     return . rulePROVE_HYP thm . fromJust $ 
                       primINST [(p, l), (q, r)] pth
                 _ -> fail "ruleCONJUNCT2: conclusion not a conjunction."
       
        ruleCONJUNCT2_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleCONJUNCT2_pth = cacheProof "ruleCONJUNCT2_pth" ctxtBool $
            do p <- toHTm "P:bool"
               q <- toHTm "Q:bool"
               pAndQ <- toHTm [str| P /\ Q |]
               sel2 <- toHTm [str| \(p:bool) (q:bool). q |]
               dAnd <- defAND
               thm1 <- ruleCONV (convRAND convBETA) #<< ruleAP_THM dAnd p
               thm2 <- ruleCONV (convRAND convBETA) #<< ruleAP_THM thm1 q
               let thm3 = fromRight $ primEQ_MP thm2 =<< primASSUME pAndQ
               ruleEQT_ELIM =<< ruleBETA #<< ruleAP_THM thm3 sel2

{-|@
    A |- t1 \/\\ t2   
----------------------
  (A |- t1, A |- t2)
@

  Throws a 'HOLException' if the conclusion of the theorem is not a conjunction.
-}
ruleCONJ_PAIR :: (BoolCtxt thry, HOLThmRep thm cls thry) => thm 
              -> HOL cls thry (HOLThm, HOLThm)
ruleCONJ_PAIR pthm =
    (do thm <- toHThm pthm
        th1 <- ruleCONJUNCT1 thm
        th2 <- ruleCONJUNCT2 thm
        return (th1, th2))
    <?> "ruleCONJ_PAIR"

{-|@
    A |- t1 \/\\ t2 \/\\ ... \/\\ tn
-----------------------------------
 [A |- t1, A |- t2, ..., A |- tn]
@

  Never fails, but may have no effect.
-}
ruleCONJUNCTS :: (BoolCtxt thry, HOLThmRep thm cls thry) => thm 
              -> HOL cls thry [HOLThm]
ruleCONJUNCTS = stripListM ruleCONJ_PAIR <=< toHThm

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
ruleMP :: (BoolCtxt thry, HOLThmRep thm cls thry) => thm -> HOLThm 
       -> HOL cls thry HOLThm
ruleMP th = liftM1 ruleMP' (toHThm th)
  where ruleMP' :: BoolCtxt thry => HOLThm -> HOLThm -> HOL cls thry HOLThm
        ruleMP' ithm@(Thm _ imp) thm@(Thm _ t1) = 
            noteHOL "ruleMP" $
              do p <- serve [bool| p:bool |]
                 q <- serve [bool| q:bool |]
                 pth <- ruleMP_pth
                 case destImp imp of
                   Just (ant, con)
                       | ant `aConv` t1 ->  
                             return . rulePROVE_HYP thm . rulePROVE_HYP ithm . 
                               fromJust $ primINST [(p, ant), (q, con)] pth
                       | otherwise -> fail "theorems do not agree."
                   _ -> fail "not an implication."
        ruleMP' _ _ = error "ruleMP: exhaustive warning."
   
        ruleMP_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleMP_pth = cacheProof "ruleMP_pth" ctxtBool $
            do p <- toHTm "p:bool"
               q <- toHTm "q:bool"
               pImpQ <- toHTm "p ==> q"
               dImp <- defIMP
               let th1 = fromRight $ liftM1 ruleAP_THM (ruleAP_THM dImp p) q
               th2 <- ruleBETA th1
               th3 <- fromRightM $ ruleSYM =<< primEQ_MP th2 =<< 
                        primASSUME pImpQ        
               ruleCONJUNCT2 #<< primEQ_MP th3 =<< primASSUME p

{-|@
     u    A |- t     
--------------------
 A - u |- u ==> t
@

  Throws a 'HOLException' if the provided term is not a proposition.
-}
ruleDISCH :: (BoolCtxt thry, HOLTermRep tm cls thry) => tm -> HOLThm
          -> HOL cls thry HOLThm
ruleDISCH tm = liftM1 ruleDISCH' (toHTm tm)
  where ruleDISCH' :: BoolCtxt thry => HOLTerm -> HOLThm -> HOL cls thry HOLThm
        ruleDISCH' a thm@(Thm _ t) = 
            (do p <- serve [bool| p:bool |]
                q <- serve [bool| q:bool |]
                pth <- ruleDISCH_pth
                th1 <- ruleCONJ (fromRight $ primASSUME a) thm
                th2 <- ruleCONJUNCT1 #<< primASSUME (concl th1)
                let pth' = fromJust $ primINST [(p, a), (q, t)] pth
                liftO . primEQ_MP pth' $ primDEDUCT_ANTISYM th1 th2) 
            <?> "ruleDISCH"
        ruleDISCH' _ _ = error "ruleDISCH: exhaustive warning."

        ruleDISCH_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleDISCH_pth = cacheProof "ruleDISCH_pth" ctxtBool $
            do p <- toHTm "p:bool"
               q <- toHTm "q:bool"
               dImp <- defIMP
               liftM (fromRight . ruleSYM) $
                 ruleBETA #<< liftM1 ruleAP_THM (ruleAP_THM dImp p) q

{-|@
      A1, ..., An |- t     
----------------------------
 |- A1 ==> ... ==> An ==> t
@

  Never fails, but may have no effect.
-}
ruleDISCH_ALL :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleDISCH_ALL thm@(Thm a _)
    | null a = return thm
    | otherwise = 
          (ruleDISCH_ALL =<< ruleDISCH (head a) thm) <|> return thm
ruleDISCH_ALL _ = error "ruleDISCH_ALL: exhaustive warning."


{-|@
 A |- t1 ==> t2
----------------
  A, t1 |- t2
@

  Throws a 'HOLException' if the conclusion of the provided theorem is not an
  implication.
-}
ruleUNDISCH :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleUNDISCH thm@(Thm _ imp) = 
    (let tm = fromJust $ rand =<< rator imp in
       ruleMP thm #<< primASSUME tm) <?> "ruleUNDISCH"
ruleUNDISCH _ = error "ruleUNDISCH: exhaustive warning."

{-|@
 A |- t1 ==> ... ==> tn ==> t
------------------------------
     A, t1, ..., tn |- t
@

  Never fails, but may have no effect.
-}
ruleUNDISCH_ALL :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleUNDISCH_ALL th@(Thm _ c)
    | isImp c = ruleUNDISCH_ALL =<< ruleUNDISCH th
    | otherwise = return th
ruleUNDISCH_ALL _ = error "ruleUNDISCH_ALL: exhaustive warning."

{-|@
 A1 |- t1 ==> t2     A2 |- t2 ==> t1
-------------------------------------
        A1 U A2 |- t1 \<=\> t2
@

  Throws a 'HOLException' if the conclusions of the provided theorems are not
  complimentary implications.
-}
ruleIMP_ANTISYM :: BoolCtxt thry => HOLThm -> HOLThm -> HOL cls thry HOLThm
ruleIMP_ANTISYM thm1 thm2 = 
    (do th1 <- ruleUNDISCH thm1
        th2 <- ruleUNDISCH thm2
        return $! primDEDUCT_ANTISYM th2 th1)
    <?> "ruleIMP_ANTISYM"

{-|@
  s   A |- t
--------------
  A U s |- t
@

  Throws a 'HOLException' if the provided term is not a proposition.
-}
ruleADD_ASSUM :: BoolCtxt thry => HOLTerm -> HOLThm -> HOL cls thry HOLThm
ruleADD_ASSUM tm thm =
    (do th <- ruleDISCH tm thm
        ruleMP th #<< primASSUME tm)
    <?> "ruleADD_ASSUM"

{-|@
           A |- t1 \<=\> t2
-----------------------------------
  (A |- t1 ==> t2, A |- t2 ==> t1)
@

  Throws a 'HOLException' if the conclusion of the theorem is not biconditional.
-}
ruleEQ_IMP :: (BoolCtxt thry, HOLThmRep thm cls thry) => thm 
           -> HOL cls thry (HOLThm, HOLThm)
ruleEQ_IMP pthm = 
    (do p <- serve [bool| p:bool |]
        q <- serve [bool| q:bool |]
        pth1 <- ruleEQ_IMP_pth1
        pth2 <- ruleEQ_IMP_pth2
        thm <- toHThm pthm
        let (l, r) = fromJust . destEq $ concl thm
            (pth1', pth2') = fromJust $ pairMapM (primINST [(p, l), (q, r)])
                                          (pth1, pth2)
        thm1 <- ruleMP pth1' thm
        thm2 <- ruleMP pth2' thm
        return (thm1, thm2))
    <?> "ruleEQ_IMP"
  where ruleEQ_IMP_pth1 :: BoolCtxt thry => HOL cls thry HOLThm
        ruleEQ_IMP_pth1 = cacheProof "ruleEQ_IMP_pth1" ctxtBool $
            do peq <- toHTm "p <=> q"
               let (p, _) = fromJust $ destEq peq
                   peqthm = fromRight $ primASSUME peq
               ruleDISCH peq =<< ruleDISCH p #<< 
                 primEQ_MP peqthm =<< primASSUME p

        ruleEQ_IMP_pth2 :: BoolCtxt thry => HOL cls thry HOLThm
        ruleEQ_IMP_pth2 = cacheProof "ruleEQ_IMP_pth2" ctxtBool $
            do peq <- toHTm "p <=> q"
               let (_, q) = fromJust $ destEq peq
                   peqthm = fromRight $ primASSUME peq
               ruleDISCH peq =<< ruleDISCH q #<< 
                 liftM1 primEQ_MP (ruleSYM peqthm) =<< primASSUME q

{-|@
 A1 |- t1 ==> t2   A2 |- t2 ==> t3
-----------------------------------
       A1 U A2 |- t1 ==> t3        
@

  Throws a 'HOLException' in the following cases:

  * The conclusions of the theorems are not implications.

  * The implications are not transitive.
-}
ruleIMP_TRANS :: BoolCtxt thry => HOLThm -> HOLThm -> HOL cls thry HOLThm
ruleIMP_TRANS thm1@(Thm _ imp1) thm2@(Thm _ imp2) = noteHOL "ruleIMP_TRANS" $
    do p <- serve [bool| p:bool |]
       q <- serve [bool| q:bool |]
       r <- serve [bool| r:bool |]
       pth <- ruleIMP_TRANS_pth
       case (destImp imp1, destImp imp2) of
         (Just (x, y), Just (y', z))
             | y /= y' -> fail "implications are not transitive."
             | otherwise -> 
                   let pth' = fromJust $ 
                                primINST [(p, x), (q, y), (r, z)] pth in
                     ruleMP (ruleMP pth' thm1) thm2
         _ -> fail "conclusions are not implications."
  where ruleIMP_TRANS_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleIMP_TRANS_pth = cacheProof "ruleIMP_TRANS_pth" ctxtBool $
            do pq <- toHTm "p ==> q"
               qr <- toHTm "q ==> r"
               p <- toHTm "p:bool"
               let qrth = fromRight $ primASSUME qr
                   pqth = fromRight $ primASSUME pq
               mpth <- ruleMP qrth =<< ruleMP pqth #<< primASSUME p
               foldrM ruleDISCH mpth [pq, qr, p]
ruleIMP_TRANS _ _ = error "ruleIMP_TRANS: exhaustive warning."


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
ruleSPEC :: (BoolCtxt thry, HOLTermRep tm cls thry, HOLThmRep thm cls thry) => 
            tm -> thm -> HOL cls thry HOLThm
ruleSPEC t = liftM1 ruleSPEC' (toHTm t) <=< toHThm
  where ruleSPEC' :: BoolCtxt thry => HOLTerm -> HOLThm -> HOL cls thry HOLThm
        ruleSPEC' tm thm@(Thm _ ab) = noteHOL "ruleSPEC" $
            do p <- serve [bool| P:A->bool |]
               x <- serve [bool| x:A |]
               pth <- ruleSPEC_pth
               (ab', bvty) <- liftMaybe "conclusion not quantified." $ 
                              do ab' <- rand ab
                                 bvty <- liftM snd $ destVar =<< bndvar ab'
                                 return (ab', bvty)
               let pth' = fromJust $ 
                            rulePINST [(tyA, bvty)] [(p, ab'), (x, tm)] pth
               (ruleCONV convBETA =<< ruleMP pth' thm) <?> "types do not agree."
        ruleSPEC' _ _ = error "ruleSPEC: exhaustive warning."
  
        ruleSPEC_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleSPEC_pth = cacheProof "ruleSPEC_pth" ctxtBool $
            do p <- toHTm "P:A->bool"
               x <- toHTm "x:A"
               forallP <- toHTm "(!)(P:A->bool)"
               dForall <- defFORALL
               let th1 = fromRight $ ruleAP_THM dForall p
               th2 <- ruleCONV convBETA #<< 
                        primEQ_MP th1 =<< primASSUME forallP
               th3 <- ruleCONV (convRAND convBETA) #<< ruleAP_THM th2 x
               ruleDISCH_ALL =<< ruleEQT_ELIM th3


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
ruleSPECL tms pthm = noteHOL "ruleSPECL" $
    do thm <- toHThm pthm
       foldlM (flip ruleSPEC) thm =<< mapM toHTm tms
                                 
{-|@
     A |- !x. t       
--------------------
 (x', A |- t[x'\/x])
@
  
  Applies 'ruleSPEC' using a 'variant' of the bound term, failing accordingly.
-}
ruleSPEC_VAR :: BoolCtxt thry => HOLThm -> HOL cls thry (HOLTerm, HOLThm)
ruleSPEC_VAR thm@(Thm _ x) =
    (let v = fromJust $ bndvar =<< rand x
         bv = variant (thmFrees thm) v in
       do thm' <- ruleSPEC bv thm
          return (bv, thm'))
    <?> "ruleSPEC_VAR: conclusion not quantified."
ruleSPEC_VAR _ = error "ruleSPEC_VAR: exhaustive warning."

{-|@
        A |- !x1 ... xn. t
----------------------------------
 A |- t[x1', ..., xn'\/x1, ..., xn]
@

  Never fails, but may have no effect.
-}
ruleSPEC_ALL :: (BoolCtxt thry, HOLThmRep thm cls thry) => thm 
             -> HOL cls thry HOLThm
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
ruleISPEC :: (BoolCtxt thry, HOLTermRep tm cls thry, 
              HOLThmRep thm cls thry) => tm -> thm 
          -> HOL cls thry HOLThm
ruleISPEC ptm pthm = noteHOL "ruleISPEC" $
    do thm@(Thm _ x) <- toHThm pthm
       tm <- toHTm ptm
       case destForall x of
         Just (Var _ ty, _) -> 
             do tyenv <- liftMaybe "can't instantiate theorem." $
                           typeMatch ty (typeOf tm) ([], [], [])
                ruleSPEC tm (primINST_TYPE_FULL tyenv thm) <?> 
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
ruleISPECL ptms pthm = noteHOL "ruleISPECL" $
    do tms <- mapM toHTm ptms
       thm@(Thm _ x) <- toHThm pthm
       let (vs, _) = stripForall x
       (avs, _) <- liftMaybe "instantiation list too long." $
                     chopList (length tms) vs
       tyenv <- liftMaybe "can't instantiate theorem." $
                  foldr2M tyFun ([], [], []) avs $ map typeOf tms
       ruleSPECL tms (primINST_TYPE_FULL tyenv thm) <?>
         "type variable(s) free in assumption list."
  where tyFun :: HOLTerm -> HOLType -> SubstTrip -> Maybe SubstTrip
        tyFun (Var _ ty1) ty2 acc = typeMatch ty1 ty2 acc
        tyFun _ _ _ = Nothing

{-|@
 x   A |- t  
------------
 A |- !x. t
@

  Throws a 'HOLException' in the following cases:

  * The provided term is not a variable.

  * The provided term is free in the assumption list of the provided theorem.
-}      
ruleGEN :: (BoolCtxt thry, HOLTermRep tm cls thry, HOLThmRep thm cls thry) => tm
        -> thm -> HOL cls thry HOLThm
ruleGEN tm thm = liftM1 ruleGEN' (toHTm tm) =<< toHThm thm
  where ruleGEN' :: BoolCtxt thry => HOLTerm -> HOLThm -> HOL cls thry HOLThm
        ruleGEN' x@(Var _ tyx) th = noteHOL "ruleGEN" $
            do qth <- liftM (primINST_TYPE [(tyA, tyx)]) $ ruleGEN_pth
               let ptm = fromJust $ rand =<< rand (concl qth)
               th1 <- ruleEQT_INTRO th
               th2 <- liftO (primABS x th1) <?> 
                        "term free in the assumption list."
               let phi = fromJust . lHand $ concl th2
                   qth' = fromJust $ primINST [(ptm, phi)] qth
               liftO $ primEQ_MP qth' th2
        ruleGEN' _ _ = fail "ruleGEN: term not a variable"
  
        ruleGEN_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleGEN_pth = cacheProof "ruleGEN_pth" ctxtBool $
            do p <- toHTm "P:A->bool"
               dForall <- defFORALL
               th <- ruleCONV (convRAND convBETA) #<< ruleAP_THM dForall p
               liftO $ ruleSYM th


{-|@
 [x1, ..., xn]     A |- t
--------------------------
    A |- !x1 ... xn. t
@

  Throws a 'HOLException' in the following cases:

  * Any of the provided terms are not a variable.

  * Any of the provided terms are free in the assumption list.
-}
ruleGENL :: (BoolCtxt thry, HOLTermRep tm cls thry, HOLThmRep thm cls thry) => 
            [tm] -> thm -> HOL cls thry HOLThm
ruleGENL tms th = noteHOL "ruleGENL" $
    liftM1 (foldrM ruleGEN) (toHThm th) tms

{-|@
       A |- t
--------------------
 A |- !x1 ... xn. t
@

  Never fails, but may have no effect.
-}
ruleGEN_ALL :: (BoolCtxt thry, HOLThmRep thm cls thry) => thm 
            -> HOL cls thry HOLThm
ruleGEN_ALL thm =
    do thm'@(Thm asl c) <- toHThm thm 
       let vars = frees c \\ catFrees asl in
         ruleGENL vars thm'


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
ruleEXISTS :: BoolCtxt thry => HOLTerm -> HOLTerm -> HOLThm 
           -> HOL cls thry HOLThm
ruleEXISTS (Comb _ ab) stm thm = 
    (do p <- serve [bool| P:A->bool |]
        x <- serve [bool| x:A |]
        pth <- ruleEXISTS_pth
        th1 <- runConv convBETA #<< mkComb ab stm
        let pth' = fromJust $ 
                     rulePINST [(tyA, typeOf stm)] [(p, ab), (x, stm)] pth
            th2 = fromRight $ liftM1 primEQ_MP (ruleSYM th1) thm
        return $ rulePROVE_HYP th2 pth')
    <?> "ruleEXISTS: witness does not match provided theorem."
  where ruleEXISTS_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleEXISTS_pth = cacheProof "ruleEXISTS_pth" ctxtBool $
            do p <- toHTm "P:A->bool"
               pX <- toHTm "(P:A->bool) x"
               fx <- toHTm "!x:A. P x ==> Q"
               dExists <- defEXISTS
               th1 <- ruleCONV (convRAND convBETA) #<< ruleAP_THM dExists p
               th2 <- ruleSPEC "x:A" #<< primASSUME fx
               th3 <- ruleDISCH fx =<< ruleMP th2 #<< primASSUME pX
               th4 <- ruleGEN "Q:bool" th3
               liftO $ liftM1 primEQ_MP (ruleSYM th1) th4
ruleEXISTS _ _ _ = fail "ruleEXISTS: conclusion not existentially quantified."

{-|@
 u   A |- p   
-------------
 A |- ?u. p
@

  Throws a 'HOLException' if the provided term is not a variable.
-}
ruleSIMPLE_EXISTS :: BoolCtxt thry => HOLTerm -> HOLThm -> HOL cls thry HOLThm
ruleSIMPLE_EXISTS v thm@(Thm _ p) = 
    (do v' <- mkExists v p
        ruleEXISTS v' v thm) <?> "ruleSIMPLE_EXISTS"
ruleSIMPLE_EXISTS _ _ = error "ruleSIMPLE_EXISTS: exhaustive warning."


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
ruleCHOOSE :: BoolCtxt thry => HOLTerm -> HOLThm -> HOLThm 
           -> HOL cls thry HOLThm
ruleCHOOSE v@(Var _ vty) thm1 thm2 = noteHOL "ruleCHOOSE" $
    do p <- serve [bool| P:A->bool |]
       q <- serve [bool| Q:bool |]
       pth <- ruleCHOOSE_pth
       case rand $ concl thm1 of
         Just ab@(Abs bv bod) -> 
             (let cmb = fromRight $ mkComb ab v
                  pat = fromJust $ varSubst [(bv, v)] bod in
                do thm3 <- ruleCONV convBETA #<< primASSUME cmb
                   thm4 <- ruleGEN v =<< ruleDISCH cmb =<< 
                             ruleMP (ruleDISCH pat thm2) thm3
                   let thm5 = fromJust $ rulePINST [(tyA, vty)] 
                                           [(p, ab), (q, concl thm2)] pth
                   ruleMP (ruleMP thm5 thm4) thm1) 
             <?> "provided term is free in resultant theorem."
         _ -> fail "conclustion not existentially quantified."
  where ruleCHOOSE_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleCHOOSE_pth = cacheProof "ruleCHOOSE_pth" ctxtBool $
            do p <- toHTm "P:A->bool"
               dExists <- defEXISTS
               th1 <- ruleCONV (convRAND convBETA) #<< ruleAP_THM dExists p
               (th2, _) <- ruleEQ_IMP th1
               th3 <- ruleSPEC "Q:bool" =<< ruleUNDISCH th2
               ruleDISCH_ALL =<< ruleDISCH "(?) (P:A->bool)" =<< 
                 ruleUNDISCH th3
ruleCHOOSE _ _ _ = fail "ruleCHOOSE: provided term not a variable."

{-|@
  v    [a1, ..., an] |- t  
---------------------------
   [?v. a1 ... an] |- t
@

  Throws a 'HOLException' in the following cases:

  * The provided term is not a variable.

  * The provided term is free in the conclusion of the provided theorem.
-}
ruleSIMPLE_CHOOSE :: BoolCtxt thry => HOLTerm -> HOLThm -> HOL cls thry HOLThm
ruleSIMPLE_CHOOSE v thm@(Thm a c)
    | v `freeIn` c = fail "ruleSIMPLE_CHOOSE: provided term free in conclusion."
    | otherwise = noteHOL "ruleSIMPLE_CHOOSE" $
          do v' <- mkExists v (head a) <?> "provided term not a variable." 
             ruleCHOOSE v (fromRight $ primASSUME v') thm
ruleSIMPLE_CHOOSE _ _ = error "ruleSIMPLE_CHOOSE: exhaustive warning."


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
ruleDISJ1 :: BoolCtxt thry => HOLThm -> HOLTerm -> HOL cls thry HOLThm
ruleDISJ1 th tm = 
    (do p <- serve [bool| P:bool |]
        q <- serve [bool| Q:bool |]
        pth <- ruleDISJ1_pth
        liftO . liftM (rulePROVE_HYP th) $ 
          primINST [(p, concl th), (q, tm)] pth)
    <?> "ruleDISJ1"
  where ruleDISJ1_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleDISJ1_pth = cacheProof "ruleDISJ1_pth" ctxtBool $
            do p <- toHTm "P:bool"
               q <- toHTm "Q:bool"
               pit <- toHTm "P ==> t"
               dOr <- defOR
               th1 <- ruleCONV (convRAND convBETA) #<< ruleAP_THM dOr p
               th2 <- ruleCONV (convRAND convBETA) #<< ruleAP_THM th1 q
               th3 <- ruleMP (fromRight $ primASSUME pit) #<< primASSUME p
               th4 <- ruleGEN "t:bool" =<< ruleDISCH pit =<< 
                        ruleDISCH "Q ==> t" th3
               liftO $ liftM1 primEQ_MP (ruleSYM th2) th4

{-|@
  t1   A |- t2   
----------------
 A |- t1 \\/ t2
@

  Throws a 'HOLException' if the provided term is not a proposition.
-}
ruleDISJ2 :: BoolCtxt thry => HOLTerm -> HOLThm -> HOL cls thry HOLThm
ruleDISJ2 tm th = 
    (do p <- serve [bool| P:bool |]
        q <- serve [bool| Q:bool |]
        pth <- ruleDISJ2_pth
        liftO . liftM (rulePROVE_HYP th) $ 
          primINST [(p, tm), (q, concl th)] pth)
    <?> "ruleDISJ2"
  where ruleDISJ2_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleDISJ2_pth = cacheProof "ruleDISJ2_pth" ctxtBool $
            do p <- toHTm "P:bool"
               q <- toHTm "Q:bool"
               qit <- toHTm "Q ==> t"
               dOr <- defOR
               th1 <- ruleCONV (convRAND convBETA) #<< ruleAP_THM dOr p
               th2 <- ruleCONV (convRAND convBETA) #<< ruleAP_THM th1 q
               th3 <- ruleMP (fromRight $ primASSUME qit) #<< primASSUME q
               th4 <- ruleGEN "t:bool" =<< ruleDISCH "P ==> t" =<< 
                        ruleDISCH qit th3
               liftO $ liftM1 primEQ_MP (ruleSYM th2) th4


{-|@
   A |- t1 \\/ t2     A1 |- t      A2 |- t     
---------------------------------------------
      A U (A1 - t1) U (A2 - t2) |- t
@

  Throws a 'HOLException' in the following cases:

  * The conclusion of the first provided theorem is not a disjunction.

  * The conclusions of the last two provided theorems are not alpha-equivalent.
-}
ruleDISJ_CASES :: BoolCtxt thry => HOLThm -> HOLThm -> HOLThm 
               -> HOL cls thry HOLThm
ruleDISJ_CASES th0 th1@(Thm _ c1) th2@(Thm _ c2)
    | not $ c1 `aConv` c2 = fail "ruleDISJ_CASES: conclusions not equivalent."
    | otherwise =
      do p <- serve [bool| P:bool |]
         q <- serve [bool| Q:bool |]
         r <- serve [bool| R:bool |]
         pth <- ruleDISJ_CASES_pth
         (l0, r0) <- liftMaybe "ruleDISJ_CASES: conclusion not a disjunction." $
                       destDisj $ concl th0
         dth1 <- ruleDISCH r0 th2
         dth2 <- ruleDISCH l0 th1
         liftO . liftM (rulePROVE_HYP dth1 . rulePROVE_HYP dth2 . 
           rulePROVE_HYP th0) $ primINST [(p, l0), (q, r0), (r, c1)] pth
  where ruleDISJ_CASES_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleDISJ_CASES_pth = cacheProof "ruleDISJ_CASES_pth" ctxtBool $
            do p <- toHTm "P:bool"
               q <- toHTm "Q:bool"
               pOrQ <- toHTm [str| P \/ Q |]
               dOr <- defOR
               thm1 <- ruleCONV (convRAND convBETA) #<< ruleAP_THM dOr p
               thm2 <- ruleCONV (convRAND convBETA) #<< ruleAP_THM thm1 q
               thm3 <- ruleSPEC "R:bool" #<< primEQ_MP thm2 =<< primASSUME pOrQ
               ruleUNDISCH =<< ruleUNDISCH thm3
ruleDISJ_CASES _ _ _ = error "ruleDISJ_CASES: exhaustive warning."


{-|@
     [p1, ..., pn] |- r    [q1, ..., qn] |- r       
--------------------------------------------------
 (p1 \\/ q1) U [p2, ..., pn] U [q2, ..., qn] |- r
@

  Throws a 'HOLException' when the conclusions of the provided theorems are
  not alpha-equivalent.
-}
ruleSIMPLE_DISJ_CASES :: BoolCtxt thry => HOLThm -> HOLThm 
                      -> HOL cls thry HOLThm
ruleSIMPLE_DISJ_CASES th1@(Thm l _) th2@(Thm r _) = 
    (do tm <- mkDisj (head l) (head r)
        ruleDISJ_CASES (fromRight $ primASSUME tm) th1 th2)
    <?> "ruleSIMPLE_DISJ_CASES"
ruleSIMPLE_DISJ_CASES _ _ = error "ruleSIMPLE_DISJ_CASE: exhaustive warning."


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
ruleNOT_ELIM :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleNOT_ELIM th@(Thm _ tm) =
    (do p <- serve [bool| P:bool |]
        pth <- ruleNOT_ELIM_pth
        let tm' = fromJust $ rand tm
            pth' = fromJust $ primINST [(p, tm')] pth
        liftO $ primEQ_MP pth' th)
    <?> "ruleNOT_ELIM"
  where ruleNOT_ELIM_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleNOT_ELIM_pth = cacheProof "ruleNOT_ELIM_pth" ctxtBool $
            do dnot <- defNOT
               p <- toHTm "P:bool"
               ruleCONV (convRAND convBETA) #<< ruleAP_THM dnot p
ruleNOT_ELIM _ = error "ruleNOT_ELIM: exhaustive warning."

{-|@
 A |- t ==> F
--------------
   A |- ~t
@

  Throws a 'HOLException' if the conclusion of the provided theorem is not of
  the form @tm ==> F@.
-}
ruleNOT_INTRO :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleNOT_INTRO th@(Thm _ tm) =
    (do p <- serve [bool| P:bool |]
        pth <- ruleNOT_INTRO_pth
        let tm' = fromJust $ rand =<< rator tm
            pth' = fromJust $ primINST [(p, tm')] pth
        liftO $ primEQ_MP pth' th)
    <?> "ruleNOT_INTO"
  where ruleNOT_INTRO_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleNOT_INTRO_pth = cacheProof "ruleNOT_INTRO_pth" ctxtBool $
            do dnot <- defNOT
               p <- toHTm "P:bool"
               th1 <- ruleCONV (convRAND convBETA) #<< ruleAP_THM dnot p
               liftO $ ruleSYM th1
ruleNOT_INTRO _ = error "ruleNOT_INTRO: exhaustive warning."


{-|@
  A |- ~t
---------------
 A |- t \<=\> F
@

  Throws a 'HOLException' if the conclusion of the provided theorem is not a
  negation.
-}
ruleEQF_INTRO :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleEQF_INTRO th = 
    (do p <- serve [bool| P:bool |]
        pth <- ruleEQF_INTRO_pth
        let tm = fromJust . rand $ concl th
            pth' = fromJust $ primINST [(p, tm)] pth
        ruleMP pth' th) 
    <?> "ruleEQF_INTRO"
  where ruleEQF_INTRO_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleEQF_INTRO_pth = cacheProof "ruleEQF_INTRO_pth" ctxtBool $
            do notP <- toHTm "~P"
               f <- toHTm "F"
               dFalse <- defFALSE
               th1 <- ruleNOT_ELIM #<< primASSUME notP
               th2 <- ruleDISCH f =<< ruleSPEC "P:bool" #<< 
                        primEQ_MP dFalse =<< primASSUME f
               ruleDISCH_ALL =<< ruleIMP_ANTISYM th1 th2

{-|@
 A |- t \<=\> F
---------------
   A |- ~t
@

  Throws a 'HOLException' if the conclusion of the provided theorem is not of 
  the form @tm \<=\> F@.
-}
ruleEQF_ELIM :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleEQF_ELIM th = 
    (do p <- serve [bool| P:bool |]
        pth <- ruleEQF_ELIM_pth
        let tm = fromJust $ rand =<< rator (concl th)
            pth' = fromJust $ primINST [(p, tm)] pth
        ruleMP pth' th) 
    <?> "ruleEQF_ELIM"
  where ruleEQF_ELIM_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleEQF_ELIM_pth = cacheProof "ruleEQF_ELIM_pth" ctxtBool $
            do p <- toHTm "P:bool"
               pEqF <- toHTm "P = F"
               dFalse <- defFALSE
               let th1 = fromRight $ primEQ_MP dFalse =<< 
                           liftM1 primEQ_MP (primASSUME pEqF) =<< primASSUME p
               ruleDISCH_ALL =<< ruleNOT_INTRO =<< ruleDISCH p =<< 
                 ruleSPEC "F" th1

{-|@
  t   A |- F
-------------
   A |- t
@

  Throws a 'HOLException' in the following cases:

  * The provided term is not a proposition.

  * The conclusion of the provided theorem is not @F@.
-}
ruleCONTR :: BoolCtxt thry => HOLTerm -> HOLThm -> HOL cls thry HOLThm
ruleCONTR tm th = noteHOL "ruleCONTR" $
    do f <- serve [bool| F |]
       if concl th /= f
          then fail "conclusion of theorem not false."
          else do p <- serve [bool| P:bool |]
                  pth <- ruleCONTR_pth
                  liftO . liftM (rulePROVE_HYP th) $ primINST [(p, tm)] pth
  where ruleCONTR_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleCONTR_pth = cacheProof "ruleCONTR_pth" ctxtBool $
            do f <- toHTm "F"
               dFalse <- defFALSE
               ruleSPEC "P:bool" #<< primEQ_MP dFalse #<< primASSUME f

{-|@
  A |- ?!x. p
---------------
  A |- ?x. p
@

  Throws a 'HOLException' when the conclusion of the provided theorem is not
  unique-existentially quantified.
-}
ruleEXISTENCE :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleEXISTENCE th =
    (do p <- serve [bool| P:A->bool |]
        pth <- ruleEXISTENCE_pth
        let ab = fromJust . rand $ concl th
            ty = snd . fromJust $ destVar =<< bndvar ab
            pth' = fromJust $ rulePINST [(tyA, ty)] [(p, ab)] pth
        ruleMP pth' th)
    <?> "ruleEXISTENCE"
  where ruleEXISTENCE_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleEXISTENCE_pth = cacheProof "ruleEXISTENCE_pth" ctxtBool $
            do p <- toHTm "P:A->bool"
               dEU <- defEXISTS_UNIQUE
               th1 <- ruleCONV (convRAND convBETA) #<< ruleAP_THM dEU p
               th2 <- ruleUNDISCH =<< liftM fst (ruleEQ_IMP th1)
               ruleDISCH_ALL =<< ruleCONJUNCT1 th2

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
