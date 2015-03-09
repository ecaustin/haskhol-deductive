{-# LANGUAGE ImplicitParams, PatternSynonyms, ScopedTypeVariables #-}
{-|
  Module:    HaskHOL.Lib.Canon
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Canon
    ( convPRESIMP
    , ruleCONJ_ACI
    , convSKOLEM
    , convPRENEX
    , convCONDS_ELIM
    , convCONDS_CELIM
    , convWEAK_DNF
    , convWEAK_CNF
    , convASSOC
    , tacASM_FOL
    , convLAMBDA_ELIM
    , tacSELECT_ELIM
    , convGEN_NNF
    , convNNF
    , convNNFC
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Bool
import HaskHOL.Lib.Classic
import HaskHOL.Lib.Equal
import HaskHOL.Lib.IndDefs
import HaskHOL.Lib.Theorems
import HaskHOL.Lib.Simp
import HaskHOL.Lib.DRule
import HaskHOL.Lib.Tactics
import HaskHOL.Lib.Trivia
import HaskHOL.Lib.Trivia.Context


pthNotNot :: TriviaCtxt thry => HOL cls thry HOLThm
pthNotNot = cacheProof "pthNotNot" ctxtTrivia $ 
    ruleTAUT "~ ~ p = p"

pthNotAnd :: TriviaCtxt thry => HOL cls thry HOLThm
pthNotAnd = cacheProof "pthNotAnd" ctxtTrivia $ 
    ruleTAUT [str| ~(p /\ q) <=> ~p \/ ~q |]

pthNotOr :: TriviaCtxt thry => HOL cls thry HOLThm
pthNotOr = cacheProof "pthNotOr" ctxtTrivia $ 
    ruleTAUT [str| ~(p \/ q) <=> ~p /\ ~q |]

pthImp :: TriviaCtxt thry => HOL cls thry HOLThm
pthImp = cacheProof "pthImp" ctxtTrivia $ 
    ruleTAUT [str| p ==> q <=> ~p \/ q |]

pthNotImp :: TriviaCtxt thry => HOL cls thry HOLThm
pthNotImp = cacheProof "pthNotImp" ctxtTrivia $ 
    ruleTAUT [str| ~(p ==> q) <=> p /\ ~q |]

pthEq :: TriviaCtxt thry => HOL cls thry HOLThm
pthEq = cacheProof "pthEq" ctxtTrivia $ 
    ruleTAUT [str| (p <=> q) <=> p /\ q \/ ~p /\ ~q |]

pthNotEq :: TriviaCtxt thry => HOL cls thry HOLThm
pthNotEq = cacheProof "pthNotEq" ctxtTrivia $ 
    ruleTAUT [str| ~(p <=> q) <=> p /\ ~q \/ ~p /\ q |]

pthEq' :: TriviaCtxt thry => HOL cls thry HOLThm
pthEq' = cacheProof "pthEq'" ctxtTrivia $ 
    ruleTAUT [str| (p <=> q) <=> (p \/ ~q) /\ (~p \/ q) |]

pthNotEq' :: TriviaCtxt thry => HOL cls thry HOLThm
pthNotEq' = cacheProof "pthNotEq'" ctxtTrivia $ 
    ruleTAUT [str| ~(p <=> q) <=> (p \/ q) /\ (~p \/ ~q) |]

pthNots :: TriviaCtxt thry => [HOL cls thry HOLThm]
pthNots =
    cacheProofs ["pthNotForall", "pthNotExists", "pthNotExu"] ctxtTrivia $
      ruleCONJUNCTS =<< 
        prove [str| (~((!) P) <=> ?x:A. ~(P x)) /\
                    (~((?) P) <=> !x:A. ~(P x)) /\
                    (~((?!) P) <=> (!x:A. ~(P x)) \/ 
                    ?x y. P x /\ P y /\ ~(y = x)) |]
          (_REPEAT tacCONJ `_THEN`
           tacGEN_REWRITE (convLAND . 
                           funpow 2 convRAND) [ruleGSYM axETA] `_THEN`
           tacREWRITE [ thmNOT_EXISTS, thmNOT_FORALL, defEXISTS_UNIQUE
                      , thmDE_MORGAN, thmNOT_IMP ] `_THEN`
           tacREWRITE [thmCONJ_ASSOC, thmEQ_SYM_EQ])

pthNotForall :: TriviaCtxt thry => HOL cls thry HOLThm
pthNotForall = pthNots !! 0

pthNotExists :: TriviaCtxt thry => HOL cls thry HOLThm
pthNotExists = pthNots !! 1

pthNotExu :: TriviaCtxt thry => HOL cls thry HOLThm
pthNotExu = pthNots !! 2

pthExu :: TriviaCtxt thry => HOL cls thry HOLThm
pthExu = cacheProof "pthExu" ctxtTrivia $
    prove [str| ((?!) P) <=> (?x:A. P x) /\ 
                !x y. ~(P x) \/ ~(P y) \/ (y = x) |] $
      tacGEN_REWRITE (convLAND . convRAND) [ruleGSYM axETA] `_THEN`
      tacREWRITE [ defEXISTS_UNIQUE
                 , ruleTAUT [str| a /\ b ==> c <=> ~a \/ ~b \/ c |] ] `_THEN`
      tacREWRITE [thmEQ_SYM_EQ]

convPRESIMP :: ClassicCtxt thry => Conversion cls thry 
convPRESIMP = Conv $ \ tm ->
    let ths = [ thmNOT_CLAUSES, thmAND_CLAUSES, thmOR_CLAUSES
              , thmIMP_CLAUSES, thmEQ_CLAUSES, thmFORALL_SIMP 
              , thmEXISTS_SIMP, thmEXISTS_OR, thmFORALL_AND 
              , thmLEFT_EXISTS_AND, thmRIGHT_EXISTS_AND 
              , thmLEFT_FORALL_OR, thmRIGHT_FORALL_OR
              ] in
      runConv (convGEN_REWRITE convTOP_DEPTH ths) tm

ruleCONJ_ACI :: BoolCtxt thry => HOLTerm -> HOL cls thry HOLThm
ruleCONJ_ACI fm =
    let (p, p') = fromJust $ destEq fm in
      if p == p' then return $! primREFL p
      else do th <- useFun p' =<< mkFun funcEmpty #<< primASSUME p
              th' <- useFun p =<< mkFun funcEmpty #<< primASSUME p'
              liftM1 ruleIMP_ANTISYM (ruleDISCH_ALL th) =<< ruleDISCH_ALL th'
  where useFun :: BoolCtxt thry => HOLTerm -> Func HOLTerm HOLThm
               -> HOL cls thry HOLThm
        useFun tm fn
            | isConj tm =
                let (l, r) = fromJust $ destConj tm in
                  do l' <- useFun l fn
                     ruleCONJ l' =<< useFun r fn
            | otherwise = liftO $ apply fn tm

        mkFun :: BoolCtxt thry => Func HOLTerm HOLThm -> HOLThm 
              -> HOL cls thry (Func HOLTerm HOLThm)
        mkFun fn th =
            let tm = concl th in
              if isConj tm 
              then do (th1, th2) <- ruleCONJ_PAIR th
                      flip mkFun th1 =<< mkFun fn th2
              else return $! (tm |-> th) fn


convSKOLEM :: ClassicCtxt thry => Conversion cls thry 
convSKOLEM = Conv $ \ tm ->
    let ths1 = [ thmEXISTS_OR, thmLEFT_EXISTS_AND
               , thmRIGHT_EXISTS_AND, thmFORALL_AND 
               , thmLEFT_FORALL_OR, thmRIGHT_FORALL_OR 
               , thmFORALL_SIMP, thmEXISTS_SIMP
               ]
        ths2 = [ thmRIGHT_AND_EXISTS, thmLEFT_AND_EXISTS 
               , thmOR_EXISTS, thmRIGHT_OR_EXISTS 
               , thmLEFT_OR_EXISTS, thmSKOLEM
               ] in
      runConv (convGEN_REWRITE convTOP_DEPTH ths1 `_THEN`
               convGEN_REWRITE convREDEPTH ths2) tm


convPRENEX :: ClassicCtxt thry => Conversion cls thry 
convPRENEX = Conv $ \ tm ->
    let ths = [ thmAND_FORALL, thmLEFT_AND_FORALL
              , thmRIGHT_AND_FORALL, thmLEFT_OR_FORALL
              , thmRIGHT_OR_FORALL, thmOR_EXISTS 
              , thmLEFT_OR_EXISTS, thmRIGHT_OR_EXISTS
              , thmLEFT_AND_EXISTS, thmRIGHT_AND_EXISTS
              ] in
      runConv (convGEN_REWRITE convREDEPTH ths) tm



-- eliminate all lambda-terms exception those part of quantifiers

convHALF_MK_ABS :: TriviaCtxt thry => [HOLTerm] -> Conversion cls thry 
convHALF_MK_ABS = conv
    where conv [] = _ALL
          conv (_:vs) = convGEN_REWRITE id [convHALF_MK_ABS_pth] `_THEN` 
                        convBINDER (conv vs)
        
          convHALF_MK_ABS_pth :: TriviaCtxt thry => HOL cls thry HOLThm
          convHALF_MK_ABS_pth = cacheProof "convHALF_MK_ABS_pth" ctxtTrivia $
              prove [str| (s = \x. t x) <=> (!x. s x = t x) |] $
                tacREWRITE [thmFUN_EQ]

findLambda :: HOLTerm -> Maybe HOLTerm
findLambda tm@( Abs{}) = Just tm
findLambda ( Var{}) = Nothing
findLambda ( Const{}) = Nothing
findLambda tm = 
    if isForall tm || isExists tm || isUExists tm
    then findLambda =<< body =<< rand tm
    else case tm of
           (Comb l r) -> case findLambda l of
                           Nothing -> findLambda r
                           res@Just{} -> res
           _ -> Nothing

elimLambda :: Conversion cls thry -> Conversion cls thry 
elimLambda conv = Conv $ \ tm ->
    runConv conv tm <|> 
    (if isAbs tm then runConv (convABS $ elimLambda conv) tm
     else if isVar tm ||  isConst tm then return $! primREFL tm
          else if isForall tm || isExists tm || isUExists tm
               then runConv (convBINDER $ elimLambda conv) tm
               else runConv (convCOMB $ elimLambda conv) tm)

applyPTH :: TriviaCtxt thry => HOLThm -> HOL cls thry HOLThm
applyPTH = ruleMATCH_MP applyPTH_pth
  where applyPTH_pth :: TriviaCtxt thry => HOL cls thry HOLThm
        applyPTH_pth = cacheProof "applyPTH_pth" ctxtTrivia $
            prove [str| (!a. (a = c) ==> (P = Q a)) ==> 
                        (P <=> !a. (a = c) ==> Q a) |] $
              tacSIMP [thmLEFT_FORALL_IMP, thmEXISTS_REFL]


convLAMB1 :: TriviaCtxt thry => Conversion cls thry
convLAMB1 = Conv $ \ tm ->
    (case findLambda tm of
       Just atm@( Abs v _) -> 
           let vs = frees atm
               vs' = vs ++ [v] in
             do aatm <- fromRightM $ listMkAbs vs atm
                f <- genVar $ typeOf aatm
                eq <- mkEq f aatm
                th1 <- liftM (fromRight . ruleSYM) $ ruleRIGHT_BETAS vs #<< primASSUME eq
                th2 <- runConv (elimLambda $ convGEN_REWRITE id [th1]) tm
                th3 <- applyPTH =<< ruleGEN f =<< ruleDISCH_ALL th2
                ruleCONV (convRAND . convBINDER . convLAND $ convHALF_MK_ABS vs') th3
       _ -> fail "")
    <?> "convLAMB1"

convLAMBDA_ELIM :: TriviaCtxt thry => Conversion cls thry
convLAMBDA_ELIM = conv
    where conv = Conv $ \ tm -> runConv (convLAMB1 `_THEN` conv) tm
                                 <|> (return $! primREFL tm)

-- eliminate select terms from a goal

selectElimThm :: TriviaCtxt thry => HOLTerm 
              -> HOL cls thry HOLThm
selectElimThm ( Comb ( Const "@" _) atm@( Abs bv _)) =
    do pth <- selectElimThm_pth
       ptm <- serve [trivia| P:A->bool |]
       ruleCONV (convLAND convBETA) #<< 
         rulePINST [(tyA, typeOf bv)] [(ptm, atm)] pth
  where selectElimThm_pth :: TriviaCtxt thry => HOL cls thry HOLThm
        selectElimThm_pth = cacheProof "selectElimThm_pth" ctxtTrivia $
            prove "(P:A->bool)((@) P) <=> (?) P" $
              tacREWRITE [thmEXISTS] `_THEN`
              tacBETA `_THEN`
              tacREFL
selectElimThm _ = fail "selectElimThm: not a select term"

 
convSELECT_ELIM :: TriviaCtxt thry => Conversion cls thry
convSELECT_ELIM = Conv $ \ tm ->
    do ths <- mapM selectElimThm $ findTerms isSelect tm
       runConv (convPURE_REWRITE ths) tm

selectAxThm :: TriviaCtxt thry => HOLTerm -> HOL cls thry HOLThm
selectAxThm ( Comb ( Const "@" _) atm@( Abs bv _)) =
    let fvs = frees atm in
      do pth <- selectAxThm_pth
         ptm <- serve [trivia| P:A->bool |]
         let th1 = fromJust $ rulePINST [(tyA, typeOf bv)] [(ptm, atm)] pth
         th2 <- ruleCONV (convBINDER $ convBINOP convBETA) th1
         ruleGENL fvs th2
  where selectAxThm_pth :: TriviaCtxt thry => HOL cls thry HOLThm
        selectAxThm_pth = cacheProof "selectAxThm_pth" ctxtTrivia $
            ruleISPEC "P:A->bool" axSELECT
selectAxThm _ = fail "selectAxThm: not a select term"

iconvSELECT_ELIM :: TriviaCtxt thry => Conversion cls thry
iconvSELECT_ELIM = Conv $ \ tm ->
    (do t <- fromJustM $ findTerm isSelect tm
        th1 <- selectAxThm t
        itm <- mkImp (concl th1) tm
        ith <- fromRightM $ primASSUME itm
        th2 <- ruleDISCH_ALL =<< ruleMP ith th1
        let fvs = frees t
        fty <- foldrM (mkFunTy . typeOf) (typeOf t) fvs
        fn <- genVar fty
        atm <- fromRightM $ listMkAbs fvs t
        rawdef <- mkEq fn atm
        def <- ruleGENL fvs =<< liftM (fromRight . ruleSYM) (ruleRIGHT_BETAS fvs #<< primASSUME rawdef)
        l <- fromJustM . lHand $ concl th2
        th3 <- runConv (convPURE_REWRITE [def]) l
        r <- fromJustM . rand $ concl th3
        gtm <- mkForall fn r
        th4 <- fromRightM $ ruleSYM th3
        th5 <- ruleSPEC fn #<< primASSUME gtm
        th6 <- fromRightM $ primEQ_MP th4 th5
        th7 <- ruleDISCH gtm th6
        th8 <- ruleIMP_TRANS th7 th2
        th9 <- ruleDISCH rawdef th8
        ruleMP (fromJust $ primINST [(fn, atm)] th9) $ primREFL atm)
    <?> "iconvSELECT_ELIM"

iconvSELECT_ELIMS :: TriviaCtxt thry => Conversion cls thry
iconvSELECT_ELIMS = Conv $ \ tm ->
    (do th <- runConv iconvSELECT_ELIM tm
        tm' <- fromJustM . lHand $ concl th
        th2 <- runConv iconvSELECT_ELIM tm'
        ruleIMP_TRANS th2 th)
    <|> (ruleDISCH tm #<< primASSUME tm)

tacSELECT_ELIM :: TriviaCtxt thry => Tactic cls thry
tacSELECT_ELIM = 
    tacCONV convSELECT_ELIM `_THEN` 
    (\ g@(Goal _ w) -> do th <- runConv iconvSELECT_ELIMS w
                          tacMATCH_MP th g) 

-- eliminate conditionals 
findConditional :: [HOLTerm] -> HOLTerm -> Maybe HOLTerm   
findConditional fvs tm@( Comb s t)
    | isCond tm =
        do freesL <- liftM frees $ lHand s
           if null (freesL `intersect` fvs)
              then return tm
              else findConditional fvs s <|> findConditional fvs t
    | otherwise = findConditional fvs s <|> findConditional fvs t
findConditional fvs ( Abs x t) = findConditional (x:fvs) t
findConditional _ _ = Nothing

condsElimConv :: TriviaCtxt thry => Bool -> Conversion cls thry    
condsElimConv dfl = Conv $ \ tm ->
    (case findConditional [] tm of
       Just t -> 
         do p <- fromJustM $ lHand =<< rator t
            prosimps <- basicNet
            falseTm <- serve [trivia| F |]
            trueTm <- serve [trivia| T |]
            thNew <- if p == falseTm || p == trueTm
                     then runConv (convDEPTH $ convREWRITES prosimps) tm
                     else do asm0 <- mkEq p falseTm
                             ath0 <- fromRightM $ primASSUME asm0
                             asm1 <- mkEq p trueTm
                             ath1 <- fromRightM $ primASSUME asm1
                             simp0 <- liftO $ netOfThm False ath0 prosimps
                             simp1 <- liftO $ netOfThm False ath1 prosimps
                             th0 <- ruleDISCH asm0 =<< runConv (convDEPTH $ convREWRITES simp0) tm
                             th1 <- ruleDISCH asm1 =<< runConv (convDEPTH $ convREWRITES simp1) tm
                             th2 <- ruleCONJ th0 th1
                             th3 <- liftM1 ruleMATCH_MP (if dfl then convCONDS_ELIM_thCond else convCONDS_ELIM_thCond') th2
                             let cnv = _TRY (convREWRITES prosimps)
                                 proptsimpConv = convBINOP cnv `_THEN` cnv
                             rth <- runConv proptsimpConv =<< (fromJustM . rand $ concl th3)
                             fromRightM $ primTRANS th3 rth
            ruleCONV (convRAND $ condsElimConv dfl) thNew
       Nothing
         | isNeg tm ->
             runConv (convRAND . condsElimConv $ not dfl) tm
         | isConj tm || isDisj tm ->
             runConv (convBINOP $ condsElimConv dfl) tm
         | isImp tm || isIff tm ->
             runConv (convCOMB2 (convRAND . condsElimConv $ not dfl)
                       (condsElimConv dfl)) tm
         | isForall tm ->
             runConv (convBINDER $ condsElimConv False) tm
         | isExists tm || isUExists tm ->
             runConv (convBINDER $ condsElimConv True) tm
         | otherwise -> return $! primREFL tm)
    <?> "condsElimConv"
  where convCONDS_ELIM_thCond :: TriviaCtxt thry => HOL cls thry HOLThm
        convCONDS_ELIM_thCond = cacheProof "convCONDS_ELIM_thCond" ctxtTrivia $
            prove [str| ((b <=> F) ==> x = x0) /\ 
                        ((b <=> T) ==> x = x1) ==> 
                        x = (b /\ x1 \/ ~b /\ x0) |] $
              tacBOOL_CASES "b:bool" `_THEN` tacASM_REWRITE_NIL

        convCONDS_ELIM_thCond' :: TriviaCtxt thry => HOL cls thry HOLThm
        convCONDS_ELIM_thCond' = 
            cacheProof "convCONDS_ELIM_thCond'" ctxtTrivia $
              prove [str| ((b <=> F) ==> x = x0) /\ 
                          ((b <=> T) ==> x = x1) ==> 
                          x = ((~b \/ x1) /\ (b \/ x0)) |] $
                tacBOOL_CASES "b:bool" `_THEN` tacASM_REWRITE_NIL


convCONDS_ELIM :: TriviaCtxt thry => Conversion cls thry
convCONDS_ELIM = condsElimConv True

convCONDS_CELIM :: TriviaCtxt thry => Conversion cls thry
convCONDS_CELIM = condsElimConv False

-- Weak DNF
distributeDNF :: TriviaCtxt thry => Conversion cls thry
distributeDNF = Conv $ \ tm ->
    (do tmA <- serve [trivia| a:bool |]
        tmB <- serve [trivia| b:bool |]
        tmC <- serve [trivia| c:bool |]
        case tm of
          (Comb (Comb (Const "/\\" _) a) (Comb (Comb (Const "\\/" _) b) c)) ->
              do pth <- convWEAK_DNF_pth1
                 th <- liftO $ primINST [(tmA, a), (tmB, b), (tmC, c)] pth
                 th' <- runConv (convBINOP distributeDNF) #<< rand (concl th)
                 liftO $ primTRANS th th'
          (Comb (Comb (Const "/\\" _) (Comb (Comb (Const "\\/" _) a) b)) c) ->
              do pth <- convWEAK_DNF_pth2
                 th <- liftO $ primINST [(tmA, a), (tmB, b), (tmC, c)] pth
                 th' <- runConv (convBINOP distributeDNF) #<< rand (concl th)
                 liftO $ primTRANS th th'
          _ -> return $! primREFL tm)
    <?> "distributeDNF"
  where convWEAK_DNF_pth1 :: TriviaCtxt thry => HOL cls thry HOLThm
        convWEAK_DNF_pth1 = cacheProof "convWEAK_DNF_pth1" ctxtTrivia $
            ruleTAUT [str| a /\ (b \/ c) <=> a /\ b \/ a /\ c |]

        convWEAK_DNF_pth2 :: TriviaCtxt thry => HOL cls thry HOLThm
        convWEAK_DNF_pth2 = cacheProof "convWEAK_DNF_pth2" ctxtTrivia $
            ruleTAUT [str| (a \/ b) /\ c <=> a /\ c \/ b /\ c |]

convWEAK_DNF :: TriviaCtxt thry => Conversion cls thry
convWEAK_DNF = Conv $ \ tm ->
    case tm of
      (Comb (Const "!" _) Abs{}) -> runConv (convBINDER convWEAK_DNF) tm
      (Comb (Const "?" _) Abs{}) -> runConv (convBINDER convWEAK_DNF) tm
      (Comb (Comb (Const "\\/" _) _) _) -> runConv (convBINOP convWEAK_DNF) tm
      (Comb (Comb op@(Const "/\\" _) l) r) ->
          do l' <- runConv convWEAK_DNF l
             r' <- runConv convWEAK_DNF r
             th <- liftO $ liftM1 primMK_COMB (ruleAP_TERM op l') r'
             th' <- runConv distributeDNF #<< rand (concl th)
             liftO $ primTRANS th th'
      _ -> return $! primREFL tm

-- Weak CNF
distribute :: TriviaCtxt thry => Conversion cls thry
distribute = Conv $ \ tm ->
    (do aTm <- serve [trivia| a:bool |]
        bTm <- serve [trivia| b:bool |]
        cTm <- serve [trivia| c:bool |]
        case tm of
          (Comb ( Comb ( Const "\\/" _) a) 
           ( Comb ( Comb ( Const "/\\" _) b) c)) ->
              do pth <- distribute_pth1
                 let th = fromJust $ primINST [(aTm, a), (bTm, b), (cTm, c)] pth
                 rth <- runConv (convBINOP distribute) =<< (fromJustM . rand $ concl th)
                 fromRightM $ primTRANS th rth
          (Comb ( Comb ( Const "\\/" _) 
                 ( Comb ( Comb ( Const "/\\" _) a) b)) c) ->
              do pth <- distribute_pth2
                 let th = fromJust $ primINST [(aTm, a), (bTm, b), (cTm, c)] pth
                 rth <- runConv (convBINOP distribute) =<< (fromJustM . rand $ concl th)
                 fromRightM $ primTRANS th rth
          _ -> return $! primREFL tm)
    <?> "distribute"
  where distribute_pth1 :: TriviaCtxt thry => HOL cls thry HOLThm
        distribute_pth1 = cacheProof "distribute_pth1" ctxtTrivia $
            ruleTAUT [str| a \/ (b /\ c) <=> (a \/ b) /\ (a \/ c) |]

        distribute_pth2 :: TriviaCtxt thry => HOL cls thry HOLThm
        distribute_pth2 = cacheProof "distribute_pth2" ctxtTrivia $
            ruleTAUT [str| (a /\ b) \/ c <=> (a \/ c) /\ (b \/ c) |]



convWEAK_CNF :: TriviaCtxt thry => Conversion cls thry
convWEAK_CNF = Conv $ \ tm ->
    (case tm of
       (Comb ( Const "!" _) ( Abs{})) -> runConv (convBINDER convWEAK_CNF) tm
       (Comb ( Const "?" _) ( Abs{})) -> runConv (convBINDER convWEAK_CNF) tm
       (Comb ( Comb ( Const "/\\" _) _) _) -> runConv (convBINOP convWEAK_CNF) tm
       (Comb ( Comb op@( Const "\\/" _) l) r) -> 
           do lth <- runConv convWEAK_CNF l
              rth <- runConv convWEAK_CNF r
              th <- fromRightM $ flip primMK_COMB rth =<< ruleAP_TERM op lth
              rtm <- fromJustM . rand $ concl th
              th2 <- runConv distribute rtm
              fromRightM $ primTRANS th th2
       _ -> return $! primREFL tm)
    <?> "convWEAK_CNF"

distrib :: HOLTerm -> HOLTerm -> HOLTerm -> HOLTerm -> HOLThm -> HOLTerm ->
           Either String HOLThm
distrib op x y z th' tm@( Comb ( Comb op' ( Comb ( Comb op'' p) q)) r)
    | op' == op && op'' == op = 
        (let th1 = fromJust $ primINST [(x, p), (y, q), (z, r)] th' in
           case rand $ concl th1 of
             Just ( Comb l r') -> 
                 do th2 <- ruleAP_TERM l =<< distrib op x y z th' r'
                    rtm <- note "" . rand $ concl th2
                    th3 <- distrib op x y z th' rtm
                    primTRANS th1 =<< primTRANS th2 th3
             _ -> Left "")
        <?> "distrib"
    | otherwise = return $! primREFL tm
distrib _ _ _ _ _ t = return $! primREFL t

canonAssoc :: HOLTerm -> HOLTerm -> HOLTerm -> HOLTerm -> HOLThm -> 
              HOLTerm -> Either String HOLThm
canonAssoc op x y z th' tm@( Comb l@( Comb op' _) q)
    | op' == op =
        (do th <- ruleAP_TERM l =<< canonAssoc op x y z th' q
            r <- note "" . rand $ concl th
            primTRANS th =<< distrib op x y z th' r)
        <?> "canonAssoc"
    | otherwise = return $! primREFL tm
canonAssoc _ _ _ _ _ tm = return $! primREFL tm

convASSOC :: (BoolCtxt thry, HOLThmRep thm cls thry) => thm 
          -> Conversion cls thry
convASSOC th = Conv $ \ tm ->
    (do th' <- liftM (fromRight . ruleSYM) $ ruleSPEC_ALL =<< toHThm th
        case rand $ concl th' of
          Just ( Comb ( Comb op x) yopz) ->
              do y <- fromJustM $ lHand yopz
                 z <- fromJustM $ rand yopz
                 fromRightM $ canonAssoc op x y z th' tm
          _ -> fail "")
    <?> "convASSOC"

getHeads :: [HOLTerm] -> HOLTerm -> ([(HOLTerm, Int)], [(HOLTerm, Int)]) ->
            ([(HOLTerm, Int)], [(HOLTerm, Int)])
getHeads lconsts tm sofar@(cheads, vheads) =
    case destForall tm of
      Just (v, bod) -> getHeads (lconsts \\ [v]) bod sofar
      Nothing -> 
          case destConj tm of
            Just (l, r) -> getHeads lconsts l (getHeads lconsts r sofar)
            Nothing -> 
                case destDisj tm of
                  Just (l, r) -> getHeads lconsts l (getHeads lconsts r sofar)
                  Nothing ->
                      case destNeg tm of
                        Just tm' -> getHeads lconsts tm' sofar
                        Nothing ->
                            let (hop, args) = stripComb tm
                                len = length args
                                newHeads 
                                    | isConst hop || hop `elem` lconsts =
                                        (insert (hop, len) cheads, vheads)
                                    | len > 0 =
                                        (cheads, insert (hop, len) vheads)
                                    | otherwise = sofar in
                              foldr (getHeads lconsts) newHeads args

getThmHeads :: HOLThm -> ([(HOLTerm, Int)], [(HOLTerm, Int)]) ->
               ([(HOLTerm, Int)], [(HOLTerm, Int)])
getThmHeads th = getHeads (catFrees $ hyp th) (concl th)

convAPP :: TriviaCtxt thry => Conversion cls thry
convAPP = convREWR convAPP_pth
    where convAPP_pth :: TriviaCtxt thry => HOL cls thry HOLThm
          convAPP_pth = cacheProof "convAPP_pth" ctxtTrivia $
              prove "!(f:A->B) x. f x = I f x" $
                tacREWRITE [thmI]

convAPP_N :: TriviaCtxt thry => Int -> Conversion cls thry
convAPP_N n =
    if n == 1 then convAPP
    else convRATOR (convAPP_N $ n - 1) `_THEN` convAPP 

convFOL :: TriviaCtxt thry => [(HOLTerm, Int)] 
        -> Conversion cls thry
convFOL hddata = Conv $ \ tm ->
    if isForall tm
    then runConv (convBINDER $ convFOL hddata) tm
    else if isConj tm || isDisj tm
         then runConv (convBINOP $ convFOL hddata) tm
         else let (op, args) = stripComb tm
                  th1 = primREFL op in
                do th2 <- mapM (runConv (convFOL hddata)) args
                   th <- fromRightM $ foldlM primMK_COMB th1 th2
                   tm' <- fromJustM . rand $ concl th
                   let n = case lookup op hddata of
                             Just x -> length args - x
                             Nothing -> 0
                   if n == 0
                      then return th
                      else do th' <- runConv (convAPP_N n) tm'
                              fromRightM $ primTRANS th th'

convGEN_FOL :: TriviaCtxt thry => ([(HOLTerm, Int)], [(HOLTerm, Int)]) 
            -> Conversion cls thry
convGEN_FOL (cheads, vheads) =
    let hddata = if null vheads
                 then let hops = setify $ map fst cheads
                          getMin h = let ns = mapFilter (\ (k, n) -> if k == h then Just n else Nothing) cheads in
                                       if length ns < 2 then Nothing else Just (h, minimum ns) in
                        mapFilter getMin hops
                 else map (\ t -> case t of
                                    ( Const "=" _) -> (t, 2)
                                    _ -> (t, 0)) (setify . map fst $ vheads ++ cheads) in
      convFOL hddata
                     

tacASM_FOL :: TriviaCtxt thry => Tactic cls thry
tacASM_FOL gl@(Goal asl _) =
    let headsp = foldr (getThmHeads . snd) ([], []) asl in
      tacRULE_ASSUM (ruleCONV $ convGEN_FOL headsp) gl

-- conv NFF
andPTm, orPTm, notPTm, pPTm, qPTm :: TriviaCtxt thry => PTerm thry
andPTm = [trivia| (/\) |]
orPTm = [trivia| (\/) |]
notPTm = [trivia| (~) |]
pPTm = [trivia| p:bool |]
qPTm = [trivia| q:bool |]

nnfDConv :: TriviaCtxt thry => Bool 
         -> (HOLTerm -> HOL cls thry (HOLThm, HOLThm)) -> HOLTerm 
         -> HOL cls thry (HOLThm, HOLThm)
nnfDConv cf baseconvs ( Comb ( Comb ( Const "/\\" _) l) r) =
    (do pth <- pthNotAnd
        andTm <- serve andPTm
        orTm <- serve orPTm
        pTm <- serve pPTm
        qTm <- serve qPTm
        (thLp, thLn) <- nnfDConv cf baseconvs l
        (thRp, thRn) <- nnfDConv cf baseconvs r
        let rth1 = fromJust $ primINST [(pTm, l), (qTm, r)] pth
        fromRightM $ do lth <- ruleAP_TERM andTm thLp
                        th1 <- primMK_COMB lth thRp
                        rth2 <- ruleAP_TERM orTm thLn
                        th2 <- primTRANS rth1 =<< primMK_COMB rth2 thRn
                        return (th1, th2))
    <?> "nnfDConv: conjunction case"
nnfDConv cf baseconvs ( Comb ( Comb ( Const "\\/" _) l) r) =
    (do pth <- pthNotOr
        andTm <- serve andPTm
        orTm <- serve orPTm
        pTm <- serve pPTm
        qTm <- serve qPTm
        (thLp, thLn) <- nnfDConv cf baseconvs l
        (thRp, thRn) <- nnfDConv cf baseconvs r
        let rth1 = fromJust $ primINST [(pTm, l), (qTm, r)] pth
        fromRightM $ do lth <- ruleAP_TERM orTm thLp
                        th1 <- primMK_COMB lth thRp
                        rth2 <- ruleAP_TERM andTm thLn
                        th2 <- primTRANS rth1 =<< primMK_COMB rth2 thRn
                        return (th1, th2))
    <?> "nnfDConv: disjunction case"
nnfDConv cf baseconvs ( Comb ( Comb ( Const "==>" _) l) r) =
    (do pth1 <- pthImp
        pth2 <- pthNotImp
        andTm <- serve andPTm
        orTm <- serve orPTm
        pTm <- serve pPTm
        qTm <- serve qPTm
        (thLp, thLn) <- nnfDConv cf baseconvs l
        (thRp, thRn) <- nnfDConv cf baseconvs r
        let lth1 = fromJust $ primINST [(pTm, l), (qTm, r)] pth1
        let rth1 = fromJust $ primINST [(pTm, l), (qTm, r)] pth2
        fromRightM $ do lth2 <- ruleAP_TERM orTm thLn
                        th1 <- primTRANS lth1 =<< primMK_COMB lth2 thRp
                        rth2 <- ruleAP_TERM andTm thLp
                        th2 <- primTRANS rth1 =<< primMK_COMB rth2 thRn
                        return (th1, th2))
    <?> "nnfDConv: implication case"
nnfDConv cf baseconvs tm@(Comb (Comb (Const "=" (TyApp f (TyApp b _ : _))) l) r)
    | f == tyOpFun && b == tyOpBool =
        (do andTm <- serve andPTm
            orTm <- serve orPTm
            pTm <- serve pPTm
            qTm <- serve qPTm
            (thLp, thLn) <- nnfDConv cf baseconvs l
            (thRp, thRn) <- nnfDConv cf baseconvs r
            if cf
               then do pth1 <- pthEq'
                       pth2 <- pthNotEq'
                       let lth1 = fromJust $ primINST [(pTm, l), (qTm, r)] pth1
                           rth1 = fromJust $ primINST [(pTm, l), (qTm, r)] pth2
                       fromRightM $ do lth2 <- ruleAP_TERM orTm thLp
                                       lth3 <- ruleAP_TERM andTm =<< primMK_COMB lth2 thRn
                                       lth4 <- ruleAP_TERM orTm thLn
                                       th1 <- primTRANS lth1 =<< primMK_COMB lth3 =<< primMK_COMB lth4 thRp
                                       rth2 <- ruleAP_TERM orTm thLp
                                       rth3 <- ruleAP_TERM andTm =<< primMK_COMB rth2 thRp
                                       rth4 <- ruleAP_TERM orTm thLn
                                       th2 <- primTRANS rth1 =<< primMK_COMB rth3 =<< primMK_COMB rth4 thRn
                                       return (th1, th2)
               else do pth1 <- pthEq
                       pth2 <- pthNotEq
                       let lth1 = fromJust $ primINST [(pTm, l), (qTm, r)] pth1
                           rth1 = fromJust $ primINST [(pTm, l), (qTm, r)] pth2
                       fromRightM $ do lth2 <- ruleAP_TERM andTm thLp
                                       lth3 <- ruleAP_TERM orTm =<< primMK_COMB lth2 thRp
                                       lth4 <- ruleAP_TERM andTm thLn
                                       th1 <- primTRANS lth1 =<< primMK_COMB lth3 =<< primMK_COMB lth4 thRn
                                       rth2 <- ruleAP_TERM andTm thLp
                                       rth3 <- ruleAP_TERM orTm =<< primMK_COMB rth2 thRn
                                       rth4 <- ruleAP_TERM andTm thLn
                                       th2 <- primTRANS rth1 =<< primMK_COMB rth3 =<< primMK_COMB rth4 thRp
                                       return (th1, th2))
        <?> "nnfDConv: equality case"
    | otherwise = nnfDConvBase baseconvs tm
nnfDConv _ baseconvs tm@(Comb q@(Const "!" (TyApp f1 (TyApp f2 (ty : _) : _))) bod@( Abs x t))
    | f1 == tyOpFun && f2 == tyOpFun =
        (do pth <- pthNotForall
            notTm <- serve notPTm
            (thP, thN) <- nnfDConv True baseconvs t
            th1 <- fromRightM $ ruleAP_TERM q =<< primABS x thP
            p <- liftM (mkVar "P") $ mkFunTy ty tyBool
            let rth1 = fromJust $ primINST [(p, bod)] $ primINST_TYPE [(tyA, ty)] pth
            rth3 <- fromRightM $ do rth2 <- ruleAP_TERM notTm =<< primBETA =<< mkComb bod x
                                    primTRANS rth2 thN
            rth4 <- ruleMK_EXISTS x rth3
            fromRightM $ do th2 <- primTRANS rth1 rth4
                            return (th1, th2))
        <?> "nnfDConv: forall case"
    | otherwise = nnfDConvBase baseconvs tm
nnfDConv cf baseconvs tm@(Comb q@(Const "?" (TyApp f1 (TyApp f2 (ty : _) : _))) bod@( Abs x t))
    | f1 == tyOpFun && f2 == tyOpFun =
        (do pth <- pthNotExists
            notTm <- serve notPTm
            (thP, thN) <- nnfDConv cf baseconvs t
            th1 <- fromRightM $ ruleAP_TERM q =<< primABS x thP
            p <- liftM (mkVar "P") $ mkFunTy ty tyBool
            let rth1 = fromJust $ primINST [(p, bod)] $ primINST_TYPE [(tyA, ty)] pth
            rth3 <- fromRightM $ do rth2 <- ruleAP_TERM notTm =<< primBETA =<< mkComb bod x
                                    primTRANS rth2 thN
            rth4 <- ruleMK_FORALL x rth3
            fromRightM $ do th2 <- primTRANS rth1 rth4 
                            return (th1, th2))
        <?> "nnfDConv: exists case"
    | otherwise = nnfDConvBase baseconvs tm
nnfDConv cf baseconvs tm@( Comb ( Const "?!" ( TyApp f1 (( TyApp f2 (ty : _)) : _))) bod@( Abs x t))
    | f1 == tyOpFun && f2 == tyOpFun =
        let y = variant (x : frees t) x in
          (do pth1 <- pthExu
              pth2 <- pthNotExu
              andTm <- serve andPTm
              orTm <- serve orPTm
              notTm <- serve notPTm
              (thP, thN) <- nnfDConv cf baseconvs t
              eq <- mkEq y x
              (ethP, ethN) <- baseconvs eq
              bth <- fromRightM $ primBETA =<< mkComb bod x
              bth' <- runConv convBETA #<< mkComb bod y
              let thP' = fromJust $ primINST [(x, y)] thP
              let thN' = fromJust $ primINST [(x, y)] thN
              p <- liftM (mkVar "P") $ mkFunTy ty tyBool
              let lth1 = fromJust $ primINST [(p, bod)] $ primINST_TYPE [(tyA, ty)] pth1
              let rth1 = fromJust $ primINST [(p, bod)] $ primINST_TYPE [(tyA, ty)] pth2
              lth2 <- ruleMK_EXISTS x #<< primTRANS bth thP
              lth3 <- fromRightM $ ruleAP_TERM andTm lth2
              lth8 <- fromRightM $ do lth4 <- ruleAP_TERM notTm bth
                                      lth5 <- ruleAP_TERM orTm =<< primTRANS lth4 thN
                                      lth6 <- ruleAP_TERM notTm bth'
                                      lth7 <- ruleAP_TERM orTm =<< primTRANS lth6 thN'
                                      primMK_COMB lth5 =<< primMK_COMB lth7 ethP
              lth9 <- ruleMK_FORALL x =<< ruleMK_FORALL y lth8
              lth10 <- fromRightM $ primMK_COMB lth3 lth9
              rth2 <- fromRightM $ flip primTRANS thN =<< ruleAP_TERM notTm bth
              rth3 <- ruleMK_FORALL x rth2
              rth4 <- fromRightM $ ruleAP_TERM orTm rth3
              rth7 <- fromRightM $ do rth5 <- ruleAP_TERM andTm =<< primTRANS bth thP
                                      rth6 <- ruleAP_TERM andTm =<< primTRANS bth' thP'
                                      primMK_COMB rth5 =<< primMK_COMB rth6 ethN
              rth8 <- ruleMK_EXISTS x =<< ruleMK_EXISTS y rth7
              fromRightM $ do rth9 <- primMK_COMB rth4 rth8
                              th1 <- primTRANS lth1 lth10
                              th2 <- primTRANS rth1 rth9
                              return (th1, th2))
          <?> "nnfDConv: unique exists case"
    | otherwise = nnfDConvBase baseconvs tm
nnfDConv cf baseconvs ( Comb ( Const "~" _) t) =
    (do pth <- pthNotNot
        pTm <- serve pPTm
        (th1, th2) <- nnfDConv cf baseconvs t
        let rth1 = fromJust $ primINST [(pTm, t)] pth
        fromRightM $ do rth2 <- primTRANS rth1 th1
                        return (th2, rth2))
    <?> "nnfDConv: not case"
nnfDConv _ baseconvs tm = nnfDConvBase baseconvs tm

nnfDConvBase :: (HOLTerm -> HOL cls thry (HOLThm, HOLThm)) -> HOLTerm -> HOL cls thry (HOLThm, HOLThm)
nnfDConvBase baseconvs tm =
    (baseconvs tm <|> (let th1 = primREFL tm in
                         do th2 <- liftM primREFL $ mkNeg tm
                            return (th1, th2)))
    <?> "nnfDConv: base case"

type NNFConv cls thry = 
    Bool -> (Conversion cls thry, HOLTerm -> HOL cls thry (HOLThm, HOLThm)) -> 
    Conversion cls thry

nnfConv' :: forall cls thry. TriviaCtxt thry => NNFConv cls thry
nnfConv' cf baseconvs@(base1, base2) = Conv $ \ tm ->
    do orTm <- serve orPTm
       notTm <- serve notPTm
       andTm <- serve andPTm
       pTm <- serve pPTm
       qTm <- serve qPTm
       case tm of
         (Comb ( Comb ( Const "/\\" _) l) r) ->
             let ?pth = pthNotAnd
                 ?lconv = nnfConv'
                 ?rconv = nnfConv'
                 ?btm = orTm in
               boolCase "conjunction" l r
         (Comb ( Comb ( Const "\\/" _) l) r) ->
             let ?pth = pthNotOr
                 ?lconv = nnfConv'
                 ?rconv = nnfConv'
                 ?btm = andTm in
               boolCase "disjunction" l r
         (Comb ( Comb ( Const "==>" _) l) r) ->
             let ?pth = pthNotImp
                 ?lconv = nnfConv
                 ?rconv = nnfConv'
                 ?btm = andTm in
               boolCase "implication" l r
         (Comb (Comb (Const "=" (TyApp _ (TyApp b _ : _))) l) r)
             | b == tyOpBool -> 
                 (do (thLp, thLn) <- nnfDConv cf base2 l
                     (thRp, thRn) <- nnfDConv cf base2 r
                     pth <- if cf then pthNotEq' else pthNotEq
                     let (ltm, rtm) = if cf then (orTm, andTm) else (andTm, orTm)
                         (rth1, rth2) = if cf then (thRp, thRn) else (thRn, thRp)
                     liftO $ do lth1 <- note "" $ primINST [(pTm, l), (qTm, r)] pth
                                lth2 <- ruleAP_TERM ltm thLp
                                lth3 <- ruleAP_TERM rtm =<< primMK_COMB lth2 rth1
                                lth4 <- ruleAP_TERM ltm thLn
                                primTRANS lth1 =<< primMK_COMB lth3 =<< primMK_COMB lth4 rth2)
                 <?> "nnfConv': equality case"
             | otherwise -> baseCase tm
         (Comb (Const "!" (TyApp _ (TyApp _ (ty : _) : _))) bod@( Abs x t)) ->
             let ?pth = pthNotForall
                 ?cf = cf
                 ?rule = ruleMK_EXISTS in
               quantCase "forall" bod x t ty
         (Comb ( Const "?" ( TyApp _ (TyApp _ (ty : _) : _))) bod@( Abs x t)) ->
             let ?pth = pthNotExists
                 ?cf = True
                 ?rule = ruleMK_FORALL in
               quantCase "exists" bod x t ty
         (Comb ( Const "?!" ( TyApp _ (TyApp _ (ty : _) : _))) bod@( Abs x t)) ->
             let y = variant (x:frees t) x in
               (do pth <- pthNotExu
                   (thP, thN) <- nnfDConv cf base2 t
                   eq <- mkEq y x
                   (_, ethN) <- base2 eq
                   bth <- fromRightM $ primBETA =<< mkComb bod x
                   bth' <- runConv convBETA #<< mkComb bod y
                   th1' <- instPth pth bod ty
                   lth1 <- fromRightM $ flip primTRANS thN =<< ruleAP_TERM notTm bth
                   lth2 <- ruleMK_FORALL x lth1
                   lth3 <- fromRightM $ ruleAP_TERM orTm lth2
                   lth6 <- fromRightM $ do lth4 <- ruleAP_TERM andTm =<< primTRANS bth thP
                                           lth5 <- ruleAP_TERM andTm =<< (primTRANS bth' #<< primINST [(x, y)] thP)
                                           primMK_COMB lth4 =<< primMK_COMB lth5 ethN
                   lth7 <- ruleMK_EXISTS x =<< ruleMK_EXISTS y lth6
                   fromRightM $ primTRANS th1' =<< primMK_COMB lth3 lth7)
               <?> "nnfConv': unique exists case"
         (Comb ( Const "~" _) t) ->
             (do pth <- pthNotNot
                 th1 <- runConv (nnfConv cf baseconvs) t
                 liftO $ primTRANS (fromJust $ primINST [(pTm, t)] pth) th1)
             <?> "nnfConv': not case"
         _ -> baseCase tm
  where boolCase :: (TriviaCtxt thry, ?pth :: HOL cls thry HOLThm, 
                     ?lconv :: NNFConv cls thry,
                     ?rconv :: NNFConv cls thry, ?btm :: HOLTerm) 
                 => String -> HOLTerm -> HOLTerm -> HOL cls thry HOLThm
        boolCase err l r =
            (do pTm <- serve pPTm
                qTm <- serve qPTm
                pth <- ?pth
                lth <- runConv (?lconv cf baseconvs) l
                rth <- runConv (?rconv cf baseconvs) r
                let lth1 = fromJust $ primINST [(pTm, l), (qTm, r)] pth
                liftO $ do lth2 <- ruleAP_TERM ?btm lth
                           primTRANS lth1 =<< primMK_COMB lth2 rth)
             <?> ("nnfConv': " ++ err ++ " case")

        quantCase :: (TriviaCtxt thry, ?pth ::HOL cls thry HOLThm, ?cf :: Bool,
                      ?rule :: HOLTerm -> HOLThm -> HOL cls thry HOLThm) 
                  => String -> HOLTerm -> HOLTerm -> HOLTerm -> HOLType 
                  -> HOL cls thry HOLThm
        quantCase err bod x t ty =
            (do notTm <- serve notPTm
                pth <- ?pth
                thN <- runConv (nnfConv' ?cf baseconvs) t
                th1 <- instPth pth bod ty
                lth <- fromRightM $ ruleAP_TERM notTm =<< primBETA =<< 
                         mkComb bod x
                th2 <- ?rule x #<< primTRANS lth thN
                fromRightM $ primTRANS th1 th2)
             <?> ("nnfConv': " ++ err ++ " case")

        baseCase :: TriviaCtxt thry => HOLTerm -> HOL cls thry HOLThm
        baseCase tm = 
            (do tm' <- mkNeg tm
                runConv base1 tm' <|> (return $! primREFL tm'))
            <?>" nnfConv': base case"

        instPth :: HOLThm -> HOLTerm -> HOLType -> HOL cls thry HOLThm
        instPth pth bod ty =
            do p <- liftM (mkVar "P") $ mkFunTy ty tyBool
               liftO . primINST [(p, bod)] $ primINST_TYPE [(tyA, ty)] pth
    

nnfConv :: TriviaCtxt thry => NNFConv cls thry
nnfConv cf baseconvs@(base1, base2) = Conv $ \ tm ->
    do orTm <- serve orPTm
       notTm <- serve notPTm
       andTm <- serve andPTm
       pTm <- serve pPTm
       qTm <- serve qPTm
       case tm of
         (Comb ( Comb ( Const "/\\" _) l) r) ->
             (do thLp <- runConv (nnfConv cf baseconvs) l
                 thRp <- runConv (nnfConv cf baseconvs) r
                 fromRightM $ do lth <- ruleAP_TERM andTm thLp
                                 primMK_COMB lth thRp)
             <?> "nnfConv: conjunction case"
         (Comb ( Comb ( Const "\\/" _) l) r) ->
             (do thLp <- runConv (nnfConv cf baseconvs) l
                 thRp <- runConv (nnfConv cf baseconvs) r
                 fromRightM $ do lth <- ruleAP_TERM orTm thLp
                                 primMK_COMB lth thRp)
             <?> "nnfConv: disjunction case"
         (Comb ( Comb ( Const "==>" _) l) r) ->
             (do pth <- pthImp
                 thLn <- runConv (nnfConv' cf baseconvs) l
                 thRp <- runConv (nnfConv cf baseconvs) r
                 let lth1 = fromJust $ primINST [(pTm, l), (qTm, r)] pth
                 fromRightM $ do lth2 <- ruleAP_TERM orTm thLn
                                 primTRANS lth1 =<< primMK_COMB lth2 thRp)
             <?> "nnfConv: implication case"
         (Comb ( Comb ( Const "=" ( TyApp f (TyApp b _ : _))) l) r)
             | f == tyOpFun && b == tyOpBool ->
                 (do (thLp, thLn) <- nnfDConv cf base2 l
                     (thRp, thRn) <- nnfDConv cf base2 r
                     if cf
                        then do pth <- pthEq'
                                let lth1 = fromJust $ primINST [(pTm, l), (qTm, r)] pth
                                fromRightM $ do lth2 <- ruleAP_TERM orTm thLp
                                                lth3 <- ruleAP_TERM orTm thLn
                                                lth4 <- ruleAP_TERM andTm =<< primMK_COMB lth2 thRn 
                                                primTRANS lth1 =<< primMK_COMB lth4 =<< primMK_COMB lth3 thRp
                        else do pth <- pthEq
                                let lth1 = fromJust $ primINST [(pTm, l), (qTm, r)] pth
                                fromRightM $ do lth2 <- ruleAP_TERM andTm thLp
                                                lth3 <- ruleAP_TERM andTm thLn
                                                lth4 <- ruleAP_TERM orTm =<< primMK_COMB lth2 thRp
                                                primTRANS lth1 =<< primMK_COMB lth4 =<< primMK_COMB lth3 thRn)
                 <?> "nnfConv: equation case"
             | otherwise -> nnfConvBase base1 tm
         (Comb q@( Const "!" ( TyApp f1 (TyApp f2 (:){} : _))) ( Abs x t))
             | f1 == tyOpFun && f2 == tyOpFun ->
                 (do thP <- runConv (nnfConv True baseconvs) t
                     fromRightM $ ruleAP_TERM q =<< primABS x thP)
                 <?> "nnfConv: forall case"
             | otherwise -> nnfConvBase base1 tm
         (Comb q@( Const "?" ( TyApp f1 (TyApp f2 (:){} : _))) ( Abs x t))
             | f1 == tyOpFun && f2 == tyOpFun ->
                 (do thP <- runConv (nnfConv cf baseconvs) t
                     fromRightM $ ruleAP_TERM q =<< primABS x thP)
                 <?> "nnfConv: exists case"
             | otherwise -> nnfConvBase base1 tm
         (Comb ( Const "?!" ( TyApp f1 (TyApp f2 (ty : _) : _))) bod@( Abs x t))
             | f1 == tyOpFun && f2 == tyOpFun ->
                 let y = variant (x:frees t) x in
                   (do pth <- pthExu
                       (thP, thN) <- nnfDConv cf base2 t
                       eq <- mkEq y x
                       (ethP, _) <- base2 eq
                       bth <- fromRightM $ primBETA =<< mkComb bod x
                       bth' <- runConv convBETA #<< mkComb bod y
                       let thN' = fromJust $ primINST [(x, y)] thN
                       p <- liftM (mkVar "P") $ mkFunTy ty tyBool
                       let th1 = fromJust . primINST [(p, bod)] $ primINST_TYPE [(tyA, ty)] pth
                       th2 <- ruleMK_EXISTS x #<< primTRANS bth thP
                       lth1 <- fromRightM $ ruleAP_TERM andTm th2
                       lth6 <- fromRightM $ do lth2 <- ruleAP_TERM notTm bth
                                               lth3 <- ruleAP_TERM orTm =<< primTRANS lth2 thN
                                               lth4 <- ruleAP_TERM notTm bth'
                                               lth5 <- ruleAP_TERM orTm =<< primTRANS lth4 thN'
                                               primMK_COMB lth3 =<< primMK_COMB lth5 ethP
                       th3 <- ruleMK_FORALL x =<< ruleMK_FORALL y lth6
                       fromRightM $ primTRANS th1 =<< primMK_COMB lth1 th3)
                   <?> "nnfConv: unique exists case"
             | otherwise -> nnfConvBase base1 tm
         (Comb ( Const "~" _) t) -> runConv (nnfConv' cf baseconvs) t
         _ -> nnfConvBase base1 tm

nnfConvBase :: Conversion cls thry -> HOLTerm -> HOL cls thry HOLThm
nnfConvBase base1 tm =
    (runConv base1 tm <|> (return $! primREFL tm))
    <?> "nnfConv: base case"


convGEN_NNF :: TriviaCtxt thry => Bool 
            -> (Conversion cls thry, HOLTerm -> HOL cls thry (HOLThm, HOLThm)) 
            -> Conversion cls thry
convGEN_NNF = nnfConv

convNNF :: TriviaCtxt thry => Conversion cls thry
convNNF = convGEN_NNF False (_ALL, \ t -> do th <- liftM primREFL $ mkNeg t
                                             return (primREFL t, th))

convNNFC :: TriviaCtxt thry => Conversion cls thry
convNNFC = convGEN_NNF True (_ALL, \ t -> do th <- liftM primREFL $ mkNeg t
                                             return (primREFL t, th))
                                                     

               
