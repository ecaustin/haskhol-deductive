{-# LANGUAGE ImplicitParams, ScopedTypeVariables #-}
{-|
  Module:    HaskHOL.Lib.Canon
  Copyright: (c) Evan Austin 2015
  LICENSE:   BSD3

  Maintainer:  e.c.austin@gmail.com
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
    , convPROP_ATOM
    ) where

import HaskHOL.Core
import qualified HaskHOL.Core.Kernel as K (typeOf)

import HaskHOL.Lib.Bool
import HaskHOL.Lib.Classic
import HaskHOL.Lib.Equal
import HaskHOL.Lib.IndDefs
import HaskHOL.Lib.Theorems
import HaskHOL.Lib.Simp
import HaskHOL.Lib.DRule
import HaskHOL.Lib.Tactics
import HaskHOL.Lib.Trivia

tmA, tmB, tmC, tmP, tmQ :: TriviaCtxt thry => HOL cls thry HOLTerm
tmA = serve [trivia| a:bool |]
tmB = serve [trivia| b:bool |]
tmC = serve [trivia| c:bool |]
tmP = serve [trivia| p:bool |]
tmQ = serve [trivia| q:bool |]

tmAnd, tmOr, tmNot, tmFalse, tmTrue :: TriviaCtxt thry => HOL cls thry HOLTerm
tmAnd = serve [trivia| (/\) |]
tmOr = serve [trivia| (\/) |]
tmNot = serve [trivia| (~) |]
tmFalse = serve [trivia| F |]
tmTrue = serve [trivia| T |]


pthNotNot :: TriviaCtxt thry => HOL cls thry HOLThm
pthNotNot = cacheProof "pthNotNot" ctxtTrivia $ 
    ruleTAUT [txt| ~ ~ p = p |]

pthNotAnd :: TriviaCtxt thry => HOL cls thry HOLThm
pthNotAnd = cacheProof "pthNotAnd" ctxtTrivia $ 
    ruleTAUT [txt| ~(p /\ q) <=> ~p \/ ~q |]

pthNotOr :: TriviaCtxt thry => HOL cls thry HOLThm
pthNotOr = cacheProof "pthNotOr" ctxtTrivia $ 
    ruleTAUT [txt| ~(p \/ q) <=> ~p /\ ~q |]

pthImp :: TriviaCtxt thry => HOL cls thry HOLThm
pthImp = cacheProof "pthImp" ctxtTrivia $ 
    ruleTAUT [txt| p ==> q <=> ~p \/ q |]

pthNotImp :: TriviaCtxt thry => HOL cls thry HOLThm
pthNotImp = cacheProof "pthNotImp" ctxtTrivia $ 
    ruleTAUT [txt| ~(p ==> q) <=> p /\ ~q |]

pthEq :: TriviaCtxt thry => HOL cls thry HOLThm
pthEq = cacheProof "pthEq" ctxtTrivia $ 
    ruleTAUT [txt| (p <=> q) <=> p /\ q \/ ~p /\ ~q |]

pthNotEq :: TriviaCtxt thry => HOL cls thry HOLThm
pthNotEq = cacheProof "pthNotEq" ctxtTrivia $ 
    ruleTAUT [txt| ~(p <=> q) <=> p /\ ~q \/ ~p /\ q |]

pthEq' :: TriviaCtxt thry => HOL cls thry HOLThm
pthEq' = cacheProof "pthEq'" ctxtTrivia $ 
    ruleTAUT [txt| (p <=> q) <=> (p \/ ~q) /\ (~p \/ q) |]

pthNotEq' :: TriviaCtxt thry => HOL cls thry HOLThm
pthNotEq' = cacheProof "pthNotEq'" ctxtTrivia $ 
    ruleTAUT [txt| ~(p <=> q) <=> (p \/ q) /\ (~p \/ ~q) |]

pthNots :: TriviaCtxt thry => [HOL cls thry HOLThm]
pthNots =
    cacheProofs ["pthNotForall", "pthNotExists", "pthNotExu"] ctxtTrivia .
      ruleCONJUNCTS .
        prove [txt| (~((!) P) <=> ?x:A. ~(P x)) /\
                    (~((?) P) <=> !x:A. ~(P x)) /\
                    (~((?!) P) <=> (!x:A. ~(P x)) \/ 
                    ?x y. P x /\ P y /\ ~(y = x)) |] $
          _REPEAT tacCONJ `_THEN`
          tacGEN_REWRITE (convLAND . funpow 2 convRAND) [ruleGSYM axETA] `_THEN`
          tacREWRITE [ thmNOT_EXISTS, thmNOT_FORALL, defEXISTS_UNIQUE
                     , thmDE_MORGAN, thmNOT_IMP ] `_THEN`
          tacREWRITE [thmCONJ_ASSOC, thmEQ_SYM_EQ]

pthNotForall :: TriviaCtxt thry => HOL cls thry HOLThm
pthNotForall = getProof "pthNotForall" <|> head pthNots

pthNotExists :: TriviaCtxt thry => HOL cls thry HOLThm
pthNotExists = getProof "pthNotExists" <|> pthNots !! 1

pthNotExu :: TriviaCtxt thry => HOL cls thry HOLThm
pthNotExu = getProof "pthNotExu" <|> pthNots !! 2

pthExu :: TriviaCtxt thry => HOL cls thry HOLThm
pthExu = cacheProof "pthExu" ctxtTrivia .
    prove [txt| ((?!) P) <=> (?x:A. P x) /\ 
                !x y. ~(P x) \/ ~(P y) \/ (y = x) |] $
      tacGEN_REWRITE (convLAND . convRAND) [ruleGSYM axETA] `_THEN`
      tacREWRITE [ defEXISTS_UNIQUE
                 , ruleTAUT [txt| a /\ b ==> c <=> ~a \/ ~b \/ c |] ] `_THEN`
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

ruleCONJ_ACI :: (BoolCtxt thry, HOLTermRep tm cls thry) 
             => tm -> HOL cls thry HOLThm
ruleCONJ_ACI ptm =
    do tm <- toHTm ptm
       case tm of
         (p := p')
             | p == p' -> primREFL p
             | otherwise ->
                 do th <- useFun p' =<< mkFun funcEmpty =<< primASSUME p
                    th' <- useFun p =<< mkFun funcEmpty =<< primASSUME p'
                    ruleIMP_ANTISYM (ruleDISCH_ALL th) $ ruleDISCH_ALL th'
         _ -> fail "ruleCONJ_ACI: not an equational term."
  where useFun :: BoolCtxt thry => HOLTerm -> Func HOLTerm HOLThm
               -> HOL cls thry HOLThm
        useFun (l :/\ r) fn =
            do l' <- useFun l fn
               ruleCONJ l' $ useFun r fn
        useFun tm fn = apply fn tm

        mkFun :: BoolCtxt thry => Func HOLTerm HOLThm -> HOLThm 
              -> HOL cls thry (Func HOLTerm HOLThm)
        mkFun fn th@(Thm _ (_ :/\ _)) =
            do (th1, th2) <- ruleCONJ_PAIR th
               flip mkFun th1 =<< mkFun fn th2
        mkFun fn th = return $! (concl th |-> th) fn


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
    where conv :: TriviaCtxt thry => [HOLTerm] -> Conversion cls thry 
          conv [] = _ALL
          conv (_:vs) = convGEN_REWRITE id [convHALF_MK_ABS_pth] `_THEN` 
                        convBINDER (conv vs)
        
          convHALF_MK_ABS_pth :: TriviaCtxt thry => HOL cls thry HOLThm
          convHALF_MK_ABS_pth = cacheProof "convHALF_MK_ABS_pth" ctxtTrivia $
              prove [txt| (s = \x. t x) <=> (!x. s x = t x) |] $
                tacREWRITE [thmFUN_EQ]

findLambda :: HOLTerm -> HOL cls thry HOLTerm
findLambda tm@Abs{} = return tm
findLambda Var{} = fail "findLambda: var case"
findLambda Const{} = fail "findLambda: const case"
findLambda tm = 
    if isForall tm || isExists tm || isUExists tm
    then findLambda =<< body (rand tm)
    else case tm of
           (Comb l r) -> 
               findLambda l <|> findLambda r
           _ -> fail "findLambda: quantified case"

elimLambda :: Conversion cls thry -> Conversion cls thry 
elimLambda conv = Conv $ \ tm ->
    runConv conv tm <|> 
    (if isAbs tm then runConv (convABS $ elimLambda conv) tm
     else if isVar tm || isConst tm then primREFL tm
          else if isForall tm || isExists tm || isUExists tm
               then runConv (convBINDER $ elimLambda conv) tm
               else runConv (convCOMB $ elimLambda conv) tm)

applyPTH :: TriviaCtxt thry => HOLThm -> HOL cls thry HOLThm
applyPTH = ruleMATCH_MP applyPTH_pth
  where applyPTH_pth :: TriviaCtxt thry => HOL cls thry HOLThm
        applyPTH_pth = cacheProof "applyPTH_pth" ctxtTrivia .
            prove [txt| (!a. (a = c) ==> (P = Q a)) ==> 
                        (P <=> !a. (a = c) ==> Q a) |] $
              tacSIMP [thmLEFT_FORALL_IMP, thmEXISTS_REFL]


convLAMB1 :: TriviaCtxt thry => Conversion cls thry
convLAMB1 = Conv $ \ tm -> note "convLAMB1" $
    do atm <- findLambda tm
       (v, _) <- destAbs atm
       let vs = frees atm
           vs' = vs ++ [v]
       aatm <- listMkAbs vs atm
       f <- genVar $ typeOf aatm
       eq <- mkEq f aatm
       th1 <- ruleSYM . ruleRIGHT_BETAS vs $ primASSUME eq
       th2 <- runConv (elimLambda $ convGEN_REWRITE id [th1]) tm
       th3 <- applyPTH =<< ruleGEN f (ruleDISCH_ALL th2)
       ruleCONV (convRAND . convBINDER .convLAND $ convHALF_MK_ABS vs') th3

convLAMBDA_ELIM :: TriviaCtxt thry => Conversion cls thry
convLAMBDA_ELIM = Conv $ \ tm -> 
    runConv (convLAMB1 `_THEN` convLAMBDA_ELIM) tm
    <|> primREFL tm

-- eliminate select terms from a goal

selectElimThm :: TriviaCtxt thry => HOLTerm 
              -> HOL cls thry HOLThm
selectElimThm (Comb (Const "@" _) atm@(Abs bv _)) =
    ruleCONV (convLAND convBETA) $ 
      rulePINST [(tyA, typeOf bv)] 
                [(serve [trivia| P:A->bool |], atm)] selectElimThm_pth
  where selectElimThm_pth :: TriviaCtxt thry => HOL cls thry HOLThm
        selectElimThm_pth = cacheProof "selectElimThm_pth" ctxtTrivia .
            prove [txt| (P:A->bool)((@) P) <=> (?) P |] $
              tacREWRITE [thmEXISTS] `_THEN`
              tacBETA `_THEN`
              tacREFL
selectElimThm _ = fail "selectElimThm: not a select term"

 
convSELECT_ELIM :: TriviaCtxt thry => Conversion cls thry
convSELECT_ELIM = Conv $ \ tm ->
    do ths <- mapM selectElimThm $ findTerms isSelect tm
       runConv (convPURE_REWRITE ths) tm

selectAxThm :: TriviaCtxt thry => HOLTerm -> HOL cls thry HOLThm
selectAxThm (Comb (Const "@" _) atm@(Abs bv _)) =
    let fvs = frees atm in
      do th1 <- rulePINST [(tyA, typeOf bv)] 
                          [(serve [trivia| P:A->bool |], atm)] selectAxThm_pth
         th2 <- ruleCONV (convBINDER $ convBINOP convBETA) th1
         ruleGENL fvs th2
  where selectAxThm_pth :: TriviaCtxt thry => HOL cls thry HOLThm
        selectAxThm_pth = cacheProof "selectAxThm_pth" ctxtTrivia $
            ruleISPEC [txt| P:A->bool |] axSELECT
selectAxThm _ = fail "selectAxThm: not a select term"

iconvSELECT_ELIM :: TriviaCtxt thry => Conversion cls thry
iconvSELECT_ELIM = Conv $ \ tm ->
    (do t <- findTerm isSelect tm
        th1 <- selectAxThm t
        itm <- mkImp (concl th1) tm
        ith <- primASSUME itm
        th2 <- ruleDISCH_ALL $ ruleMP ith th1
        let fvs = frees t
        fty <- foldrM (mkFunTy . typeOf) (K.typeOf t) fvs
        fn <- genVar fty
        atm <- listMkAbs fvs t
        rawdef <- mkEq fn atm
        def <- ruleGENL fvs . ruleSYM . ruleRIGHT_BETAS fvs $ primASSUME rawdef
        l <- lHand $ concl th2
        th3 <- runConv (convPURE_REWRITE [def]) l
        r <- rand $ concl th3
        gtm <- mkForall fn r
        th4 <- ruleSYM th3
        th5 <- ruleSPEC fn $ primASSUME gtm
        th6 <- primEQ_MP th4 th5
        th7 <- ruleDISCH gtm th6
        th8 <- ruleIMP_TRANS th7 th2
        th9 <- ruleDISCH rawdef th8
        ruleMP (primINST [(fn, atm)] th9) $ primREFL atm)
    <?> "iconvSELECT_ELIM"

iconvSELECT_ELIMS :: TriviaCtxt thry => Conversion cls thry
iconvSELECT_ELIMS = Conv $ \ tm ->
    (do th <- runConv iconvSELECT_ELIM tm
        tm' <- lHand $ concl th
        th2 <- runConv iconvSELECT_ELIM tm'
        ruleIMP_TRANS th2 th)
    <|> (ruleDISCH tm $ primASSUME tm)

tacSELECT_ELIM :: TriviaCtxt thry => Tactic cls thry
tacSELECT_ELIM = 
    tacCONV convSELECT_ELIM `_THEN` 
    (\ g@(Goal _ w) -> do th <- runConv iconvSELECT_ELIMS w
                          tacMATCH_MP th g) 

-- eliminate conditionals 
condsElimConv :: TriviaCtxt thry => Bool -> Conversion cls thry    
condsElimConv dfl = Conv $ \ tm ->
    (do t <- findConditional [] tm
        p <- lHand $ rator t
        prosimps <- basicNet
        let conv = convDEPTH (gconvREWRITES prosimps)
        thNew <- case p of
                   F -> runConv conv tm
                   T -> runConv conv tm
                   _ ->
                       do asm0 <- mkEq p $ tmFalse
                          ath0 <- primASSUME asm0
                          asm1 <- mkEq p $ tmTrue
                          ath1 <- primASSUME asm1
                          simp0 <- netOfThm False ath0 prosimps
                          simp1 <- netOfThm False ath1 prosimps
                          th0 <- ruleDISCH asm0 $ 
                                   runConv (convDEPTH $ gconvREWRITES simp0) tm
                          th1 <- ruleDISCH asm1 $
                                   runConv (convDEPTH $ gconvREWRITES simp1) tm
                          th2 <- ruleCONJ th0 th1
                          let convTh = if dfl then convCONDS_ELIM_thCond
                                       else convCONDS_ELIM_thCond'
                          th3 <- ruleMATCH_MP convTh th2
                          let cnv = _TRY (gconvREWRITES prosimps)
                              proptsimpConv = convBINOP cnv `_THEN` cnv
                          rth <- runConv proptsimpConv $ rand (concl th3)
                          primTRANS th3 rth
        ruleCONV (convRAND $ condsElimConv dfl) thNew) <|>
       (if isNeg tm 
             then runConv (convRAND . condsElimConv $ not dfl) tm
        else if isConj tm || isDisj tm 
             then runConv (convBINOP $ condsElimConv dfl) tm
        else if isImp tm || isIff tm
             then runConv (convCOMB2 (convRAND . condsElimConv $ not dfl)
                    (condsElimConv dfl)) tm
        else if isForall tm
             then runConv (convBINDER $ condsElimConv False) tm
        else if isExists tm || isUExists tm
             then runConv (convBINDER $ condsElimConv True) tm
        else primREFL tm)
    <?> "condsElimConv"
  where convCONDS_ELIM_thCond :: TriviaCtxt thry => HOL cls thry HOLThm
        convCONDS_ELIM_thCond = cacheProof "convCONDS_ELIM_thCond" ctxtTrivia .
            prove [txt| ((b <=> F) ==> x = x0) /\ 
                        ((b <=> T) ==> x = x1) ==> 
                        x = (b /\ x1 \/ ~b /\ x0) |] $
              tacBOOL_CASES [txt| b:bool |] `_THEN` tacASM_REWRITE_NIL

        convCONDS_ELIM_thCond' :: TriviaCtxt thry => HOL cls thry HOLThm
        convCONDS_ELIM_thCond' = 
            cacheProof "convCONDS_ELIM_thCond'" ctxtTrivia .
              prove [txt| ((b <=> F) ==> x = x0) /\ 
                          ((b <=> T) ==> x = x1) ==> 
                          x = ((~b \/ x1) /\ (b \/ x0)) |] $
                tacBOOL_CASES [txt| b:bool |] `_THEN` tacASM_REWRITE_NIL

        findConditional :: [HOLTerm] -> HOLTerm -> HOL cls thry HOLTerm   
        findConditional fvs tm@(Comb s t)
            | isCond tm =
                do freesL <- frees `fmap` lHand s
                   if null (freesL `intersect` fvs)
                      then return tm
                      else findConditional fvs s <|> findConditional fvs t
            | otherwise = findConditional fvs s <|> findConditional fvs t
        findConditional fvs (Abs x t) = findConditional (x:fvs) t
        findConditional _ _ = fail "findConditional"


convCONDS_ELIM :: TriviaCtxt thry => Conversion cls thry
convCONDS_ELIM = condsElimConv True

convCONDS_CELIM :: TriviaCtxt thry => Conversion cls thry
convCONDS_CELIM = condsElimConv False

-- Weak DNF
distributeDNF :: TriviaCtxt thry => Conversion cls thry
distributeDNF = Conv $ \ tm -> note "distributeDNF" $
    case tm of
      (a :/\ (b :\/ c)) ->
          do th <- primINST [(tmA, a), (tmB, b), (tmC, c)] convWEAK_DNF_pth1
             th' <- runConv (convBINOP distributeDNF) $ rand (concl th)
             primTRANS th th'
      ((a :\/ b) :/\ c) ->
          do th <- primINST [(tmA, a), (tmB, b), (tmC, c)] convWEAK_DNF_pth2
             th' <- runConv (convBINOP distributeDNF) $ rand (concl th)
             primTRANS th th'
      _ -> primREFL tm
  where convWEAK_DNF_pth1 :: TriviaCtxt thry => HOL cls thry HOLThm
        convWEAK_DNF_pth1 = cacheProof "convWEAK_DNF_pth1" ctxtTrivia $
            ruleTAUT [txt| a /\ (b \/ c) <=> a /\ b \/ a /\ c |]

        convWEAK_DNF_pth2 :: TriviaCtxt thry => HOL cls thry HOLThm
        convWEAK_DNF_pth2 = cacheProof "convWEAK_DNF_pth2" ctxtTrivia $
            ruleTAUT [txt| (a \/ b) /\ c <=> a /\ c \/ b /\ c |]

convWEAK_DNF :: TriviaCtxt thry => Conversion cls thry
convWEAK_DNF = Conv $ \ tm -> note "convWEAK_DNF" $
    case tm of
      Forall{} -> runConv (convBINDER convWEAK_DNF) tm
      Exists{} -> runConv (convBINDER convWEAK_DNF) tm
      (_ :\/ _) -> runConv (convBINOP convWEAK_DNF) tm
      (l :/\ r) ->
          do l' <- runConv convWEAK_DNF l
             r' <- runConv convWEAK_DNF r
             th <- primMK_COMB (ruleAP_TERM tmAnd l') r'
             th' <- runConv distributeDNF $ rand (concl th)
             primTRANS th th'
      _ -> primREFL tm

-- Weak CNF
distribute :: TriviaCtxt thry => Conversion cls thry
distribute = Conv $ \ tm -> note "distribute" $
    case tm of
      (a :\/ (b :/\ c)) ->
          do th <- primINST [(tmA, a), (tmB, b), (tmC, c)] distribute_pth1
             rth <- runConv (convBINOP distribute) $ rand (concl th)
             primTRANS th rth
      ((a :/\ b) :\/ c) ->
          do th <- primINST [(tmA, a), (tmB, b), (tmC, c)] distribute_pth2
             rth <- runConv (convBINOP distribute) $ rand (concl th)
             primTRANS th rth
      _ -> primREFL tm
  where distribute_pth1 :: TriviaCtxt thry => HOL cls thry HOLThm
        distribute_pth1 = cacheProof "distribute_pth1" ctxtTrivia $
            ruleTAUT [txt| a \/ (b /\ c) <=> (a \/ b) /\ (a \/ c) |]

        distribute_pth2 :: TriviaCtxt thry => HOL cls thry HOLThm
        distribute_pth2 = cacheProof "distribute_pth2" ctxtTrivia $
            ruleTAUT [txt| (a /\ b) \/ c <=> (a \/ c) /\ (b \/ c) |]



convWEAK_CNF :: TriviaCtxt thry => Conversion cls thry
convWEAK_CNF = Conv $ \ tm -> note "convWEAK_CNF" $
    case tm of
      Forall{} -> runConv (convBINDER convWEAK_CNF) tm
      Exists{} -> runConv (convBINDER convWEAK_CNF) tm
      (_ :/\ _) -> runConv (convBINOP convWEAK_CNF) tm
      (l :\/ r) -> 
          do lth <- runConv convWEAK_CNF l
             rth <- runConv convWEAK_CNF r
             th <- primMK_COMB (ruleAP_TERM tmOr lth) rth
             rtm <- rand $ concl th
             th2 <- runConv distribute rtm
             primTRANS th th2
      _ -> primREFL tm

distrib :: HOLTerm -> HOLTerm -> HOLTerm -> HOLTerm -> HOLThm -> HOLTerm 
        -> HOL cls thry HOLThm
distrib op x y z th' tm@(Comb (Comb op' (Comb (Comb op'' p) q)) r)
    | op' == op && op'' == op = note "distrib" $
        do th1 <- primINST [(x, p), (y, q), (z, r)] th'
           case concl th1 of
             (Comb _ (Comb l r')) -> 
                 do th2 <- ruleAP_TERM l $ distrib op x y z th' r'
                    rtm <- rand $ concl th2
                    th3 <- distrib op x y z th' rtm
                    primTRANS th1 $ primTRANS th2 th3
             _ -> fail "not a combination."
    | otherwise = primREFL tm
distrib _ _ _ _ _ t = primREFL t

convASSOC :: (BoolCtxt thry, HOLThmRep thm cls thry) => thm 
          -> Conversion cls thry
convASSOC thm = Conv $ \ tm -> note "convASSOC" $
    do thm' <- ruleSYM $ ruleSPEC_ALL thm
       case concl thm' of
         (_ := (Binop op x (Binop _ y z))) ->
             canonAssoc op x y z thm' tm
         _ -> fail "bad term structure."
  where canonAssoc :: HOLTerm -> HOLTerm -> HOLTerm -> HOLTerm -> HOLThm 
                   -> HOLTerm -> HOL cls thry HOLThm
        canonAssoc op x y z th' tm@(Comb l@(Comb op' _) q)
            | op' == op =
                (do th <- ruleAP_TERM l $ canonAssoc op x y z th' q
                    r <- rand $ concl th
                    primTRANS th $ distrib op x y z th' r)
                <?> "canonAssoc"
            | otherwise = primREFL tm
        canonAssoc _ _ _ _ _ tm = primREFL tm

getHeads :: [HOLTerm] -> HOLTerm -> ([(HOLTerm, Int)], [(HOLTerm, Int)]) 
         -> ([(HOLTerm, Int)], [(HOLTerm, Int)])
getHeads lconsts (Forall v bod) sofar =
    getHeads (lconsts \\ [v]) bod sofar
getHeads lconsts (l :/\ r) sofar =
    getHeads lconsts l (getHeads lconsts r sofar)
getHeads lconsts (l :\/ r) sofar =
    getHeads lconsts l (getHeads lconsts r sofar)
getHeads lconsts (Neg tm') sofar =
    getHeads lconsts tm' sofar
getHeads lconsts tm sofar@(cheads, vheads) =
    let (hop, args) = stripComb tm
        len = length args
        newHeads 
            | isConst hop || hop `elem` lconsts =
                (insert (hop, len) cheads, vheads)
            | len > 0 =
                (cheads, insert (hop, len) vheads)
            | otherwise = sofar in
      foldr (getHeads lconsts) newHeads args

getThmHeads :: HOLThm -> ([(HOLTerm, Int)], [(HOLTerm, Int)])
            -> ([(HOLTerm, Int)], [(HOLTerm, Int)])
getThmHeads th = getHeads (catFrees $ hyp th) (concl th)

convAPP :: TriviaCtxt thry => Conversion cls thry
convAPP = convREWR convAPP_pth
    where convAPP_pth :: TriviaCtxt thry => HOL cls thry HOLThm
          convAPP_pth = cacheProof "convAPP_pth" ctxtTrivia .
              prove [txt| !(f:A->B) x. f x = I f x |] $
                tacREWRITE [thmI]

convAPP_N :: TriviaCtxt thry => Int -> Conversion cls thry
convAPP_N 1 = convAPP
convAPP_N n = convRATOR (convAPP_N $ n - 1) `_THEN` convAPP 

convFOL :: TriviaCtxt thry => [(HOLTerm, Int)] 
        -> Conversion cls thry
convFOL hddata = Conv $ \ tm ->
    case tm of
      Forall{} -> runConv (convBINDER $ convFOL hddata) tm
      (_ :/\ _) -> runConv (convBINOP $ convFOL hddata) tm
      (_ :\/ _) -> runConv (convBINOP $ convFOL hddata) tm
      _ ->
          let (op, args) = stripComb tm in
            do th1 <- primREFL op
               th2 <- mapM (runConv (convFOL hddata)) args
               th <- foldlM primMK_COMB th1 th2
               tm' <- rand $ concl th
               let n = case lookup op hddata of
                         Just x -> length args - x
                         Nothing -> 0
               if n == 0
                  then return th
                  else primTRANS th $ runConv (convAPP_N n) tm'

convGEN_FOL :: TriviaCtxt thry => ([(HOLTerm, Int)], [(HOLTerm, Int)]) 
            -> Conversion cls thry
convGEN_FOL (cheads, []) =
    let hops = setify $ map fst cheads
        getMin h = let ns = mapFilter (\ (k, n) -> 
                                       if k == h then return n 
                                       else fail' "getMin") cheads in
                     if length ns < 2 then fail' "getMin" 
                     else return (h, minimum ns)
        hddata = mapFilter getMin hops in
    convFOL hddata
convGEN_FOL (cheads, vheads) =
    let hddata = map (\ t -> case t of
                               (Const "=" _) -> (t, 2)
                               _ -> (t, 0)) 
                   (setify . map fst $ vheads ++ cheads) in
      convFOL hddata
                     

tacASM_FOL :: TriviaCtxt thry => Tactic cls thry
tacASM_FOL gl@(Goal asl _) =
    let headsp = foldr (getThmHeads . snd) ([], []) asl in
      tacRULE_ASSUM (ruleCONV $ convGEN_FOL headsp) gl

-- conv NFF
nnfDConv :: TriviaCtxt thry => Bool 
         -> (HOLTerm -> HOL cls thry (HOLThm, HOLThm)) -> HOLTerm 
         -> HOL cls thry (HOLThm, HOLThm)
nnfDConv cf baseconvs (l :/\ r) =
    (do (thLp, thLn) <- nnfDConv cf baseconvs l
        (thRp, thRn) <- nnfDConv cf baseconvs r
        rth1 <- primINST [(tmP, l), (tmQ, r)] pthNotAnd
        lth <- ruleAP_TERM tmAnd thLp
        th1 <- primMK_COMB lth thRp
        rth2 <- ruleAP_TERM tmOr thLn
        th2 <- primTRANS rth1 $ primMK_COMB rth2 thRn
        return (th1, th2))
    <?> "nnfDConv: conjunction case"
nnfDConv cf baseconvs (l :\/ r) =
    (do (thLp, thLn) <- nnfDConv cf baseconvs l
        (thRp, thRn) <- nnfDConv cf baseconvs r
        rth1 <- primINST [(tmP, l), (tmQ, r)] pthNotOr
        lth <- ruleAP_TERM tmOr thLp
        th1 <- primMK_COMB lth thRp
        rth2 <- ruleAP_TERM tmAnd thLn
        th2 <- primTRANS rth1 $ primMK_COMB rth2 thRn
        return (th1, th2))
    <?> "nnfDConv: disjunction case"
nnfDConv cf baseconvs (l :==> r) =
    (do (thLp, thLn) <- nnfDConv cf baseconvs l
        (thRp, thRn) <- nnfDConv cf baseconvs r
        lth1 <- primINST [(tmP, l), (tmQ, r)] pthImp
        rth1 <- primINST [(tmP, l), (tmQ, r)] pthNotImp
        lth2 <- ruleAP_TERM tmOr thLn
        th1 <- primTRANS lth1 $ primMK_COMB lth2 thRp
        rth2 <- ruleAP_TERM tmAnd thLp
        th2 <- primTRANS rth1 $ primMK_COMB rth2 thRn
        return (th1, th2))
    <?> "nnfDConv: implication case"
nnfDConv True baseconvs (l :<=> r) =
    (do (thLp, thLn) <- nnfDConv True baseconvs l
        (thRp, thRn) <- nnfDConv True baseconvs r
        lth1 <- primINST [(tmP, l), (tmQ, r)] pthEq'
        rth1 <- primINST [(tmP, l), (tmQ, r)] pthNotEq'
        lth2 <- ruleAP_TERM tmOr thLp
        lth3 <- ruleAP_TERM tmAnd $ primMK_COMB lth2 thRn
        lth4 <- ruleAP_TERM tmOr thLn
        th1 <- primTRANS lth1 . primMK_COMB lth3 $ primMK_COMB lth4 thRp
        rth2 <- ruleAP_TERM tmOr thLp
        rth3 <- ruleAP_TERM tmAnd $ primMK_COMB rth2 thRp
        rth4 <- ruleAP_TERM tmOr thLn
        th2 <- primTRANS rth1 . primMK_COMB rth3 $ primMK_COMB rth4 thRn
        return (th1, th2))
    <?> "nnfDConv: true equality case"
nnfDConv False baseconvs (l :<=> r) =
    (do (thLp, thLn) <- nnfDConv False baseconvs l
        (thRp, thRn) <- nnfDConv False baseconvs r
        lth1 <- primINST [(tmP, l), (tmQ, r)] pthEq
        rth1 <- primINST [(tmP, l), (tmQ, r)] pthNotEq
        lth2 <- ruleAP_TERM tmAnd thLp
        lth3 <- ruleAP_TERM tmOr $ primMK_COMB lth2 thRp
        lth4 <- ruleAP_TERM tmAnd thLn
        th1 <- primTRANS lth1 . primMK_COMB lth3 $ primMK_COMB lth4 thRn
        rth2 <- ruleAP_TERM tmAnd thLp
        rth3 <- ruleAP_TERM tmOr $ primMK_COMB rth2 thRn
        rth4 <- ruleAP_TERM tmAnd thLn
        th2 <- primTRANS rth1 . primMK_COMB rth3 $ primMK_COMB rth4 thRp
        return (th1, th2))
        <?> "nnfDConv: equality case"
nnfDConv _ baseconvs (Comb q@(Const "!" ((ty :-> _) :-> _)) bod@(Abs x t)) =
    (do (thP, thN) <- nnfDConv True baseconvs t
        th1 <- ruleAP_TERM q $ primABS x thP
        p <- liftM (mkVar "P") $ mkFunTy ty tyBool
        rth1 <- primINST [(p, bod)] $ primINST_TYPE [(tyA, ty)] pthNotForall
        rth2 <- ruleAP_TERM tmNot . primBETA $ mkComb bod x
        rth3 <- primTRANS rth2 thN
        rth4 <- ruleMK_EXISTS x rth3
        th2 <- primTRANS rth1 rth4
        return (th1, th2))
    <?> "nnfDConv: forall case"
nnfDConv cf baseconvs (Comb q@(Const "?" ((ty :-> _) :-> _)) bod@(Abs x t)) =
    (do (thP, thN) <- nnfDConv cf baseconvs t
        th1 <- ruleAP_TERM q $ primABS x thP
        p <- liftM (mkVar "P") $ mkFunTy ty tyBool
        rth1 <- primINST [(p, bod)] $ primINST_TYPE [(tyA, ty)] pthNotExists
        rth2 <- ruleAP_TERM tmNot . primBETA $ mkComb bod x
        rth3 <- primTRANS rth2 thN
        rth4 <- ruleMK_FORALL x rth3
        th2 <- primTRANS rth1 rth4 
        return (th1, th2))
    <?> "nnfDConv: exists case"
nnfDConv cf baseconvs (Comb (Const "?!" ((ty :-> _) :-> _)) bod@(Abs x t)) =
    (do (thP, thN) <- nnfDConv cf baseconvs t
        let y = variant (x : frees t) x
        eq <- mkEq y x
        (ethP, ethN) <- baseconvs eq
        bth <- primBETA $ mkComb bod x
        bth' <- runConv convBETA $ mkComb bod y
        thP' <- primINST [(x, y)] thP
        thN' <- primINST [(x, y)] thN
        p <- liftM (mkVar "P") $ mkFunTy ty tyBool
        lth1 <- primINST [(p, bod)] $ primINST_TYPE [(tyA, ty)] pthExu
        rth1 <- primINST [(p, bod)] $ primINST_TYPE [(tyA, ty)] pthNotExu
        lth2 <- ruleMK_EXISTS x $ primTRANS bth thP
        lth3 <- ruleAP_TERM tmAnd lth2
        lth4 <- ruleAP_TERM tmNot bth
        lth5 <- ruleAP_TERM tmOr $ primTRANS lth4 thN
        lth6 <- ruleAP_TERM tmNot bth'
        lth7 <- ruleAP_TERM tmOr $ primTRANS lth6 thN'
        lth8 <- primMK_COMB lth5 $ primMK_COMB lth7 ethP
        lth9 <- ruleMK_FORALL x $ ruleMK_FORALL y lth8
        lth10 <- primMK_COMB lth3 lth9
        rth2 <- primTRANS (ruleAP_TERM tmNot bth) thN
        rth3 <- ruleMK_FORALL x rth2
        rth4 <- ruleAP_TERM tmOr rth3
        rth5 <- ruleAP_TERM tmAnd $ primTRANS bth thP
        rth6 <- ruleAP_TERM tmAnd $ primTRANS bth' thP'
        rth7 <- primMK_COMB rth5 $ primMK_COMB rth6 ethN
        rth8 <- ruleMK_EXISTS x $ ruleMK_EXISTS y rth7
        rth9 <- primMK_COMB rth4 rth8
        th1 <- primTRANS lth1 lth10
        th2 <- primTRANS rth1 rth9
        return (th1, th2))
    <?> "nnfDConv: unique exists case"
nnfDConv cf baseconvs (Neg t) =
    (do (th1, th2) <- nnfDConv cf baseconvs t
        rth1 <- primINST [(tmP, t)] pthNotNot
        rth2 <- primTRANS rth1 th1
        return (th2, rth2))
    <?> "nnfDConv: not case"
nnfDConv _ baseconvs tm = nnfDConvBase baseconvs tm

nnfDConvBase :: (HOLTerm -> HOL cls thry (HOLThm, HOLThm)) -> HOLTerm 
             -> HOL cls thry (HOLThm, HOLThm)
nnfDConvBase baseconvs tm =
    (baseconvs tm <|> 
     (do th1 <- primREFL tm
         th2 <- primREFL $ mkNeg tm
         return (th1, th2)))
    <?> "nnfDConv: base case"

type NNFConv cls thry = 
    Bool -> (Conversion cls thry, HOLTerm -> HOL cls thry (HOLThm, HOLThm)) -> 
    Conversion cls thry

nnfConv' :: forall cls thry. TriviaCtxt thry => NNFConv cls thry
nnfConv' cf baseconvs@(base1, base2) = Conv $ \ tm ->
    case tm of
      (l :/\ r) ->
          let ?pth = pthNotAnd
              ?lconv = nnfConv'
              ?rconv = nnfConv'
              ?btm = tmOr in
            boolCase "conjunction" l r
      (l :\/ r) ->
          let ?pth = pthNotOr
              ?lconv = nnfConv'
              ?rconv = nnfConv'
              ?btm = tmAnd in
            boolCase "disjunction" l r
      (l :==> r) ->
          let ?pth = pthNotImp
              ?lconv = nnfConv
              ?rconv = nnfConv'
              ?btm = tmAnd in
            boolCase "implication" l r
      (l :<=> r) ->
          (do (thLp, thLn) <- nnfDConv cf base2 l
              (thRp, thRn) <- nnfDConv cf base2 r
              pth <- if cf then pthNotEq' else pthNotEq
              let (ltm, rtm) = if cf then (tmOr, tmAnd) else (tmAnd, tmOr)
                  (rth1, rth2) = if cf then (thRp, thRn) else (thRn, thRp)
              lth1 <- primINST [(tmP, l), (tmQ, r)] pth
              lth2 <- ruleAP_TERM ltm thLp
              lth3 <- ruleAP_TERM rtm $ primMK_COMB lth2 rth1
              lth4 <- ruleAP_TERM ltm thLn
              primTRANS lth1 . primMK_COMB lth3 $ primMK_COMB lth4 rth2)
          <?> "nnfConv': equality case"
      (BindWhole "!" bod@(Abs x@(Var _ ty) t)) ->
          let ?pth = pthNotForall
              ?cf = cf
              ?rule = ruleMK_EXISTS in
            quantCase "forall" bod x t ty
      (BindWhole "?" bod@(Abs x@(Var _ ty) t)) ->
          let ?pth = pthNotExists
              ?cf = True
              ?rule = ruleMK_FORALL in
            quantCase "exists" bod x t ty
      (BindWhole "?!" bod@(Abs x@(Var _ ty) t)) ->
          (do (thP, thN) <- nnfDConv cf base2 t
              let y = variant (x:frees t) x 
              eq <- mkEq y x
              (_, ethN) <- base2 eq
              bth <- primBETA $ mkComb bod x
              bth' <- runConv convBETA $ mkComb bod y
              th1' <- instPth pthNotExu bod ty
              lth1 <- primTRANS (ruleAP_TERM tmNot bth) thN
              lth2 <- ruleMK_FORALL x lth1
              lth3 <- ruleAP_TERM tmOr lth2
              lth4 <- ruleAP_TERM tmAnd $ primTRANS bth thP
              lth5 <- ruleAP_TERM tmAnd . primTRANS bth' $ primINST [(x, y)] thP
              lth6 <- primMK_COMB lth4 $ primMK_COMB lth5 ethN
              lth7 <- ruleMK_EXISTS x $ ruleMK_EXISTS y lth6
              primTRANS th1' $ primMK_COMB lth3 lth7)
          <?> "nnfConv': unique exists case"
      (Neg t) ->
          (do th1 <- runConv (nnfConv cf baseconvs) t
              primTRANS (primINST [(tmP, t)] pthNotNot) th1)
          <?> "nnfConv': not case"
      _ -> baseCase tm
  where boolCase :: (TriviaCtxt thry, ?pth :: HOL cls thry HOLThm, 
                     ?lconv :: NNFConv cls thry,
                     ?rconv :: NNFConv cls thry, ?btm :: HOL cls thry HOLTerm) 
                 => String -> HOLTerm -> HOLTerm -> HOL cls thry HOLThm
        boolCase err l r =
            (do pth <- ?pth
                lth <- runConv (?lconv cf baseconvs) l
                rth <- runConv (?rconv cf baseconvs) r
                lth1 <- primINST [(tmP, l), (tmQ, r)] pth
                lth2 <- ruleAP_TERM ?btm lth
                primTRANS lth1 $ primMK_COMB lth2 rth)
             <?> ("nnfConv': " ++ err ++ " case")

        quantCase :: (TriviaCtxt thry, ?pth :: HOL cls thry HOLThm, ?cf :: Bool,
                      ?rule :: HOLTerm -> HOLThm -> HOL cls thry HOLThm) 
                  => String -> HOLTerm -> HOLTerm -> HOLTerm -> HOLType 
                  -> HOL cls thry HOLThm
        quantCase err bod x t ty =
            (do pth <- ?pth
                thN <- runConv (nnfConv' ?cf baseconvs) t
                th1 <- instPth pth bod ty
                lth <- ruleAP_TERM tmNot . primBETA $ mkComb bod x
                th2 <- ?rule x =<< primTRANS lth thN
                primTRANS th1 th2)
             <?> ("nnfConv': " ++ err ++ " case")

        baseCase :: TriviaCtxt thry => HOLTerm -> HOL cls thry HOLThm
        baseCase tm = 
            (do tm' <- mkNeg tm
                runConv base1 tm' <|> (primREFL tm'))
            <?>" nnfConv': base case"

        instPth :: HOLThmRep thm cls thry 
                => thm -> HOLTerm -> HOLType -> HOL cls thry HOLThm
        instPth pth bod ty =
            do p <- liftM (mkVar "P") $ mkFunTy ty tyBool
               primINST [(p, bod)] $ primINST_TYPE [(tyA, ty)] pth
    

nnfConv :: TriviaCtxt thry => NNFConv cls thry
nnfConv cf baseconvs@(base1, base2) = Conv $ \ tm ->
    case tm of
      (l :/\ r) ->
          (do thLp <- runConv (nnfConv cf baseconvs) l
              thRp <- runConv (nnfConv cf baseconvs) r
              lth <- ruleAP_TERM tmAnd thLp
              primMK_COMB lth thRp)
          <?> "nnfConv: conjunction case"
      (l :\/ r) ->
          (do thLp <- runConv (nnfConv cf baseconvs) l
              thRp <- runConv (nnfConv cf baseconvs) r
              lth <- ruleAP_TERM tmOr thLp
              primMK_COMB lth thRp)
          <?> "nnfConv: disjunction case"
      (l :==> r) ->
          (do thLn <- runConv (nnfConv' cf baseconvs) l
              thRp <- runConv (nnfConv cf baseconvs) r
              lth1 <- primINST [(tmP, l), (tmQ, r)] pthImp
              lth2 <- ruleAP_TERM tmOr thLn
              primTRANS lth1 $ primMK_COMB lth2 thRp)
          <?> "nnfConv: implication case"
      (l :<=> r) ->
          (do (thLp, thLn) <- nnfDConv cf base2 l
              (thRp, thRn) <- nnfDConv cf base2 r
              if cf
                 then do lth1 <- primINST [(tmP, l), (tmQ, r)] pthEq'
                         lth2 <- ruleAP_TERM tmOr thLp
                         lth3 <- ruleAP_TERM tmOr thLn
                         lth4 <- ruleAP_TERM tmAnd $ primMK_COMB lth2 thRn 
                         primTRANS lth1 . primMK_COMB lth4 $ 
                           primMK_COMB lth3 thRp
                 else do lth1 <- primINST [(tmP, l), (tmQ, r)] pthEq
                         lth2 <- ruleAP_TERM tmAnd thLp
                         lth3 <- ruleAP_TERM tmAnd thLn
                         lth4 <- ruleAP_TERM tmOr $ primMK_COMB lth2 thRp
                         primTRANS lth1 . primMK_COMB lth4 $ 
                           primMK_COMB lth3 thRn)
          <?> "nnfConv: equation case"
      (Comb q@(Const "!" _) (Abs x t)) ->
          (do thP <- runConv (nnfConv True baseconvs) t
              ruleAP_TERM q $ primABS x thP)
          <?> "nnfConv: forall case"
      (Comb q@(Const "?" _) (Abs x t)) ->
          (do thP <- runConv (nnfConv cf baseconvs) t
              ruleAP_TERM q $ primABS x thP)
          <?> "nnfConv: exists case"
      (BindWhole "?!" bod@(Abs x@(Var _ ty) t)) ->
          (do (thP, thN) <- nnfDConv cf base2 t
              let y = variant (x:frees t) x
              eq <- mkEq y x
              (ethP, _) <- base2 eq
              bth <- primBETA $ mkComb bod x
              bth' <- runConv convBETA $ mkComb bod y
              thN' <- primINST [(x, y)] thN
              p <- liftM (mkVar "P") $ mkFunTy ty tyBool
              th1 <- primINST [(p, bod)] $ primINST_TYPE [(tyA, ty)] pthExu
              th2 <- ruleMK_EXISTS x $ primTRANS bth thP
              lth1 <- ruleAP_TERM tmAnd th2
              lth2 <- ruleAP_TERM tmNot bth
              lth3 <- ruleAP_TERM tmOr $ primTRANS lth2 thN
              lth4 <- ruleAP_TERM tmNot bth'
              lth5 <- ruleAP_TERM tmOr $ primTRANS lth4 thN'
              lth6 <- primMK_COMB lth3 $ primMK_COMB lth5 ethP
              th3 <- ruleMK_FORALL x $ ruleMK_FORALL y lth6
              primTRANS th1 $ primMK_COMB lth1 th3)
          <?> "nnfConv: unique exists case"
      (Neg t) ->
          runConv (nnfConv' cf baseconvs) t
      _ -> nnfConvBase base1 tm

nnfConvBase :: Conversion cls thry -> HOLTerm -> HOL cls thry HOLThm
nnfConvBase base1 tm =
    (runConv base1 tm <|> (primREFL tm))
    <?> "nnfConv: base case"


convGEN_NNF :: TriviaCtxt thry => Bool 
            -> (Conversion cls thry, HOLTerm -> HOL cls thry (HOLThm, HOLThm)) 
            -> Conversion cls thry
convGEN_NNF = nnfConv

convNNF :: TriviaCtxt thry => Conversion cls thry
convNNF = convGEN_NNF False (_ALL, \ t -> do th1 <- primREFL t
                                             th2 <- primREFL $ mkNeg t
                                             return (th1, th2))

convNNFC :: TriviaCtxt thry => Conversion cls thry
convNNFC = convGEN_NNF True (_ALL, \ t -> do th1 <- primREFL t
                                             th2 <- primREFL $ mkNeg t
                                             return (th1, th2))
                                                     
convPROP_ATOM :: Conversion cls thry -> Conversion cls thry
convPROP_ATOM conv = Conv $ \ tm ->
  case tm of
    (Comb (Const op _) Abs{})
        | op == "!" || op == "?" || op == "?!" ->
            runConv (convBINDER (convPROP_ATOM conv)) tm
        | otherwise -> runConv (_TRY conv) tm
    (Comb (Comb (Const op (TyFun TyBool _)) _) _)
        | op == "/\\" || op == "\\/" || op == "==>" || op == "=" ->
            runConv (convBINOP (convPROP_ATOM conv)) tm
        | otherwise -> runConv (_TRY conv) tm
    (Comb (Const "~" _) _) -> runConv (convRAND (convPROP_ATOM conv)) tm
    _ -> runConv (_TRY conv) tm
