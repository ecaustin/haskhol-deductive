{-# LANGUAGE FlexibleContexts, PatternSynonyms #-}
{-|
  Module:    HaskHOL.Lib.IndDefs
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.IndDefs
    ( IndDefsCtxt
    , ctxtIndDefs
    , indDefs
    , ruleRIGHT_BETAS
    , ruleEXISTS_EQUATION
    , tacMONO
    , proveMonotonicityHyps
    , deriveNonschematicInductiveRelations
    , proveInductiveRelationsExist
    , newInductiveDefinition
    , getInductiveDefinition
    , addMonoThm
    , thmIMP_REFL
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Bool
import HaskHOL.Lib.Equal
import HaskHOL.Lib.Itab
import HaskHOL.Lib.Theorems
import HaskHOL.Lib.Simp
import HaskHOL.Lib.DRule
import HaskHOL.Lib.Tactics

import HaskHOL.Lib.IndDefs.Base
import HaskHOL.Lib.IndDefs.Context


strip_ncomb :: Int -> HOLTerm -> Maybe (HOLTerm, [HOLTerm])
strip_ncomb n tm = stripRec n tm []
    where stripRec x t acc
              | x < 1 = Just (t, acc)
              | otherwise = case t of
                              (Comb l r) -> stripRec (x - 1) l (r:acc)
                              _ -> Nothing

ruleRIGHT_BETAS :: [HOLTerm] -> HOLThm -> HOL cls thry HOLThm
ruleRIGHT_BETAS tms thm = 
    foldlM (\ a b -> ruleCONV (convRAND convBETA) #<< 
                       ruleAP_THM a b) thm tms

ruleEXISTS_EQUATION :: IndDefsCtxt thry => HOLTerm -> HOLThm 
                    -> HOL cls thry HOLThm
ruleEXISTS_EQUATION tm thm =
    do (l, r, p, pL) <- liftEither "ruleEXISTS_EQUATION: mkTerms" $
                        do (l, r) <- note "" $ destEq tm
                           p <- mkAbs l $ concl thm
                           pL <- mkComb p l
                           return (l, r, p, pL)
       th1 <- ruleISPECL [p, r] ruleEXISTS_EQUATION_pth
       th2 <- liftM (fromRight . ruleSYM) $ runConv convBETA pL
       ruleMP th1 =<< ruleGEN l =<< ruleDISCH tm #<< primEQ_MP th2 thm
  where ruleEXISTS_EQUATION_pth :: IndDefsCtxt thry => HOL cls thry HOLThm
        ruleEXISTS_EQUATION_pth = 
            cacheProof "ruleEXISTS_EQUATION_pth" ctxtIndDefs $
              do t <- toHTm "t:A"
                 dexists <- defEXISTS
                 prove "!P t. (!x:A. (x = t) ==> P x) ==> (?) P" $
                   tacREWRITE [dexists] `_THEN`
                   tacBETA `_THEN`
                   _REPEAT tacSTRIP `_THEN`
                   _FIRST_ASSUM tacMATCH_MP `_THEN`
                   tacEXISTS t `_THEN`
                   _FIRST_ASSUM tacMATCH_MP `_THEN`
                   tacREFL

 
getConcl :: HOLTerm -> HOLTerm
getConcl tm = fromJust $
    do bod <- repeatM (liftM snd . destForall) tm
       liftM snd (destImp bod) <|> return bod

ruleCONJ_ACI :: TheoremsCtxt thry => HOLTerm -> HOL cls thry HOLThm
ruleCONJ_ACI tm = 
    do thm <- thmCONJ_ACI
       runConv (convAC thm) tm

ruleSIMPLE_DISJ_PAIR :: BoolCtxt thry => HOLThm -> HOL cls thry (HOLThm, HOLThm)
ruleSIMPLE_DISJ_PAIR thm =
    do (l, r) <- liftMaybe "ruleSIMPLE_DISJ_PAIR: disj theorems" $
                   destDisj . head $ hyp thm
       th1 <- flip ruleDISJ1 r #<< primASSUME l 
       th2 <- ruleDISJ2 l #<< primASSUME r
       return $ pairMap (`rulePROVE_HYP` thm) (th1, th2)


ruleHALF_BETA_EXPAND :: BoolCtxt thry => [HOLTerm] -> HOLThm -> HOL cls thry HOLThm
ruleHALF_BETA_EXPAND args thm = ruleGENL args =<< ruleRIGHT_BETAS args thm

ruleAND_IMPS_CONV :: BoolCtxt thry => HOLTerm -> HOL cls thry HOLThm
ruleAND_IMPS_CONV tm =
    do ths <- ruleCONJUNCTS #<< primASSUME tm
       let avs = fst . stripForall . concl $ head ths
       thl <- mapM (ruleDISCH tm <=< ruleUNDISCH <=< ruleSPEC_ALL) ths
       th1 <- foldr1M ruleSIMPLE_DISJ_CASES thl
       let tm1 = head $ hyp th1
       th2 <- ruleGENL avs =<< ruleDISCH tm1 =<< ruleUNDISCH th1
       let tm2 = concl th2
       th3 <- ruleDISCH tm2 =<< ruleUNDISCH =<< ruleSPEC_ALL #<< 
                primASSUME tm2
       (thts, tht) <- nsplitM ruleSIMPLE_DISJ_PAIR (tail ths) th3
       let procFun thm = let t = head $ hyp thm in
                           ruleGENL avs =<< ruleDISCH t =<< ruleUNDISCH thm
       th4 <- itlistM (liftM1 ruleCONJ . procFun) thts =<< procFun tht
       liftM1 ruleIMP_ANTISYM (ruleDISCH_ALL th2) =<< ruleDISCH_ALL th4

calculateSimpSequence :: [HOLTerm] -> HOLTermEnv -> (HOLTermEnv, HOLTermEnv)
calculateSimpSequence avs plis =
    let oks = getequs avs plis in
      (oks, plis \\ oks)
    where getequs _ [] = []
          getequs as (h@(_, r):t) = 
              if r `elem` as
              then h : getequs as (filter (\ (_, x) -> x /= r) t)
              else getequs as t 

convFORALL_IMPS :: BoolCtxt thry => Conversion cls thry
convFORALL_IMPS = Conv $ \ tm ->
    let (avs, bod) = stripForall tm in
      do th1 <- ruleDISCH tm =<< ruleUNDISCH =<< ruleSPEC_ALL =<< 
                  liftEither "convFORALL_IMPS: primASSUME" (primASSUME tm)
         th2 <- foldrM ruleSIMPLE_CHOOSE th1 avs
         tm2 <- liftMaybe "convFORALL_IMPS" . tryHead $ hyp th2
         th3 <- ruleDISCH tm2 =<< ruleUNDISCH th2
         th4 <- liftEither "convFORALL_IMPS: primASSUME" . primASSUME $ concl th3
         ant <- liftMaybe "convFORALL_IMPS: lHand" $ lHand bod
         th5 <- liftEither "convFORALL_IMPS: primASSUME" $ primASSUME ant
         th6 <- foldrM ruleSIMPLE_EXISTS th5 avs
         th7 <- ruleGENL avs =<< ruleDISCH ant =<< ruleMP th4 th6
         th8 <- ruleDISCH_ALL th3
         ruleIMP_ANTISYM th8 =<< ruleDISCH_ALL th7

canonicalizeClause :: IndDefsCtxt thry => HOLTerm -> [HOLTerm] -> HOL cls thry HOLThm
canonicalizeClause cls args =
    (do trueTm <- serve [indDefs| T |]
        let (avs, bimp) = stripForall cls
            (ant, con) = fromMaybe (trueTm, bimp) $ destImp bimp
            (rel, xargs) = stripComb con
            plis = zip args xargs
            (yes, no) = calculateSimpSequence avs plis
            nvs = filter (\ x -> x `notElem` map snd yes) avs
            canon' = canon rel plis yes nvs
        eth <- if isImp bimp 
               then do atm <- foldrM (\ x y -> liftM1 mkConj (uncurry mkEq x) y)
                                ant $ yes ++ no
                       (ths, tth) <- nsplitM ruleCONJ_PAIR plis #<< 
                                       primASSUME atm
                       th0 <- liftM1 ruleMP (ruleSPECL avs #<< primASSUME cls)
                                tth
                       (th6, th5') <- canon' atm th0 ths
                       th7 <- itlistM (ruleCONJ . primREFL . snd) no #<<
                                primASSUME ant
                       th8 <- ruleGENL avs =<< ruleDISCH ant =<< ruleMP th6 th7
                       ruleIMP_ANTISYM th5' =<< ruleDISCH_ALL th8
               else do atm <- listMkConj =<< mapM (uncurry mkEq) (yes ++ no)
                       ths <- ruleCONJUNCTS #<< primASSUME atm
                       th0 <- ruleSPECL avs #<< primASSUME cls
                       (th6, th5') <- canon' atm th0 ths
                       th7 <- foldr1M ruleCONJ $ map (primREFL . snd) no
                       th8 <- ruleGENL avs =<< ruleMP th6 th7
                       ruleIMP_ANTISYM th5' =<< ruleDISCH_ALL th8
        ftm <- fromJustM $ funpowM (length args) (body <=< rand) =<< 
                 rand (concl eth)
        fth' <- itlistM ruleMK_FORALL args =<< runConv convFORALL_IMPS ftm
        fromRightM $ primTRANS eth fth')
    <?> "canonicalizeClause"
  where canon :: BoolCtxt thry => HOLTerm -> HOLTermEnv -> HOLTermEnv 
              -> [HOLTerm] -> HOLTerm -> HOLThm -> [HOLThm] 
              -> HOL cls thry (HOLThm, HOLThm)
        canon rel plis yes nvs atm th0 ths =
            do thl <- fromJustM $ 
                        mapM (\ t -> find (\ th -> lhs (concl th) == 
                                                   Just t) ths) args
               th1 <- fromRightM $ foldlM primMK_COMB (primREFL rel) thl
               th1_5 <- fromRightM $ ruleSYM th1
               th2 <- fromRightM $ primEQ_MP th1_5 th0
               th3 <- ruleDISCH atm th2
               tm4 <- fromJustM $ funpowM (length yes) rand =<< lHand =<<
                        liftM concl (primINST yes th3)
               th4 <- itlistM (ruleCONJ . primREFL . fst) yes #<<
                        primASSUME tm4
               th5 <- ruleGENL args =<< ruleGENL nvs =<< 
                        ruleDISCH tm4 =<< ruleMP th3 th4
               th6 <- ruleSPECL nvs =<< ruleSPECL (map snd plis) #<<
                        primASSUME (concl th5)
               th5' <- ruleDISCH_ALL th5
               return (th6, th5')
           
canonicalizeClauses :: IndDefsCtxt thry => [HOLTerm] -> HOL cls thry HOLThm
canonicalizeClauses clauses = 
  let concls = map getConcl clauses
      uncs = map stripComb concls
      rels = foldr (insert . fst) [] uncs in
    do xargs <- liftMaybe "canonicalizeClauses: lookup" $
                  mapM (`lookup` uncs) rels
       closed <- listMkConj clauses
       let avoids = variables closed
           flargs = mkArgs "a" avoids . map typeOf $ foldr1 (++) xargs
       cargs <- liftMaybe "canonicalClauses: zargs and cargs" $
                  do zargs <- liftM (zip rels) $ shareOut xargs flargs
                     mapM (\ (x, _) -> x `lookup` zargs) uncs
       cthms <- map2M canonicalizeClause clauses cargs
       pclauses <- liftMaybe "canonicalizeClauses: rand" $ 
                     mapM (rand . concl) cthms
       let collectClauses tm = mapFilter (\ (x, y) -> if x == tm 
                                                      then Just y 
                                                      else Nothing) $  
                                 zip (map fst uncs) pclauses
           clausell = map collectClauses rels
       cclausel <- mapM listMkConj clausell
       cclauses <- listMkConj cclausel
       oclauses <- listMkConj pclauses
       eth <- ruleCONJ_ACI =<< mkEq oclauses cclauses
       cth <- foldr1M ruleMK_CONJ cthms
       pth <- fromRightM $ primTRANS cth eth
       th1 <- foldr1M ruleMK_CONJ =<< mapM ruleAND_IMPS_CONV cclausel 
       fromRightM $ primTRANS pth th1

deriveCanonInductiveRelations :: BoolCtxt thry => [HOLTerm] 
                              -> HOL cls thry HOLThm
deriveCanonInductiveRelations cls =
    (do closed <- listMkConj cls
        let clauses = conjuncts closed
            (vargs, bodies) = unzip $ map stripForall clauses
            (ants, concs) = unzip . fromJust $ mapM destImp bodies
            rels = fromJust $ mapM (repeatM rator) concs
            avoids = variables closed
            rels' = variants avoids rels
            crels = zip rels rels'
            primeFun = subst crels
        closed' <- liftO $ primeFun closed
        defTms <- map2M (mkDef primeFun closed' rels') vargs concs
        defThms <- map2M ruleHALF_BETA_EXPAND vargs #<< mapM primASSUME defTms
        indThms <- map2M (mkInd rels') vargs defThms
        indThmr <- foldr1M ruleCONJ indThms
        indThm <- ruleGENL rels' =<< ruleDISCH closed' indThmr
        mConcs <- map2M (\ a t -> do t' <- mkImp t #<< primeFun t
                                     listMkForall a t') vargs ants
        monoTm <- mkImp (concl indThmr) =<< listMkConj mConcs
        monoTm' <- listMkForall rels' monoTm
        forallMonoTm' <- listMkForall rels monoTm'
        monoThm <- fromRightM $ primASSUME forallMonoTm'
        closeThm <- fromRightM $ primASSUME closed'
        monoTh1 <- ruleSPEC_ALL monoThm
        monoTh2 <- ruleSPECL rels' indThm
        monoThms <- ruleCONJUNCTS =<< ruleMP monoTh1 =<< ruleMP monoTh2 closeThm
        closeThms <- ruleCONJUNCTS closeThm
        ruleThms <- map2M (proveRule rels' closed') monoThms $ zip closeThms defThms
        ruleThm <- foldr1M ruleCONJ ruleThms
        dTms <- fromRightM $ map2M listMkAbs vargs ants
        let doubleFun = subst (zip rels dTms)
        unThs <- map2M (mkUnbetas doubleFun) clauses dTms
        unThs' <- liftM (fromRight . ruleSYM) . foldr1M ruleMK_CONJ $ map fst unThs
        irThm <- fromRightM $ primEQ_MP unThs' ruleThm
        monoThm' <- ruleSPECL rels =<< ruleSPECL dTms monoThm
        mrThm <- ruleMP monoThm' irThm
        unThs'' <- liftM (fromRight . ruleSYM) . foldr1M ruleMK_CONJ $ map (fst . snd) unThs
        imrThm <- fromRightM $ primEQ_MP unThs'' mrThm
        indThm' <- ruleSPECL dTms indThm
        ifThm <- ruleMP indThm' imrThm
        unThs''' <- foldr1M ruleMK_CONJ $ map (snd . snd) unThs
        fThm <- fromRightM $ primEQ_MP unThs''' ifThm
        fThms <- ruleCONJUNCTS fThm
        caseThm <- foldr1M ruleCONJ =<< map2M mkCase fThms =<< ruleCONJUNCTS ruleThm
        ruleCONJ ruleThm =<< ruleCONJ indThm caseThm)
    <?> "deriveCanonInductiveRelations"

    where mkDef f closed rels arg con = 
              do tm <- mkImp closed #<< f con
                 tm' <- listMkForall rels tm
                 (l, r) <- liftEither "mkDef" $ do l <- note "" $ repeatM rator con
                                                   r <- listMkAbs arg tm'
                                                   return (l, r)
                 mkEq l r
          
          mkInd :: BoolCtxt thry => [HOLTerm] -> [HOLTerm] -> HOLThm 
                -> HOL cls thry HOLThm
          mkInd rels args thm = 
              do (th1, _) <- ruleEQ_IMP =<< ruleSPEC_ALL thm
                 ant <- liftMaybe "mkInd: lHand" . lHand $ concl th1
                 th2 <- ruleSPECL rels =<< ruleUNDISCH th1
                 ruleGENL args =<< ruleDISCH ant =<< ruleUNDISCH th2

          proveRule :: BoolCtxt thry => [HOLTerm] -> HOLTerm -> HOLThm 
                    -> (HOLThm, HOLThm) -> HOL cls thry HOLThm
          proveRule rels closed mth (cth, dth) = 
              let (avs, bod) = stripForall $ concl mth in
                do th1 <- ruleSPECL avs mth
                   th2 <- ruleIMP_TRANS th1 =<< ruleSPECL avs cth
                   th3 <- ruleGENL rels =<< ruleDISCH closed =<< ruleUNDISCH th2
                   th4 <- liftM (fromRight . ruleSYM) $ ruleSPECL avs dth
                   tm <- liftMaybe "proveRule: lHand" $ lHand bod
                   ruleGENL avs =<< ruleDISCH tm #<< primEQ_MP th4 th3

          mkUnbetas f tm dtm = case stripForall tm of
                                 (avs, Comb (Comb i l) r) -> 
                                     do bth <- ruleRIGHT_BETAS avs $ primREFL dtm
                                        let l' = fromJust $ f l
                                        (il', ir) <- liftEither "mkUnbetas: mkComb" $ pairMapM (mkComb i) (l', r)
                                        (munb, iunb, junb) <- fromRightM $ do munb <- flip ruleAP_THM r =<< ruleAP_TERM i bth
                                                                              iunb <- ruleAP_TERM il' bth
                                                                              junb <- ruleAP_TERM ir bth
                                                                              return (munb, iunb, junb)
                                        let quantify th = foldrM ruleMK_FORALL th avs
                                        munb' <- quantify munb
                                        iunb' <- quantify iunb
                                        junb' <- quantify junb
                                        return (munb', (iunb', junb'))
                                 _ -> fail "mkUnbetas"

          mkCase th1 th2 = let (avs, _) = stripForall $ concl th1 in
                             do th1' <- ruleSPEC_ALL th1
                                ruleGENL avs =<< ruleIMP_ANTISYM th1' =<< 
                                  ruleSPEC_ALL th2

deriveNonschematicInductiveRelations :: IndDefsCtxt thry => HOLTerm 
                                     -> HOL cls thry HOLThm
deriveNonschematicInductiveRelations tm =
    let clauses = conjuncts tm in
      do canonThm <- canonicalizeClauses clauses
         canonThm' <- fromRightM $ ruleSYM canonThm
         pclosed <- liftMaybe "deriveNonschematicInductiveRelations" . rand $ concl canonThm
         let pclauses = conjuncts pclosed
         rawThm <- deriveCanonInductiveRelations pclauses
         (ruleThm, otherThms) <- ruleCONJ_PAIR rawThm
         (indThm, caseThm) <- ruleCONJ_PAIR otherThms
         ruleThm' <- fromRightM $ primEQ_MP canonThm' ruleThm
         indThm' <- ruleCONV (convONCE_DEPTH (convREWR canonThm')) indThm
         ruleCONJ ruleThm' =<< ruleCONJ indThm' caseThm

tacBackChain :: BoolCtxt thry => HOLThm -> Tactic cls thry
tacBackChain thm (Goal asl w) =
    let matchFun = rulePART_MATCH (liftM snd . destImp) thm in
      do th1 <- matchFun w
         case destImp $ concl th1 of
           Just (ant, _) -> return . GS nullMeta [Goal asl ant] $ just th1
           _ -> fail "tacBackChain"
    where just th i (t:[]) = do th' <- ruleINSTANTIATE i th
                                ruleMATCH_MP th' t
          just _ _ _ = fail "tacBackChain: bad justification"

tacMonoAbs :: IndDefsCtxt thry => Tactic cls thry
tacMonoAbs g@(Goal _ w) =
    do imp <- serve [indDefs| (==>) |]
       (ant, con) <- liftMaybe "tacMonoAbs: goal not an implication" $ destImp w
       let (_, vars) = stripComb con
           rnum = length vars - 1
       ((hd1, args1), (hd2, args2)) <- liftMaybe "tacMonoAbs: strip_ncomb failed" $ 
                                       pairMapM (strip_ncomb rnum) (ant, con)
       hd1th <- runConv convBETA hd1
       th1 <- fromRightM $ foldlM ruleAP_THM hd1th args1
       hd2th <- runConv convBETA hd2
       th4 <- fromRightM $ do th2 <- foldlM ruleAP_THM hd2th args2
                              th3 <- ruleAP_TERM imp th1
                              primMK_COMB th3 th2
       tacCONV (convREWR th4) g

thmIMP_REFL :: IndDefsCtxt thry => HOL cls thry HOLThm
thmIMP_REFL = cacheProof "thmIMP_REFL" ctxtIndDefs $
    ruleITAUT "!p . p ==> p"

tacApplyMono :: IndDefsCtxt thry => [(Text, Tactic cls thry)] 
             -> Tactic cls thry
tacApplyMono tacs g@(Goal _ w) =
    case destImp w of
      Just (a,c) -> if a `aConv` c then do th <- ruleSPEC a thmIMP_REFL
                                           tacACCEPT th g
                    else let cn = case repeatM rator c of
                                    Just (Const n _) -> n
                                    _ -> "" in
                           tryFind (\ (k, t) -> if k == cn then t g else fail "") tacs
      _ -> fail "tacApplyMono: not an implication"

tacMONO :: IndDefsCtxt thry => Tactic cls thry
tacMONO g = 
    do acid <- openLocalStateHOL (MonoThms [])
       thms <- queryHOL acid GetMonos
       closeAcidStateHOL acid
       tacs <- liftMaybe "tacMONO: tacs" $ foldrM tacFun [("", tacMonoAbs)] thms
       let tacMonoStep = _REPEAT tacGEN `_THEN` tacApplyMono tacs
       (_REPEAT tacMonoStep `_THEN` tacASM_REWRITE_NIL) g
    where tacFun th l =
              do x <- rand =<< rand (concl th)
                 x' <- repeatM rator x
                 let c = case x' of
                             Const n _ -> n
                             _ -> ""
                 return ((c, tacBackChain th `_THEN` _REPEAT tacCONJ) : l)

proveMonotonicityHyps :: IndDefsCtxt thry => HOLThm -> HOL cls thry HOLThm
proveMonotonicityHyps thm = 
    let proveFun :: IndDefsCtxt thry => HOLTerm -> HOL cls thry HOLThm
        proveFun t = prove t $ _REPEAT tacGEN `_THEN`
                               _DISCH_THEN (_REPEAT _CONJUNCTS_THEN tacASSUME) `_THEN`
                               _REPEAT tacCONJ `_THEN` tacMONO in
      do mths <- mapFilterM proveFun . filter (not . isEq) $ hyp thm
         return $ foldr rulePROVE_HYP thm mths

data IndDefs = IndDefs !(Map Text (HOLThm, HOLThm, HOLThm)) deriving Typeable

deriveSafeCopy 0 'base ''IndDefs

addInductiveDef :: Text -> (HOLThm, HOLThm, HOLThm) -> Update IndDefs ()
addInductiveDef lbl trip =
    do (IndDefs defs) <- get
       put (IndDefs (mapInsert lbl trip defs))

getInductiveDefs :: Query IndDefs [(HOLThm, HOLThm, HOLThm)]
getInductiveDefs =
    do (IndDefs defs) <- ask
       return $! mapElems defs

getAnInductiveDef :: Text -> Query IndDefs (Maybe (HOLThm, HOLThm, HOLThm))
getAnInductiveDef ty =
    do (IndDefs defs) <- ask
       return $! mapLookup ty defs

makeAcidic ''IndDefs ['addInductiveDef, 'getInductiveDefs, 'getAnInductiveDef]

generalizeDef :: BoolCtxt thry => [HOLTerm] -> HOLTerm -> HOLThm 
              -> HOL cls thry HOLThm
generalizeDef vs tm thm =
    case destEq tm of
      Just (l@(Var lname lty), r) -> 
          do ty <- foldrM (mkFunTy . typeOf) lty vs
             r' <- liftEither "generalizeDef: listMkAbs" $ listMkAbs vs r
             tm' <- mkEq (mkVar lname ty) r'
             th0 <- ruleRIGHT_BETAS vs =<< 
                      liftEither "generalizeDef: primASSUME" (primASSUME tm')
             l'' <- liftMaybe "generalizeDef: lHand" . lHand $ concl th0
             th1 <- ruleDISCH tm thm
             ruleMP (fromJust $ primINST [(l'', l)] th1) th0
      _ -> fail "generalizeDef: term not an equation"
                    

generalizeSchematicVariables :: BoolCtxt thry => Bool -> [HOLTerm] -> HOLThm -> HOL cls thry HOLThm
generalizeSchematicVariables gflag vs thm =
    let (defs, others) = partition isEq $ hyp thm in
      do th1 <- foldrM (generalizeDef vs) thm defs
         if gflag
            then do others' <- mapM (\ t -> let fvs = frees t in
                                              do forallT <- listMkForall fvs t
                                                 ruleSPECL fvs =<< liftEither "generalizeSchematicVariables: forallT" (primASSUME forallT)) others
                    ruleGENL vs $ foldr rulePROVE_HYP th1 others'
            else return th1

deriveExistence :: IndDefsCtxt thry => HOLThm -> HOL cls thry HOLThm
deriveExistence thm =
    let defs = filter isEq $ hyp thm in
      foldrM ruleEXISTS_EQUATION thm defs

makeDefinitions :: BoolCtxt thry => HOLThm -> HOL Theory thry HOLThm
makeDefinitions thm =
    let defs = filter isEq $ hyp thm in
      do dths <- mapM (\ x -> case x of
                                ((Var name _) := _) -> newDefinition name x
                                _ -> fail "makeDefinitions") defs
         let insts = zip (fromJust $ mapM lhs defs)
                         (fromJust $ mapM (lhs . concl) dths)
         th <- foldrM ruleDISCH thm defs
         foldlM ruleMP (fromJust $ primINST insts th) dths


unschematizeClauses :: [HOLTerm] -> HOL cls thry ([HOLTerm], [HOLTerm])
unschematizeClauses clauses =
    do schem <- liftMaybe "unschematizeClauses: schem" $ mapM schemFun clauses
       let schems = setify schem
       if isVar (head schem) 
          then return (clauses, [])
          else if (length . setify $ map (snd . stripComb) schems) /= 1
               then fail "unschematizeClauses: schematic variables not used consistently"
               else do avoids <- liftM variables $ listMkConj clauses
                       let grels = variants avoids $ map hackFun schems
                       let crels = zip grels schems
                       clauses' <- liftO $ mapM (subst crels) clauses
                       return (clauses', snd . stripComb $ head schems)
    where schemFun cls = 
              let (avs, bod) = stripForall cls in
                do bod' <- liftM snd (destImp bod) <|> Just bod
                   pareComb avs bod'

          pareComb qvs tm =
              if null (frees tm `intersect` qvs) &&
                 all isVar (snd $ stripComb tm)
              then return tm
              else pareComb qvs =<< rator tm

          hackFun tm = mkVar (fst . fromJust $ destVar =<< repeatM rator tm) $
                         typeOf tm

proveInductiveProperties :: (IndDefsCtxt thry, 
                             HOLTermRep tm cls thry) 
                         => tm -> HOL cls thry ([HOLTerm], HOLThm)
proveInductiveProperties ptm = 
    do tm <- toHTm ptm
       (clauses', fvs) <- unschematizeClauses $ conjuncts tm
       th <- deriveNonschematicInductiveRelations =<< listMkConj clauses'
       mth <- proveMonotonicityHyps th
       return (fvs, mth)

proveInductiveRelationsExist :: (IndDefsCtxt thry, 
                                 HOLTermRep tm cls thry) 
                             => tm -> HOL cls thry HOLThm
proveInductiveRelationsExist tm =
    do (fvs, th1) <- proveInductiveProperties tm
       th2 <- generalizeSchematicVariables True fvs th1
       deriveExistence th2

-- Returns a triple of theorems
-- Rule theorem -> says new relations are closed under the rules
-- Inductive Theorem -> says the relations are the least closed
-- Cases Theorem -> showing how each set of satisfying values can be composed

newInductiveDefinition :: (IndDefsCtxt thry, 
                           HOLTermRep tm Theory thry) => Text -> tm 
                       -> HOL Theory thry (HOLThm, HOLThm, HOLThm)
newInductiveDefinition lbl ptm =
    do acid <- openLocalStateHOL (IndDefs mapEmpty)
       qth <- queryHOL acid (GetAnInductiveDef lbl)
       closeAcidStateHOL acid
       case qth of
         Just trip -> 
             return trip
         Nothing -> 
             do tm <- toHTm ptm
                (fvs, th1) <- proveInductiveProperties tm
                th2 <- generalizeSchematicVariables True fvs th1
                th3 <- makeDefinitions th2
                let (avs, _) = stripForall $ concl th3
                (r, ic) <- ruleCONJ_PAIR =<< ruleSPECL avs th3
                (i, c) <- ruleCONJ_PAIR ic
                rth <- ruleGENL avs r
                ith <- ruleGENL avs i
                cth <- ruleGENL avs c
                let trip = (rth, ith, cth)
                acid' <- openLocalStateHOL (IndDefs mapEmpty)
                updateHOL acid' (AddInductiveDef lbl trip)
                createCheckpointAndCloseHOL acid'
                return trip

getInductiveDefinition :: Text -> HOL cls thry (HOLThm, HOLThm, HOLThm)
getInductiveDefinition ty =
    do acid <- openLocalStateHOL (IndDefs mapEmpty)
       def <- queryHOL acid (GetAnInductiveDef ty)
       closeAcidStateHOL acid
       liftMaybe "getAnInductiveDefinition:  definition not found." def



    



                       
