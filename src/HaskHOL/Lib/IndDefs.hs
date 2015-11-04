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
    , stripNComb
    , ruleRIGHT_BETAS
    , ruleEXISTS_EQUATION
    , tacMONO
    , proveMonotonicityHyps
    , deriveNonschematicInductiveRelations
    , proveInductiveRelationsExist
    , newInductiveDefinition
    , getInductiveDefinition
    , addMonoThm
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
import HaskHOL.Lib.IndDefs.PQ

stripNComb :: MonadThrow m => Int -> HOLTerm -> m (HOLTerm, [HOLTerm])
stripNComb n tm = stripRec n tm []
    where stripRec x t acc
              | x < 1 = return (t, acc)
              | otherwise = 
                  case t of
                    (Comb l r) -> stripRec (x - 1) l (r:acc)
                    _ -> fail' "stripNComb"

ruleRIGHT_BETAS :: (HOLTermRep tm cls thry, HOLThmRep thm cls thry) 
                => [tm] -> thm -> HOL cls thry HOLThm
ruleRIGHT_BETAS tms = 
    itlistM (\ a -> ruleCONV (convRAND convBETA) . 
                    flip ruleAP_THM a) tms <=< toHThm

ruleEXISTS_EQUATION :: (IndDefsCtxt thry, HOLTermRep tm cls thry, 
                        HOLThmRep thm cls thry) 
                    => tm -> thm -> HOL cls thry HOLThm
ruleEXISTS_EQUATION ptm pthm = note "ruleEXISTS_EQUATION" $
    do tm <- toHTm ptm
       case tm of
         (l := r) ->
             do thm@(Thm _ c) <- toHThm pthm
                p <- mkAbs l c
                th1 <- ruleISPECL [p, r] ruleEXISTS_EQUATION_pth
                th2 <- ruleSYM $ runConv convBETA =<< mkComb p l
                ruleMP th1 . ruleGEN l . ruleDISCH tm $ primEQ_MP th2 thm
         _ -> fail "not an equation."
  where ruleEXISTS_EQUATION_pth :: IndDefsCtxt thry => HOL cls thry HOLThm
        ruleEXISTS_EQUATION_pth = 
            cacheProof "ruleEXISTS_EQUATION_pth" ctxtIndDefs .
              prove [txt| !P t. (!x:A. (x = t) ==> P x) ==> (?) P |] $
                tacREWRITE [defEXISTS] `_THEN`
                tacBETA `_THEN`
                _REPEAT tacSTRIP `_THEN`
                _FIRST_ASSUM tacMATCH_MP `_THEN`
                tacEXISTS [txt| t:A |] `_THEN`
                _FIRST_ASSUM tacMATCH_MP `_THEN`
                tacREFL

canonicalizeClause :: IndDefsCtxt thry 
                   => HOLTerm -> [HOLTerm] -> HOL cls thry HOLThm
canonicalizeClause cls args = note "canonicalizeClause" $
    let (avs, bimp) = stripForall cls in
      do (ant, con) <- destImp bimp <|> 
                       pairMapM id (serve [indDefs| T |], return bimp)
         let (rel, xargs) = stripComb con
             plis = zip args xargs
             (yes, no) = calculateSimpSequence avs plis
             nvs = filter (\ x -> x `notElem` map snd yes) avs
             canon' = canon rel plis yes nvs
         eth <- if isImp bimp 
                then do atm <- foldrM (\ x y -> flip mkConj y =<< 
                                                  uncurry mkEq x) ant (yes++no)
                        (ths, tth) <- nsplit ruleCONJ_PAIR plis =<< 
                                        primASSUME atm
                        th0 <- ruleMP (ruleSPECL avs $ primASSUME cls) tth
                        (th6, th5') <- canon' atm th0 ths
                        th7 <- itlistM (ruleCONJ . primREFL . snd) no =<< 
                                 primASSUME ant
                        th8 <- ruleGENL avs . ruleDISCH ant $ ruleMP th6 th7
                        ruleIMP_ANTISYM th5' $ ruleDISCH_ALL th8
                else do atm <- listMkConj =<< mapM (uncurry mkEq) (yes ++ no)
                        ths <- ruleCONJUNCTS $ primASSUME atm
                        th0 <- ruleSPECL avs $ primASSUME cls
                        (th6, th5') <- canon' atm th0 ths
                        th7 <- foldr1M ruleCONJ =<< mapM (primREFL . snd) no
                        th8 <- ruleGENL avs $ ruleMP th6 th7
                        ruleIMP_ANTISYM th5' $ ruleDISCH_ALL th8
         ftm <- funpowM (length args) (body <=< rand) =<< rand (concl eth)
         fth <- itlistM ruleMK_FORALL args =<< runConv convFORALL_IMPS ftm
         primTRANS eth fth
  where convFORALL_IMPS :: BoolCtxt thry => Conversion cls thry
        convFORALL_IMPS = Conv $ \ tm ->
            let (avs, bod) = stripForall tm in
              do th1 <- ruleDISCH tm . ruleUNDISCH . ruleSPEC_ALL $ 
                          primASSUME tm
                 th2 <- foldrM ruleSIMPLE_CHOOSE th1 avs
                 let tm2 = head $ hyp th2
                 th3 <- ruleDISCH tm2 $ ruleUNDISCH th2
                 th4 <- primASSUME $ concl th3
                 ant <- lHand bod
                 th5 <- itlistM ruleSIMPLE_EXISTS avs =<< primASSUME ant
                 th6 <- ruleGENL avs . ruleDISCH ant $ ruleMP th4 th5
                 ruleIMP_ANTISYM (ruleDISCH_ALL th3) $ ruleDISCH_ALL th6

        canon :: BoolCtxt thry => HOLTerm -> HOLTermEnv -> HOLTermEnv 
              -> [HOLTerm] -> HOLTerm -> HOLThm -> [HOLThm] 
              -> HOL cls thry (HOLThm, HOLThm)
        canon rel plis yes nvs atm th0 ths =
            do thl <- mapM (\ t -> find (\ th -> 
                            case runCatch . lhs $ concl th of
                              Right res -> res == t
                              _ -> False) ths) args
               th1 <- revItlistM (flip primMK_COMB) thl =<< primREFL rel
               th2 <- primEQ_MP (ruleSYM th1) th0
               th3 <- primINST yes $ ruleDISCH atm th2
               tm4 <- funpowM (length yes) rand =<< lHand (concl th3)
               th4 <- itlistM (ruleCONJ . primREFL . fst) yes =<< primASSUME tm4
               th5 <- ruleGENL args . ruleGENL nvs . ruleDISCH tm4 $ 
                        ruleMP th3 th4
               th6 <- ruleSPECL nvs . ruleSPECL (map snd plis) $
                        primASSUME (concl th5)
               th5' <- ruleDISCH_ALL th5
               return (th6, th5')

        calculateSimpSequence :: [HOLTerm] -> HOLTermEnv 
                              -> (HOLTermEnv, HOLTermEnv)
        calculateSimpSequence avs plis =
            let oks = getequs avs plis in (oks, plis \\ oks)
          where getequs :: Eq b => [b] -> [(a, b)] -> [(a, b)]
                getequs _ [] = []
                getequs as (h@(_, r):t)
                    | r `elem` as = 
                        h : getequs as (filter (\ (_, x) -> x /= r) t)
                    | otherwise = 
                        getequs as t 
           
canonicalizeClauses :: IndDefsCtxt thry => [HOLTerm] -> HOL cls thry HOLThm
canonicalizeClauses clauses = 
  let concls = map getConcl clauses
      uncs = map stripComb concls
      rels = foldr (insert . fst) [] uncs in
    do xargs <- mapM (`assoc` uncs) rels
       closed <- listMkConj clauses
       let avoids = variables closed
           flargs = mkArgs "a" avoids . map typeOf $ foldr1 (++) xargs
       zargs <- liftM (zip rels) $ shareOut xargs flargs
       cargs <- mapM (\ (x, _) -> x `assoc` zargs) uncs
       cthms <- map2M canonicalizeClause clauses cargs
       pclauses <- mapM (rand . concl) cthms
       let collectClauses tm = 
               mapFilter (\ (x, y) -> if x == tm then return y 
                                      else fail' "collectClauses") $  
                 zip (map fst uncs) pclauses
           clausell = map collectClauses rels
       cclausel <- mapM listMkConj clausell
       cclauses <- listMkConj cclausel
       oclauses <- listMkConj pclauses
       eth <- ruleCONJ_ACI =<< mkEq oclauses cclauses
       cth <- foldr1M ruleMK_CONJ cthms
       pth <- primTRANS cth eth
       th1 <- foldr1M ruleMK_CONJ =<< mapM ruleAND_IMPS_CONV cclausel 
       primTRANS pth th1
  where getConcl :: HOLTerm -> HOLTerm
        getConcl tm =
            let bod = try' $ repeatM (liftM snd . destForall) tm in
              case runCatch . liftM snd $ destImp bod of
                Right res -> res
                Left  _   -> bod

        ruleCONJ_ACI :: (TheoremsCtxt thry, HOLTermRep tm cls thry) 
                     => tm -> HOL cls thry HOLThm
        ruleCONJ_ACI = runConv (convAC thmCONJ_ACI)

        ruleAND_IMPS_CONV :: (BoolCtxt thry, HOLTermRep tm cls thry) 
                          => tm -> HOL cls thry HOLThm
        ruleAND_IMPS_CONV tm =
            do ths <- ruleCONJUNCTS $ primASSUME tm
               let avs = fst . stripForall . concl $ head ths
               thl <- mapM (ruleDISCH tm . ruleUNDISCH . ruleSPEC_ALL) ths
               th1 <- foldr1M ruleSIMPLE_DISJ_CASES thl
               let tm1 = head $ hyp th1
               th2 <- ruleGENL avs . ruleDISCH tm1 $ ruleUNDISCH th1
               let tm2 = concl th2
               th3 <- ruleDISCH tm2 . ruleUNDISCH . ruleSPEC_ALL $ 
                        primASSUME tm2
               (thts, tht) <- nsplit ruleSIMPLE_DISJ_PAIR (tail ths) th3
               let procFun thm = let t = head $ hyp thm in
                       ruleGENL avs . ruleDISCH t $ ruleUNDISCH thm
               th4 <- itlistM (ruleCONJ . procFun) thts =<< procFun tht
               ruleIMP_ANTISYM (ruleDISCH_ALL th2) $ ruleDISCH_ALL th4
          where ruleSIMPLE_DISJ_PAIR :: BoolCtxt thry 
                                     => HOLThm -> HOL cls thry (HOLThm, HOLThm)
                ruleSIMPLE_DISJ_PAIR thm@(Thm ((l :\/ r):_) _) =
                    do th1 <- ruleDISJ1 (primASSUME l) r 
                       th2 <- ruleDISJ2 l $ primASSUME r
                       pairMapM (`rulePROVE_HYP` thm) (th1, th2)
                ruleSIMPLE_DISJ_PAIR _ = fail $ "ruleSIMPLE_DISJ_PAIR: " ++
                    "first assumption not a disjunction."

deriveCanonInductiveRelations :: BoolCtxt thry => [HOLTerm] 
                              -> HOL cls thry HOLThm
deriveCanonInductiveRelations cls =
    (do closed <- listMkConj cls
        let clauses = conjuncts closed
            (vargs, bodies) = unzip $ map stripForall clauses
        (ants, concs) <- liftM unzip $ mapM destImp bodies
        rels <- mapM (repeatM rator) concs
        let avoids = variables closed
            rels' = variants avoids rels
            crels = zip rels rels'
            primeFun = subst crels
        closed' <- primeFun closed
        defTms <- map2M (mkDef primeFun closed' rels') vargs concs
        defThms <- map2M ruleHALF_BETA_EXPAND vargs =<< mapM primASSUME defTms
        indThms <- map2M (mkInd rels') vargs defThms
        indThmr <- foldr1M ruleCONJ indThms
        indThm <- ruleGENL rels' $ ruleDISCH closed' indThmr
        mConcs <- map2M (\ a t -> do t' <- mkImp t =<< primeFun t
                                     listMkForall a t') vargs ants
        monoTm <- mkImp (concl indThmr) =<< listMkConj mConcs
        monoTm' <- listMkForall rels' monoTm
        forallMonoTm' <- listMkForall rels monoTm'
        monoThm <- primASSUME forallMonoTm'
        closeThm <- primASSUME closed'
        monoTh1 <- ruleSPEC_ALL monoThm
        monoTh2 <- ruleSPECL rels' indThm
        monoThms <- ruleCONJUNCTS . ruleMP monoTh1 $ ruleMP monoTh2 closeThm
        closeThms <- ruleCONJUNCTS closeThm
        ruleThms <- map2M (proveRule rels' closed') monoThms $ 
                      zip closeThms defThms
        ruleThm <- foldr1M ruleCONJ ruleThms
        dTms <- map2M listMkAbs vargs ants
        let doubleFun = subst (zip rels dTms)
        unThs <- map2M (mkUnbetas doubleFun) clauses dTms
        unThs' <- ruleSYM . foldr1M ruleMK_CONJ $ map fst unThs
        irThm <- primEQ_MP unThs' ruleThm
        monoThm' <- ruleSPECL rels $ ruleSPECL dTms monoThm
        mrThm <- ruleMP monoThm' irThm
        unThs'' <- ruleSYM . foldr1M ruleMK_CONJ $ map (fst . snd) unThs
        imrThm <- primEQ_MP unThs'' mrThm
        indThm' <- ruleSPECL dTms indThm
        ifThm <- ruleMP indThm' imrThm
        unThs''' <- foldr1M ruleMK_CONJ $ map (snd . snd) unThs
        fThm <- primEQ_MP unThs''' ifThm
        fThms <- ruleCONJUNCTS fThm
        caseThm <- foldr1M ruleCONJ =<< map2M mkCase fThms =<< 
                     ruleCONJUNCTS ruleThm
        ruleCONJ ruleThm =<< ruleCONJ indThm caseThm)
    <?> "deriveCanonInductiveRelations"

    where mkDef :: (HOLTerm -> HOL cls thry HOLTerm) -> HOLTerm -> [HOLTerm]
                -> [HOLTerm] -> HOLTerm -> HOL cls thry HOLTerm
          mkDef f closed rels arg con = 
              do tm <- mkImp closed =<< f con
                 tm' <- listMkForall rels tm
                 l <- repeatM rator con
                 r <- listMkAbs arg tm'
                 mkEq l r
          
          mkInd :: BoolCtxt thry => [HOLTerm] -> [HOLTerm] -> HOLThm 
                -> HOL cls thry HOLThm
          mkInd rels args thm = 
              do (th1, _) <- ruleEQ_IMP $ ruleSPEC_ALL thm
                 ant <- lHand $ concl th1
                 th2 <- ruleSPECL rels $ ruleUNDISCH th1
                 ruleGENL args . ruleDISCH ant $ ruleUNDISCH th2

          proveRule :: BoolCtxt thry => [HOLTerm] -> HOLTerm -> HOLThm 
                    -> (HOLThm, HOLThm) -> HOL cls thry HOLThm
          proveRule rels closed mth (cth, dth) = 
              let (avs, bod) = stripForall $ concl mth in
                do th1 <- ruleSPECL avs mth
                   th2 <- ruleIMP_TRANS th1 $ ruleSPECL avs cth
                   th3 <- ruleGENL rels . ruleDISCH closed $ ruleUNDISCH th2
                   th4 <- ruleSYM $ ruleSPECL avs dth
                   tm <- lHand bod
                   ruleGENL avs . ruleDISCH tm $ primEQ_MP th4 th3

          mkUnbetas :: BoolCtxt thry => (HOLTerm -> HOL cls thry HOLTerm) 
                    -> HOLTerm -> HOLTerm 
                    -> HOL cls thry (HOLThm, (HOLThm, HOLThm))
          mkUnbetas f tm dtm = 
              case stripForall tm of
                (avs, Comb (Comb i l) r) -> 
                    do bth <- ruleRIGHT_BETAS avs $ primREFL dtm
                       let quantify th = foldrM ruleMK_FORALL th avs
                       munb <- quantify =<< ruleAP_THM (ruleAP_TERM i bth) r
                       iunb <- quantify =<< ruleAP_TERM (mkComb i =<< f l) bth
                       ir <- mkComb i r
                       junb <- quantify =<< ruleAP_TERM ir bth
                       return (munb, (iunb, junb))
                _ -> fail "mkUnbetas"

          mkCase :: BoolCtxt thry => HOLThm -> HOLThm -> HOL cls thry HOLThm
          mkCase th1 th2 = 
              let (avs, _) = stripForall $ concl th1 in
                ruleGENL avs . ruleIMP_ANTISYM (ruleSPEC_ALL th1) $ 
                  ruleSPEC_ALL th2

          ruleHALF_BETA_EXPAND :: (BoolCtxt thry, HOLTermRep tm cls thry, 
                                   HOLThmRep thm cls thry) 
                               => [tm] -> thm -> HOL cls thry HOLThm
          ruleHALF_BETA_EXPAND args = ruleGENL args . ruleRIGHT_BETAS args

deriveNonschematicInductiveRelations :: IndDefsCtxt thry => HOLTerm 
                                     -> HOL cls thry HOLThm
deriveNonschematicInductiveRelations tm =
    let clauses = conjuncts tm in
      do canonThm <- canonicalizeClauses clauses
         canonThm' <- ruleSYM canonThm
         pclosed <- rand $ concl canonThm
         let pclauses = conjuncts pclosed
         rawThm <- deriveCanonInductiveRelations pclauses
         (ruleThm, otherThms) <- ruleCONJ_PAIR rawThm
         (indThm, caseThm) <- ruleCONJ_PAIR otherThms
         ruleThm' <- primEQ_MP canonThm' ruleThm
         indThm' <- ruleCONV (convONCE_DEPTH (convREWR canonThm')) indThm
         ruleCONJ ruleThm' $ ruleCONJ indThm' caseThm

tacMONO :: IndDefsCtxt thry => Tactic cls thry
tacMONO g = 
    do acid <- openLocalStateHOL (MonoThms [])
       thms <- queryHOL acid GetMonos
       closeAcidStateHOL acid
       tacs <- foldrM tacFun [("", tacMonoAbs)] thms
       let tacMonoStep = _REPEAT tacGEN `_THEN` tacApplyMono tacs
       (_REPEAT tacMonoStep `_THEN` tacASM_REWRITE_NIL) g
    where tacMonoAbs :: IndDefsCtxt thry => Tactic cls thry
          tacMonoAbs gl@(Goal _ (ant :==> con)) = note "tacMonoAbs" $
              let (_, vars) = stripComb con
                  rnum = length vars - 1 in
                do ((hd1, args1), (hd2, args2)) <- pairMapM (stripNComb rnum) 
                                                     (ant, con)
                   th1 <- revItlistM (flip ruleAP_THM) args1 =<< 
                            runConv convBETA hd1
                   th2 <- revItlistM (flip ruleAP_THM) args2 =<<
                            runConv convBETA hd2
                   th3 <- ruleAP_TERM (serve [indDefs| (==>) |]) th1
                   th4 <- primMK_COMB th3 th2
                   tacCONV (convREWR th4) gl
          tacMonoAbs _ = fail "tacMonoAbs: not an implication."

          tacApplyMono :: IndDefsCtxt thry => [(Text, Tactic cls thry)] 
                       -> Tactic cls thry
          tacApplyMono tacs gl@(Goal _ (a :==> c))
              | a `aConv` c = 
                  do th <- ruleSPEC a thmIMP_REFL
                     tacACCEPT th gl
              | otherwise = 
                  let cn = case runCatch $ repeatM rator c of
                             Right (Const n _) -> n
                             _ -> "" in
                    tryFind (\ (k, t) -> if k == cn then t gl 
                                         else fail "tacApplyMono") tacs
            where thmIMP_REFL :: IndDefsCtxt thry => HOL cls thry HOLThm
                  thmIMP_REFL = cacheProof "thmIMP_REFL" ctxtIndDefs $
                      ruleITAUT [txt| !p . p ==> p |]
          tacApplyMono _ _ = fail "tacApplyMono: not an implication"

          tacFun :: BoolCtxt thry => HOLThm -> [(Text, Tactic cls thry)] 
                 -> HOL cls thry [(Text, Tactic cls thry)]
          tacFun th l =
              do x <- rand =<< rand (concl th)
                 x' <- repeatM rator x
                 let c = case x' of
                           Const n _ -> n
                           _ -> ""
                 return ((c, tacBackChain th `_THEN` _REPEAT tacCONJ) : l)
            where tacBackChain :: BoolCtxt thry => HOLThm -> Tactic cls thry
                  tacBackChain thm (Goal asl w) =
                      let matchFun = rulePART_MATCH (liftM snd . destImp) thm in
                        do th1 <- matchFun w
                           case concl th1 of
                             (ant :==> _) -> 
                                 return . GS nullMeta [Goal asl ant] $ just th1
                             _ -> fail "tacBackChain"
                    where just :: BoolCtxt thry 
                               => HOLThm -> Justification cls thry
                          just th1 i [t] = do th' <- ruleINSTANTIATE i th1
                                              ruleMATCH_MP th' t
                          just _ _ _ = fail "tacBackChain: bad justification"

proveMonotonicityHyps :: IndDefsCtxt thry => HOLThm -> HOL cls thry HOLThm
proveMonotonicityHyps thm = 
    let proveFun :: IndDefsCtxt thry => HOLTerm -> HOL cls thry HOLThm
        proveFun t = prove t $ 
            _REPEAT tacGEN `_THEN`
            _DISCH_THEN (_REPEAT _CONJUNCTS_THEN tacASSUME) `_THEN`
            _REPEAT tacCONJ `_THEN` tacMONO in
      foldrM rulePROVE_HYP thm =<< 
        (mapFilterM proveFun . filter (not . isEq) $ hyp thm)


proveInductiveProperties :: (IndDefsCtxt thry, 
                             HOLTermRep tm cls thry) 
                         => tm -> HOL cls thry ([HOLTerm], HOLThm)
proveInductiveProperties ptm = 
    do tm <- toHTm ptm
       (clauses', fvs) <- unschematizeClauses $ conjuncts tm
       th <- deriveNonschematicInductiveRelations =<< listMkConj clauses'
       mth <- proveMonotonicityHyps th
       return (fvs, mth)
  where unschematizeClauses :: [HOLTerm] -> HOL cls thry ([HOLTerm], [HOLTerm])
        unschematizeClauses clauses =
            do schem <- mapM schemFun clauses
               let schems = setify schem
               if isVar (head schem) 
                  then return (clauses, [])
                  else if (length . setify $ map (snd . stripComb) schems) /= 1
                       then fail $ "unschematizeClauses: " ++ 
                                   "schematic variables not used consistently"
                       else do avoids <- liftM variables $ listMkConj clauses
                               grels <- liftM (variants avoids) $ 
                                          mapM hackFun schems
                               let crels = zip grels schems
                               clauses' <- mapM (subst crels) clauses
                               return (clauses', snd . stripComb $ head schems)

        schemFun :: (MonadCatch m, MonadThrow m) => HOLTerm -> m HOLTerm
        schemFun cls = 
            let (avs, bod) = stripForall cls in
              do bod' <- liftM snd (destImp bod) <|> return bod
                 pareComb avs bod'

        pareComb :: MonadThrow m => [HOLTerm] -> HOLTerm -> m HOLTerm
        pareComb qvs tm =
            if null (frees tm `intersect` qvs) &&
               all isVar (snd $ stripComb tm)
            then return tm
            else pareComb qvs =<< rator tm

        hackFun :: (MonadCatch m, MonadThrow m) => HOLTerm -> m HOLTerm
        hackFun tm = 
            do (s, _) <- destVar =<< repeatM rator tm
               return . mkVar s $! typeOf tm

generalizeSchematicVariables :: BoolCtxt thry => Bool -> [HOLTerm] 
                                     -> HOLThm -> HOL cls thry HOLThm
generalizeSchematicVariables gflag vs thm =
    let (defs, others) = partition isEq $ hyp thm in
      do th1 <- foldrM (generalizeDef vs) thm defs
         if gflag
         then do others' <- mapM (\ t -> 
                                  let fvs = frees t in
                                    do forallT <- listMkForall fvs t
                                       ruleSPECL fvs $ primASSUME forallT
                                 ) others
                 ruleGENL vs $ foldrM rulePROVE_HYP th1 others'
         else return th1

  where generalizeDef :: BoolCtxt thry => [HOLTerm] -> HOLTerm -> HOLThm 
                      -> HOL cls thry HOLThm
        generalizeDef xs tm@(l@(Var lname lty) := r) th =
            do ty <- foldrM (mkFunTy . typeOf) lty xs
               r' <- listMkAbs xs r
               tm' <- mkEq (mkVar lname ty) r'
               th0 <- ruleRIGHT_BETAS xs $ primASSUME tm'
               l'' <- lHand $ concl th0
               th1 <- ruleDISCH tm th
               ruleMP (primINST [(l'', l)] th1) th0
        generalizeDef _ _ _ = fail "generalizeDef: term not an equation."

proveInductiveRelationsExist :: (IndDefsCtxt thry, HOLTermRep tm cls thry) 
                             => tm -> HOL cls thry HOLThm
proveInductiveRelationsExist tm =
    do (fvs, th1) <- proveInductiveProperties tm
       th2 <- generalizeSchematicVariables True fvs th1
       deriveExistence th2
  where deriveExistence :: IndDefsCtxt thry => HOLThm -> HOL cls thry HOLThm
        deriveExistence thm =
            let defs = filter isEq $ hyp thm in
              foldrM ruleEXISTS_EQUATION thm defs


-- Inductive Definitions
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
       return $! mapAssoc ty defs

makeAcidic ''IndDefs ['addInductiveDef, 'getInductiveDefs, 'getAnInductiveDef]

getAnInductiveDefinition :: Text 
                         -> HOL cls thry (Maybe (HOLThm, HOLThm, HOLThm))
getAnInductiveDefinition lbl =
    do acid <- openLocalStateHOL (IndDefs mapEmpty)
       qth <- queryHOL acid (GetAnInductiveDef lbl)
       closeAcidStateHOL acid
       return qth


-- Returns a triple of theorems
-- Rule theorem -> says new relations are closed under the rules
-- Inductive Theorem -> says the relations are the least closed
-- Cases Theorem -> showing how each set of satisfying values can be composed
newInductiveDefinition :: (IndDefsCtxt thry, 
                           HOLTermRep tm Theory thry) => Text -> tm 
                       -> HOL Theory thry (HOLThm, HOLThm, HOLThm)
newInductiveDefinition lbl ptm =
    do qth <- getAnInductiveDefinition lbl
       case qth of
         Just trip -> return trip
         Nothing -> 
           do (fvs, th1) <- proveInductiveProperties ptm
              th2 <- generalizeSchematicVariables True fvs th1
              th3 <- makeDefinitions th2
              let (avs, _) = stripForall $ concl th3
              (r, ic) <- ruleCONJ_PAIR $ ruleSPECL avs th3
              (i, c) <- ruleCONJ_PAIR ic
              rth <- ruleGENL avs r
              ith <- ruleGENL avs i
              cth <- ruleGENL avs c
              let trip = (rth, ith, cth)
              acid' <- openLocalStateHOL (IndDefs mapEmpty)
              updateHOL acid' (AddInductiveDef lbl trip)
              createCheckpointAndCloseHOL acid'
              return trip
  where makeDefinitions :: BoolCtxt thry => HOLThm -> HOL Theory thry HOLThm
        makeDefinitions thm =
            let defs = filter isEq $ hyp thm in
              do dths <- mapM (\ x -> case x of
                                        (Var name _ := _) -> 
                                            newDefinition (name, x)
                                        _ -> fail "makeDefinitions") defs
                 defs' <- mapM lhs defs
                 dths' <- mapM (lhs . concl) dths
                 let insts = zip defs' dths'
                 th <- primINST insts $ foldrM ruleDISCH thm defs
                 foldlM ruleMP th dths

getInductiveDefinition :: Text -> HOL cls thry (HOLThm, HOLThm, HOLThm)
getInductiveDefinition lbl =
    do def <- getAnInductiveDefinition lbl 
       case def of
         Just res -> return res
         _ -> fail "getAnInductiveDefinition:  definition not found."



    



                       
