{-# LANGUAGE FlexibleContexts, PatternSynonyms #-}
{-|
  Module:    HaskHOL.Lib.Quot
  Copyright: (c) Evan Austin 2015
  LICENSE:   BSD3

  Maintainer:  e.c.austin@gmail.com
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Quot
    ( defineQuotientType
    , getQuotientType
    , liftTheorem
    , liftFunction
    , getLiftedFunction
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Bool
import HaskHOL.Lib.Classic
import HaskHOL.Lib.DRule
import HaskHOL.Lib.Equal
import HaskHOL.Lib.Meson
import HaskHOL.Lib.Simp
import HaskHOL.Lib.Tactics
import HaskHOL.Lib.Theorems
import HaskHOL.Lib.Trivia

data LiftedFunctions = 
    LiftedFunctions !(Map Text (HOLThm, HOLThm)) deriving Typeable

deriveSafeCopy 0 'base ''LiftedFunctions

addLiftedFunction :: Text -> (HOLThm, HOLThm) -> Update LiftedFunctions ()
addLiftedFunction lbl ths =
    do (LiftedFunctions m) <- get
       put (LiftedFunctions (mapInsert lbl ths m))

getLiftedFunction' :: Text -> Query LiftedFunctions (Maybe (HOLThm, HOLThm))
getLiftedFunction' name =
    do (LiftedFunctions m) <- ask
       return $! mapAssoc name m

makeAcidic ''LiftedFunctions ['addLiftedFunction, 'getLiftedFunction']

data QuotientTypes = 
    QuotientTypes !(Map Text (HOLThm, HOLThm)) deriving Typeable

deriveSafeCopy 0 'base ''QuotientTypes

addQuotientType :: Text -> (HOLThm, HOLThm) -> Update QuotientTypes ()
addQuotientType lbl ths =
    do (QuotientTypes m) <- get
       put (QuotientTypes (mapInsert lbl ths m))

getQuotientType' :: Text -> Query QuotientTypes (Maybe (HOLThm, HOLThm))
getQuotientType' name =
    do (QuotientTypes m) <- ask
       return $! mapAssoc name m

makeAcidic ''QuotientTypes ['addQuotientType, 'getQuotientType']

defineQuotientType :: (BoolCtxt thry, HOLTermRep tm Theory thry) => Text 
                   -> Text -> Text -> tm 
                   -> HOL Theory thry (HOLThm, HOLThm)
defineQuotientType tyname absname repname tm = 
    do acid <- openLocalStateHOL (QuotientTypes mapEmpty)
       qth <- queryHOL acid (GetQuotientType' tyname)
       closeAcidStateHOL acid
       case qth of
         Just th -> 
             return th
         Nothing -> note "defineQuotientType" $
             do eqv <- toHTm tm
                case typeOf eqv of
                  (TyApp _ (ty:_)) ->
                      do pty <- mkFunTy ty tyBool
                         let s = mkVar "s" pty
                             x = mkVar "x" ty
                         eqvx <- mkComb eqv x
                         exx <- mkExists x =<< mkEq s eqvx
                         predtm <- mkAbs s exx
                         th0 <- runConv convBETA =<< mkComb predtm eqvx
                         rtm <- rand $ concl th0
                         th1 <- ruleEXISTS rtm x $ primREFL eqvx
                         th2 <- ruleSYM th0
                         th3 <- primEQ_MP th2 th1
                         (absth, repth) <- newBasicTypeDefinition tyname 
                                             absname repname th3
                         th4 <- ruleCONV (convLAND convBETA) repth
                         acid' <- openLocalStateHOL (QuotientTypes mapEmpty)
                         updateHOL acid' (AddQuotientType tyname (absth, th4))
                         closeAcidStateHOL acid'
                         return (absth, th4)
                  _ -> fail "provided term has bad type"

getQuotientType :: Text -> HOL cls thry (HOLThm, HOLThm)
getQuotientType name =
    do acid <- openLocalStateHOL (QuotientTypes mapEmpty)
       qth <- queryHOL acid (GetQuotientType' name)
       closeAcidStateHOL acid
       case qth of
         Nothing -> fail "getQuotientType: type not found."
         Just res -> return res

thmSELECT_LEMMA :: TriviaCtxt thry => HOL cls thry HOLThm
thmSELECT_LEMMA = cacheProof "thmSELECT_LEMMA" ctxtTrivia $
    prove [txt| !x:A. (@y. x = y) = x |] $
      tacGEN `_THEN`
      tacGEN_REWRITE (convLAND . convBINDER) [thmEQ_SYM_EQ] `_THEN`
      tacMATCH_ACCEPT thmSELECT_REFL

liftFunction :: (TriviaCtxt thry, HOLThmRep thm1 Theory thry,
                 HOLThmRep thm2 Theory thry, HOLThmRep thm3 Theory thry,
                 HOLThmRep thm4 Theory thry) => thm1 -> thm2 -> thm3 -> Text 
             -> thm4 -> HOL Theory thry (HOLThm, HOLThm)
liftFunction ptybij2 prefl_th ptrans_th fname pwth =
    do acid <- openLocalStateHOL (LiftedFunctions mapEmpty)
       qth <- queryHOL acid (GetLiftedFunction' fname)
       closeAcidStateHOL acid
       case qth of
         Just th -> 
             return th
         Nothing -> note "liftFunction" $
           do tybij2 <- toHThm ptybij2
              refl_th <- toHThm prefl_th
              trans_th <- toHThm ptrans_th
              wth <- toHThm pwth
              case concl tybij2 of
                (Comb (Comb _ (Comb _ (Abs _ (Comb _ eqvx@(Comb eqv xtm))))) 
                      tybr) ->
                  case destEq tybr of
                    Just (Comb dest mrt@(Comb mk _), rtm) ->
                       let ety = typeOf mrt in
                         do wtm <- repeatM 
                                     (liftM snd . destForall) $ concl wth
                            let wfvs = frees wtm
                                (hyps, con) = case destImp wtm of
                                                Just (l, r) -> (conjuncts l, r)
                                                Nothing -> ([], wtm)
                                (eqs, rels) = partition isEq hyps
                            rvs <- mapM lHand rels
                            qvs <- mapM lHand eqs
                            rvs' <- mapM (\ tm -> case tm of
                                                    (Var v _ ) -> 
                                                      return $! mkVar v ety
                                                    _ -> fail "") rvs
                            let evs = variants wfvs rvs'
                            mems <- map2M (\ rv ev -> flip mkComb rv =<< mkComb dest ev) rvs evs
                            (lcon, rcon) <- destComb con
                            let uvar = mkVar "u" $ typeOf rcon
                                u = variant (evs ++ wfvs) uvar
                            ucon <- mkComb lcon u
                            dbod <- listMkConj (ucon:mems)
                            detm <- listMkExists rvs dbod
                            datm <- mkAbs u detm
                            def <- if isEq con then listMkIComb "@" [datm]
                                   else mkComb mk datm
                            newargs <- mapM (\ e -> liftM fst (destEq e) 
                                                         <|> (do le <- lHand e
                                                                 assoc le $ zip rvs evs)) hyps
                            rdef <- listMkAbs newargs def
                            let ldef = mkVar fname $ typeOf rdef
                            edef <- mkEq ldef rdef
                            dth <- newDefinition (fname, edef)
                            eth <- foldlM (\ th v -> ruleCONV (convRAND convBETA) =<<
                                                  (ruleAP_THM th v)) dth newargs
                            targs <- mapM (mkComb mk <=< mkComb eqv) rvs
                            th <- primINST [(rtm, eqvx)] tybij2
                            thTm <- lHand $ concl th
                            dme_th <- primEQ_MP th . ruleEXISTS thTm xtm $ 
                                        primREFL eqvx
                            ith <- primINST (zip evs targs) eth
                            rvs_ths <- mapM (\ v -> primINST [(xtm, v)] dme_th) rvs
                            jth <- ruleSUBS rvs_ths ith
                            (apop, uxtm) <- destComb =<< rand (concl jth)
                            extm <- body uxtm
                            let (evs', bod) = stripExists extm
                            th1 <- primASSUME bod
                            th2 <- if null evs' then return th1
                                   else do (th2a, th2b) <- ruleCONJ_PAIR th1
                                           as <- ruleCONJUNCTS th2b
                                           bs <- mapM primREFL qvs
                                           let ethlist = as ++ bs
                                           ethlist' <- mapM (\ v -> findM (\ thm -> do v' <- lHand v
                                                                                       c <- lHand $ concl thm
                                                                                       return $! v' == c) ethlist) hyps 
                                           th2c <- foldr1M ruleCONJ ethlist'
                                           th2d <- ruleMATCH_MP wth th2c
                                           th2e <- (primTRANS th2d th2a) 
                                                   <|> (ruleMATCH_MP trans_th =<< 
                                                     ruleCONJ th2d th2a)
                                           foldrM ruleSIMPLE_CHOOSE th2e evs'
                            th3 <- primASSUME $ concl th2
                            ths <- mapM (`ruleSPEC` refl_th) rvs
                            th4 <- foldr1M ruleCONJ (th3:ths)
                            th5 <- primASSUME bod
                            th6 <- foldrM ruleSIMPLE_EXISTS th5 evs'
                            th7 <- ruleDISCH_ALL th6
                            th8 <- ruleMATCH_MP th7 th4
                            th9 <- ruleDISCH_ALL th2
                            th10 <- ruleIMP_ANTISYM th9 =<< ruleDISCH_ALL th8
                            th11 <- primTRANS jth =<< ruleAP_TERM apop =<< primABS u th10
                            let fconv = if isEq con then Conv $ \ tm -> thmSELECT_LEMMA >>= \ thm -> runConv (convREWR thm) tm
                                        else convRAND convETA
                            th12 <- ruleCONV (convRAND fconv) th11
                            th13 <- ruleGSYM th12
                            acid' <- openLocalStateHOL (LiftedFunctions mapEmpty)
                            updateHOL acid' (AddLiftedFunction fname (eth, th13))
                            closeAcidStateHOL acid'
                            return (eth, th13)
                    _ -> fail "not an equation"
                _ -> fail "term of improper form"

getLiftedFunction :: Text -> HOL cls thry (HOLThm, HOLThm)
getLiftedFunction name =
    do acid <- openLocalStateHOL (LiftedFunctions mapEmpty)
       qth <- queryHOL acid (GetLiftedFunction' name)
       closeAcidStateHOL acid
       case qth of
         Nothing -> fail "getLiftedFunction: type not found."
         Just res -> return res


liftTheorem :: (TriviaCtxt thry, HOLThmRep thm1 cls thry, 
                HOLThmRep thm2 cls thry, HOLThmRep thm3 cls thry,
                HOLThmRep thm4 cls thry, HOLThmRep thm5 cls thry,
                HOLThmRep thm6 cls thry) => (thm1, thm1) -> thm2 -> thm3 -> thm4
            -> [thm5] -> thm6 -> HOL cls thry HOLThm
liftTheorem ptybij prefl_th psym_th ptrans_th ptrths pthm =
    do (tybij1, tybij2) <- pairMapM ruleGEN_ALL ptybij
       refl_th <- toHThm prefl_th
       sym_th <- toHThm psym_th
       trans_th <- toHThm ptrans_th
       trths <- mapM toHThm ptrths
       cth <- foldr1M ruleCONJ [refl_th, sym_th, trans_th, tybij1, tybij2]
       ith <- ruleMATCH_MP liftTheorem_pth cth
       ruleREWRITE (ith:trths) pthm
  where liftTheorem_pth :: TriviaCtxt thry => HOL cls thry HOLThm
        liftTheorem_pth = cacheProof "liftTheorem_pth" ctxtTrivia $
            prove [txt| (!x:Repty. R x x) /\
                        (!x y. R x y <=> R y x) /\
                        (!x y z. R x y /\ R y z ==> R x z) /\
                        (!a. mk(dest a) = a) /\
                        (!r. (?x. r = R x) <=> (dest(mk r) = r))
                          ==> (!x y. R x y <=> (mk(R x) = mk(R y))) /\
                              (!P. (!x. P(mk(R x))) <=> (!x. P x)) /\
                              (!P. (?x. P(mk(R x))) <=> (?x. P x)) /\
                              (!x:Absty. mk(R((@)(dest x))) = x) |] $
              tacSTRIP `_THEN`
              _SUBGOAL_THEN [txt| !x y. (mk((R:Repty->Repty->bool) x):Absty = 
                                           mk(R y)) <=> (R x = R y) |]
              tacASSUME `_THENL`
              [ tacASM_MESON_NIL
              , _ALL
              ] `_THEN`
              tacMATCH_MP (ruleTAUT [txt| (a /\ b /\ c) /\ (b ==> a ==> d) ==> 
                                           a /\ b /\ c /\ d |]) `_THEN`
              tacCONJ `_THENL`
              [ tacASM_REWRITE_NIL `_THEN` tacREWRITE [thmFUN_EQ] `_THEN` 
                tacASM_MESON_NIL
              , _ALL
              ] `_THEN`
              _REPEAT (_DISCH_THEN 
                       (\ th g -> tacREWRITE [ruleGSYM th] g)) `_THEN`
              tacX_GEN [txt| x:Repty |] `_THEN`
              _SUBGOAL_THEN [txt| dest(mk((R:Repty->Repty->bool) x):Absty) = R x|]
              tacSUBST1 `_THENL`
              [ tacASM_MESON_NIL
              , _ALL
              ] `_THEN`
              tacGEN_REWRITE (convLAND . convRAND) [ruleGSYM axETA] `_THEN`
              _FIRST_ASSUM (\ th -> tacGEN_REWRITE id [th]) `_THEN`
              tacCONV convSELECT `_THEN`
              tacASM_MESON_NIL
