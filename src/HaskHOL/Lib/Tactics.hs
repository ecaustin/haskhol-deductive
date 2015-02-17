{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, PatternSynonyms, 
             TypeSynonymInstances, UndecidableInstances #-}
{-|
  Module:    HaskHOL.Lib.Tactics
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Tactics
    ( Goal(..)
    , Tactic
    , ThmTactic
    , ThmTactical
    , nullInst
    , nullMeta
    , def_FALSITY_
    , tacVALID
    , _MAP_EVERY
    , tacREPLICATE
    , tacSUBST_VAR
    , tacRULE_ASSUM
    -- tactic combinators
    , _THENL
    , tacLABEL  -- assumption list manipulations
    , tacASSUME
    , tacASM
    , _POP_ASSUM
    , _ASSUM_LIST
    , _POP_ASSUM_LIST
    , _EVERY_ASSUM
    , _FIRST_ASSUM
    , tacACCEPT
    , tacCONV
    , tacREFL  -- equality tactics
    , tacABS
    , tacMK_COMB
    , tacAP_TERM
    , tacAP_THM
    , tacBINOP
    , tacSUBST1
    , tacSUBST_ALL
    , tacBETA
    , tacDISCH  -- basic logical tactics
    , tacMP
    , tacEQ
    , tacUNDISCH
    , tacSPEC
    , tacX_GEN
    , tacGEN
    , tacEXISTS
    , tacX_CHOOSE
    , tacCHOOSE
    , tacCONJ
    , tacDISJ1
    , tacDISJ2
    , tacDISJ_CASES
    , tacCONTR
    , tacMATCH_ACCEPT
    , tacMATCH_MP
    , _CONJUNCTS_THEN2  -- theorem continuations
    , _CONJUNCTS_THEN
    , _DISJ_CASES_THEN2
    , _DISJ_CASES_THEN
    , _DISCH_THEN
    , _X_CHOOSE_THEN
    , _CHOOSE_THEN
    , tacSTRIP_ASSUME  -- derived tactics
    , _STRIP_THM_THEN
    , _ANTE_RES_THEN
    , tacSTRUCT_CASES
    , tacSTRIP
    , _STRIP_GOAL_THEN
    , _UNDISCH_THEN
    , _FIRST_X_ASSUM
    , _SUBGOAL_THEN
    , tacX_META_EXISTS
    , tacMETA_SPEC
    , ruleTAC_PROOF
    , prove
    , mkGoalstate
    , GoalState(..)
    , ppGoal
    , ppGoalState
    , Refinement
    , Justification
    , by
    , composeInsts
    ) where

import HaskHOL.Core hiding (empty)

import HaskHOL.Lib.Bool
import HaskHOL.Lib.Bool.Context
import HaskHOL.Lib.Equal
import HaskHOL.Lib.DRule

import Text.PrettyPrint

-- Types

type Justification cls thry = Instantiation -> [HOLThm] -> HOL cls thry HOLThm
type JustificationList cls thry = 
    Instantiation -> [HOLThm] -> HOL cls thry [HOLThm]

data Goal = Goal [(Text, HOLThm)] HOLTerm deriving Eq

instance ShowHOL Goal where
    showHOL g = do ctxt <- prepHOLContext
                   return $! ppGoal ctxt g

ppGoal :: HOLContext thry -> Goal -> String
ppGoal ctxt (Goal asl w) = 
    let asl' = if null asl then empty
               else ppASL ctxt 0 (reverse asl) in
      render $ asl' $+$ text "-----" $+$ text (ppTerm ctxt w)

ppASL :: HOLContext thry -> Int -> [(Text, HOLThm)] -> Doc
ppASL ctxt = ppASLrec
  where ppASLrec :: Int -> [(Text, HOLThm)] -> Doc
        ppASLrec _ [] = empty
        ppASLrec n ((s, th):rest) = 
            let s' = if textNull s then empty
                     else lparen <> text (unpack s) <> rparen in
              int n <+> text (ppTerm ctxt $ concl th) <> s' $+$
                ppASLrec (n+1) rest

-- metavariables, instantiation, goal list, and justification
data GoalState cls thry = 
    GS ([HOLTerm], Instantiation) [Goal] (Justification cls thry)

{-
instance ShowHOL [GoalState cls thry] where
    showHOL [] = return "Empty goalstack"
    showHOL (gs:[]) = 
        ppGoalState 1 gs
    showHOL (gs@(GS _ g _):GS _ g0 _:_) =
        let p = length g - length g0
            p' = if p < 1 then 1 else p + 1 in
          ppGoalState p' gs
-}
         
ppGoalState :: HOLContext thry -> Int -> GoalState cls thry -> String
ppGoalState _ _ (GS _ [] _) = "No subgoals"
ppGoalState ctxt x (GS _ gls _) = 
    let n = length gls in
      render
        (int x <+> text "subgoal(s)" <+> parens (int n <+> text "total") $+$
         (vcat . map (text . ppGoal ctxt) $ take x gls))

type Refinement cls thry = GoalState cls thry -> HOL cls thry (GoalState cls thry)

type Tactic cls thry = Goal -> HOL cls thry (GoalState cls thry)
type ThmTactic cls thry = HOLThm -> Tactic cls thry
type ThmTactical cls thry = ThmTactic cls thry -> ThmTactic cls thry

{-# INLINE nullInst #-}
nullInst :: Instantiation
nullInst = ([], [], ([], [], []))

{-# INLINE nullMeta #-}
nullMeta :: ([HOLTerm], Instantiation)
nullMeta = ([], nullInst)

-- instantiation functions
-- apply instantiation to a goal
inst_goal :: BoolCtxt thry => Instantiation -> Goal -> HOL cls thry Goal
inst_goal p (Goal thms w) = 
    do thms' <- mapM (return `ffCombM` ruleINSTANTIATE_ALL p) thms
       return . Goal thms' $ instantiate p w

-- compose instantiations
composeInsts :: Instantiation -> Instantiation -> HOL cls thry Instantiation
composeInsts (pats1, tmenv1, (tys1, tyops, opops)) 
              i2@(pats2, tmenv2, tyenv2@(tys2, tyops2, opops2)) =
    let tmenv = map (instFull tyenv2 `ffComb` instantiate i2) tmenv1
        tys = map (typeSubstFull tyenv2 `ffComb` id) tys1
        tmenv' = filter (\ (x, _) -> isNothing $ lookup x tmenv) tmenv2
        tys' = filter (\ (a, _) -> isNothing $ lookup a tys) tys2
        tyops' = filter (\ (a, _) -> isNothing $ lookup a tyops) tyops2
        opops' = filter (\ (a, _) -> isNothing $ lookup a opops) opops2 in
      return (pats1++pats2, tmenv++tmenv', 
              (tys++tys', tyops++tyops', opops++opops'))

-- falsity
mk_fthm :: BoolCtxt thry => [HOLTerm] -> HOLTerm -> HOL cls thry HOLThm
mk_fthm asl c = 
    do pth <- mk_fthm_pth
       qth <- mk_fthm_qth
       th <- ruleCONTR c pth
       aths <- foldrM ruleADD_ASSUM th $ reverse asl
       return $ rulePROVE_HYP qth aths
  where mk_fthm_pth :: BoolCtxt thry => HOL cls thry HOLThm
        mk_fthm_pth = cacheProof "mk_fthm_pth" ctxtBool $
            do (pth', _) <- ruleEQ_IMP def_FALSITY_
               ruleUNDISCH pth'

        mk_fthm_qth :: BoolCtxt thry => HOL cls thry HOLThm
        mk_fthm_qth = cacheProof "mk_fthm_qth" ctxtBool $
            do falsity <- toHTm "_FALSITY_"
               liftO $ primASSUME falsity


-- validity of tactics.
fake_thm :: BoolCtxt thry => Goal -> HOL cls thry HOLThm
fake_thm (Goal asl w) = let asms = foldr (union . hyp . snd) [] asl in
                          mk_fthm asms w

tacVALID :: BoolCtxt thry => Tactic cls thry -> Tactic cls thry
tacVALID tac g =
  do ftm <- serve [bool| _FALSITY_ |]
     res@(GS (_, i) gls just) <- tac g
     ths <- mapM fake_thm gls
     thm <- just nullInst ths
     let (asl', w') = destThm thm
     (Goal asl'' w'') <- inst_goal i g
     let maxasms = foldr (\ (_, th) -> union (nub (concl th:hyp th))) [] asl''
     if aConv w' w'' && 
        all (\ t -> aConv t `any` maxasms) (asl' \\ [ftm])
        then return res
        else fail "VALID: Invalid tactic"
                           

-- convert tactic to refinement based on head subgoal
by :: BoolCtxt thry => Tactic cls thry -> Refinement cls thry
by _ (GS _ [] _) = fail "by: no goal set"
by tac (GS (mvs, i) (g:ogls) just) =
    do (GS (newmvs, newinst) subgls subjust) <- tac g
       let n = length subgls
           mvs' = newmvs `union` mvs
       i' <- composeInsts i newinst
       ogls' <- mapM (inst_goal newinst) ogls
       let gls' = subgls ++ ogls'
           just' i2 ths = do i2' <- composeInsts i' i2
                             case chopList n ths of
                               Just (cths, oths) ->
                                   do cths' <- subjust i2 cths
                                      let sths = cths':oths
                                      just i2' sths
                               _ -> fail "byJust"
       return (GS (mvs', i') gls' just')

-- tactic language
propagate_empty :: JustificationList cls thry
propagate_empty _ [] = return []
propagate_empty _ _  = fail "propagate_empty: improper justification"

propagate_thm :: BoolCtxt thry => HOLThm -> Justification cls thry
propagate_thm th i [] = ruleINSTANTIATE_ALL i th
propagate_thm _ _ _   = fail "propagate_thm: improper justification"

compose_justs :: Int -> Justification cls thry -> JustificationList cls thry -> 
                 JustificationList cls thry
compose_justs n just1 just2 i ths =
    case chopList n ths of
      Just (ths1, ths2) -> do res1 <- just1 i ths1
                              res2 <- just2 i ths2
                              return (res1:res2)
      Nothing -> fail "compose_justs"

seqapply :: BoolCtxt thry => [Tactic cls thry] -> [Goal] -> 
            HOL cls thry (([HOLTerm], Instantiation), [Goal], JustificationList cls thry)
seqapply [] [] = return (nullMeta, [], propagate_empty)
seqapply (tac:tacs) (goal:goals) = 
    do (GS (mvs1, insts1) gls1 just1) <- tac goal
       goals' <- mapM (inst_goal insts1) goals
       ((mvs2, insts2), gls2, just2) <- seqapply tacs goals'
       insts' <- composeInsts insts1 insts2
       let justs' = compose_justs (length gls1) just1 just2
       return ((mvs1 `union` mvs2, insts'), gls1++gls2, justs')
seqapply _ _ = fail "seqapply: length mismatch"

justsequence :: Justification cls thry -> JustificationList cls thry -> 
                Instantiation -> Justification cls thry
justsequence just1 just2 insts2 i ths =
    do insts' <- composeInsts insts2 i
       ths' <- just2 i ths
       just1 insts' ths'

tacsequence :: BoolCtxt thry => GoalState cls thry -> [Tactic cls thry] -> 
               HOL cls thry (GoalState cls thry)
tacsequence (GS (mvs1, insts1) gls1 just1) tacl =
    do ((mvs2, insts2), gls2, just2) <- seqapply tacl gls1
       let jst = justsequence just1 just2 insts2
           just = if null gls2
                  then (\ i thl -> do th1 <- jst nullInst []
                                      propagate_thm th1 i thl)
                  else jst
       insts' <- composeInsts insts1 insts2
       return $! GS (mvs1 `union` mvs2, insts') gls2 just

-- tactic combinators
instance Lang (Tactic cls thry) where
    _FAIL = tacFAIL
    _NO = tacNO
    _ORELSE = tacORELSE
    _FIRST = tacFIRST
    _CHANGED = tacCHANGED
    _TRY = tacTRY
    _ALL g = return (GS nullMeta [g] justification) 
      where justification _ [th] = return th
            justification _ _    = fail "tacALL: improper justification"

-- should be just tacTHEN but there's a weird linking bug with ghci right now
instance BoolCtxt thry => LangSeq (Tactic cls thry) where
    tac1 `_THEN` tac2 = tacTHEN tac1 tac2 
    _REPEAT = tacREPEAT
    _EVERY = tacEVERY


tacTHEN :: BoolCtxt thry => Tactic cls thry -> Tactic cls thry -> Tactic cls thry
tacTHEN tac1 tac2 g =
    do gstate@(GS _ gls _) <- tac1 g
       let tacs = replicate (length gls) tac2
       tacsequence gstate tacs

_THENL :: BoolCtxt thry => Tactic cls thry -> [Tactic cls thry] -> Tactic cls thry
_THENL tac1 tacs g =
    do gstate@(GS _ gls _) <- tac1 g
       tacsequence gstate $ if null gls then [] else tacs

tacORELSE :: Tactic cls thry -> Tactic cls thry -> Tactic cls thry
tacORELSE tac1 tac2 g = tac1 g <|> tac2 g

tacFAIL :: String -> Tactic cls thry
tacFAIL s _ = fail s 

tacNO :: Tactic cls thry
tacNO = tacFAIL "tacNO"

{-
tacALL :: Tactic cls thry
tacALL g = return (GS nullMeta [g] justification) 
    where justification _ [th] = return th
          justification _ _    = fail "tacALL: improper justification"
-}

tacTRY :: Tactic cls thry -> Tactic cls thry
tacTRY tac = tac `_ORELSE` _ALL

tacREPEAT :: BoolCtxt thry => Tactic cls thry -> Tactic cls thry
tacREPEAT tac = (tac `_THEN` tacREPEAT tac) `_ORELSE` _ALL

tacEVERY :: BoolCtxt thry => [Tactic cls thry] -> Tactic cls thry
tacEVERY = foldr _THEN _ALL

tacFIRST :: [Tactic cls thry] -> Tactic cls thry
tacFIRST [] = tacFAIL "empty tactic list for tacFIRST"
tacFIRST tacs = foldr1 _ORELSE tacs

_MAP_EVERY :: BoolCtxt thry => (b -> Tactic cls thry) -> [b] -> Tactic cls thry
_MAP_EVERY f xs = tacEVERY $ map f xs

tacCHANGED :: Tactic cls thry -> Tactic cls thry
tacCHANGED tac g =
    do gstate@(GS meta gl _) <- tac g
       if meta /= nullMeta 
          then return gstate
          else case gl of
                 (g':[])
                     | g' == g -> fail "tacCHANGED"
                     | otherwise -> return gstate
                 _ -> return gstate

tacREPLICATE :: BoolCtxt thry => Int -> Tactic cls thry -> Tactic cls thry
tacREPLICATE n tac
    | n <= 0 = _ALL
    | otherwise = tac `_THEN` tacREPLICATE (n - 1) tac

-- combinators for theorem tacticals
instance Lang (ThmTactical cls thry) where
    _FAIL = tclFAIL
    _NO = tclNO
    _ALL = tclALL
    _ORELSE = tclORELSE
    _FIRST = tclFIRST
    _CHANGED = tclCHANGED
    _TRY = tclTRY

instance LangSeq (ThmTactical cls thry) where
    _THEN = tclTHEN
    _REPEAT = tclREPEAT
    _EVERY = tclEVERY

tclFAIL :: String -> ThmTactical cls thry
tclFAIL msg _ _ = fail msg

tclNO :: ThmTactical cls thry
tclNO = _FAIL "tclNO"

tclALL :: ThmTactical cls thry
tclALL = id

tclORELSE :: ThmTactical cls thry -> ThmTactical cls thry 
          -> ThmTactical cls thry
tclORELSE ttcl1 ttcl2 ttac th g = ttcl1 ttac th g <|> ttcl2 ttac th g

tclFIRST :: [ThmTactical cls thry] -> ThmTactical cls thry
tclFIRST [] = _FAIL "tclFIRST: empty list"
tclFIRST ttcll = foldr1 _ORELSE ttcll

tclCHANGED :: ThmTactical cls thry -> ThmTactical cls thry
tclCHANGED _ = _FAIL "tclCHANGED: undefined"


tclTRY :: ThmTactical cls thry -> ThmTactical cls thry
tclTRY ttcl = ttcl `_ORELSE` _ALL

tclTHEN :: ThmTactical cls thry -> ThmTactical cls thry -> ThmTactical cls thry
tclTHEN ttcl1 ttcl2 ttac = ttcl1 (ttcl2 ttac)

tclREPEAT :: ThmTactical cls thry -> ThmTactical cls thry
tclREPEAT ttcl = (ttcl `_THEN` _REPEAT ttcl) `_ORELSE` _ALL

tclEVERY :: [ThmTactical cls thry] -> ThmTactical cls thry
tclEVERY = foldr _THEN _ALL


-- manipulation of assumption list
tacLABEL :: BoolCtxt thry => Text -> ThmTactic cls thry
tacLABEL s thm (Goal asl w) =
    return $! GS nullMeta [Goal ((s, thm):asl) w] justification
    where justification i [th] = do thm' <- ruleINSTANTIATE_ALL i thm
                                    return $ rulePROVE_HYP thm' th
          justification _ _    = fail "tacLABEL: improper justification"

tacASSUME :: (BoolCtxt thry, HOLThmRep thm cls thry) => thm -> Tactic cls thry
tacASSUME th = liftM1 (tacLABEL "") $ toHThm th

_POP_ASSUM :: ThmTactic cls thry -> Tactic cls thry
_POP_ASSUM ttac (Goal ((_, th):asl) w) = ttac th (Goal asl w)
_POP_ASSUM _ _ = fail "_POP_ASSUM: no assumption to pop"

_ASSUM_LIST :: ([HOLThm] -> Tactic cls thry) -> Tactic cls thry
_ASSUM_LIST aslfun g@(Goal asl _) = aslfun (map snd asl) g

_POP_ASSUM_LIST :: ([HOLThm] -> Tactic cls thry) -> Tactic cls thry
_POP_ASSUM_LIST aslfun (Goal asl w) = aslfun (map snd asl) (Goal [] w)

_EVERY_ASSUM :: BoolCtxt thry => ThmTactic cls thry -> Tactic cls thry
_EVERY_ASSUM ttac = _ASSUM_LIST (_MAP_EVERY ttac)

_FIRST_ASSUM :: ThmTactic cls thry -> Tactic cls thry
_FIRST_ASSUM ttac g@(Goal asl _) = tryFind (\ (_, th) -> ttac th g) asl

tacRULE_ASSUM :: BoolCtxt thry => (HOLThm -> HOL cls thry HOLThm) -> Tactic cls thry
tacRULE_ASSUM rule g@(Goal asl _) =
    (_POP_ASSUM_LIST (const _ALL) `_THEN`
     _MAP_EVERY (\ (s, th) gl -> do th' <- rule th
                                    tacLABEL s th' gl) (reverse asl)) g

-- augment a set of theorems with assumptions
tacASM :: HOLThmRep thm cls thry => ([HOLThm] -> Tactic cls thry) -> [thm] 
       -> Tactic cls thry
tacASM tltac ths g@(Goal asl _) = 
    do ths' <- mapM toHThm ths
       tltac (map snd asl++ths') g

-- basic tactic that uses a theorem equal to the goal
tacACCEPT' :: BoolCtxt thry => ThmTactic cls thry
tacACCEPT' th (Goal _ w) =
    if aConv (concl th) w
    then return . GS nullMeta [] $ propagate_thm th
    else fail "tacACCEPT"

tacACCEPT :: (BoolCtxt thry, HOLThmRep thm cls thry) => thm -> Tactic cls thry
tacACCEPT pth = liftM1 tacACCEPT' (toHThm pth)

-- create a tactic from a conversion
tacCONV :: BoolCtxt thry => Conversion cls thry -> Tactic cls thry
tacCONV conv g@(Goal asl w) =
    do t_tm <- serve [bool| T |]
       th <- runConv conv w
       let tm = concl th
       if aConv tm w
          then tacACCEPT th g
          else case destEq tm of
                 Just (l, r)
                     | aConv l w -> 
                         if r == t_tm then do th' <- ruleEQT_ELIM th
                                              tacACCEPT th' g
                         else do th' <- fromRightM $ ruleSYM th
                                 return . GS nullMeta [Goal asl r] $ justification th'
                     | otherwise -> fail "tacCONV: bad equation"
                 _ -> fail "tacCONV: not an equation"
    where justification th' i [thm] = do th'' <- ruleINSTANTIATE_ALL i th'
                                         fromRightM $ primEQ_MP th'' thm
          justification _ _ _       = fail "tacCONV: improper justification"
                                                                 
-- equality tactics
tacREFL :: BoolCtxt thry => Tactic cls thry
tacREFL g@(Goal _ (Comb _ x)) = tacACCEPT (primREFL x) g
tacREFL _ = fail "tacREFL: goal not a combination"

tacABS :: Tactic cls thry
tacABS (Goal asl w@(Abs lv lb := Abs rv rb)) =
    let avoids = foldr (union . thmFrees . snd) (frees w) asl in
      do v <- mkPrimedVar avoids lv 
         l' <- liftO $ varSubst [(lv, v)] lb
         w' <- mkEq l' #<< varSubst [(rv, v)] rb
         return . GS nullMeta [Goal asl w'] $ justification v
  where justification v i [thm] = liftO $
            do ath <- primABS v thm
               liftM1 primEQ_MP (ruleALPHA (concl ath) $ instantiate i w) ath
        justification _ _ _ = fail "tacABS: improper justification"
tacABS _ = fail "tacREFL: goal not an equality."

tacMK_COMB :: Tactic cls thry
tacMK_COMB (Goal asl gl) =
    do ((f, x), (g, y)) <- fromJustM (pairMapM destComb =<< destEq gl)
       g1 <- mkEq f g
       g2 <- mkEq x y
       return $! GS nullMeta [Goal asl g1, Goal asl g2] justification 

  where justification _ [th1, th2] = fromRightM $ primMK_COMB th1 th2
        justification _ _ = fail "tacMK_COMB: improper justification"

tacAP_TERM :: BoolCtxt thry => Tactic cls thry
tacAP_TERM g = (tacMK_COMB `_THENL` [tacREFL, _ALL]) g <?> "tacAP_TERM"

tacAP_THM :: BoolCtxt thry => Tactic cls thry
tacAP_THM g = (tacMK_COMB `_THENL` [_ALL, tacREFL]) g <?> "tacAP_THM"
      
tacBINOP :: BoolCtxt thry => Tactic cls thry
tacBINOP g = (tacMK_COMB `_THENL` [tacAP_TERM, _ALL]) g <?> "tacAP_THM"

tacSUBST1' :: BoolCtxt thry => ThmTactic cls thry
tacSUBST1' th = tacCONV (convSUBS [th])

tacSUBST1 :: (BoolCtxt thry, HOLThmRep thm cls thry) => thm -> Tactic cls thry
tacSUBST1 th = liftM1 tacSUBST1' (toHThm th)

tacSUBST_ALL :: (BoolCtxt thry, HOLThmRep thm cls thry) => thm 
             -> Tactic cls thry
tacSUBST_ALL rth =
    tacSUBST1 rth `_THEN` tacRULE_ASSUM (ruleSUBS [rth])

tacBETA :: BoolCtxt thry => Tactic cls thry
tacBETA = tacCONV (convREDEPTH convBETA)

tacSUBST_VAR :: BoolCtxt thry => ThmTactic cls thry
tacSUBST_VAR th =
    let (asm, eq) = destThm th in
      case destEq eq of
        Nothing -> _FAIL "tacSUBST_VAR: conclusion not an equivalence"
        Just (l, r)
          | l `aConv` r -> _ALL
          | not (frees eq `subset` catFrees asm) -> _FAIL "tacSUBST_VAR"
          | (isConst l || isVar l) && not (l `freeIn` r) -> tacSUBST_ALL th
          | (isConst r ||  isVar r) && not (r `freeIn` l) -> 
              liftM1 tacSUBST_ALL (fromRightM $ ruleSYM th)
          | otherwise -> _FAIL "tacSUBST_VAR"

-- basic logical tactics
tacDISCH :: BoolCtxt thry => Tactic cls thry
tacDISCH (Goal asl w) =
    do f_tm <- serve [bool| F |]
       (do (ant, c) <- fromJustM $ destImp w
           th <- fromRightM $ primASSUME ant
           return . GS nullMeta [Goal (("", th):asl) c] $ justification1 ant)
         <|> 
         do ant <- fromJustM $ destNeg w
            th <- fromRightM $ primASSUME ant
            return . GS nullMeta [Goal (("", th):asl) f_tm] $ justification2 ant
         <?> "tDISCH_TAC"
    where justification1 ant i [th] = 
              ruleDISCH (instantiate i ant) th
          justification1 _ _ _      = fail "tDISCH_TAC: improper justification"
          justification2 ant i [th] = 
              ruleNOT_INTRO =<< ruleDISCH (instantiate i ant) th
          justification2 _ _ _      = fail "tDISCH_TAC: improper justification"

tacMP :: (BoolCtxt thry, HOLThmRep thm cls thry) => thm -> Tactic cls thry
tacMP th = liftM1 tacMP' $ toHThm th

tacMP' :: BoolCtxt thry => ThmTactic cls thry
tacMP' thm (Goal asl w) =
    (do tm <- mkImp (concl thm) w
        return $ GS nullMeta [Goal asl tm] justification) <?> "tacMP"
    where justification i [th] = ruleMP th =<< ruleINSTANTIATE_ALL i thm
          justification _ _    = fail "tMP_TAC: improper justification"

tacEQ :: BoolCtxt thry => Tactic cls thry
tacEQ (Goal asl w) =
    case destEq w of
      Just (l, r) -> (do tm1 <- mkImp l r
                         tm2 <- mkImp r l
                         return $! GS nullMeta [Goal asl tm1, Goal asl tm2] justification)
                     <?> "tacEQ"
      _ -> fail "tacEQ: not an equality conclusion"
    where justification _ [th1, th2] = ruleIMP_ANTISYM th1 th2
          justification _ _          = fail "tacEQ: improper justification"

tacUNDISCH :: (BoolCtxt thry, HOLTermRep tm cls thry) => tm -> Tactic cls thry
tacUNDISCH t = liftM1 tacUNDISCH' (toHTm t)
  where tacUNDISCH' :: BoolCtxt thry => HOLTerm -> Tactic cls thry
        tacUNDISCH' tm (Goal asl w) =
            case remove (\ (_, asm) -> concl asm `aConv` tm) asl of
              Just ((_, thm), asl') -> (do tm' <- mkImp tm w
                                           return . GS nullMeta [Goal asl' tm'] $ just thm) <?> "tacUNDISCH"
              Nothing -> fail "tacUNDISCH"
        
        just thm i (th:[]) = ruleMP th =<< ruleINSTANTIATE_ALL i thm
        just _ _ _ = fail "tacUNDISCH: bad justification"

tacSPEC :: (BoolCtxt thry, HOLTermRep tm1 cls thry,
            HOLTermRep tm2 cls thry) => (tm1, tm2) -> Tactic cls thry
tacSPEC (pt, px) (Goal asl w) =
    do x <- toHTm px
       t <- toHTm pt
       tm' <- (mkForall x #<< subst [(t, x)] w) <?> "tacSPEC"
       return $! GS nullMeta [Goal asl tm'] justification
    where justification i (th:[]) = 
              do t <- toHTm pt
                 ruleSPEC (instantiate i t) th
          justification _ _ = fail "tacSPEC: bad justification"

tacX_GEN :: (BoolCtxt thry, HOLTermRep tm cls thry) => tm -> Tactic cls thry
tacX_GEN px (Goal asl w) =
    do x' <- toHTm px
       case (x', destForall w) of
         (Var{}, Just (x, bod)) -> 
           let avoids = foldr (union . thmFrees . snd) (frees w) asl in
             if x' `elem` avoids then fail "tacX_GEN"
             else (let afn = ruleCONV (convGEN_ALPHA x) in
                    do bod' <- liftMaybe "tacX_GEN" $ varSubst [(x, x')] bod
                       return . GS nullMeta [Goal asl bod'] $ justification afn)
                      <?> "tacX_GEN"
         (_, Nothing) -> fail "tacX_GEN: not a forall conclusion"
         _ -> fail "tacX_GEN: provided term not a variable."
  where justification afn _ [th] = afn =<< ruleGEN px th
        justification _ _ _      = fail "tacX_GEN: improper justification"

tacGEN :: BoolCtxt thry => Tactic cls thry
tacGEN g@(Goal asl w) =
    case destForall w of
      Just (x, _) -> let avoids = foldr (union . thmFrees . snd) (frees w) asl in
                       (do x' <- mkPrimedVar avoids x
                           tacX_GEN x' g)
                      <?> "tacGEN"
      _ -> fail "tacGEN"

tacEXISTS' :: BoolCtxt thry => HOLTerm -> Tactic cls thry
tacEXISTS' t (Goal asl w) =
    case destExists w of
      Just (v, bod) -> 
          do bod' <- liftMaybe "tacEXISTS" $ varSubst [(v, t)] bod
             return $! GS nullMeta [Goal asl bod'] justification
      _ -> fail "tEXISTS_TAC"
    where justification i [th] = 
              ruleEXISTS (instantiate i w) (instantiate i t) th
          justification _ _    = fail "tEXISTS_TAC: improper justification"

tacEXISTS :: (BoolCtxt thry, HOLTermRep tm cls thry) => tm -> Tactic cls thry
tacEXISTS t = liftM1 tacEXISTS' (toHTm t)

tacX_CHOOSE' :: BoolCtxt thry => HOLTerm -> ThmTactic cls thry
tacX_CHOOSE' x' xth (Goal asl w) =
    do (x, bod) <- liftMaybe "tacX_CHOOSE: not an exists conclusion" . 
                     destExists $ concl xth
       xth' <- liftEither "tacX_CHOOSE" $ primASSUME #<< varSubst [(x, x')] bod
       let avoids = foldr (union . frees . concl . snd) 
                          (frees w `union` thmFrees xth) asl
       if x' `elem` avoids 
          then fail "tacX_CHOOSE: provided variable is free in provided theorem"
          else return $! GS nullMeta [Goal (("", xth'):asl) w] justification
    where justification i [th] = do xth2 <- ruleINSTANTIATE_ALL i xth
                                    ruleCHOOSE x' xth2 th
          justification _ _    = fail "tacX_CHOOSE: improper justification"

tacX_CHOOSE :: (BoolCtxt thry, HOLTermRep tm cls thry, HOLThmRep thm cls thry) 
            => tm -> thm -> Tactic cls thry
tacX_CHOOSE tm th g = 
    do tm' <- toHTm tm
       th' <- toHThm th
       tacX_CHOOSE' tm' th' g

tacCHOOSE :: (BoolCtxt thry, HOLThmRep thm cls thry) => thm -> Tactic cls thry
tacCHOOSE pth (Goal asl w) =
    do xth <- toHThm pth
       case destExists $ concl xth of
         Just (x, _) -> 
           let avoids = foldr (union . thmFrees . snd) 
                              (frees w `union` thmFrees xth) asl in
             (do x' <- mkPrimedVar avoids x
                 tacX_CHOOSE x' xth $ Goal asl w)
             <?> "tacCHOOSE"
         _ -> fail "tacCHOOSE: not an exists conclusion"

tacCONJ :: BoolCtxt thry => Tactic cls thry
tacCONJ (Goal asl w) =
    case destConj w of
      Just (l, r) -> return $! GS nullMeta [Goal asl l, Goal asl r] justification
      _ -> fail "tacCONJ"
    where justification _ [th1, th2] = ruleCONJ th1 th2
          justification _ _          = fail "tacCONJ: improper justification"

tacDISJ1 :: BoolCtxt thry => Tactic cls thry
tacDISJ1 (Goal asl w) =
    case destDisj w of
      Just (l, r) -> return $! GS nullMeta [Goal asl l] (justification r)
      _ -> fail "tacDISJ1"
    where justification r i [th] = ruleDISJ1 th $ instantiate i r
          justification _ _ _    = fail "tacDISJ1: improper justification"

tacDISJ2 :: BoolCtxt thry => Tactic cls thry
tacDISJ2 (Goal asl w) =
    case destDisj w of
      Just (l, r) -> return $! GS nullMeta [Goal asl r] (justification l)
      _ -> fail "tacDISJ2"
    where justification l i [th] =
              ruleDISJ2 (instantiate i l) th
          justification _ _ _    = fail "tacDISJ2: improper justification"

tacDISJ_CASES :: (BoolCtxt thry, HOLThmRep thm cls thry) => thm 
              -> Tactic cls thry
tacDISJ_CASES pth (Goal asl w) =
    do dth <- toHThm pth
       (lth, rth) <- liftEither "tacDISJ_CASES: Maybe block" $
                       pairMapM primASSUME #<< destDisj (concl dth)
       return $! GS nullMeta [Goal (("", lth):asl) w, 
                               Goal (("", rth):asl) w] justification
    where justification i [th1, th2] = do dth' <- ruleINSTANTIATE_ALL i pth
                                          ruleDISJ_CASES dth' th1 th2
          justification _ _          = fail "tacDISJ_CASES: improper justification"

tacCONTR :: BoolCtxt thry => ThmTactic cls thry
tacCONTR cth (Goal _ w) =
    (do th <- ruleCONTR w cth
        return . GS nullMeta [] $ propagate_thm th)
    <?> "tacCONTR"

rawtac :: BoolCtxt thry => ThmTactic cls thry
rawtac thm (Goal _ w) =
    (do ith <- rulePART_MATCH return thm w
        return . GS nullMeta [] $ propagate_thm ith)
    <?> "tacACCEPT"

tacMATCH_ACCEPT' :: BoolCtxt thry => ThmTactic cls thry
tacMATCH_ACCEPT' th = _REPEAT tacGEN `_THEN` rawtac th

tacMATCH_ACCEPT :: (BoolCtxt thry, HOLThmRep thm cls thry) => 
                   thm -> Tactic cls thry
tacMATCH_ACCEPT pth = liftM1 tacMATCH_ACCEPT' (toHThm pth)

tacMATCH_MP :: (BoolCtxt thry, HOLThmRep thm cls thry) => thm -> Tactic cls thry
tacMATCH_MP pth (Goal asl w) =
    (do th <- toHThm pth
        sth <- let tm = concl th
                   (avs, bod) = stripForall tm in
                 (do (ant, con) <- fromJustM $ destImp bod
                     th1 <- ruleSPECL avs #<< primASSUME tm
                     th2 <- ruleUNDISCH th1
                     let evs = filter (\ v -> varFreeIn v ant && not (varFreeIn v con)) avs
                     th2_5 <- ruleDISCH tm th2
                     th3 <- foldrM ruleSIMPLE_CHOOSE th2_5 evs
                     tm3 <- liftMaybe "tacMATCH_MP" . tryHead $ hyp th3
                     th4 <- ruleDISCH tm =<< ruleGEN_ALL =<< ruleDISCH tm3 =<< ruleUNDISCH th3
                     ruleMP th4 th) <?> "tacMATCH_MP: bad theorem"
        let match_fun = rulePART_MATCH (liftM snd . destImp) sth
        xth <- match_fun w
        (lant, _) <- fromJustM . destImp $ concl xth
        return $! GS nullMeta [Goal asl lant] (justification xth)) 
    <?> "tacMATCH_MP: no match"
    where justification xth i [thm] = do thm2 <- ruleINSTANTIATE_ALL i xth
                                         ruleMP thm2 thm
          justification _ _ _       = fail "tacMATCH_MP: improper justification"

-- theorem continuations
_CONJUNCTS_THEN2 :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                 => ThmTactic cls thry -> ThmTactic cls thry -> thm 
                 -> Tactic cls thry
_CONJUNCTS_THEN2 ttac1 ttac2 pth gl = 
    do cth <- toHThm pth
       (c1th, c2th) <- liftEither "_CONJUNCTS_THEN2: Maybe block" $
                         pairMapM primASSUME #<< destConj (concl cth)
       (GS ti gls jfn) <- (ttac1 c1th `_THEN` ttac2 c2th) gl
       let jfn' i ths =
               do (thm1, thm2) <- ruleCONJ_PAIR =<< ruleINSTANTIATE_ALL i cth
                  thm3 <- jfn i ths
                  return . rulePROVE_HYP thm1 $ rulePROVE_HYP thm2 thm3
       return (GS ti gls jfn')

_CONJUNCTS_THEN :: BoolCtxt thry => ThmTactical cls thry
_CONJUNCTS_THEN = wComb _CONJUNCTS_THEN2

_DISJ_CASES_THEN2 :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                  => ThmTactic cls thry -> ThmTactic cls thry 
                  -> thm -> Tactic cls thry
_DISJ_CASES_THEN2 ttac1 ttac2 cth =
  tacDISJ_CASES cth `_THENL` [_POP_ASSUM ttac1, _POP_ASSUM ttac2]

_DISJ_CASES_THEN :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                 => ThmTactic cls thry -> thm -> Tactic cls thry
_DISJ_CASES_THEN = wComb _DISJ_CASES_THEN2

_DISCH_THEN :: BoolCtxt thry => ThmTactic cls thry -> Tactic cls thry
_DISCH_THEN ttac = tacDISCH `_THEN` _POP_ASSUM ttac

_X_CHOOSE_THEN :: (BoolCtxt thry, HOLTermRep tm cls thry, 
                   HOLThmRep thm cls thry) => tm -> ThmTactic cls thry -> thm 
               -> Tactic cls thry
_X_CHOOSE_THEN tm a thm g = 
    do tm' <- toHTm tm
       thm' <- toHThm thm
       _X_CHOOSE_THEN' tm' a thm' g
  where _X_CHOOSE_THEN' :: BoolCtxt thry => HOLTerm -> ThmTactical cls thry
        _X_CHOOSE_THEN' x ttac th = tacX_CHOOSE x th `_THEN` _POP_ASSUM ttac

_CHOOSE_THEN :: (BoolCtxt thry, HOLThmRep thm cls thry) => ThmTactic cls thry
             -> thm -> Tactic cls thry
_CHOOSE_THEN ttac th = tacCHOOSE th `_THEN` _POP_ASSUM ttac

-- some derived tactics
_STRIP_THM_THEN :: BoolCtxt thry => ThmTactical cls thry
_STRIP_THM_THEN = 
    _FIRST [ _CONJUNCTS_THEN
           , _DISJ_CASES_THEN
           , _CHOOSE_THEN
           ]

_ANTE_RES_THEN :: BoolCtxt thry => ThmTactical cls thry
_ANTE_RES_THEN ttac ante =
    _ASSUM_LIST (\ asl g -> 
                 do tacs <- mapFilterM (\ imp -> 
                                        do th' <- ruleMATCH_MP imp ante
                                           return (ttac th')) asl
                    if null tacs 
                       then fail "_ANTE_RES_THEN"
                       else _EVERY tacs g)

tacSTRIP_ASSUME :: BoolCtxt thry => ThmTactic cls thry
tacSTRIP_ASSUME = 
    _REPEAT _STRIP_THM_THEN
    (\ gth -> _FIRST [tacCONTR gth, tacACCEPT gth,
                      tDISCARD_TAC gth, tacASSUME gth])
    where tDISCARD_TAC :: ThmTactic cls thry
          tDISCARD_TAC th g@(Goal asl _) =
              let tm = concl th in
                if any (aConv tm . concl . snd) asl
                then _ALL g
                else fail "tDISCARD_TAC: not already present"

tacSTRUCT_CASES :: BoolCtxt thry => ThmTactic cls thry
tacSTRUCT_CASES = 
    _REPEAT _STRIP_THM_THEN 
    (\ th -> tacSUBST1 th `_ORELSE` tacASSUME th)

tacSTRIP :: BoolCtxt thry => Tactic cls thry
tacSTRIP g =
    _STRIP_GOAL_THEN tacSTRIP_ASSUME g <?> "tacSTRIP"

_STRIP_GOAL_THEN :: BoolCtxt thry => ThmTactic cls thry -> Tactic cls thry
_STRIP_GOAL_THEN ttac = _FIRST [tacGEN, tacCONJ, _DISCH_THEN ttac]

_UNDISCH_THEN :: HOLTermRep tm cls thry => tm -> ThmTactic cls thry 
              -> Tactic cls thry
_UNDISCH_THEN ptm ttac g@(Goal asl w) =
    case asl of
      [] -> _FAIL "_UNDISCH_THEN: goal with empty assumption list" g
      _ -> do tm <- toHTm ptm
              (thp, asl') <- liftMaybe "_UNDISCH_THEN: remove" $ 
                               remove (\ (_, th) -> aConv (concl th) tm) asl
              ttac (snd thp) $ Goal asl' w

_FIRST_X_ASSUM :: ThmTactic cls thry -> Tactic cls thry
_FIRST_X_ASSUM ttac = _FIRST_ASSUM (\ th -> _UNDISCH_THEN (concl th) ttac)

-- subgoaling
_SUBGOAL_THEN :: HOLTermRep tm cls thry => tm -> ThmTactic cls thry
              -> Tactic cls thry
_SUBGOAL_THEN tm a b =
    do tm' <- toHTm tm
       _SUBGOAL_THEN' tm' a b
  where _SUBGOAL_THEN' :: HOLTerm -> ThmTactic cls thry -> Tactic cls thry
        _SUBGOAL_THEN' wa ttac g@(Goal asl _) =
            (do wath <- fromRightM $ primASSUME wa
                (GS meta gl just) <- ttac wath g
                return (GS meta (Goal asl wa:gl) $ justification just))
            <?> "_SUBGOAL_THEN"
        
        justification just i (l:ls) = 
            liftM (rulePROVE_HYP l) $ just i ls
        justification _ _ _ = fail "_SUBGOAL_THEN: improper justification"

-- metavariable tactics
tacX_META_EXISTS :: BoolCtxt thry => HOLTerm -> Tactic cls thry
tacX_META_EXISTS t@Var{} (Goal asl w) =
    case destExists w of
      Just (v, bod) -> 
          do bod' <- liftMaybe "tacX_META_EXISTS" $ varSubst [(v, t)] bod
             return $! GS ([t], nullInst) [Goal asl bod'] justification
      Nothing -> fail "tacX_META_EXISTS: not an existance conclusion"
    where justification i [th] = 
              ruleEXISTS (instantiate i w) (instantiate i t) th
          justification _ _    = fail "tacX_META_EXISTS: improper justification"
tacX_META_EXISTS _ _ = fail "tacX_META_EXISTS"


tacMETA_SPEC :: BoolCtxt thry => HOLTerm -> ThmTactic cls thry
tacMETA_SPEC t thm (Goal asl w) =
    do sth <- ruleSPEC t thm
       return $! GS ([t], nullInst) [Goal (("", sth):asl) w] justification
    where justification i [th] = 
              do thm' <- ruleSPEC (instantiate i t) thm
                 return $ rulePROVE_HYP thm' th
          justification _ _    = fail "tacMETA_SPEC: improper justification"

-- tactic proofs
mkGoalstate :: BoolCtxt thry => Goal -> HOL cls thry (GoalState cls thry)
mkGoalstate g@(Goal _ w)
    | typeOf w == tyBool = return $! GS nullMeta [g] justification
    | otherwise = fail "mkGoalstate: non-boolean goal"
    where justification i [th] = ruleINSTANTIATE_ALL i th
          justification _ _    = fail "mkGoalstate: improper justification"

ruleTAC_PROOF :: BoolCtxt thry => Goal -> Tactic cls thry -> HOL cls thry HOLThm
ruleTAC_PROOF g tac = 
    do gstate <- mkGoalstate g
       (GS _ sgs just) <- by tac gstate
       if null sgs 
          then just nullInst []
          else fail "ruleTAC_PROOF: unsolved goals"

prove' :: BoolCtxt thry => HOLTerm -> Tactic cls thry -> HOL cls thry HOLThm
prove' tm tac = 
    do th <- ruleTAC_PROOF (Goal [] tm) tac
       let tm' = concl th
       if tm' == tm 
          then return th
          else liftEither "prove: justification generated wrong theorem" $ 
                 do th1 <- ruleALPHA tm' tm
                    primEQ_MP th1 th

prove :: (BoolCtxt thry, HOLTermRep tm cls thry) => 
         tm -> Tactic cls thry -> HOL cls thry HOLThm
prove ptm = liftM1 prove' (toHTm ptm)
