{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, UndecidableInstances #-}
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

import Prelude hiding ((<$>))
import HaskHOL.Core

import HaskHOL.Lib.Bool
import HaskHOL.Lib.Equal
import HaskHOL.Lib.DRule

import Text.PrettyPrint.Free
import System.Console.Terminfo.PrettyPrint

-- Types

type Justification cls thry = Instantiation -> [HOLThm] -> HOL cls thry HOLThm
type JustificationList cls thry = 
    Instantiation -> [HOLThm] -> HOL cls thry [HOLThm]

data Goal = Goal [(Text, HOLThm)] HOLTerm deriving (Eq, Typeable)

instance ShowHOL Goal where
    showHOL = ppGoal

ppGoal :: Goal -> PrintM s TermDoc
ppGoal (Goal asl w) = 
    do asl' <- if null asl then return empty
               else setPrec 0 >> ppASL (reverse asl)
       w' <- setPrec 0 >> ppTerm w
       return $! asl' `above` text "-----" `above` w'

ppASL :: [(Text, HOLThm)] -> PrintM s TermDoc
ppASL [] = return empty
ppASL ((s, th):rest) = 
    let s' = if textNull s then empty
             else lparen <> pretty s <> rparen in
      do n <- getPrec
         c <- setPrec 0 >> ppTerm (concl th)
         rest' <- setPrec (n + 1) >> ppASL rest
         return $! pretty n <+> c <> s' `above` rest'

-- metavariables, instantiation, goal list, and justification
data GoalState cls thry = 
    GS ([HOLTerm], Instantiation) [Goal] (Justification cls thry) 
       deriving Typeable

instance ShowHOL (GoalState cls thry) where
    showHOL gs = setPrec 1 >> ppGoalState gs
    showHOLList [] = return $! text "Empty goalstack"
    showHOLList [gs] = showHOL gs
    showHOLList (gs@(GS _ g _):GS _ g0 _:_) =
        let p = length g - length g0
            p' = if p < 1 then 1 else p + 1 in
          setPrec p' >> ppGoalState gs
         
ppGoalState :: GoalState cls thry -> PrintM s TermDoc
ppGoalState (GS _ [] _) = return $! text "No subgoals"
ppGoalState (GS _ gls _) = 
    let n = length gls in
      do x <- getPrec
         gls' <- mapM ppGoal $ take x gls
         return $! pretty x <+> text "subgoal(s)" <+> 
                   parens (pretty n <+> text "total") `above` (vcat gls')

type Refinement cls thry = 
    GoalState cls thry -> HOL cls thry (GoalState cls thry)

type Tactic cls thry = Goal -> HOL cls thry (GoalState cls thry)
type ThmTactic thm cls thry = thm -> Tactic cls thry
type ThmTactical thm cls thry = ThmTactic thm cls thry -> ThmTactic thm cls thry

{-# INLINE nullInst #-}
nullInst :: Instantiation
nullInst = ([], [], ([], [], []))

{-# INLINE nullMeta #-}
nullMeta :: ([HOLTerm], Instantiation)
nullMeta = ([], nullInst)

-- instantiation functions
-- apply instantiation to a goal
instGoal :: BoolCtxt thry => Instantiation -> Goal -> HOL cls thry Goal
instGoal p (Goal thms w) = 
    do thms' <- mapM (return `ffCombM` ruleINSTANTIATE_ALL p) thms
       return . Goal thms' $ instantiate p w

-- compose instantiations
composeInsts :: Instantiation -> Instantiation -> Instantiation
composeInsts (pats1, tmenv1, (tys1, tyops, opops)) 
              i2@(pats2, tmenv2, tyenv2@(tys2, tyops2, opops2)) =
    let tmenv = map (instFull tyenv2 `ffComb` instantiate i2) tmenv1
        tys = map (typeSubstFull tyenv2 `ffComb` id) tys1
        tmenv' = filter (\ (x, _) -> isNothing $ lookup x tmenv) tmenv2
        tys' = filter (\ (a, _) -> isNothing $ lookup a tys) tys2
        tyops' = filter (\ (a, _) -> isNothing $ lookup a tyops) tyops2
        opops' = filter (\ (a, _) -> isNothing $ lookup a opops) opops2 in
      (pats1++pats2, tmenv++tmenv', (tys++tys', tyops++tyops', opops++opops'))
  where isNothing :: Maybe a -> Bool
        isNothing Nothing = True
        isNothing _ = False

-- falsity
mkFThm :: BoolCtxt thry => [HOLTerm] -> HOLTerm -> HOL cls thry HOLThm
mkFThm asl c = 
    do th <- ruleCONTR c mkFThm_pth
       aths <- foldrM ruleADD_ASSUM th $ reverse asl
       rulePROVE_HYP mkFThm_qth aths
  where mkFThm_pth :: BoolCtxt thry => HOL cls thry HOLThm
        mkFThm_pth = cacheProof "mkFThm_pth" ctxtBool $
            do (pth', _) <- ruleEQ_IMP def_FALSITY_
               ruleUNDISCH pth'

        mkFThm_qth :: BoolCtxt thry => HOL cls thry HOLThm
        mkFThm_qth = cacheProof "mkFThm_qth" ctxtBool $
            primASSUME [txt| _FALSITY_ |]


-- validity of tactics.
fakeThm :: BoolCtxt thry => Goal -> HOL cls thry HOLThm
fakeThm (Goal asl w) = mkFThm (foldr (union . hyp . snd) [] asl) w

tacVALID :: BoolCtxt thry => Tactic cls thry -> Tactic cls thry
tacVALID tac g =
  do ftm <- serve [bool| _FALSITY_ |]
     res@(GS (_, i) gls just) <- tac g
     ths <- mapM fakeThm gls
     (Thm asl' w') <- just nullInst ths
     (Goal asl'' w'') <- instGoal i g
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
           i' = composeInsts i newinst
       ogls' <- mapM (instGoal newinst) ogls
       let gls' = subgls ++ ogls'
           just' i2 ths = let i2' = composeInsts i' i2 in
                            case trySplitAt n ths of
                              Just (cths, oths) ->
                                  do cths' <- subjust i2 cths
                                     let sths = cths':oths
                                     just i2' sths
                              _ -> fail "byJust"
       return (GS (mvs', i') gls' just')

-- tactic language
propagateEmpty :: JustificationList cls thry
propagateEmpty _ [] = return []
propagateEmpty _ _  = fail "propagateEmpty: improper justification"

propagateThm :: BoolCtxt thry => HOLThm -> Justification cls thry
propagateThm th i [] = ruleINSTANTIATE_ALL i th
propagateThm _ _ _   = fail "propagateThm: improper justification"

composeJusts :: Int -> Justification cls thry -> JustificationList cls thry 
             -> JustificationList cls thry
composeJusts n just1 just2 i ths =
    case trySplitAt n ths of
      Just (ths1, ths2) -> do res1 <- just1 i ths1
                              res2 <- just2 i ths2
                              return (res1:res2)
      Nothing -> fail "composeJusts"

seqapply :: BoolCtxt thry => [Tactic cls thry] -> [Goal] 
         -> HOL cls thry (([HOLTerm], Instantiation), [Goal], 
                          JustificationList cls thry)
seqapply [] [] = return (nullMeta, [], propagateEmpty)
seqapply (tac:tacs) (goal:goals) = 
    do (GS (mvs1, insts1) gls1 just1) <- tac goal
       goals' <- mapM (instGoal insts1) goals
       ((mvs2, insts2), gls2, just2) <- seqapply tacs goals'
       let insts' = composeInsts insts1 insts2
           justs' = composeJusts (length gls1) just1 just2
       return ((mvs1 `union` mvs2, insts'), gls1++gls2, justs')
seqapply _ _ = fail "seqapply: length mismatch"

justsequence :: Justification cls thry -> JustificationList cls thry 
             -> Instantiation -> Justification cls thry
justsequence just1 just2 insts2 i ths =
    let insts' = composeInsts insts2 i in
      just1 insts' =<< just2 i ths

tacsequence :: BoolCtxt thry => GoalState cls thry -> [Tactic cls thry]
            -> HOL cls thry (GoalState cls thry)
tacsequence (GS (mvs1, insts1) gls1 just1) tacl =
    do ((mvs2, insts2), gls2, just2) <- seqapply tacl gls1
       let jst = justsequence just1 just2 insts2
           just = if null gls2
                  then (\ i thl -> do th1 <- jst nullInst []
                                      propagateThm th1 i thl)
                  else jst
       let insts' = composeInsts insts1 insts2
       return $! GS (mvs1 `union` mvs2, insts') gls2 just

-- tactic combinators
instance Lang (Tactic cls thry) where
    _FAIL = tacFAIL
    _ALL = tacALL
    _ORELSE = tacORELSE
    _CHANGED = tacCHANGED

-- should be just tacTHEN but there's a weird linking bug with ghci right now
instance BoolCtxt thry => LangSeq (Tactic cls thry) where
    _THEN = tacTHEN


tacTHEN :: BoolCtxt thry 
        => Tactic cls thry -> Tactic cls thry -> Tactic cls thry
tacTHEN tac1 tac2 g =
    do gstate@(GS _ gls _) <- tac1 g
       let tacs = replicate (length gls) tac2
       tacsequence gstate tacs

_THENL :: BoolCtxt thry 
       => Tactic cls thry -> [Tactic cls thry] -> Tactic cls thry
_THENL tac1 tacs g =
    do gstate@(GS _ gls _) <- tac1 g
       tacsequence gstate $ if null gls then [] else tacs

tacORELSE :: Tactic cls thry -> Tactic cls thry -> Tactic cls thry
tacORELSE tac1 tac2 g = tac1 g <|> tac2 g

tacFAIL :: String -> Tactic cls thry
tacFAIL s _ = fail s 

tacALL :: Tactic cls thry
tacALL g = return (GS nullMeta [g] justification) 
    where justification :: Justification cls thry
          justification _ [th] = return th
          justification _ _    = fail "tacALL: improper justification"

_MAP_EVERY :: BoolCtxt thry 
           => ThmTactic thm cls thry -> [thm] -> Tactic cls thry
_MAP_EVERY f xs = _EVERY $ map f xs

tacCHANGED :: Tactic cls thry -> Tactic cls thry
tacCHANGED tac g =
    do gstate@(GS meta gl _) <- tac g
       if meta /= nullMeta 
          then return gstate
          else case gl of
                 [g']
                     | g' == g -> fail "tacCHANGED"
                     | otherwise -> return gstate
                 _ -> return gstate

tacREPLICATE :: BoolCtxt thry => Int -> Tactic cls thry -> Tactic cls thry
tacREPLICATE n tac
    | n <= 0 = _ALL
    | otherwise = tac `_THEN` tacREPLICATE (n - 1) tac

-- combinators for theorem tacticals
instance Lang (ThmTactical thm cls thry) where
    _FAIL = tclFAIL
    _ALL = tclALL
    _ORELSE = tclORELSE
    _CHANGED = tclCHANGED

instance LangSeq (ThmTactical thm cls thry) where
    _THEN = tclTHEN

tclFAIL :: String -> ThmTactical thm cls thry
tclFAIL msg _ _ = fail msg

tclALL :: ThmTactical thm cls thry
tclALL = id

tclORELSE :: ThmTactical thm cls thry -> ThmTactical thm cls thry 
          -> ThmTactical thm cls thry
tclORELSE ttcl1 ttcl2 ttac th g = ttcl1 ttac th g <|> ttcl2 ttac th g

tclCHANGED :: ThmTactical thm cls thry -> ThmTactical thm cls thry
tclCHANGED ttcl ttac th g =
    do gstate@(GS meta gl _) <- ttcl ttac th g
       if meta /= nullMeta
          then return gstate
          else case gl of
                 [g']
                     | g' == g -> fail "tclCHANGED"
                     | otherwise -> return gstate
                 _ -> return gstate

tclTHEN :: ThmTactical thm cls thry -> ThmTactical thm cls thry 
        -> ThmTactical thm cls thry
tclTHEN ttcl1 ttcl2 ttac = ttcl1 (ttcl2 ttac)


-- manipulation of assumption list
tacLABEL :: (BoolCtxt thry, HOLThmRep thm cls thry) 
         => Text -> ThmTactic thm cls thry
tacLABEL s pthm (Goal asl w) =
    do thm <- toHThm pthm
       return . GS nullMeta [Goal ((s, thm):asl) w] $ justification thm
    where justification :: BoolCtxt thry => HOLThm -> Justification cls thry
          justification thm i [th] = do thm' <- ruleINSTANTIATE_ALL i thm
                                        rulePROVE_HYP thm' th
          justification _ _ _      = fail "tacLABEL: improper justification"

tacASSUME :: (BoolCtxt thry, HOLThmRep thm cls thry) => ThmTactic thm cls thry
tacASSUME = tacLABEL ""

_POP_ASSUM :: ThmTactic HOLThm cls thry -> Tactic cls thry
_POP_ASSUM ttac (Goal ((_, th):asl) w) = ttac th (Goal asl w)
_POP_ASSUM _ _ = fail "_POP_ASSUM: no assumption to pop"

_ASSUM_LIST :: ([HOLThm] -> Tactic cls thry) -> Tactic cls thry
_ASSUM_LIST aslfun g@(Goal asl _) = aslfun (map snd asl) g

_POP_ASSUM_LIST :: ([HOLThm] -> Tactic cls thry) -> Tactic cls thry
_POP_ASSUM_LIST aslfun (Goal asl w) = aslfun (map snd asl) (Goal [] w)

_EVERY_ASSUM :: BoolCtxt thry => ThmTactic HOLThm cls thry -> Tactic cls thry
_EVERY_ASSUM ttac = _ASSUM_LIST (_MAP_EVERY ttac)

_FIRST_ASSUM :: ThmTactic HOLThm cls thry -> Tactic cls thry
_FIRST_ASSUM ttac g@(Goal asl _) = tryFind (\ (_, th) -> ttac th g) asl

tacRULE_ASSUM :: BoolCtxt thry 
              => (HOLThm -> HOL cls thry HOLThm) -> Tactic cls thry
tacRULE_ASSUM rule g@(Goal asl _) =
    (_POP_ASSUM_LIST (const _ALL) `_THEN`
     _MAP_EVERY (\ (s, th) gl -> tacLABEL s (rule th) gl) (reverse asl)) g

-- augment a set of theorems with assumptions
tacASM :: HOLThmRep thm cls thry 
       => ([HOLThm] -> Tactic cls thry) -> [thm] -> Tactic cls thry
tacASM tltac ths g@(Goal asl _) = 
    do ths' <- mapM toHThm ths
       tltac (map snd asl++ths') g

-- basic tactic that uses a theorem equal to the goal
tacACCEPT :: (BoolCtxt thry, HOLThmRep thm cls thry) => ThmTactic thm cls thry
tacACCEPT pthm (Goal _ w) = 
    do thm@(Thm _ c) <- toHThm pthm
       if c `aConv` w
          then return . GS nullMeta [] $ propagateThm thm
          else fail "tacACCEPT"

-- create a tactic from a conversion
tacCONV :: BoolCtxt thry => Conversion cls thry -> Tactic cls thry
tacCONV conv g@(Goal asl w) =
    do ttm <- serve [bool| T |]
       th@(Thm _ tm) <- runConv conv w
       if aConv tm w
          then tacACCEPT th g
          else case destEq tm of
                 Just (l, r)
                     | aConv l w -> 
                         if r == ttm then tacACCEPT (ruleEQT_ELIM th) g
                         else do th' <- ruleSYM th
                                 return . GS nullMeta [Goal asl r] $ 
                                            justification th'
                     | otherwise -> fail "tacCONV: bad equation"
                 _ -> fail "tacCONV: not an equation"
    where justification :: BoolCtxt thry => HOLThm -> Justification cls thry
          justification th' i [thm] = do th'' <- ruleINSTANTIATE_ALL i th'
                                         primEQ_MP th'' thm
          justification _ _ _       = fail "tacCONV: improper justification"
                                                                 
-- equality tactics
tacREFL :: BoolCtxt thry => Tactic cls thry
tacREFL g@(Goal _ (Comb _ x)) = tacACCEPT (primREFL x) g
tacREFL _ = fail "tacREFL: goal not a combination."

tacABS :: Tactic cls thry
tacABS (Goal asl w@(Abs lv lb := Abs rv rb)) =
    let avoids = foldr (union . thmFrees . snd) (frees w) asl in
      do v <- mkPrimedVar avoids lv 
         l' <- varSubst [(lv, v)] lb
         w' <- mkEq l' =<< varSubst [(rv, v)] rb
         return . GS nullMeta [Goal asl w'] $ justification v
  where justification :: HOLTerm -> Justification cls thry
        justification v i [thm] =
            do ath <- primABS v thm
               primEQ_MP (ruleALPHA (concl ath) $ instantiate i w) ath
        justification _ _ _ = fail "tacABS: improper justification"
tacABS _ = fail "tacREFL: goal not an equality of abstractions."

tacMK_COMB :: Tactic cls thry
tacMK_COMB (Goal asl ((Comb f x) := (Comb g y))) =
    do g1 <- mkEq f g
       g2 <- mkEq x y
       return $! GS nullMeta [Goal asl g1, Goal asl g2] justification 
  where justification :: Justification cls thry
        justification _ [th1, th2] = primMK_COMB th1 th2
        justification _ _ = fail "tacMK_COMB: improper justification"
tacMK_COMB _ = fail "tacMK_COMB: goal not an equality of combinations."

tacAP_TERM :: BoolCtxt thry => Tactic cls thry
tacAP_TERM g = (tacMK_COMB `_THENL` [tacREFL, _ALL]) g <?> "tacAP_TERM"

tacAP_THM :: BoolCtxt thry => Tactic cls thry
tacAP_THM g = (tacMK_COMB `_THENL` [_ALL, tacREFL]) g <?> "tacAP_THM"
      
tacBINOP :: BoolCtxt thry => Tactic cls thry
tacBINOP g = (tacMK_COMB `_THENL` [tacAP_TERM, _ALL]) g <?> "tacAP_THM"

tacSUBST1 :: (BoolCtxt thry, HOLThmRep thm cls thry) => ThmTactic thm cls thry
tacSUBST1 th = tacCONV (convSUBS [th])

tacSUBST_ALL :: (BoolCtxt thry, HOLThmRep thm cls thry) 
             => ThmTactic thm cls thry
tacSUBST_ALL rth =
    tacSUBST1 rth `_THEN` tacRULE_ASSUM (ruleSUBS [rth])

tacBETA :: BoolCtxt thry => Tactic cls thry
tacBETA = tacCONV (convREDEPTH convBETA)

tacSUBST_VAR :: (BoolCtxt thry, HOLThmRep thm cls thry) 
             => ThmTactic thm cls thry
tacSUBST_VAR pthm g =
    do th@(Thm asm eq) <- toHThm pthm
       case destEq eq of
         Nothing -> _FAIL "tacSUBST_VAR: conclusion not an equivalence" g
         Just (l, r)
           | l `aConv` r -> _ALL g
           | not (frees eq `subset` catFrees asm) -> _FAIL "tacSUBST_VAR" g
           | (isConst l || isVar l) && not (l `freeIn` r) -> tacSUBST_ALL th g
           | (isConst r || isVar r) && not (r `freeIn` l) -> 
               tacSUBST_ALL (ruleSYM th) g
           | otherwise -> _FAIL "tacSUBST_VAR" g

-- basic logical tactics
tacDISCH :: BoolCtxt thry => Tactic cls thry
tacDISCH (Goal asl (ant :==> c)) =
    do th <- primASSUME ant
       return $! GS nullMeta [Goal (("", th):asl) c] justification1
  where justification1 :: BoolCtxt thry => Justification cls thry
        justification1 i [th] = ruleDISCH (instantiate i ant) th
        justification1 _ _      = fail "tacDISCH: improper justification"
tacDISCH (Goal asl (Neg ant)) =
    do ftm <- serve [bool| F |]
       th <- primASSUME ant
       return $! GS nullMeta [Goal (("", th):asl) ftm] justification2
  where justification2 :: BoolCtxt thry => Justification cls thry
        justification2 i [th] = 
            ruleNOT_INTRO $ ruleDISCH (instantiate i ant) th
        justification2 _ _      = fail "tacDISCH: improper justification"
tacDISCH _ = fail "tacDISCH"

tacMP :: (BoolCtxt thry, HOLThmRep thm cls thry) => ThmTactic thm cls thry
tacMP pthm (Goal asl w) =
    (do thm@(Thm _ c) <- toHThm pthm
        tm <- mkImp c w
        return . GS nullMeta [Goal asl tm] $ justification thm) <?> "tacMP"
  where justification :: BoolCtxt thry => HOLThm -> Justification cls thry
        justification thm i [th] = ruleMP th $ ruleINSTANTIATE_ALL i thm
        justification _ _ _      = fail "tacMP: improper justification"

tacEQ :: BoolCtxt thry => Tactic cls thry
tacEQ (Goal asl (l := r)) =
    (do tm1 <- mkImp l r
        tm2 <- mkImp r l
        return $! GS nullMeta [Goal asl tm1, Goal asl tm2] justification)
    <?> "tacEQ"
  where justification :: BoolCtxt thry => Justification cls thry
        justification _ [th1, th2] = ruleIMP_ANTISYM th1 th2
        justification _ _          = fail "tacEQ: improper justification"
tacEQ _ = fail "tacEQ: not an equality conclusion."

tacUNDISCH :: (BoolCtxt thry, HOLTermRep tm cls thry) => tm -> Tactic cls thry
tacUNDISCH ptm (Goal asl w) =
    do tm <- toHTm ptm
       case remove (\ (_, asm) -> concl asm `aConv` tm) asl of
         Just ((_, thm), asl') -> 
             (do tm' <- mkImp tm w
                 return . GS nullMeta [Goal asl' tm'] $ justification thm) 
             <?> "tacUNDISCH"
         Nothing -> fail "tacUNDISCH"
  where justification :: BoolCtxt thry => HOLThm -> Justification cls thry    
        justification thm i [th] = ruleMP th $ ruleINSTANTIATE_ALL i thm
        justification _ _ _      = fail "tacUNDISCH: bad justification"

tacSPEC :: (BoolCtxt thry, HOLTermRep tm1 cls thry,
            HOLTermRep tm2 cls thry) 
        => (tm1, tm2) -> Tactic cls thry
tacSPEC (pt, px) (Goal asl w) =
    (do x <- toHTm px
        t <- toHTm pt
        tm' <- mkForall x =<< subst [(t, x)] w
        return $! GS nullMeta [Goal asl tm'] $ justification t) <?> "tacSPEC"
  where justification :: BoolCtxt thry => HOLTerm -> Justification cls thry
        justification t i [th] = ruleSPEC (instantiate i t) th
        justification _ _ _    = fail "tacSPEC: bad justification"

tacX_GEN :: (BoolCtxt thry, HOLTermRep tm cls thry) => tm -> Tactic cls thry
tacX_GEN px (Goal asl w@(Forall x bod)) =
    do x' <- toHTm px
       let avoids = foldr (union . thmFrees . snd) (frees w) asl
       if x' `elem` avoids 
          then fail "tacX_GEN: variable free in goal."
          else (do bod' <- varSubst [(x, x')] bod
                   return . GS nullMeta [Goal asl bod'] $ justification x')
               <?> "tacX_GEN"
  where afn :: HOLThm -> HOL cls thry HOLThm
        afn = ruleCONV (convGEN_ALPHA x)

        justification :: BoolCtxt thry => HOLTerm -> Justification cls thry
        justification x' _ [th] = afn =<< ruleGEN x' th
        justification _ _ _     = fail "tacX_GEN: improper justification"
tacX_GEN _ _ = fail "tacX_GEN: goal not universally quantified."

tacGEN :: BoolCtxt thry => Tactic cls thry
tacGEN g@(Goal asl w@(Forall x _)) =
    let avoids = foldr (union . thmFrees . snd) (frees w) asl in
      (do x' <- mkPrimedVar avoids x
          tacX_GEN x' g)
      <?> "tacGEN"
tacGEN _ = fail "tacGEN: goal not universally quantified."

tacEXISTS :: (BoolCtxt thry, HOLTermRep tm cls thry) => tm -> Tactic cls thry
tacEXISTS ptm (Goal asl w@(Exists v bod)) =
    (do t <- toHTm ptm
        bod' <- varSubst [(v, t)] bod
        return . GS nullMeta [Goal asl bod'] $ justification t) <?> "tacEXISTS"
  where justification :: BoolCtxt thry => HOLTerm -> Justification cls thry
        justification t i [th] = 
            ruleEXISTS (instantiate i w) (instantiate i t) th
        justification _ _ _    = fail "tacEXISTS: improper justification"
tacEXISTS _ _ = fail "tacEXISTS: goal not existentially quantified."

tacX_CHOOSE :: (BoolCtxt thry, HOLTermRep tm cls thry, HOLThmRep thm cls thry) 
            => tm -> ThmTactic thm cls thry
tacX_CHOOSE ptm pthm (Goal asl w@(Exists x bod)) =
    do x' <- toHTm ptm
       xth <- toHThm pthm
       xth' <- primASSUME =<< varSubst [(x, x')] bod
       let avoids = foldr (union . frees . concl . snd) 
                          (frees w `union` thmFrees xth) asl
       if x' `elem` avoids 
          then fail "tacX_CHOOSE: provided variable is free in provided theorem"
          else return . GS nullMeta [Goal (("", xth'):asl) w] $ 
                          justification x' xth
  where justification :: BoolCtxt thry 
                      => HOLTerm -> HOLThm -> Justification cls thry
        justification x' xth i [th] = 
            do xth2 <- ruleINSTANTIATE_ALL i xth
               ruleCHOOSE x' xth2 th
        justification _ _ _ _       = fail "tacX_CHOOSE: improper justification"
tacX_CHOOSE _ _ _ = fail "tacX_CHOOSE: goal not existentially quantified."

tacCHOOSE :: (BoolCtxt thry, HOLThmRep thm cls thry) => ThmTactic thm cls thry
tacCHOOSE pth (Goal asl w@(Exists x _)) =
    (do xth <- toHThm pth
        let avoids = foldr (union . thmFrees . snd) 
                     (frees w `union` thmFrees xth) asl
        x' <- mkPrimedVar avoids x
        tacX_CHOOSE x' xth $ Goal asl w)
    <?> "tacCHOOSE"
tacCHOOSE _ _ = fail "tacCHOOSE: goal not existentially quantified."

tacCONJ :: BoolCtxt thry => Tactic cls thry
tacCONJ (Goal asl (l :/\ r)) =
    return $! GS nullMeta [Goal asl l, Goal asl r] justification
  where justification :: BoolCtxt thry => Justification cls thry
        justification _ [th1, th2] = ruleCONJ th1 th2
        justification _ _          = fail "tacCONJ: improper justification"
tacCONJ _ = fail "tacCONJ: goal not a conjunction."

tacDISJ1 :: BoolCtxt thry => Tactic cls thry
tacDISJ1 (Goal asl (l :\/ r)) =
    return $! GS nullMeta [Goal asl l] justification
  where justification :: BoolCtxt thry => Justification cls thry
        justification i [th] = ruleDISJ1 th $ instantiate i r
        justification _ _    = fail "tacDISJ1: improper justification"
tacDISJ1 _ = fail "tacDISJ1: goal not a disjunction."

tacDISJ2 :: BoolCtxt thry => Tactic cls thry
tacDISJ2 (Goal asl (l :\/ r)) =
    return $! GS nullMeta [Goal asl r] justification
    where justification :: BoolCtxt thry => Justification cls thry
          justification i [th] = ruleDISJ2 (instantiate i l) th
          justification _ _    = fail "tacDISJ2: improper justification"
tacDISJ2 _ = fail "tacDISJ2: goal not a disjunction."

tacDISJ_CASES :: (BoolCtxt thry, HOLThmRep thm cls thry) => thm 
              -> Tactic cls thry
tacDISJ_CASES pth (Goal asl w) =
    (do dth <- toHThm pth
        (lth, rth) <- pairMapM primASSUME =<< destDisj (concl dth)
        return . GS nullMeta [Goal (("", lth):asl) w, 
                              Goal (("", rth):asl) w] $ justification dth)
    <?> "tacDISJ_CASES"
  where justification :: BoolCtxt thry => HOLThm -> Justification cls thry
        justification dth i [th1, th2] = 
            do dth' <- ruleINSTANTIATE_ALL i dth
               ruleDISJ_CASES dth' th1 th2
        justification _ _ _ = fail "tacDISJ_CASES: improper justification."

tacCONTR :: (BoolCtxt thry, HOLThmRep thm cls thry) => ThmTactic thm cls thry
tacCONTR cth (Goal _ w) =
    (do th <- ruleCONTR w cth
        return . GS nullMeta [] $ propagateThm th)
    <?> "tacCONTR"

rawtac :: (BoolCtxt thry, HOLThmRep thm cls thry) => ThmTactic thm cls thry
rawtac thm (Goal _ w) =
    (do ith <- rulePART_MATCH return thm w
        return . GS nullMeta [] $ propagateThm ith)
    <?> "tacACCEPT"

tacMATCH_ACCEPT :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                => ThmTactic thm cls thry
tacMATCH_ACCEPT th = _REPEAT tacGEN `_THEN` rawtac th

tacMATCH_MP :: (BoolCtxt thry, HOLThmRep thm cls thry) => ThmTactic thm cls thry
tacMATCH_MP pth (Goal asl w) =
    (do th@(Thm _ tm) <- toHThm pth
        let (avs, bod) = stripForall tm
        (ant, con) <- destImp bod
        th1 <- ruleSPECL avs $ primASSUME tm
        th2 <- ruleUNDISCH th1
        let evs = filter (\ v -> varFreeIn v ant && not (varFreeIn v con)) avs
        th3 <- itlistM ruleSIMPLE_CHOOSE evs =<< ruleDISCH tm th2
        tm3 <- tryHead $ hyp th3
        th4 <- ruleDISCH tm . ruleGEN_ALL . ruleDISCH tm3 $ ruleUNDISCH th3
        sth <- ruleMP th4 th
        xth <- rulePART_MATCH (liftM snd . destImp) sth w
        (lant, _) <- destImp $ concl xth
        return $! GS nullMeta [Goal asl lant] (justification xth)) 
    <?> "tacMATCH_MP: no match"
  where justification :: BoolCtxt thry => HOLThm -> Justification cls thry
        justification xth i [thm] = do thm2 <- ruleINSTANTIATE_ALL i xth
                                       ruleMP thm2 thm
        justification _ _ _       = fail "tacMATCH_MP: improper justification"

-- theorem continuations
_CONJUNCTS_THEN2 :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                 => ThmTactic HOLThm cls thry -> ThmTactic HOLThm cls thry 
                 -> ThmTactic thm cls thry
_CONJUNCTS_THEN2 ttac1 ttac2 pth gl = 
    do cth <- toHThm pth
       (c1th, c2th) <- pairMapM primASSUME =<< destConj (concl cth)
       (GS ti gls jfn) <- (ttac1 c1th `_THEN` ttac2 c2th) gl
       let jfn' i ths =
               do (thm1, thm2) <- ruleCONJ_PAIR $ ruleINSTANTIATE_ALL i cth
                  thm3 <- jfn i ths
                  rulePROVE_HYP thm1 $ rulePROVE_HYP thm2 thm3
       return (GS ti gls jfn')

_CONJUNCTS_THEN :: BoolCtxt thry => ThmTactical HOLThm cls thry
_CONJUNCTS_THEN = wComb _CONJUNCTS_THEN2

_DISJ_CASES_THEN2 :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                  => ThmTactic HOLThm cls thry -> ThmTactic HOLThm cls thry 
                  -> ThmTactic thm cls thry
_DISJ_CASES_THEN2 ttac1 ttac2 cth =
  tacDISJ_CASES cth `_THENL` [_POP_ASSUM ttac1, _POP_ASSUM ttac2]

_DISJ_CASES_THEN :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                 => ThmTactic HOLThm cls thry -> ThmTactic thm cls thry
_DISJ_CASES_THEN = wComb _DISJ_CASES_THEN2

_DISCH_THEN :: BoolCtxt thry => ThmTactic HOLThm cls thry -> Tactic cls thry
_DISCH_THEN ttac = tacDISCH `_THEN` _POP_ASSUM ttac

_X_CHOOSE_THEN :: (BoolCtxt thry, HOLTermRep tm cls thry, 
                   HOLThmRep thm cls thry) 
               => tm -> ThmTactic HOLThm cls thry -> ThmTactic thm cls thry
_X_CHOOSE_THEN tm ttac thm = tacX_CHOOSE tm thm `_THEN` _POP_ASSUM ttac

_CHOOSE_THEN :: (BoolCtxt thry, HOLThmRep thm cls thry) 
             => ThmTactic HOLThm cls thry -> ThmTactic thm cls thry
_CHOOSE_THEN ttac th = tacCHOOSE th `_THEN` _POP_ASSUM ttac

-- some derived tactics
_STRIP_THM_THEN :: BoolCtxt thry => ThmTactical HOLThm cls thry
_STRIP_THM_THEN = 
    _FIRST [ _CONJUNCTS_THEN
           , _DISJ_CASES_THEN
           , _CHOOSE_THEN
           ]

_ANTE_RES_THEN :: BoolCtxt thry => ThmTactical HOLThm cls thry
_ANTE_RES_THEN ttac ante = _ASSUM_LIST $ \ asl g -> 
    do tacs <- mapFilterM (\ imp -> do th' <- ruleMATCH_MP imp ante
                                       return (ttac th')) asl
       if null tacs 
          then fail "_ANTE_RES_THEN"
          else _EVERY tacs g

tacSTRIP_ASSUME :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                => ThmTactic thm cls thry
tacSTRIP_ASSUME pthm g =
    do thm <- toHThm pthm 
       (_REPEAT _STRIP_THM_THEN
        (\ gth -> _FIRST [tacCONTR gth, tacACCEPT gth,
                          tacDISCARD gth, tacASSUME gth])) thm g
  where tacDISCARD :: ThmTactic HOLThm cls thry
        tacDISCARD thm gl@(Goal asl _) =
            let tm = concl thm in
              if any (aConv tm . concl . snd) asl
                 then _ALL gl
                 else fail "tacDISCARD: not already present."

tacSTRUCT_CASES :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                => ThmTactic thm cls thry
tacSTRUCT_CASES pthm g =
    do thm <- toHThm pthm 
       (_REPEAT _STRIP_THM_THEN 
        (\ th -> tacSUBST1 th `_ORELSE` tacASSUME th)) thm g

tacSTRIP :: BoolCtxt thry => Tactic cls thry
tacSTRIP g =
    _STRIP_GOAL_THEN tacSTRIP_ASSUME g <?> "tacSTRIP"

_STRIP_GOAL_THEN :: BoolCtxt thry 
                 => ThmTactic HOLThm cls thry -> Tactic cls thry
_STRIP_GOAL_THEN ttac = _FIRST [tacGEN, tacCONJ, _DISCH_THEN ttac]

_UNDISCH_THEN :: HOLTermRep tm cls thry 
              => tm -> ThmTactic HOLThm cls thry -> Tactic cls thry
_UNDISCH_THEN _ _ (Goal [] _) = 
    fail "_UNDISCH_THEN: goal with empty assumption list."
_UNDISCH_THEN ptm ttac (Goal asl w) = note "_UNDISCH_THEN" $
    do tm <- toHTm ptm
       (thp, asl') <- remove (\ (_, th) -> aConv (concl th) tm) asl
       ttac (snd thp) $ Goal asl' w

_FIRST_X_ASSUM :: ThmTactic HOLThm cls thry -> Tactic cls thry
_FIRST_X_ASSUM ttac = _FIRST_ASSUM (\ th -> _UNDISCH_THEN (concl th) ttac)

-- subgoaling
_SUBGOAL_THEN :: HOLTermRep tm cls thry 
              => tm -> ThmTactic HOLThm cls thry -> Tactic cls thry
_SUBGOAL_THEN ptm ttac g@(Goal asl _) =
    (do wa <- toHTm ptm 
        wath <- primASSUME wa
        (GS meta gl just) <- ttac wath g
        return (GS meta (Goal asl wa:gl) $ justification just))
    <?> "_SUBGOAL_THEN"
  where justification :: Justification cls thry -> Justification cls thry
        justification just i (l:ls) = rulePROVE_HYP l $ just i ls
        justification _ _ _ = fail "_SUBGOAL_THEN: improper justification"

-- metavariable tactics
tacX_META_EXISTS :: (BoolCtxt thry, HOLTermRep tm cls thry) 
                 => tm -> Tactic cls thry
tacX_META_EXISTS ptm (Goal asl w@(Exists v bod)) = note "tacX_META_EXISTS" $
    do t <- toHTm ptm
       bod' <- varSubst [(v, t)] bod
       return . GS ([t], nullInst) [Goal asl bod'] $ justification t
  where justification :: BoolCtxt thry => HOLTerm -> Justification cls thry 
        justification t i [th] =
            ruleEXISTS (instantiate i w) (instantiate i t) th
        justification _ _ _    = fail "tacX_META_EXISTS: improper justification"
tacX_META_EXISTS _ _ = 
    fail "tacX_META_EXISTS: goal not existentially quantified."

tacMETA_SPEC :: (BoolCtxt thry, HOLTermRep tm cls thry, HOLThmRep thm cls thry) 
             => tm -> ThmTactic thm cls thry
tacMETA_SPEC ptm pthm (Goal asl w) = note "tacMETA_SPEC" $
    do t <- toHTm ptm
       thm <- toHThm pthm
       sth <- ruleSPEC t thm
       return . GS ([t], nullInst) [Goal (("", sth):asl) w] $ 
                  justification t thm
  where justification :: BoolCtxt thry 
                      => HOLTerm -> HOLThm -> Justification cls thry
        justification t thm i [th] = 
            do thm' <- ruleSPEC (instantiate i t) thm
               rulePROVE_HYP thm' th
        justification _ _ _ _      = fail "tacMETA_SPEC: improper justification"

-- tactic proofs
mkGoalstate :: BoolCtxt thry => Goal -> HOL cls thry (GoalState cls thry)
mkGoalstate g@(Goal _ w)
    | typeOf w == tyBool = return $! GS nullMeta [g] justification
    | otherwise = fail "mkGoalstate: non-boolean goal"
  where justification :: BoolCtxt thry => Justification cls thry
        justification i [th] = ruleINSTANTIATE_ALL i th
        justification _ _    = fail "mkGoalstate: improper justification"

ruleTAC_PROOF :: BoolCtxt thry => Goal -> Tactic cls thry -> HOL cls thry HOLThm
ruleTAC_PROOF g tac = 
    do gstate <- mkGoalstate g
       (GS _ sgs just) <- by tac gstate
       if null sgs 
          then just nullInst []
          else fail "ruleTAC_PROOF: unsolved goals"

prove :: (BoolCtxt thry, HOLTermRep tm cls thry) 
      => tm -> Tactic cls thry -> HOL cls thry HOLThm
prove ptm tac = 
    do tm <- toHTm ptm
       th@(Thm _ tm') <- ruleTAC_PROOF (Goal [] tm) tac
       if tm' == tm 
          then return th
          else (primEQ_MP (ruleALPHA tm' tm) th) <?> 
                 "prove: justification generated wrong theorem."

