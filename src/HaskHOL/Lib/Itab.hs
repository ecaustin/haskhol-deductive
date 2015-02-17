{-|
  Module:    HaskHOL.Lib.Itab
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Itab
    ( tacITAUT
    , ruleITAUT
    ) where

import HaskHOL.Core
import HaskHOL.Lib.Bool
import HaskHOL.Lib.Equal
import HaskHOL.Lib.DRule
import HaskHOL.Lib.Tactics


tacUnifyAccept :: [HOLTerm] -> ThmTactic cls thry
tacUnifyAccept mvs th (Goal _ w) =
    do insts <- liftO $ termUnify mvs (concl th) w
       return (GS ([], insts) []
               (\ i _ -> do th' <- ruleINSTANTIATE insts th
                            ruleINSTANTIATE i th'))

conjunctsThen' :: BoolCtxt thry => ThmTactic cls thry -> ThmTactic cls thry
conjunctsThen' ttac cth g =
  do th1 <- ruleCONJUNCT1 cth
     th2 <- ruleCONJUNCT2 cth
     (ttac th1 `_THEN` ttac th2) g

rIMPLICATE :: BoolCtxt thry => HOLTerm -> HOL cls thry HOLThm
rIMPLICATE t = 
    case destNeg t of
      Just t' -> do dNot <- defNOT
                    ruleCONV (convRAND convBETA) #<< ruleAP_THM dNot t'
      _ -> fail "rIMPLICATE"

tacRightReversible :: BoolCtxt thry => Tactic cls thry
tacRightReversible = 
    _FIRST [ tacCONJ
           , tacGEN
           , tacDISCH
           , \ gl@(Goal _ w) -> tacCONV (Conv $ \ _ -> rIMPLICATE w) gl
           , tacEQ
           ]

tacLeftReversible :: BoolCtxt thry => ThmTactic cls thry
tacLeftReversible th gl =
  tryFind (\ ttac -> ttac th gl)
    [ conjunctsThen' tacASSUME
    , tacDISJ_CASES
    , tacCHOOSE
    , \ thm g -> do thm' <- rIMPLICATE (concl thm)
                    tacASSUME (fromRight $ primEQ_MP thm' thm) g
    , \ thm g -> do thm' <- uncurry ruleCONJ =<< ruleEQ_IMP thm
                    conjunctsThen' tacMP thm' g
    ] 


itautTac :: BoolCtxt thry => [HOLTerm] -> Int -> Tactic cls thry
itautTac mvs n gl
    | n <= 0 = _FAIL "tITAUT_TAC: too deep" gl
    | otherwise =
        (_FIRST_ASSUM (tacUnifyAccept mvs) `_ORELSE`
         tacACCEPT thmTRUTH `_ORELSE`
         _FIRST_ASSUM tacCONTR `_ORELSE`
         (tacRightReversible `_THEN` _TRY (itautTac mvs n)) `_ORELSE`
         (_FIRST_X_ASSUM tacLeftReversible `_THEN` _TRY (itautTac mvs n)) `_ORELSE`
         _FIRST_X_ASSUM (\ th -> tacASSUME th `_THEN`
                        (\ g -> case destForall $ concl th of
                                  Just (v, _) -> do gv <- genVar $ typeOf v
                                                    (tacMETA_SPEC gv th `_THEN` 
                                                     itautTac (gv:mvs) (n-2) `_THEN`
                                                     _NO) g
                                  _ -> fail "")) `_ORELSE`
         (tacDISJ1 `_THEN` itautTac mvs n `_THEN` _NO) `_ORELSE`
         (tacDISJ2 `_THEN` itautTac mvs n `_THEN` _NO) `_ORELSE`
         (\ gl2@(Goal _ w) -> case destExists w of
                                Just (v, _) ->  do gv <- genVar $ typeOf v
                                                   (tacX_META_EXISTS gv `_THEN`
                                                    itautTac (gv:mvs) (n-2) `_THEN` 
                                                    _NO) gl2
                                _ -> fail "") `_ORELSE`
         _FIRST_ASSUM (\ th g -> case destImp $ concl th of
                                   Just (v, _) -> 
                                       (_SUBGOAL_THEN v (\ ath g2 -> do th' <- ruleMP th ath
                                                                        tacASSUME th' g2) `_THEN`
                                        itautTac mvs (n-1) `_THEN` 
                                        _NO) g
                                   _ -> _NO g)) gl

itautIterdeepTac :: BoolCtxt thry => Int -> Tactic cls thry
itautIterdeepTac n gl =
  printDebugLn ("searching with limit: " ++ show n) $
  ((itautTac [] n `_THEN` _NO) `_ORELSE` itautIterdeepTac (n+1)) gl

tacITAUT :: BoolCtxt thry => Tactic cls thry
tacITAUT = itautIterdeepTac 0

ruleITAUT' :: BoolCtxt thry => HOLTerm -> HOL cls thry HOLThm
ruleITAUT' tm = prove tm tacITAUT

ruleITAUT :: (HOLTermRep tm cls thry, BoolCtxt thry) => tm 
          -> HOL cls thry HOLThm
ruleITAUT = ruleITAUT' <=< toHTm
