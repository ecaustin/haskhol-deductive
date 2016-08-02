{-|
  Module:    HaskHOL.Lib.Itab
  Copyright: (c) Evan Austin 2015
  LICENSE:   BSD3

  Maintainer:  e.c.austin@gmail.com
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Itab
    ( tacITAUT
    , ruleITAUT
    , tacITAUT_PRIM
    , tacUNIFY_ACCEPT
    , tacRIGHT_REVERSIBLE
    ) where

import HaskHOL.Core
import HaskHOL.Lib.Bool
import HaskHOL.Lib.Equal
import HaskHOL.Lib.DRule
import HaskHOL.Lib.Tactics


tacUNIFY_ACCEPT :: [HOLTerm] -> ThmTactic HOLThm cls thry
tacUNIFY_ACCEPT mvs th (Goal _ w) =
    do insts <- termUnify mvs (concl th) w
       return (GS ([], insts) []
               (\ i _ -> do th' <- ruleINSTANTIATE insts th
                            ruleINSTANTIATE i th'))

_CONJUNCTS_THEN' :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                 => ThmTactic HOLThm cls thry -> thm -> Tactic cls thry
_CONJUNCTS_THEN' ttac cth g =
  do th1 <- ruleCONJUNCT1 cth
     th2 <- ruleCONJUNCT2 cth
     (ttac th1 `_THEN` ttac th2) g

ruleIMPLICATE :: BoolCtxt thry => HOLTerm -> HOL cls thry HOLThm
ruleIMPLICATE (Neg t') = 
    ruleCONV (convRAND convBETA) $ ruleAP_THM defNOT t'
ruleIMPLICATE _ = throwM $! HOLExhaustiveWarning "ruleIMPLICATE"

tacRIGHT_REVERSIBLE :: BoolCtxt thry => Tactic cls thry
tacRIGHT_REVERSIBLE = 
    _FIRST [ tacCONJ
           , tacGEN
           , tacDISCH
           , \ gl@(Goal _ w) -> tacCONV (Conv $ \ _ -> ruleIMPLICATE w) gl
           , tacEQ
           ]

tacLEFT_REVERSIBLE :: BoolCtxt thry => ThmTactic HOLThm cls thry
tacLEFT_REVERSIBLE th gl =
  tryFind (\ ttac -> ttac th gl)
    [ _CONJUNCTS_THEN' tacASSUME
    , tacDISJ_CASES
    , tacCHOOSE
    , \ thm -> tacASSUME $ primEQ_MP (ruleIMPLICATE $ concl thm) thm
    , _CONJUNCTS_THEN' tacMP . (uncurry ruleCONJ <=< ruleEQ_IMP)
    ] 


tacITAUT_PRIM :: BoolCtxt thry => [HOLTerm] -> Int -> Tactic cls thry
tacITAUT_PRIM mvs n gl
    | n <= 0 = fail "tacITAUT: too deep"
    | otherwise =
        (_FIRST_ASSUM (tacUNIFY_ACCEPT mvs) `_ORELSE`
         tacACCEPT thmTRUTH `_ORELSE`
         _FIRST_ASSUM tacCONTR `_ORELSE`
         (tacRIGHT_REVERSIBLE `_THEN` _TRY (tacITAUT_PRIM mvs n)) `_ORELSE`
         (_FIRST_X_ASSUM tacLEFT_REVERSIBLE `_THEN` 
          _TRY (tacITAUT_PRIM mvs n)) `_ORELSE`
         _FIRST_X_ASSUM (\ th -> tacASSUME th `_THEN`
                        (\ g -> let (Forall v _) = concl th in
                                  do gv <- genVar $ typeOf v
                                     (tacMETA_SPEC gv th `_THEN`
                                      tacITAUT_PRIM (gv:mvs) (n-2) `_THEN`
                                      _NO) g)) `_ORELSE`
         (tacDISJ1 `_THEN` tacITAUT_PRIM mvs n `_THEN` _NO) `_ORELSE`
         (tacDISJ2 `_THEN` tacITAUT_PRIM mvs n `_THEN` _NO) `_ORELSE`
         (\ gl2@(Goal _ w) -> let (Exists v _) = w in
                                do gv <- genVar $ typeOf v
                                   (tacX_META_EXISTS gv `_THEN`
                                    tacITAUT_PRIM (gv:mvs) (n-2) `_THEN` 
                                    _NO) gl2) `_ORELSE`
         _FIRST_ASSUM (\ th -> let (v :==> _) = concl th in 
                                 (_SUBGOAL_THEN v 
                                   (tacASSUME . ruleMP th) `_THEN`
                                  tacITAUT_PRIM mvs (n-1) `_THEN` 
                                  _NO))) gl

tacITAUT :: BoolCtxt thry => Tactic cls thry
tacITAUT = tacITAUT_ITERDEEP 0
  where tacITAUT_ITERDEEP :: BoolCtxt thry => Int -> Tactic cls thry
        tacITAUT_ITERDEEP n gl =
            printDebugLn ("searching with limit: " ++ show n) $
              ((tacITAUT_PRIM [] n `_THEN` _NO) `_ORELSE` 
               tacITAUT_ITERDEEP (n+1)) gl

ruleITAUT :: (HOLTermRep tm cls thry, BoolCtxt thry) => tm 
          -> HOL cls thry HOLThm
ruleITAUT tm = prove tm tacITAUT
