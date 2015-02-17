{-# LANGUAGE PatternSynonyms #-}
module HaskHOL.Lib.Classic.C.Base where

import HaskHOL.Core

import HaskHOL.Lib.Equal
import HaskHOL.Lib.Bool
import HaskHOL.Lib.Itab
import HaskHOL.Lib.Tactics
import HaskHOL.Lib.Simp

import HaskHOL.Lib.Classic.B

-- derive excluded middle (proof from Beeson's book)
thmEXCLUDED_MIDDLE1 :: ClassicBCtxt thry => HOL cls thry HOLThm
thmEXCLUDED_MIDDLE1 = cacheProof "thmEXCLUDED_MIDDLE1" ctxtClassicB $
    ruleITAUT "~(T <=> F)"

thmEXCLUDED_MIDDLE2 :: ClassicBCtxt thry => HOL cls thry HOLThm
thmEXCLUDED_MIDDLE2 = cacheProof "thmEXCLUDED_MIDDLE2" ctxtClassicB $
    ruleITAUT [str| p \/ T <=> T |]

thmEXCLUDED_MIDDLE :: (BasicConvs thry, ClassicBCtxt thry)
                   => HOL cls thry HOLThm
thmEXCLUDED_MIDDLE = cacheProof "thmEXCLUDED_MIDDLE" ctxtClassicB $
    prove [str| !t. t \/ ~t |] $
      tacGEN `_THEN` 
      _SUBGOAL_THEN [str| (((@x. (x <=> F) \/ t) <=> F) \/ t) /\ 
                          (((@x. (x <=> T) \/ t) <=> T) \/ t) |]
      tacMP `_THENL`
      [ tacCONJ `_THEN` 
        tacCONV convSELECT `_THENL` 
        [ tacEXISTS "F"
        , tacEXISTS "T"
        ] `_THEN` 
        tacDISJ1 `_THEN` tacREFL
      , _DISCH_THEN (\ th g -> do th' <- ruleGSYM th
                                  tacSTRIP_ASSUME th' g) `_THEN`
        _TRY (tacDISJ1 `_THEN` _FIRST_ASSUM tacACCEPT) `_THEN`
        tacDISJ2 `_THEN` 
        tacDISCH `_THEN` 
        tacMP thmEXCLUDED_MIDDLE1 `_THEN`
        tacPURE_ONCE_ASM_REWRITE [] `_THEN`
        tacASM_REWRITE [thmEXCLUDED_MIDDLE2]
      ]
             

-- basic selection operator rule
ruleSELECT :: (BasicConvs thry, ClassicBCtxt thry, HOLThmRep thm cls thry) 
           => thm -> HOL cls thry HOLThm
ruleSELECT pthm = 
    do p <- serve [classicB| P:A->bool |]
       th <- toHThm pthm
       pth <- ruleSELECT_pth
       case rand $ concl th of
         Just lam@(Abs (Var _ ty) _) -> 
             ruleCONV convBETA =<< 
               ruleMP (fromJust $ rulePINST [(tyA, ty)] [(p, lam)] pth) th
         _ -> fail "ruleSELECT"
  where ruleSELECT_pth :: (BasicConvs thry, ClassicBCtxt thry) 
                       => HOL cls thry HOLThm
        ruleSELECT_pth = cacheProof "ruleSELECT_pth" ctxtClassicB $
            prove "(?) (P:A->bool) ==> P((@) P)" $
              tacSIMP [axSELECT, axETA]

thmBOOL_CASES_AX :: (BasicConvs thry, ClassicBCtxt thry) => HOL cls thry HOLThm
thmBOOL_CASES_AX = cacheProof "thmBOOL_CASES_AX" ctxtClassicB $
    prove [str| !t. (t <=> T) \/ (t <=> F) |] $
      tacGEN `_THEN` 
      tacDISJ_CASES (ruleSPEC "t:bool" thmEXCLUDED_MIDDLE) `_THEN` 
      tacASM_REWRITE_NIL

-- classically based tactics
tacBOOL_CASES' :: (BasicConvs thry, ClassicBCtxt thry) => HOLTerm 
               -> Tactic cls thry
tacBOOL_CASES' p g = 
    do th <- ruleSPEC p thmBOOL_CASES_AX
       tacSTRUCT_CASES th g

tacBOOL_CASES :: (BasicConvs thry, ClassicBCtxt thry, HOLTermRep tm cls thry) 
              => tm -> Tactic cls thry
tacBOOL_CASES p = liftM1 tacBOOL_CASES' (toHTm p)

tacASM_CASES :: (BasicConvs thry, ClassicBCtxt thry, HOLTermRep tm cls thry) 
             => tm -> Tactic cls thry
tacASM_CASES t g = 
    do th <- ruleSPEC t thmEXCLUDED_MIDDLE
       tacDISJ_CASES th g

-- tautology checker for classical logic

-- depends on ordering of terms as prepared by findTerms, probably not good
rtaut_tac :: (BasicConvs thry, ClassicBCtxt thry) => Tactic cls thry
rtaut_tac g@(Goal _ w) = 
    let ok t = typeOf t == tyBool && isJust (findTerm isVar t) && t `freeIn` w
        tac gl = do tm <- liftMaybe "rtaut_tac" . tryHead . sort freeIn $ 
                            findTerms ok w
                    tacBOOL_CASES tm gl in

      (tacREWRITE_NIL `_THEN`
       (tacREWRITE_NIL `_THEN` tac)) g

tTAUT_TAC :: (BasicConvs thry, ClassicBCtxt thry) => Tactic cls thry
tTAUT_TAC = _REPEAT (tacGEN `_ORELSE` tacCONJ) `_THEN` _REPEAT rtaut_tac

ruleTAUT' :: (BasicConvs thry, ClassicBCtxt thry) => HOLTerm 
          -> HOL cls thry HOLThm
ruleTAUT' tm = prove tm tTAUT_TAC

ruleTAUT :: (BasicConvs thry, HOLTermRep tm cls thry, ClassicBCtxt thry) => tm 
         -> HOL cls thry HOLThm
ruleTAUT = ruleTAUT' <=< toHTm

thmNOT_CLAUSES :: (BasicConvs thry, ClassicBCtxt thry) => HOL cls thry HOLThm
thmNOT_CLAUSES = cacheProof "thmNOT_CLAUSES" ctxtClassicB $
    ruleTAUT [str| (!t. ~ ~t <=> t) /\ (~T <=> F) /\ (~F <=> T) |]

thmNOT_IMP :: (BasicConvs thry, ClassicBCtxt thry) => HOL cls thry HOLThm
thmNOT_IMP = cacheProof "thmNOT_IMP" ctxtClassicB $
    ruleTAUT [str| !t1 t2. ~(t1 ==> t2) <=> t1 /\ ~t2 |]

thmCOND_CLAUSES :: (BasicConvs thry, ClassicBCtxt thry) => HOL cls thry HOLThm
thmCOND_CLAUSES = cacheProof "thmCOND_CLAUSES" ctxtClassicB $
    prove [str| !(t1:A) t2. ((if T then t1 else t2) = t1) /\ 
                            ((if F then t1 else t2) = t2) |] $
      tacREWRITE [defCOND]
