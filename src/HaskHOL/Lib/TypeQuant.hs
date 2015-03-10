{-# LANGUAGE PatternSynonyms #-}
{-|
  Module:    HaskHOL.Lib.TypeQuant
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.TypeQuant
    ( TypeQuantType
    , TypeQuantThry
    , TypeQuantCtxt
    , ctxtTypeQuant
    , convALPHA_TY
    , convGEN_ALPHA_TY
    , ruleGEN_TY
    , ruleSPEC_TY
    , tacX_GEN_TY
    , tacGEN_TY
    , tacTYABS
    , tacUTYPE_E
    , tacTYABS_E
    , tacTYALL_ELIM
    , tacTYALL_E
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Equal
import HaskHOL.Lib.Bool
import HaskHOL.Lib.DRule
import HaskHOL.Lib.Tactics
import HaskHOL.Lib.Misc

import HaskHOL.Lib.TypeQuant.Context

-- Equality Rules
convALPHA_TY :: HOLType -> Conversion cls thry
convALPHA_TY v@(TyVar True _) = Conv $ \ tm ->
    fromRightM (ruleALPHA tm =<< alphaTyabs v tm) <?> "convALPHA_TY"
convALPHA_TY _ = 
    _FAIL "convALPHA_TY: provided type is not a small type variable."

convGEN_ALPHA_TY :: HOLType -> Conversion cls thry
convGEN_ALPHA_TY v@(TyVar True _) = Conv $ \ tm ->
    case tm of
      TyAbs{} -> runConv (convALPHA_TY v) tm
      (Comb b ab@TyAbs{}) ->
          do abth <- runConv (convALPHA_TY v) ab
             fromRightM $ ruleAP_TERM b abth
      _ -> fail "convGEN_ALPHA_TY"
convGEN_ALPHA_TY _ =
    _FAIL "convGEN_ALPHA_TY: provided type not a small type variable."

-- Boolean Logic Rules
{-|@
   A |- t  
------------ given 'x
 A |- !! 'x. t
@-}
ruleGEN_TY :: TypeQuantCtxt thry => HOLType -> HOLThm -> HOL cls thry HOLThm
ruleGEN_TY ty@(TyVar True _) th =
    do pth <- ruleGEN_TY_pth
       th1 <- ruleEQT_INTRO th
       liftO $ do th2 <- primTYABS ty th1
                  phi <- note "" . lHand $ concl th2
                  ptm <- note "" $ rand =<< rand (concl pth)
                  pth' <- note "" $ primINST [(ptm, phi)] pth
                  primEQ_MP pth' th2
  where -- proves |- P = (\\ 'x . T) <=> (!!) P
        ruleGEN_TY_pth :: TypeQuantCtxt thry => HOL cls thry HOLThm
        ruleGEN_TY_pth = cacheProof "ruleGEN_TY_pth" ctxtTypeQuant $
            do p <- toHTm "P: %'X . bool"
               dTyForall <- defTY_FORALL
               thm <- ruleCONV (convRAND convBETA) #<< ruleAP_THM dTyForall p
               liftO $ ruleSYM thm
ruleGEN_TY _ _ = fail "ruleGEN_TY: not a small, type variable"


-- !! 'x. t ----> t [u/'x]
ruleSPEC_TY :: TypeQuantCtxt thry => HOLType -> HOLThm 
            -> HOL cls thry HOLThm
ruleSPEC_TY ty thm =
    do p <- toHTm "P: % 'A. bool"
       x <- toHTy "'X"
       pth <- ruleSPEC_TY_pth
       case rand $ concl thm of
         Just ab@TyAbs{} ->
             (ruleCONV convTYBETA =<< 
                ruleMP (fromJust $ rulePINST [(x, ty)] [(p, ab)] pth) thm) <?> "ruleSPEC_TY"
         _ -> fail "ruleSPEC_TY: not a type abstraction"
  where -- proves |- (!!) P ==> P [: 'X]
        ruleSPEC_TY_pth :: TypeQuantCtxt thry
                        => HOL cls thry HOLThm
        ruleSPEC_TY_pth = cacheProof "ruleSPEC_TY_pth" ctxtTypeQuant $
            do p <- toHTm "P: % 'A. bool"
               x <- toHTy "'X"
               tyForallP <- toHTm "(!!)(P: % 'A. bool)"
               dTyForall <- defTY_FORALL
               let th1 = fromRight $ ruleAP_THM dTyForall p
               th2 <- ruleCONV convBETA #<< 
                        primEQ_MP th1 =<< primASSUME tyForallP
               th3 <- ruleCONV (convRAND convTYBETA) #<< primTYAPP x th2
               ruleDISCH_ALL =<< ruleEQT_ELIM th3

-- Basic boolean tactics
tacX_GEN_TY :: TypeQuantCtxt thry => HOLType -> Tactic cls thry
tacX_GEN_TY x'@(TyVar True _) (Goal asl w) =
    do (x, bod) <- liftMaybe "tacX_GEN_TY: not a tyforall" $ destTyAll w
       let avoids = foldr (union . typeVarsInThm . snd) (typeVarsInTerm w) asl
       if x' `elem` avoids 
          then fail "tacX_GEN_TY: provided type is free in goal"
          else (let afn = ruleCONV (convGEN_ALPHA_TY x)
                    bod' = inst [(x, x')] bod in
                  return . GS nullMeta [Goal asl bod'] $ justification afn)
               <?> "tacX_GEN_TY"
  where justification afn _ [th] = afn =<< ruleGEN_TY x' th
        justification _ _ _ = fail "tacX_GEN_TY: improper justification"
tacX_GEN_TY _ _ = 
    fail "tacX_GEN_TY: provided type is not a small type variable."

tacGEN_TY :: TypeQuantCtxt thry => Tactic cls thry
tacGEN_TY g@(Goal asl w) =
    do (x, _) <- liftMaybe "tacGEN_TY: not a tyforall" $ destTyAll w
       let avoids = foldr (union . typeVarsInThm . snd) (typeVarsInTerm w) asl
           x' = variantTyVar avoids x
       tacX_GEN_TY x' g

-- More advanced elimination tactics

tacUTYPE_E :: BoolCtxt thry => HOLType -> Tactic cls thry
tacUTYPE_E ty = tacASSUM_REWRITE (ruleTYBETA <#< primTYAPP ty)

tacTYABS_E :: BoolCtxt thry => Tactic cls thry
tacTYABS_E = tacASSUM_REWRITE $ \ thm -> 
    do tv <- liftMaybe ("tacTYABS_E: assumption not an equation of " ++ 
                        "universal type") $ do (l, _) <- destEq $ concl thm
                                               (tv, _) <- destUType $ typeOf l
                                               return tv
       ruleTYBETA #<< primTYAPP tv thm

tacTYALL_ELIM :: TypeQuantCtxt thry => HOLType 
              -> Tactic cls thry
tacTYALL_ELIM ty = tacASSUM_REWRITE (ruleSPEC_TY ty)

tacTYALL_E :: TypeQuantCtxt thry => Tactic cls thry
tacTYALL_E = tacASSUM_REWRITE $ \ thm -> 
    do tv <- liftMaybe ("tacTYALL_E: assumption does not have a universally " ++
                        "quantified type") . liftM fst . destTyAll $ concl thm
       ruleSPEC_TY tv thm

tacTYABS :: Tactic cls thry
tacTYABS (Goal asl w@(TyAbs ltv lb := TyAbs rtv rb)) =
    let lb' = inst [(ltv, tv)] lb
        rb' = inst [(rtv, tv)] rb in
      do w' <- mkEq lb' rb'
         return $! GS nullMeta [Goal asl w'] justification
  where avoids = foldr (union . typeVarsInThm . snd) (typeVarsInTerm w) asl
        tv = variantTyVar avoids ltv
        justification i [thm] =liftO $ 
            do ath <- primTYABS tv thm
               bth <- ruleALPHA (concl ath) (instantiate i w)
               primEQ_MP bth ath
        justification _ _ = fail "tacTYABS: bad justification."
tacTYABS _ = fail "tacTYABS: not an equation of type abstractions."
