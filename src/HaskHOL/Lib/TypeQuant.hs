{-|
  Module:    HaskHOL.Lib.TypeQuant
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.TypeQuant
    ( TypeQuantCtxt
    , ctxtTypeQuant
    , typeQuant
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
    , convTYBETA
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Equal
import HaskHOL.Lib.Bool
import HaskHOL.Lib.DRule
import HaskHOL.Lib.Tactics
import HaskHOL.Lib.Misc

import HaskHOL.Lib.TypeQuant.Context
import HaskHOL.Lib.TypeQuant.PQ

-- Equality Rules
convALPHA_TY :: HOLType -> Conversion cls thry
convALPHA_TY v@(TyVar True _) = Conv $ \ tm ->
    (ruleALPHA tm =<< alphaTyabs v tm) <?> "convALPHA_TY"
convALPHA_TY _ = 
    _FAIL "convALPHA_TY: provided type is not a small type variable."

convGEN_ALPHA_TY :: HOLType -> Conversion cls thry
convGEN_ALPHA_TY v@(TyVar True _) = Conv $ \ tm ->
    case tm of
      TyAbs{} -> runConv (convALPHA_TY v) tm
      (Comb b ab@TyAbs{}) ->
          do abth <- runConv (convALPHA_TY v) ab
             ruleAP_TERM b abth
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
       th2 <- primTYABS ty th1
       phi <- lHand $ concl th2
       ptm <- rand =<< rand (concl pth)
       pth' <- primINST [(ptm, phi)] pth
       primEQ_MP pth' th2
  where -- proves |- P = (\\ 'x . T) <=> (!!) P
        ruleGEN_TY_pth :: TypeQuantCtxt thry => HOL cls thry HOLThm
        ruleGEN_TY_pth = cacheProof "ruleGEN_TY_pth" ctxtTypeQuant $
            do thm <- ruleCONV (convRAND convBETA) $ 
                        ruleAP_THM defTY_FORALL [txt| P: %'X . bool |]
               ruleSYM thm
ruleGEN_TY _ _ = fail "ruleGEN_TY: not a small, type variable"


-- !! 'x. t ----> t [u/'x]
ruleSPEC_TY :: (TypeQuantCtxt thry, HOLTypeRep ty cls thry, 
                HOLThmRep thm cls thry) 
            => ty -> thm -> HOL cls thry HOLThm
ruleSPEC_TY pty pthm =
    do thm <- toHThm pthm
       case concl thm of
         (Comb _ ab@TyAbs{}) ->
             do ty <- toHTy pty
                x <- mkSmall $ mkVarType "X"
                pth <- rulePINST [(x, ty)] 
                                 [(serve [typeQuant| P: % 'A. bool |], ab)] 
                                 ruleSPEC_TY_pth
                (ruleCONV convTYBETA $ ruleMP pth thm) <?> "ruleSPEC_TY"
         _ -> fail "ruleSPEC_TY: not a type abstraction"
  where -- proves |- (!!) P ==> P [: 'X]
        ruleSPEC_TY_pth :: TypeQuantCtxt thry
                        => HOL cls thry HOLThm
        ruleSPEC_TY_pth = cacheProof "ruleSPEC_TY_pth" ctxtTypeQuant $
            do th1 <- ruleAP_THM defTY_FORALL [txt| P: % 'A. bool |]
               th2 <- ruleCONV convBETA . primEQ_MP th1 $
                        primASSUME [txt| (!!)(P: % 'A. bool) |]
               th3 <- ruleCONV (convRAND convTYBETA) $ 
                        primTYAPP [txt| :'X |] th2
               ruleDISCH_ALL $ ruleEQT_ELIM th3

-- Basic boolean tactics
tacX_GEN_TY :: TypeQuantCtxt thry => HOLType -> Tactic cls thry
tacX_GEN_TY x'@(TyVar True _) (Goal asl w@(TyAll x bod))
    | x `elem` avoids = fail "tacX_GEN_TY: provided type is free in goal"
    | otherwise =
        (let afn = ruleCONV (convGEN_ALPHA_TY x)
             bod' = inst [(x, x')] bod in
           return . GS nullMeta [Goal asl bod'] $ justification afn)
        <?> "tacX_GEN_TY"
  where avoids :: [HOLType]
        avoids = foldr (union . typeVarsInThm . snd) (typeVarsInTerm w) asl

        justification :: TypeQuantCtxt thry => (HOLThm -> HOL cls thry HOLThm) 
                      -> Justification cls thry
        justification afn _ [th] = afn =<< ruleGEN_TY x' th
        justification _ _ _ = fail "tacX_GEN_TY: improper justification"
tacX_GEN_TY _ _ = 
    fail "tacX_GEN_TY: goal not universally quantified over a type."

tacGEN_TY :: TypeQuantCtxt thry => Tactic cls thry
tacGEN_TY g@(Goal asl w@(TyAll x _)) =
    let avoids = foldr (union . typeVarsInThm . snd) (typeVarsInTerm w) asl
        x' = variantTyVar avoids x in
      tacX_GEN_TY x' g
tacGEN_TY _ =
    fail "tacGEN_TY: goal not universally quantified over a type."

-- More advanced elimination tactics

tacUTYPE_E :: BoolCtxt thry => HOLType -> Tactic cls thry
tacUTYPE_E ty = tacASSUM_REWRITE (ruleTYBETA . primTYAPP ty)

tacTYABS_E :: BoolCtxt thry => Tactic cls thry
tacTYABS_E = tacASSUM_REWRITE $ \ thm -> 
    do (l, _) <- destEq $ concl thm
       (tv, _) <- destUType $ typeOf l
       ruleTYBETA $ primTYAPP tv thm

tacTYALL_ELIM :: TypeQuantCtxt thry => HOLType -> Tactic cls thry
tacTYALL_ELIM ty = tacASSUM_REWRITE (ruleSPEC_TY ty)

tacTYALL_E :: TypeQuantCtxt thry => Tactic cls thry
tacTYALL_E = tacASSUM_REWRITE $ \ thm -> 
    do tv <- liftM fst . destTyAll $ concl thm
       ruleSPEC_TY tv thm

tacTYABS :: Tactic cls thry
tacTYABS (Goal asl w@(TyAbs ltv lb := TyAbs rtv rb)) =
    let avoids = foldr (union . typeVarsInThm . snd) (typeVarsInTerm w) asl
        tv = variantTyVar avoids ltv
        lb' = inst [(ltv, tv)] lb
        rb' = inst [(rtv, tv)] rb in
      do w' <- mkEq lb' rb'
         return . GS nullMeta [Goal asl w'] $ justification tv
  where justification :: HOLType -> Justification cls thry
        justification tv i [thm] =
            do ath <- primTYABS tv thm
               bth <- ruleALPHA (concl ath) (instantiate i w)
               primEQ_MP bth ath
        justification _ _ _ = fail "tacTYABS: bad justification."
tacTYABS _ = fail "tacTYABS: not an equation of type abstractions."
