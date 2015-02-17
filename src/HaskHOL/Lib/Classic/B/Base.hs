{-# LANGUAGE PatternSynonyms #-}
module HaskHOL.Lib.Classic.B.Base where

import HaskHOL.Core

import HaskHOL.Lib.Equal
import HaskHOL.Lib.DRule
import HaskHOL.Lib.Bool
import HaskHOL.Lib.Tactics
import HaskHOL.Lib.Simp 

import HaskHOL.Lib.Classic.A

-- guarded definitions from classicA
-- | @!t:A->B. (\x. t x) = t@
axETA :: ClassicACtxt thry => HOL cls thry HOLThm
axETA = cacheProof "axETA" ctxtClassicA $ getAxiom "axETA"

-- | @!P (x:A). P x ==> P((@) P)@
axSELECT :: ClassicACtxt thry => HOL cls thry HOLThm
axSELECT = cacheProof "axSELECT" ctxtClassicA $ getAxiom "axSELECT"

-- | @COND = \t t1 t2. @x:A. ((t <=> T) ==> (x = t1)) /\ ((t <=> F) ==> (x = t2))@
defCOND :: ClassicACtxt thry => HOL cls thry HOLThm
defCOND = cacheProof "defCOND" ctxtClassicA $ getDefinition "COND"

-- bootstrapping selection
thmEQ_EXT :: (BasicConvs thry, ClassicACtxt thry) => HOL cls thry HOLThm
thmEQ_EXT = cacheProof "thmEQ_EXT" ctxtClassicA $
    do x <- toHTm "x:A" 
       prove "!(f:A->B) g. (!x. f x = g x) ==> f = g" $
         _REPEAT tacGEN `_THEN`
         _DISCH_THEN (\ th g -> do th' <- ruleSPEC x th
                                   th'' <- fromRightM $ primABS x th'
                                   tacMP th'' g) `_THEN`
         tacREWRITE [axETA]

thmEXISTS :: (BasicConvs thry, ClassicACtxt thry) => HOL cls thry HOLThm
thmEXISTS = cacheProof "thmEXISTS" ctxtClassicA $
    prove [str| (?) = \P:A->bool. P ((@) P) |] $
      tacMATCH_MP thmEQ_EXT `_THEN`
      tacBETA `_THEN`
      tacX_GEN "P:A->bool" `_THEN`
      tacGEN_REWRITE (convLAND . convRAND) [ruleGSYM axETA] `_THEN`
      tacEQ `_THENL`
      [ _DISCH_THEN (_CHOOSE_THEN tacMP) `_THEN`
        tacMATCH_ACCEPT axSELECT
      , tacDISCH `_THEN` tacEXISTS "((@) P):A" `_THEN`
        _POP_ASSUM tacACCEPT
      ]

-- basic selection conversions
convSELECT :: (BasicConvs thry, ClassicACtxt thry) => Conversion cls thry
convSELECT = Conv $ \ tm ->
    do p <- serve [classicA| P:A->bool |]
       pth <- convSELECT_pth
       case findTerm (is_epsok tm) tm of
         Just (Comb _ lam@(Abs (Var _ ty) _)) -> 
             ruleCONV (convLAND convBETA) #<< 
               rulePINST [(tyA, ty)] [(p, lam)] pth
         _ -> do stm <- showHOL tm
                 fail $ "cSELECT_CONV: " ++ stm
    where is_epsok tm t 
              | isBinder "@" t = 
                    case destBinder "@" t of
                      Just (bv, bod) -> aConv tm . fromJust $ 
                                          varSubst [(bv, t)] bod
                      _ -> False
              | otherwise = False
  
          convSELECT_pth :: (BasicConvs thry, ClassicACtxt thry) 
                         => HOL cls thry HOLThm
          convSELECT_pth = cacheProof "convSELECT_pth" ctxtClassicA $
              prove "(P:A->bool)((@)P) = (?) P" $
                tacREWRITE [thmEXISTS] `_THEN`
                tacBETA `_THEN`
                tacREFL

thmSELECT_REFL :: (BasicConvs thry, ClassicACtxt thry) => HOL cls thry HOLThm
thmSELECT_REFL = cacheProof "thmSELECT_REFL" ctxtClassicA $
    prove "!x:A. (@y. y = x) = x" $
      tacGEN `_THEN` 
      tacCONV convSELECT `_THEN`
      tacEXISTS "x:A" `_THEN`
      tacREFL
    
