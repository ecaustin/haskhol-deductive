module HaskHOL.Lib.Classic.Base where

import HaskHOL.Core

import HaskHOL.Lib.Bool
import HaskHOL.Lib.DRule
import HaskHOL.Lib.Equal
import HaskHOL.Lib.Itab
import HaskHOL.Lib.Tactics
import HaskHOL.Lib.Simp

tmPred :: BoolCtxt thry => HOL cls thry HOLTerm
tmPred = serve [bool| P:A->bool |]

-- Stage 1
axETA :: HOL cls thry HOLThm
axETA = unsafeCacheProof "axETA" $ getAxiom "axETA"

axSELECT :: HOL cls thry HOLThm
axSELECT = unsafeCacheProof "axSELECT" $ getAxiom "axSELECT"

defCOND :: HOL cls thry HOLThm
defCOND = unsafeCacheProof "defCOND" $ getDefinition "COND"

-- Stage 2
thmEQ_EXT :: BoolCtxt thry => HOL cls thry HOLThm
thmEQ_EXT = unsafeCacheProof "thmEQ_EXT" .
    prove [txt| !(f:A->B) g. (!x. f x = g x) ==> f = g |] $
      _REPEAT tacGEN `_THEN`
      _DISCH_THEN (tacMP . primABS [txt| x:A |] . ruleSPEC [txt| x:A |]) `_THEN`
      tacREWRITE [axETA]

thmEXISTS :: BoolCtxt thry => HOL cls thry HOLThm
thmEXISTS = unsafeCacheProof "thmEXISTS" .
    prove [txt| (?) = \P:A->bool. P ((@) P) |] $
      tacMATCH_MP thmEQ_EXT `_THEN`
      tacBETA `_THEN`
      tacX_GEN [txt| P:A->bool |] `_THEN`
      tacGEN_REWRITE (convLAND . convRAND) [ruleGSYM axETA] `_THEN`
      tacEQ `_THENL`
      [ _DISCH_THEN (_CHOOSE_THEN tacMP) `_THEN`
        tacMATCH_ACCEPT axSELECT
      , tacDISCH `_THEN` tacEXISTS [txt| ((@) P):A |] `_THEN`
        _POP_ASSUM tacACCEPT
      ]

convSELECT :: BoolCtxt thry => Conversion cls thry
convSELECT = Conv $ \ tm -> note "convSELECT" $
    case runCatch $ findTerm (isEpsOK tm) tm of
      Right (Comb _ lam@(Abs (Var _ ty) _)) -> 
        ruleCONV (convLAND convBETA) $
          rulePINST [(tyA, ty)] [(tmPred, lam)] convSELECT_pth
      _ -> fail "not a selection."
  where isEpsOK :: HOLTerm -> HOLTerm -> Bool        
        isEpsOK tm t 
            | isBinder "@" t = 
                  case runCatch $ do (bv, bod) <- destBinder "@" t
                                     varSubst [(bv, t)] bod of
                    Right tm' -> tm `aConv` tm'
                    _ -> False
            | otherwise = False

        convSELECT_pth :: BoolCtxt thry => HOL cls thry HOLThm
        convSELECT_pth = unsafeCacheProof "convSELECT_pth" .
            prove [txt| (P:A->bool)((@)P) = (?) P |] $
              tacREWRITE [thmEXISTS] `_THEN`
              tacBETA `_THEN`
              tacREFL
  
thmSELECT_REFL :: BoolCtxt thry => HOL cls thry HOLThm
thmSELECT_REFL = unsafeCacheProof "thmSELECT_REFL" .
    prove [txt| !x:A. (@y. y = x) = x |] $
      tacGEN `_THEN` 
      tacCONV convSELECT `_THEN`
      tacEXISTS [txt| x:A |] `_THEN`
      tacREFL

thmEXCLUDED_MIDDLE :: BoolCtxt thry => HOL cls thry HOLThm
thmEXCLUDED_MIDDLE = unsafeCacheProof "thmEXCLUDED_MIDDLE" .
    prove [txt| !t. t \/ ~t |] $
      tacGEN `_THEN` 
      _SUBGOAL_THEN [txt| (((@x. (x <=> F) \/ t) <=> F) \/ t) /\ 
                          (((@x. (x <=> T) \/ t) <=> T) \/ t) |]
      tacMP `_THENL`
      [ tacCONJ `_THEN` 
        tacCONV convSELECT `_THENL` 
        [ tacEXISTS [txt| F |]
        , tacEXISTS [txt| T |]
        ] `_THEN` 
        tacDISJ1 `_THEN` tacREFL
      , _DISCH_THEN (tacSTRIP_ASSUME . ruleGSYM) `_THEN`
        _TRY (tacDISJ1 `_THEN` _FIRST_ASSUM tacACCEPT) `_THEN`
        tacDISJ2 `_THEN` 
        tacDISCH `_THEN` 
        tacMP (ruleITAUT [txt| ~(T <=> F) |]) `_THEN`
        tacPURE_ONCE_ASM_REWRITE_NIL `_THEN`
        tacASM_REWRITE [ruleITAUT [txt| p \/ T <=> T |]]
      ]

tacBOOL_CASES :: (BoolCtxt thry, HOLTermRep tm cls thry) 
               => tm -> Tactic cls thry
tacBOOL_CASES tm = tacSTRUCT_CASES (ruleSPEC tm thmBOOL_CASES_AX)

thmBOOL_CASES_AX :: BoolCtxt thry => HOL cls thry HOLThm
thmBOOL_CASES_AX = unsafeCacheProof "thmBOOL_CASES_AX" .
    prove [txt| !t. (t <=> T) \/ (t <=> F) |] $
      tacGEN `_THEN` 
      tacDISJ_CASES (ruleSPEC [txt| t:bool |] thmEXCLUDED_MIDDLE) `_THEN` 
      tacASM_REWRITE_NIL

tacTAUT :: BoolCtxt thry => Tactic cls thry
tacTAUT = _REPEAT (tacGEN `_ORELSE` tacCONJ) `_THEN` _REPEAT tacRTAUT
  where tacRTAUT :: BoolCtxt thry => Tactic cls thry
        tacRTAUT g@(Goal _ w) = 
            let ok t = typeOf t == tyBool && 
                       test' (findTerm isVar t) && 
                       t `freeIn` w
                (tm:_) = sort freeIn $ findTerms ok w  in
              (tacREWRITE_NIL `_THEN` 
               (tacREWRITE_NIL `_THEN` tacBOOL_CASES tm)) g

thmNOT_CLAUSE :: BoolCtxt thry => HOL cls thry HOLThm
thmNOT_CLAUSE = prove [txt| (!t. ~ ~t <=> t) |] tacTAUT

thmCOND_CLAUSES :: BoolCtxt thry => HOL cls thry HOLThm
thmCOND_CLAUSES = unsafeCacheProof "thmCOND_CLAUSES" .
    prove [txt| !(t1:A) t2. ((if T then t1 else t2) = t1) /\ 
                            ((if F then t1 else t2) = t2) |] $
      tacREWRITE [defCOND]

-- Stage 3
thmMONO_COND :: BoolCtxt thry => HOL cls thry HOLThm
thmMONO_COND = unsafeCacheProof "thmMONO_COND" .
    prove [txt| (A ==> B) /\ (C ==> D) ==> 
                (if b then A else C) ==> 
                (if b then B else D) |] $
      tacSTRIP `_THEN`
      tacBOOL_CASES [txt| b:bool |] `_THEN`
      tacASM_REWRITE_NIL

thmCOND_CONG :: BoolCtxt thry => HOL cls thry HOLThm
thmCOND_CONG = unsafeCacheProof "thmCOND_CONG" $
    prove [txt| (g = g') ==>
                (g' ==> (t = t')) ==>
                (~g' ==> (e = e')) ==>
                ((if g then t else e) = 
                (if g' then t' else e')) |]
      tacTAUT
       
thmCOND_EQ_CLAUSE :: BoolCtxt thry => HOL cls thry HOLThm
thmCOND_EQ_CLAUSE = unsafeCacheProof "thmCOND_EQ_CLAUSE" $
    prove [txt| (if x = x then y else z) = y |] tacREWRITE_NIL

inductBool :: BoolCtxt thry => HOL cls thry HOLThm
inductBool = unsafeCacheProof "inductBool" .
    prove [txt| !P. P F /\ P T ==> !x. P x |] $
      _REPEAT tacSTRIP `_THEN`
      tacDISJ_CASES (ruleSPEC [txt| x:bool |] thmBOOL_CASES_AX) `_THEN`
      tacASM_REWRITE_NIL

recursionBool :: BoolCtxt thry => HOL cls thry HOLThm
recursionBool = unsafeCacheProof "recursionBool" .
    prove [txt| !a b:A. ?f. f F = a /\ f T = b |] $
      _REPEAT tacGEN `_THEN`
      tacEXISTS [txt| \x. if x then b:A else a |] `_THEN`
      tacREWRITE_NIL

-- Inductive Type Store

data IndTypeStore = 
    IndTypeStore !(Map Text (Int, HOLThm, HOLThm)) deriving Typeable

deriveSafeCopy 0 'base ''IndTypeStore

addIndDefPrim :: Text -> (Int, HOLThm, HOLThm) -> Update IndTypeStore ()
addIndDefPrim name def =
    do (IndTypeStore defs) <- get
       case mapAssoc name defs of
         Nothing -> put (IndTypeStore (mapInsert name def defs))
         _ -> return ()

getIndDefsPrim :: Query IndTypeStore (Map Text (Int, HOLThm, HOLThm))
getIndDefsPrim =
    do (IndTypeStore indTys) <- ask
       return indTys

makeAcidic ''IndTypeStore ['addIndDefPrim, 'getIndDefsPrim]
       

addIndDef :: (HOLThmRep thm1 Theory thry, HOLThmRep thm2 Theory thry)
          => (Text, (Int, thm1, thm2)) -> HOL Theory thry ()
addIndDef (name, (n, pth1, pth2)) =
    do th1 <- toHThm pth1
       th2 <- toHThm pth2
       acid <- openLocalStateHOL (IndTypeStore mapEmpty)
       updateHOL acid (AddIndDefPrim name (n, th1, th2))
       createCheckpointAndCloseHOL acid

getIndDefs :: HOL cls thry (Map Text (Int, HOLThm, HOLThm))
getIndDefs =
    do acid <- openLocalStateHOL (IndTypeStore mapEmpty)
       indTys <- queryHOL acid GetIndDefsPrim
       closeAcidStateHOL acid
       return indTys
