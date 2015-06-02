module HaskHOL.Lib.Classic.Base where

import HaskHOL.Core

import HaskHOL.Lib.Bool
import HaskHOL.Lib.DRule
import HaskHOL.Lib.Equal
import HaskHOL.Lib.Itab
import HaskHOL.Lib.Tactics
import HaskHOL.Lib.Simp

-- Stage 1

-- eta conv stuff
axETA' :: HOL Theory thry HOLThm
axETA' = newAxiom "axETA" [str| !t:A->B. (\x. t x) = t |]

axSELECT' :: HOL Theory thry HOLThm
axSELECT' = newAxiom "axSELECT" "!P (x:A). P x ==> P((@) P)"

-- conditionals
defCOND' :: BoolCtxt thry => HOL Theory thry HOLThm
defCOND' = newDefinition "COND"
    [str| COND = \t t1 t2. @x:A. ((t <=> T) ==> (x = t1)) /\ 
                                 ((t <=> F) ==> (x = t2)) |]


-- Stage 2
thmEQ_EXT' :: BoolCtxt thry => HOL cls thry HOLThm
thmEQ_EXT' =
    do x <- toHTm "x:A" 
       prove "!(f:A->B) g. (!x. f x = g x) ==> f = g" $
         _REPEAT tacGEN `_THEN`
         _DISCH_THEN (\ th g -> do th' <- ruleSPEC x th
                                   th'' <- fromRightM $ primABS x th'
                                   tacMP th'' g) `_THEN`
         tacREWRITE [getAxiom "axETA"]

thmEXISTS' :: BoolCtxt thry => HOL cls thry HOLThm
thmEXISTS' = 
    prove [str| (?) = \P:A->bool. P ((@) P) |] $
      tacMATCH_MP thmEQ_EXT' `_THEN`
      tacBETA `_THEN`
      tacX_GEN "P:A->bool" `_THEN`
      tacGEN_REWRITE (convLAND . convRAND) [ruleGSYM (getAxiom "axETA")] `_THEN`
      tacEQ `_THENL`
      [ _DISCH_THEN (_CHOOSE_THEN tacMP) `_THEN`
        tacMATCH_ACCEPT (getAxiom "axSELECT")
      , tacDISCH `_THEN` tacEXISTS "((@) P):A" `_THEN`
        _POP_ASSUM tacACCEPT
      ]

convSELECT_pth' :: BoolCtxt thry => HOL cls thry HOLThm
convSELECT_pth' =
    prove "(P:A->bool)((@)P) = (?) P" $
      tacREWRITE [thmEXISTS'] `_THEN`
      tacBETA `_THEN`
      tacREFL

convSELECT' :: BoolCtxt thry => HOL cls thry HOLThm -> Conversion cls thry
convSELECT' pth' = Conv $ \ tm ->
    do p <- serve [bool| P:A->bool |]
       pth <- pth'
       case findTerm (isEpsOK tm) tm of
         Just (Comb _ lam@(Abs (Var _ ty) _)) -> 
           ruleCONV (convLAND convBETA) #<< rulePINST [(tyA, ty)] [(p, lam)] pth
         _ -> fail "convSELECT_CONV"
  where isEpsOK :: HOLTerm -> HOLTerm -> Bool        
        isEpsOK tm t 
            | isBinder "@" t = 
                  case destBinder "@" t of
                    Just (bv, bod) -> aConv tm . fromJust $ 
                                        varSubst [(bv, t)] bod
                    _ -> False
            | otherwise = False
  
thmSELECT_REFL' :: BoolCtxt thry => HOL cls thry HOLThm
thmSELECT_REFL' = 
    prove "!x:A. (@y. y = x) = x" $
      tacGEN `_THEN` 
      tacCONV (convSELECT' convSELECT_pth') `_THEN`
      tacEXISTS "x:A" `_THEN`
      tacREFL


-- Stage 3
thmEXCLUDED_MIDDLE' :: BoolCtxt thry => HOL cls thry HOLThm
thmEXCLUDED_MIDDLE' =
    prove [str| !t. t \/ ~t |] $
      tacGEN `_THEN` 
      _SUBGOAL_THEN [str| (((@x. (x <=> F) \/ t) <=> F) \/ t) /\ 
                          (((@x. (x <=> T) \/ t) <=> T) \/ t) |]
      tacMP `_THENL`
      [ tacCONJ `_THEN` 
        tacCONV (convSELECT' convSELECT_pth') `_THENL` 
        [ tacEXISTS "F"
        , tacEXISTS "T"
        ] `_THEN` 
        tacDISJ1 `_THEN` tacREFL
      , _DISCH_THEN (\ th g -> do th' <- ruleGSYM th
                                  tacSTRIP_ASSUME th' g) `_THEN`
        _TRY (tacDISJ1 `_THEN` _FIRST_ASSUM tacACCEPT) `_THEN`
        tacDISJ2 `_THEN` 
        tacDISCH `_THEN` 
        tacMP thmEXCLUDED_MIDDLE_pth1 `_THEN`
        tacPURE_ONCE_ASM_REWRITE [] `_THEN`
        tacASM_REWRITE [thmEXCLUDED_MIDDLE_pth2]
      ]
  where thmEXCLUDED_MIDDLE_pth1 :: BoolCtxt thry => HOL cls thry HOLThm
        thmEXCLUDED_MIDDLE_pth1 = 
            cacheProof "thmEXCLUDED_MIDDLE_pth1" ctxtBool $ 
              ruleITAUT "~(T <=> F)"

        thmEXCLUDED_MIDDLE_pth2 :: BoolCtxt thry => HOL cls thry HOLThm
        thmEXCLUDED_MIDDLE_pth2 = 
            cacheProof "thmEXCLUDED_MIDDLE_pth2" ctxtBool $
              ruleITAUT [str| p \/ T <=> T |]

thmBOOL_CASES_AX' :: BoolCtxt thry => HOL cls thry HOLThm
thmBOOL_CASES_AX' =
    prove [str| !t. (t <=> T) \/ (t <=> F) |] $
      tacGEN `_THEN` 
      tacDISJ_CASES (ruleSPEC "t:bool" thmEXCLUDED_MIDDLE') `_THEN` 
      tacASM_REWRITE_NIL

tacBOOL_CASES' :: (BoolCtxt thry, HOLTermRep tm cls thry) 
               => HOL cls thry HOLThm -> tm -> Tactic cls thry
tacBOOL_CASES' pth ptm g =
    do tm <- toHTm ptm
       th <- ruleSPEC tm pth
       tacSTRUCT_CASES th g

tacTAUT' :: BoolCtxt thry => (HOLTerm -> Tactic cls thry) -> Tactic cls thry
tacTAUT' baseTac = _REPEAT (tacGEN `_ORELSE` tacCONJ) `_THEN` _REPEAT rtaut_tac
  where rtaut_tac g@(Goal _ w) = 
            let ok t = typeOf t == tyBool && 
                       isJust (findTerm isVar t) && 
                       t `freeIn` w
                tac gl = let (tm:_) = sort freeIn $ findTerms ok w in
                           baseTac tm gl in
              (tacREWRITE_NIL `_THEN` (tacREWRITE_NIL `_THEN` tac)) g

thmNOT_CLAUSE' :: BoolCtxt thry => HOL cls thry HOLThm
thmNOT_CLAUSE' = 
    prove "(!t. ~ ~t <=> t)" . tacTAUT' $ tacBOOL_CASES' thmBOOL_CASES_AX'

thmCOND_CLAUSES' :: BoolCtxt thry => HOL cls thry HOLThm
thmCOND_CLAUSES' =
    prove [str| !(t1:A) t2. ((if T then t1 else t2) = t1) /\ 
                            ((if F then t1 else t2) = t2) |] $
      tacREWRITE [getDefinition "COND"]

thmMONO_COND' :: BoolCtxt thry => HOL cls thry HOLThm
thmMONO_COND' =
    prove [str| (A ==> B) /\ (C ==> D) ==> 
                (if b then A else C) ==> 
                (if b then B else D) |] $
      tacSTRIP `_THEN`
      tacBOOL_CASES' thmBOOL_CASES_AX' "b:bool" `_THEN`
      tacASM_REWRITE_NIL

thmCOND_CONG' :: BoolCtxt thry => HOL cls thry HOLThm
thmCOND_CONG' =
    prove [str| (g = g') ==>
                (g' ==> (t = t')) ==>
                (~g' ==> (e = e')) ==>
                ((if g then t else e) = 
                (if g' then t' else e')) |] $
      tacTAUT' (tacBOOL_CASES' thmBOOL_CASES_AX')
       
thmCOND_EQ_CLAUSE' :: BoolCtxt thry => HOL cls thry HOLThm
thmCOND_EQ_CLAUSE' =
    prove "(if x = x then y else z) = y" tacREWRITE_NIL

inductBool' :: BoolCtxt thry => HOL cls thry HOLThm
inductBool' =
    prove [str| !P. P F /\ P T ==> !x. P x |] $
      _REPEAT tacSTRIP `_THEN`
      tacDISJ_CASES (ruleSPEC "x:bool" thmBOOL_CASES_AX') `_THEN`
      tacASM_REWRITE_NIL

recursionBool' :: BoolCtxt thry => HOL cls thry HOLThm
recursionBool' =
    prove [str| !a b:A. ?f. f F = a /\ f T = b |] $
      _REPEAT tacGEN `_THEN`
      tacEXISTS [str| \x. if x then b:A else a |] `_THEN`
      tacREWRITE_NIL

-- Inductive Type Store

data IndTypeStore = 
    IndTypeStore !(Map Text (Int, HOLThm, HOLThm)) deriving Typeable

deriveSafeCopy 0 'base ''IndTypeStore

addIndDef :: Text -> (Int, HOLThm, HOLThm) -> Update IndTypeStore ()
addIndDef name def =
    do (IndTypeStore defs) <- get
       case mapLookup name defs of
         Nothing -> put (IndTypeStore (mapInsert name def defs))
         _ -> return ()

getIndDefs' :: Query IndTypeStore (Map Text (Int, HOLThm, HOLThm))
getIndDefs' =
    do (IndTypeStore indTys) <- ask
       return indTys

makeAcidic ''IndTypeStore ['addIndDef, 'getIndDefs']
       

addIndDefs :: [(Text, (Int, HOLThm, HOLThm))] -> HOL Theory thry ()
addIndDefs ds =
    do acid <- openLocalStateHOL (IndTypeStore mapEmpty)
       mapM_ (\ (name, def) -> updateHOL acid (AddIndDef name def)) ds
       createCheckpointAndCloseHOL acid

getIndDefs :: HOL cls thry (Map Text (Int, HOLThm, HOLThm))
getIndDefs =
    do acid <- openLocalStateHOL (IndTypeStore mapEmpty)
       indTys <- queryHOL acid GetIndDefs'
       closeAcidStateHOL acid
       return indTys
