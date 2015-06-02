{-# LANGUAGE FlexibleContexts, PatternSynonyms #-}
{-|
  Module:    HaskHOL.Lib.Classic
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Classic
    ( ClassicCtxt
    , ctxtClassic
    , classic
    , axETA
    , convETA
    , thmEQ_EXT
    , thmFUN_EQ
    , isSelect
    , destSelect
    , mkSelect
    , axSELECT
    , thmEXISTS
    , ruleSELECT
    , convSELECT
    , thmSELECT_REFL
    , thmSELECT_UNIQUE
    , thmEXCLUDED_MIDDLE
    , tacTAUT
    , ruleTAUT
    , tacBOOL_CASES
    , tacASM_CASES
    , thmNOT_EXISTS
    , thmEXISTS_NOT
    , thmNOT_FORALL
    , thmFORALL_BOOL
    , thmEXISTS_BOOL
    , thmDE_MORGAN
    , thmNOT_CLAUSES
    , thmNOT_IMP
    , thmCONTRAPOS
    , thmLEFT_FORALL_OR
    , thmRIGHT_FORALL_OR
    , thmLEFT_OR_FORALL
    , thmRIGHT_OR_FORALL
    , isCond
    , mkCond
    , thmCOND_CLAUSES
    , convCONTRAPOS
    , tacREFUTE_THEN
    , thmSKOLEM
    , thmUNIQUE_SKOLEM_ALT
    , newTypeDefinition
    , getTypeDefinition
    , addIndDefs
    , getIndDefs
    , newSpecification
    , getSpecification
    , thmMONO_COND
    , thmCOND_CONG
    , thmCOND_EQ_CLAUSE
    , inductBool
    , recursionBool
    , defCOND
    , thmCOND_ELIM
    , convCOND_ELIM
    , tacCOND_CASES
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Bool
import HaskHOL.Lib.Equal
import HaskHOL.Lib.Simp
import HaskHOL.Lib.DRule
import HaskHOL.Lib.Tactics
import HaskHOL.Lib.Theorems

import HaskHOL.Lib.Classic.Base
import HaskHOL.Lib.Classic.Context
import HaskHOL.Lib.Classic.PQ

-- | @!t:A->B. (\x. t x) = t@
axETA :: ClassicCtxt thry => HOL cls thry HOLThm
axETA = cacheProof "axETA" ctxtClassic $ getAxiom "axETA"

-- | @!P (x:A). P x ==> P((@) P)@
axSELECT :: ClassicCtxt thry => HOL cls thry HOLThm
axSELECT = cacheProof "axSELECT" ctxtClassic $ getAxiom "axSELECT"

{-| 
   @COND = \t t1 t2. @x:A. ((t <=> T) ==> (x = t1)) /\ ((t <=> F) ==> (x = t2))@
-}
defCOND :: ClassicCtxt thry => HOL cls thry HOLThm
defCOND = cacheProof "defCOND" ctxtClassic $ getDefinition "COND"

thmEQ_EXT :: ClassicCtxt thry => HOL cls thry HOLThm
thmEQ_EXT = cacheProof "thmEQ_EXT" ctxtClassic  thmEQ_EXT'

thmEXISTS :: ClassicCtxt thry => HOL cls thry HOLThm
thmEXISTS = cacheProof "thmEXISTS" ctxtClassic thmEXISTS'

convSELECT :: ClassicCtxt thry => Conversion cls thry
convSELECT = convSELECT' convSELECT_pth
    where convSELECT_pth :: ClassicCtxt thry => HOL cls thry HOLThm
          convSELECT_pth = 
              cacheProof "convSELECT_pth" ctxtClassic convSELECT_pth'

thmSELECT_REFL :: ClassicCtxt thry => HOL cls thry HOLThm
thmSELECT_REFL = cacheProof "thmSELECT_REFL" ctxtClassic thmSELECT_REFL'

-- Stage2
thmEXCLUDED_MIDDLE :: ClassicCtxt thry => HOL cls thry HOLThm
thmEXCLUDED_MIDDLE = 
    cacheProof "thmEXCLUDED_MIDDLE" ctxtClassic thmEXCLUDED_MIDDLE'
             

-- basic selection operator rule
ruleSELECT :: (ClassicCtxt thry, HOLThmRep thm cls thry) 
           => thm -> HOL cls thry HOLThm
ruleSELECT pthm = 
    do p <- serve [bool| P:A->bool |]
       th <- toHThm pthm
       pth <- ruleSELECT_pth
       case rand $ concl th of
         Just lam@(Abs (Var _ ty) _) -> 
             ruleCONV convBETA =<< 
               ruleMP (fromJust $ rulePINST [(tyA, ty)] [(p, lam)] pth) th
         _ -> fail "ruleSELECT"
  where ruleSELECT_pth :: ClassicCtxt thry => HOL cls thry HOLThm
        ruleSELECT_pth = cacheProof "ruleSELECT_pth" ctxtClassic $
            prove "(?) (P:A->bool) ==> P((@) P)" $
              tacSIMP [axSELECT, axETA]

-- classically based tactics
tacBOOL_CASES :: (ClassicCtxt thry, HOLTermRep tm cls thry) => tm 
              -> Tactic cls thry
tacBOOL_CASES = tacBOOL_CASES' thmBOOL_CASES_AX
  where thmBOOL_CASES_AX :: ClassicCtxt thry => HOL cls thry HOLThm
        thmBOOL_CASES_AX = 
            cacheProof "thmBOOL_CASES_AX" ctxtClassic thmBOOL_CASES_AX'

tacASM_CASES :: (ClassicCtxt thry, HOLTermRep tm cls thry) => tm 
             -> Tactic cls thry
tacASM_CASES t g = 
    do th <- ruleSPEC t thmEXCLUDED_MIDDLE
       tacDISJ_CASES th g

-- tautology checker for classical logic
tacTAUT :: ClassicCtxt thry => Tactic cls thry
tacTAUT = tacTAUT' tacBOOL_CASES

ruleTAUT :: (HOLTermRep tm cls thry, ClassicCtxt thry) => tm 
         -> HOL cls thry HOLThm
ruleTAUT tm = prove tm tacTAUT

thmNOT_CLAUSES :: ClassicCtxt thry => HOL cls thry HOLThm
thmNOT_CLAUSES = cacheProof "thmNOT_CLAUSES" ctxtClassic $
    ruleTAUT [str| (!t. ~ ~t <=> t) /\ (~T <=> F) /\ (~F <=> T) |]

thmNOT_IMP :: ClassicCtxt thry => HOL cls thry HOLThm
thmNOT_IMP = cacheProof "thmNOT_IMP" ctxtClassic $
    ruleTAUT [str| !t1 t2. ~(t1 ==> t2) <=> t1 /\ ~t2 |]

thmCOND_CLAUSES :: ClassicCtxt thry => HOL cls thry HOLThm
thmCOND_CLAUSES = cacheProof "thmCOND_CLAUSES" ctxtClassic thmCOND_CLAUSES'

-- Stage 3

thmMONO_COND :: ClassicCtxt thry => HOL cls thry HOLThm
thmMONO_COND = cacheProof "thmMONO_COND" ctxtClassic thmMONO_COND'


thmCOND_CONG :: ClassicCtxt thry => HOL cls thry HOLThm
thmCOND_CONG = cacheProof "thmCOND_CONG" ctxtClassic thmCOND_CONG'
       
thmCOND_EQ_CLAUSE :: ClassicCtxt thry => HOL cls thry HOLThm
thmCOND_EQ_CLAUSE = 
    cacheProof "thmCOND_EQ_CLAUSE" ctxtClassic thmCOND_EQ_CLAUSE'

inductBool :: ClassicCtxt thry => HOL cls thry HOLThm
inductBool = cacheProof "inductBool" ctxtClassic inductBool

recursionBool :: ClassicCtxt thry => HOL cls thry HOLThm
recursionBool = cacheProof "recursionBool" ctxtClassic recursionBool


-- Base

thmDE_MORGAN :: ClassicCtxt thry => HOL cls thry HOLThm
thmDE_MORGAN = cacheProof "thmDE_MORGAN" ctxtClassic $
    ruleTAUT [str| !t1 t2. (~(t1 /\ t2) <=> ~t1 \/ ~t2) /\ 
                           (~(t1 \/ t2) <=> ~t1 /\ ~t2) |]

thmFORALL_BOOL :: ClassicCtxt thry => HOL cls thry HOLThm
thmFORALL_BOOL = cacheProof "thmFORALL_BOOL" ctxtClassic $
    prove [str| (!b. P b) <=> P T /\ P F |] $
      tacEQ `_THEN`
      tacDISCH `_THEN`
      tacASM_REWRITE_NIL `_THEN`
      tacGEN `_THEN`
      tacBOOL_CASES "b:bool" `_THEN`
      tacASM_REWRITE_NIL

thmNOT_EXISTS :: ClassicCtxt thry => HOL cls thry HOLThm
thmNOT_EXISTS = cacheProof "thmNOT_EXISTS" ctxtClassic $
    prove "!P. ~(?x:A. P x) <=> (!x. ~(P x))" $
      tacGEN `_THEN`
      tacEQ `_THEN`
      tacDISCH `_THENL`
      [ tacGEN `_THEN` 
        tacDISCH `_THEN`
        tacUNDISCH "~(?x:A. P x)" `_THEN`
        tacREWRITE_NIL `_THEN` 
        tacEXISTS "x:A" `_THEN`
        _POP_ASSUM tacACCEPT
      , _DISCH_THEN (_CHOOSE_THEN tacMP) `_THEN`
        tacASM_REWRITE_NIL
      ]

thmEXISTS_NOT :: ClassicCtxt thry => HOL cls thry HOLThm
thmEXISTS_NOT = cacheProof "thmEXISTS_NOT" ctxtClassic $
    prove "!P. (?x:A. ~(P x)) <=> ~(!x. P x)" $
      tacONCE_REWRITE [ruleTAUT "(a <=> ~b) <=> (~a <=> b)"] `_THEN`
      tacREWRITE [thmNOT_EXISTS]

thmNOT_FORALL :: ClassicCtxt thry => HOL cls thry HOLThm
thmNOT_FORALL = cacheProof "thmNOT_FORALL" ctxtClassic $
    prove "!P. ~(!x. P x) <=> (?x:A. ~(P x))" $
      tacMATCH_ACCEPT (ruleGSYM thmEXISTS_NOT)

thmLEFT_FORALL_OR :: ClassicCtxt thry => HOL cls thry HOLThm
thmLEFT_FORALL_OR = cacheProof "thmLEFT_FORALL_OR" ctxtClassic $
   prove [str| !P Q. (!x:A. P x \/ Q) <=> (!x. P x) \/ Q |] $
     _REPEAT tacGEN `_THEN`
     tacONCE_REWRITE [ruleTAUT "(a <=> b) <=> (~a <=> ~b)"] `_THEN`
     tacREWRITE [thmNOT_FORALL, thmDE_MORGAN, thmLEFT_EXISTS_AND]

thmRIGHT_FORALL_OR :: ClassicCtxt thry => HOL cls thry HOLThm
thmRIGHT_FORALL_OR = cacheProof "thmRIGHT_FORALL_OR" ctxtClassic $
    prove [str| !P Q. (!x:A. P \/ Q x) <=> P \/ (!x. Q x) |] $
      _REPEAT tacGEN `_THEN`
      tacONCE_REWRITE [ruleTAUT "(a <=> b) <=> (~a <=> ~b)"] `_THEN`
      tacREWRITE [thmNOT_FORALL, thmDE_MORGAN, thmRIGHT_EXISTS_AND]

thmLEFT_OR_FORALL :: ClassicCtxt thry => HOL cls thry HOLThm
thmLEFT_OR_FORALL = cacheProof "thmLEFT_OR_FORALL" ctxtClassic $
    prove [str| !P Q. (!x:A. P x) \/ Q <=> (!x. P x \/ Q) |] $
      tacMATCH_ACCEPT (ruleGSYM thmLEFT_FORALL_OR)

thmRIGHT_OR_FORALL :: ClassicCtxt thry => HOL cls thry HOLThm
thmRIGHT_OR_FORALL = cacheProof "thmRIGHT_OR_FORALL" ctxtClassic $
    prove [str| !P Q. P \/ (!x:A. Q x) <=> (!x. P \/ Q x) |] $
      tacMATCH_ACCEPT (ruleGSYM thmRIGHT_FORALL_OR)

thmSKOLEM :: ClassicCtxt thry => HOL cls thry HOLThm
thmSKOLEM = cacheProof "thmSKOLEM" ctxtClassic $
    prove "!P. (!x:A. ?y:B. P x y) <=> (?y. !x. P x (y x))" $
      _REPEAT (tacSTRIP `_ORELSE` tacEQ) `_THENL`
      [ tacEXISTS [str| \x:A. @y:B. P x y |]  `_THEN` 
        tacGEN `_THEN`
        tacBETA `_THEN`
        tacCONV convSELECT
      , tacEXISTS "(y:A->B) x"
      ] `_THEN`
      _POP_ASSUM tacMATCH_ACCEPT

-- select operator, giving associativity and commutativity
isSelect :: HOLTerm -> Bool
isSelect = isBinder "@"

destSelect :: HOLTerm -> Maybe (HOLTerm, HOLTerm)
destSelect = destBinder "@"

mkSelect :: HOLTerm -> HOLTerm -> HOL cls thry HOLTerm
mkSelect = mkBinder "@"

isCond :: HOLTerm -> Bool
isCond tm = 
    case rator =<< rator =<< rator tm of
      Just (Const "COND" _) -> True
      _ -> False

mkCond :: HOLTerm -> HOLTerm -> HOLTerm -> HOL cls thry HOLTerm
mkCond b x y =
    (do c <- mkConst "COND" [(tyA, typeOf x)]
        fromRightM $ flip mkComb y =<< flip mkComb x =<< mkComb c b) 
    <?> "mkCond"

convETA :: ClassicCtxt thry => Conversion cls thry
convETA = Conv $ \ tm ->
    do t <- serve [classic| t:A->B |]
       pth <- convETA_pth
       case tm of
         (Abs bv bod@(Comb l r)) -> 
             if r == bv && not (varFreeIn bv l)
             then fromRightM $ primTRANS (primREFL tm) #<< 
                    rulePINST [(tyA, typeOf bv), (tyB, typeOf bod)] [(t, l)] pth
             else fail "convETA"
         _ -> fail "convETA: term not an abstraction"
  where convETA_pth :: ClassicCtxt thry => HOL cls thry HOLThm
        convETA_pth = cacheProof "convETA_pth" ctxtClassic $
            prove [str| (\x. (t:A->B) x) = t |] $
              tacMATCH_ACCEPT axETA

                  


thmFUN_EQ :: ClassicCtxt thry => HOL cls thry HOLThm
thmFUN_EQ = cacheProof "thmFUN_EQ" ctxtClassic $
    prove "!(f:A->B) g. f = g <=> (!x. f x = g x)" $
      _REPEAT tacGEN `_THEN`
      tacEQ `_THENL`
      [ _DISCH_THEN tacSUBST1 `_THEN` tacGEN `_THEN` tacREFL
      , tacMATCH_ACCEPT thmEQ_EXT
      ]

-- expand quantification over booleans

thmEXISTS_BOOL :: ClassicCtxt thry => HOL cls thry HOLThm
thmEXISTS_BOOL = cacheProof "thmEXISTS_BOOL" ctxtClassic $
    prove [str| (?b. P b) <=> P T \/ P F |] $
      tacMATCH_MP (ruleTAUT "(~p <=> ~q) ==> (p <=> q)") `_THEN`
      tacREWRITE [thmDE_MORGAN, thmNOT_EXISTS, thmFORALL_BOOL]

-- classically based rules
convCONTRAPOS :: ClassicCtxt thry => Conversion cls thry
convCONTRAPOS = Conv $ \ tm ->
    do (a, b) <- pairMapM serve ([classic| a:bool |], [classic| b:bool |])
       pth <- convCONTRAPOS_pth
       liftMaybe "convCONTRAPOS: " $
         do (p, q) <- destImp tm
            primINST [(a, p), (b, q)] pth
  where convCONTRAPOS_pth :: ClassicCtxt thry => HOL cls thry HOLThm
        convCONTRAPOS_pth = cacheProof "convCONTRAPOS_pth" ctxtClassic $
            ruleTAUT "(a ==> b) <=> (~b ==> ~a)"

-- refutation tactic
tacREFUTE_THEN :: ClassicCtxt thry => ThmTactic cls thry -> Tactic cls thry
tacREFUTE_THEN ttac gl@(Goal _ w) =
    do fTm <- serve [classic| F |]
       if w == fTm 
          then _ALL gl
          else if isNeg w then _DISCH_THEN ttac gl
               else (tacCONV (convREWR tacREFUTE_THEN_pth) `_THEN` 
                     _DISCH_THEN ttac) gl
  where tacREFUTE_THEN_pth :: ClassicCtxt thry => HOL cls thry HOLThm
        tacREFUTE_THEN_pth = cacheProof "tacREFUTE_THEN_pth" ctxtClassic $
            ruleTAUT "p <=> ~p ==> F"


-- skolemization

thmUNIQUE_SKOLEM_ALT :: ClassicCtxt thry => HOL cls thry HOLThm
thmUNIQUE_SKOLEM_ALT = cacheProof "thmUNIQUE_SKOLEM_ALT" ctxtClassic $
    prove [str| !P:A->B->bool. 
                (!x. ?!y. P x y) <=> ?f. !x y. P x y <=> (f x = y) |] $
      tacGEN `_THEN` tacREWRITE [thmEXISTS_UNIQUE_ALT, thmSKOLEM]

-- basic selection theorems
thmSELECT_UNIQUE :: ClassicCtxt thry => HOL cls thry HOLThm
thmSELECT_UNIQUE = cacheProof "thmSELECT_UNIQUE" ctxtClassic $
    prove "!P x. (!y:A. P y = (y = x)) ==> ((@) P = x)" $
      _REPEAT tacSTRIP `_THEN`
      tacGEN_REWRITE (convLAND . convRAND) [ruleGSYM axETA] `_THEN`
      tacASM_REWRITE [thmSELECT_REFL]

-- type definitions

data TypeDefs = TypeDefs !(Map Text ((Text, Text), (HOLThm, HOLThm))) 
                  deriving Typeable

deriveSafeCopy 0 'base ''TypeDefs

getTypeDefs :: Query TypeDefs (Map Text ((Text, Text), (HOLThm, HOLThm)))
getTypeDefs =
    do (TypeDefs defs) <- ask
       return defs

getTypeDef :: Text -> Query TypeDefs (Maybe HOLThm)
getTypeDef name =
    do (TypeDefs defs) <- ask
       case mapLookup name defs of
         Just (_, (_, th)) -> return (Just th)
         Nothing -> return Nothing

addTypeDef :: Text -> ((Text, Text), (HOLThm, HOLThm)) 
           -> Update TypeDefs ()
addTypeDef name stuff =
    do (TypeDefs defs) <- get
       put (TypeDefs (mapInsert name stuff defs))

makeAcidic ''TypeDefs ['getTypeDefs, 'getTypeDef, 'addTypeDef]


newTypeDefinition :: (ClassicCtxt thry, 
                      HOLThmRep thm Theory thry) => Text 
                  -> Text -> Text -> thm -> HOL Theory thry HOLThm
newTypeDefinition tyname absname repname pth =
    do acid <- openLocalStateHOL (TypeDefs mapEmpty)
       defs <- queryHOL acid GetTypeDefs
       closeAcidStateHOL acid
       th <- toHThm pth
       case mapLookup tyname defs of
         Just (_, (th', tth')) -> 
             if concl th' /= concl th 
             then fail "newTypeDefinition: bad redefinition"
             else printDebugLn "newTypeDefinition: benign redefinition." $ 
                    return tth'
         Nothing ->
             do th0 <- ruleCONV (convRATOR (convREWR thmEXISTS) `_THEN` 
                                 convBETA) th
                (th1, th2) <- newBasicTypeDefinition tyname absname repname th0
                th3 <- ruleGEN_ALL th1
                tth <- ruleCONJ th3 =<< ruleGEN_ALL =<< 
                         ruleCONV (convLAND (_TRY convBETA)) th2
                acid' <- openLocalStateHOL (TypeDefs mapEmpty)
                updateHOL acid'
                    (AddTypeDef tyname ((absname, repname), (th, tth)))
                createCheckpointAndCloseHOL acid'
                return tth

getTypeDefinition :: Text -> HOL cls thry HOLThm
getTypeDefinition tyname =
    do acid <- openLocalStateHOL (TypeDefs mapEmpty)
       th <- queryHOL acid (GetTypeDef tyname)
       closeAcidStateHOL acid
       liftMaybe "getTypeDefinition: type name not found." th

ruleSEL :: ClassicCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleSEL = ruleCONV (convRATOR (convREWR thmEXISTS) `_THEN` convBETA)

checkDistinct :: Eq a => [a] -> Bool
checkDistinct l =
    case foldr (\ t res -> case res of
                             Nothing -> Nothing
                             Just res' -> if t `elem` res' then Nothing else Just $ t : res') (Just []) l of
      Just{} -> True
      _ -> False

specify :: ClassicCtxt thry => HOLThm -> Text -> HOL Theory thry HOLThm
specify th name =
    do th1 <- ruleSEL th
       case concl th1 of
         (Comb l r) -> 
             let ty = typeOf r in
               do th2 <- newDefinition name =<< mkEq (mkVar name ty) r
                  th3 <- fromRightM $ ruleSYM th2
                  ruleCONV convBETA #<< flip primEQ_MP th1 =<< ruleAP_TERM l th3
         _ -> fail "specify"

data Specifications = 
    Specifications ![(([Text], HOLThm), HOLThm)] deriving Typeable

deriveSafeCopy 0 'base ''Specifications

getSpecifications :: Query Specifications [(([Text], HOLThm), HOLThm)]
getSpecifications =
    do (Specifications specs) <- ask
       return specs

getASpecification :: [Text] -> Query Specifications (Maybe HOLThm)
getASpecification names =
    do (Specifications specs) <- ask
       case find (\ ((names', _), _) -> names' == names) specs of
         Just (_, th) -> return (Just th)
         Nothing -> return Nothing

addSpecification :: [Text] -> HOLThm -> HOLThm -> Update Specifications ()
addSpecification names th sth =
    do (Specifications specs) <- get
       put (Specifications (((names, th), sth) : specs))

makeAcidic ''Specifications 
    ['getSpecifications, 'getASpecification, 'addSpecification]


newSpecification :: ClassicCtxt thry => [Text] -> HOLThm 
                 -> HOL Theory thry HOLThm
newSpecification names th =
    let (asl, c) = destThm th in
      do failWhen (return . not $ null asl) 
           "newSpecification: Assumptions not allowed in theorem"
         failWhen (return . not . null $ frees c)
           "newSpecification: Free variables in predicate"
         let avs = fst $ stripExists c
         failWhen (return $ null names || length names > length avs)
           "newSpecification: Unsuitable number of constant names"
         failWhen (return . not $ checkDistinct names)
           "newSpecification: Constant names not distinct"
         acid <- openLocalStateHOL (Specifications [])
         specs <- queryHOL acid GetSpecifications
         closeAcidStateHOL acid
         case find (\ ((names', th'), _) ->
                    names' == names &&
                    concl th' `aConv` concl th) specs of
           Just (_, sth) -> 
             return sth
           Nothing ->
             do sth <- foldlM specify th names
                acid' <- openLocalStateHOL (Specifications [])
                updateHOL acid' (AddSpecification names th sth)
                createCheckpointAndCloseHOL acid'
                return sth
                                      
getSpecification :: [Text] -> HOL cls thry HOLThm
getSpecification names =
    do acid <- openLocalStateHOL (Specifications [])
       th <- queryHOL acid (GetASpecification names)
       closeAcidStateHOL acid
       liftMaybe "getSpecification: constants not found." th

thmCOND_ELIM :: ClassicCtxt thry => HOL cls thry HOLThm
thmCOND_ELIM = cacheProof "thmCOND_ELIM" ctxtClassic $
    prove [str| (P:A->bool) (if c then x else y) <=> 
                (c ==> P x) /\ (~c ==> P y) |] $
      tacBOOL_CASES "c:bool" `_THEN` tacREWRITE_NIL

convCOND_ELIM :: ClassicCtxt thry => Conversion cls thry
convCOND_ELIM = convHIGHER_REWRITE [thmCOND_ELIM] True

tacCOND_CASES :: ClassicCtxt thry => Tactic cls thry
tacCOND_CASES =
    tacCONV convCOND_ELIM `_THEN` tacCONJ `_THENL`
    [ _DISCH_THEN (\ th -> tacASSUME th `_THEN` tacSUBST1 (ruleEQT_INTRO th))
    , _DISCH_THEN (\ th g -> (do th' <- ruleDENEG th
                                 (tacASSUME th' `_THEN` 
                                    tacSUBST1 (ruleEQT_INTRO th')) g)
                             <|> (tacASSUME th `_THEN` 
                                  tacSUBST1 (ruleEQF_INTRO th)) g)
    ]
  where ruleDENEG :: ClassicCtxt thry => HOLThm 
                  -> HOL cls thry HOLThm
        ruleDENEG = ruleGEN_REWRITE id [tacCOND_CASES_pth]

        tacCOND_CASES_pth :: ClassicCtxt thry => HOL cls thry HOLThm
        tacCOND_CASES_pth = cacheProof "tacCOND_CASES_pth" ctxtClassic $ 
            ruleTAUT "~ ~ p <=> p"

thmCONTRAPOS :: ClassicCtxt thry => HOL cls thry HOLThm
thmCONTRAPOS = cacheProof "thmCONTRAPOS" ctxtClassic $
    ruleTAUT "!t1 t2. (~t1 ==> ~t2) <=> (t2 ==> t1)"
