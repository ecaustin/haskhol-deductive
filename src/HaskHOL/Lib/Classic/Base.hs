module HaskHOL.Lib.Classic.Base where

import HaskHOL.Core

import HaskHOL.Lib.Bool
import HaskHOL.Lib.Tactics
import HaskHOL.Lib.Simp

import HaskHOL.Lib.Classic.C

thmMONO_COND :: ClassicCCtxt thry => HOL cls thry HOLThm
thmMONO_COND = cacheProof "thmMONO_COND" ctxtClassicC $
    prove [str| (A ==> B) /\ (C ==> D) ==> 
                (if b then A else C) ==> 
                (if b then B else D) |] $
      tacSTRIP `_THEN`
      tacBOOL_CASES "b:bool" `_THEN`
      tacASM_REWRITE_NIL

thmCOND_CONG :: ClassicCCtxt thry => HOL cls thry HOLThm
thmCOND_CONG = cacheProof "thmCOND_CONG" ctxtClassicC $
    ruleTAUT [str| (g = g') ==>
                   (g' ==> (t = t')) ==>
                   (~g' ==> (e = e')) ==>
                   ((if g then t else e) = 
                   (if g' then t' else e')) |]
       
thmCOND_EQ_CLAUSE :: ClassicCCtxt thry => HOL cls thry HOLThm
thmCOND_EQ_CLAUSE = cacheProof "thmCOND_EQ_CLAUSE" ctxtClassicC $
    prove "(if x = x then y else z) = y" tacREWRITE_NIL

inductBool :: ClassicCCtxt thry => HOL cls thry HOLThm
inductBool = cacheProof "inductBool" ctxtClassicC $
    prove [str| !P. P F /\ P T ==> !x. P x |] $
      _REPEAT tacSTRIP `_THEN`
      tacDISJ_CASES (ruleSPEC "x:bool" thmBOOL_CASES_AX) `_THEN`
      tacASM_REWRITE_NIL

recursionBool :: ClassicCCtxt thry => HOL cls thry HOLThm
recursionBool = cacheProof "recursionBool" ctxtClassicC $
    prove [str| !a b:A. ?f. f F = a /\ f T = b |] $
      _REPEAT tacGEN `_THEN`
      tacEXISTS [str| \x. if x then b:A else a |] `_THEN`
      tacREWRITE_NIL

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
