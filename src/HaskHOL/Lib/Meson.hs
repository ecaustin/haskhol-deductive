{-# LANGUAGE PatternSynonyms, ScopedTypeVariables #-}
{-|
  Module:    HaskHOL.Lib.Meson
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Meson
    ( tacGEN_MESON
    , tacASM_MESON
    , tacASM_MESON_NIL
    , tacMESON
    , tacMESON_NIL
    , ruleMESON
    , ruleMESON_NIL
    , mesonDepth
    , setMesonDepth
    , unsetMesonDepth
    , mesonPRefine
    , setMesonPRefine
    , unsetMesonPRefine
    , mesonBrand
    , setMesonBrand
    , unsetMesonBrand
    , mesonChatty
    , setMesonChatty
    , unsetMesonChatty
    , mesonSkew
    , setMesonSkew
    , mesonSplitLimit
    , setMesonSplitLimit
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Bool
import HaskHOL.Lib.Canon
import HaskHOL.Lib.Classic
import HaskHOL.Lib.Equal
import HaskHOL.Lib.Theorems
import HaskHOL.Lib.Simp
import HaskHOL.Lib.DRule
import HaskHOL.Lib.Tactics
import HaskHOL.Lib.Trivia
import HaskHOL.Lib.Trivia.Context


-- AST for negation normal form terms
data FOLTerm
    = FVar Int
    | FNApp Int [FOLTerm]
    deriving (Eq, Ord)

type FOLAtom = (Int, [FOLTerm])

-- Type of a MESON proof tree
data FOLGoal = Subgoal FOLAtom [FOLGoal] (Int, HOLThm) Int [(FOLTerm, Int)] 
    deriving Eq

type FOLTermEnv = [(FOLTerm, Int)]
type Tup = (FOLTermEnv, Int, Int)
type Rule = (Int, [(([FOLAtom], FOLAtom), (Int, HOLThm))])
type State = ((FOLAtom, [Rule]), Tup)

data MesonErr = Fail | Cut deriving (Show, Typeable)
instance Exception MesonErr

-- cacheing continuations.
-- HaskHOL thry caches at the global level, rather than locally as ML does, so each function does not maintain it's own cache automatically.
-- Additionally, caches are flushed 

type ContMem1 cls thry = (FOLGoal, Tup) -> HOL cls thry (FOLGoal, Tup)
type ContMemMany cls thry = ([FOLGoal], Tup) -> HOL cls thry (FOLGoal, Tup)

data DeCont1 = Return1 
             | Base DeCont 
             | Goals11 DeCont [Rule] Int [(FOLAtom, [Rule])] 
             | Cache1 DeCont1 deriving Eq

data DeCont = TopRec FOLTermEnv Int FOLTermEnv FOLAtom (Int, HOLThm) DeCont1 Int
            | Goals1 DeCont [Rule] Int [(FOLAtom, [Rule])] Int
            | Goals2 DeCont [FOLGoal]
            | Goals3 Int Int DeCont [Rule] Int [(FOLAtom, [Rule])]
            | Goals4 Int Int Int DeCont [FOLGoal] 
            | Goals5 DeCont FOLGoal 
            | CacheMany DeCont deriving Eq

cachecont :: DeCont1 -> DeCont1
cachecont = Cache1

cacheconts :: DeCont -> DeCont
cacheconts = CacheMany

-- local MESON state
type MesonState = HOLRef MesonRefs
data MesonRefs = MesonRefs
    { infs :: !Int
    , cutIn :: !Int
    , vstore :: ![(HOLTerm, Int)]
    , gstore :: ![(HOLTerm, Int)]
    , vcounter :: !Int
    , cstore :: ![(HOLTerm, Int)]
    , ccounter :: !Int
    , memory :: ![((Int, HOLTerm), HOLThm)]
    , cont1 :: ![(DeCont1, [(FOLGoal, Tup)])]
    , cont2 :: ![(DeCont, [([FOLGoal], Tup)])]
    }

initializeMeson :: TriviaCtxt thry => HOL cls thry MesonRefs
initializeMeson = 
    do falseTm <- serve [trivia| F |]
       return $! MesonRefs 0 1 [] [] 0 [(falseTm, 1)] 2 [] [] []

-- meson settings
mesonOffInc :: Int
mesonOffInc = 10000

data MesonDepth = MesonDepth !Bool deriving Typeable

deriveSafeCopy 0 'base ''MesonDepth

getMesonDepth :: Query MesonDepth Bool
getMesonDepth =
    do (MesonDepth depth) <- ask
       return depth

setMesonDepth' :: Bool -> Update MesonDepth ()
setMesonDepth' depth =
    put (MesonDepth depth)

makeAcidic ''MesonDepth ['getMesonDepth, 'setMesonDepth']

setMesonDepth :: HOL Theory thry ()
setMesonDepth =
    do acid <- openLocalStateHOL (MesonDepth False)
       updateHOL acid (SetMesonDepth' True)
       createCheckpointAndCloseHOL acid

unsetMesonDepth :: HOL Theory thry ()
unsetMesonDepth =
    do acid <- openLocalStateHOL (MesonDepth False)
       updateHOL acid (SetMesonDepth' False)
       createCheckpointAndCloseHOL acid

mesonDepth :: HOL cls thry Bool
mesonDepth =
    do acid <- openLocalStateHOL (MesonDepth False)
       depth <- queryHOL acid GetMesonDepth
       closeAcidStateHOL acid
       return depth


data MesonPRefine = MesonPRefine !Bool deriving Typeable

deriveSafeCopy 0 'base ''MesonPRefine

getMesonPRefine :: Query MesonPRefine Bool
getMesonPRefine =
    do (MesonPRefine prefine) <- ask
       return prefine

setMesonPRefine' :: Bool -> Update MesonPRefine ()
setMesonPRefine' prefine =
    put (MesonPRefine prefine)

makeAcidic ''MesonPRefine ['getMesonPRefine, 'setMesonPRefine']

setMesonPRefine :: HOL Theory thry ()
setMesonPRefine =
    do acid <- openLocalStateHOL (MesonPRefine True)
       updateHOL acid (SetMesonPRefine' True)
       createCheckpointAndCloseHOL acid

unsetMesonPRefine :: HOL Theory thry ()
unsetMesonPRefine =
    do acid <- openLocalStateHOL (MesonPRefine True)
       updateHOL acid (SetMesonPRefine' False)
       createCheckpointAndCloseHOL acid

mesonPRefine :: HOL cls thry Bool
mesonPRefine =
    do acid <- openLocalStateHOL (MesonPRefine True)
       prefine <- queryHOL acid GetMesonPRefine
       closeAcidStateHOL acid
       return prefine


data MesonBrand = MesonBrand !Bool deriving Typeable

deriveSafeCopy 0 'base ''MesonBrand

getMesonBrand :: Query MesonBrand Bool
getMesonBrand =
    do (MesonBrand brand) <- ask
       return brand

setMesonBrand' :: Bool -> Update MesonBrand ()
setMesonBrand' brand =
    put (MesonBrand brand)

makeAcidic ''MesonBrand ['getMesonBrand, 'setMesonBrand']

setMesonBrand :: HOL Theory thry ()
setMesonBrand =
    do acid <- openLocalStateHOL (MesonBrand False)
       updateHOL acid (SetMesonBrand' True)
       createCheckpointAndCloseHOL acid

unsetMesonBrand :: HOL Theory thry ()
unsetMesonBrand =
    do acid <- openLocalStateHOL (MesonBrand False)
       updateHOL acid (SetMesonBrand' False)
       createCheckpointAndCloseHOL acid

mesonBrand :: HOL cls thry Bool
mesonBrand =
    do acid <- openLocalStateHOL (MesonBrand False)
       brand <- queryHOL acid GetMesonBrand
       closeAcidStateHOL acid
       return brand


data MesonChatty = MesonChatty !Bool deriving Typeable

deriveSafeCopy 0 'base ''MesonChatty

getMesonChatty :: Query MesonChatty Bool
getMesonChatty =
    do (MesonChatty chatty) <- ask
       return chatty

setMesonChatty' :: Bool -> Update MesonChatty ()
setMesonChatty' chatty =
    put (MesonChatty chatty)

makeAcidic ''MesonChatty ['getMesonChatty, 'setMesonChatty']

setMesonChatty :: HOL Theory thry ()
setMesonChatty =
    do acid <- openLocalStateHOL (MesonChatty False)
       updateHOL acid (SetMesonChatty' True)
       createCheckpointAndCloseHOL acid

unsetMesonChatty :: HOL Theory thry ()
unsetMesonChatty =
    do acid <- openLocalStateHOL (MesonChatty False)
       updateHOL acid (SetMesonChatty' False)
       createCheckpointAndCloseHOL acid

mesonChatty :: HOL cls thry Bool
mesonChatty =
    do acid <- openLocalStateHOL (MesonChatty False)
       chatty <- queryHOL acid GetMesonChatty
       closeAcidStateHOL acid
       return chatty


data MesonSkew = MesonSkew !Int deriving Typeable

deriveSafeCopy 0 'base ''MesonSkew

getMesonSkew :: Query MesonSkew Int
getMesonSkew =
    do (MesonSkew n) <- ask
       return n

setMesonSkew' :: Int -> Update MesonSkew ()
setMesonSkew' n =
    put (MesonSkew n)

makeAcidic ''MesonSkew ['getMesonSkew, 'setMesonSkew']

setMesonSkew :: Int -> HOL Theory thry ()
setMesonSkew n =
    do acid <- openLocalStateHOL (MesonSkew 3)
       updateHOL acid (SetMesonSkew' n)
       createCheckpointAndCloseHOL acid

mesonSkew :: HOL cls thry Int
mesonSkew =
    do acid <- openLocalStateHOL (MesonSkew 3)
       depth <- queryHOL acid GetMesonSkew
       closeAcidStateHOL acid
       return depth


data MesonSplitLimit = MesonSplitLimit !Int deriving Typeable

deriveSafeCopy 0 'base ''MesonSplitLimit

getMesonSplitLimit :: Query MesonSplitLimit Int
getMesonSplitLimit =
    do (MesonSplitLimit n) <- ask
       return n

setMesonSplitLimit' :: Int -> Update MesonSplitLimit ()
setMesonSplitLimit' n =
    put (MesonSplitLimit n)

makeAcidic ''MesonSplitLimit ['getMesonSplitLimit, 'setMesonSplitLimit']

setMesonSplitLimit :: Int -> HOL Theory thry ()
setMesonSplitLimit n =
    do acid <- openLocalStateHOL (MesonSplitLimit 8)
       updateHOL acid (SetMesonSplitLimit' n)
       createCheckpointAndCloseHOL acid

mesonSplitLimit :: HOL cls thry Int
mesonSplitLimit =
    do acid <- openLocalStateHOL (MesonSplitLimit 8)
       depth <- queryHOL acid GetMesonSplitLimit
       closeAcidStateHOL acid
       return depth

-- misc stuff

qpartition :: Eq a => (a -> Bool) -> [a] -> [a] -> ([a], [a])
qpartition p m l = fromMaybe ([], l) $ partRec l
    where partRec lst =
              if lst == m then Nothing
              else case lst of
                     [] -> Nothing
                     (h:t) -> if p h then case partRec t of
                                            Nothing -> Just ([h], t)
                                            Just (yes, no) -> Just (h:yes, no)
                              else case partRec t of
                                     Just (yes, no) -> Just (yes, h:no)
                                     Nothing -> Nothing

-- nnf substitution functions

folSubst :: [(FOLTerm, Int)] -> FOLTerm -> FOLTerm
folSubst theta tm@(FVar v) = revLookupd v theta tm
folSubst theta (FNApp f args) = FNApp f $ map (folSubst theta) args

folInst :: [(FOLTerm, Int)] -> FOLAtom -> FOLAtom
folInst theta (p, args) = (p, map (folSubst theta) args)

folSubstBump :: Int -> [(FOLTerm, Int)] -> FOLTerm -> HOL cls thry FOLTerm
folSubstBump offset theta tm@(FVar v)
    | v < mesonOffInc = let v' = v + offset in
                          return . revLookupd v' theta $ FVar v'
    | otherwise = return $! revLookupd v theta tm
folSubstBump offset theta (FNApp f args) =
    liftM (FNApp f) $ mapM (folSubstBump offset theta) args 

folInstBump :: Int -> [(FOLTerm, Int)] -> FOLAtom -> HOL cls thry FOLAtom
folInstBump offset theta (p, args) =
    do args' <- mapM (folSubstBump offset theta) args
       return (p, args')


-- main nnf unification function

isTriv :: [(FOLTerm, Int)] -> Int -> FOLTerm -> Bool
isTriv env x (FVar y) = 
    (y == x) || case revLookup y env of
                  Nothing -> False
                  Just t' -> isTriv env x t'
isTriv env x (FNApp _ args) = any (isTriv env x) args && error "isTriv: cyclic"

folUnify :: Int -> FOLTerm -> FOLTerm -> [(FOLTerm, Int)] -> HOL cls thry [(FOLTerm, Int)]
folUnify offset (FNApp f fargs) (FNApp g gargs) sofar =
    if f /= g then fail "folUnify"
    else foldr2M (folUnify offset) sofar fargs gargs
folUnify offset tm1 (FVar x) sofar =
    let x' = x + offset in
      case revLookup x' sofar of
        Just tm2' -> folUnify 0 tm1 tm2' sofar
        Nothing   -> return $! if isTriv sofar x' tm1 then sofar
                               else (tm1, x'):sofar
folUnify offset (FVar x) tm2 sofar =
    case revLookup x sofar of
      Just tm1' -> folUnify offset tm1' tm2 sofar
      Nothing   -> do tm2' <- folSubstBump offset [] tm2
                      return $! if isTriv sofar x tm2' then sofar
                                else (tm2', x):sofar


-- test for nnf equality
folEq :: [(FOLTerm, Int)] -> FOLTerm -> FOLTerm -> HOL cls thry Bool
folEq insts tm1 tm2 =
    if tm1 == tm2 then return True
    else case (tm1, tm2) of
             (FNApp f fargs, FNApp g gargs) ->
                 do conds <- zipWithM (folEq insts) fargs gargs
                    return $! f == g && and conds
             (_, FVar x) ->
                 case revLookup x insts of
                   Just tm2' -> folEq insts tm1 tm2'
                   Nothing   -> return (isTriv insts x tm1) <|> return False
             (FVar x, _) ->
                 case revLookup x insts of
                   Just tm1' -> folEq insts tm1' tm2
                   Nothing   -> return (isTriv insts x tm2) <|> return False

folAtomEq :: [(FOLTerm, Int)] -> FOLAtom -> FOLAtom -> HOL cls thry Bool
folAtomEq insts (p1, args1) (p2, args2) =
    if p1 /= p2 then return False
    else do conds <- zipWithM (folEq insts) args1 args2
            return $! and conds

-- check ancestor list for repetition
checkan :: FOLTermEnv -> FOLAtom -> [Rule] -> HOL cls thry [Rule]
checkan insts (p, a) ancestors =
    let p' = negate p
        t' = (p', a) in
      case lookup p' ancestors of
        Nothing -> return ancestors
        Just ours -> do conds <- mapM (folAtomEq insts t' . snd . fst) ours
                        if or conds
                           then fail "checkan"
                           else return ancestors


-- insert new goal's negation in ancestor clause, given refinement
insertan :: BoolCtxt thry => FOLTermEnv -> FOLAtom -> [Rule] -> HOL cls thry [Rule]
insertan insts (p, a) ancestors =
    let p' = negate p
        t' = (p', a)
        (ourancp, otheranc) = fromMaybe ((p', []), ancestors) $ 
                                remove (\ (pr, _) -> pr ==  p') ancestors
        ouranc = snd ourancp in
      do conds <- mapM (\ u -> folAtomEq insts t' (snd $ fst u)) ouranc
         if or conds
            then fail "insertan: loop"
            else do th <- thmTRUTH
                    return ((p', (([], t'), (0, th)):ouranc):otheranc)
        
        
-- apply a multi-level "graph" instantiation

folSubstPartial :: [(FOLTerm, Int)] -> FOLTerm -> FOLTerm
folSubstPartial insts tm@(FVar v) = 
    case revLookup v insts of
      Nothing -> tm
      Just t -> folSubstPartial insts t
folSubstPartial insts (FNApp f args) = 
    FNApp f $ map (folSubstPartial insts) args


-- tease apart local and global instantiations.
separateInsts2 :: Int -> FOLTermEnv -> FOLTermEnv -> (FOLTermEnv, FOLTermEnv)
separateInsts2 offset old new =
    let (loc, glob) = qpartition (\ (_, v) -> offset <= v) old new in
      if glob == old 
      then (map (first (folSubstPartial new)) loc, old)
      else (map (first (folSubstPartial new)) loc,
            map (first (folSubstPartial new)) glob)
               
mkNegated :: FOLAtom -> FOLAtom
mkNegated (p, a) = (negate p, a)

mkContraposes :: Int -> HOLThm -> [FOLAtom] -> [FOLAtom] -> [(([FOLAtom], FOLAtom), (Int, HOLThm))] ->
                 [(([FOLAtom], FOLAtom), (Int, HOLThm))]
mkContraposes _ _ _ [] sofar = sofar
mkContraposes n th used (h:t) sofar = 
    let nw = ((map mkNegated (used ++ t), h), (n, th)) in
      mkContraposes (n + 1) th (used ++ [h]) t (nw:sofar)


-- optimize set of clausesa
optimizeRules :: [Rule] -> [Rule]
optimizeRules = map (second optimizeClauseOrder)
    where optimizeClauseOrder = 
              sort (\ ((l1, _), _) ((l2, _), _) -> length l1 <= length l2)

convDISJ_AC :: TheoremsCtxt thry => Conversion cls thry
convDISJ_AC = convAC thmDISJ_ACI

convImp :: TriviaCtxt thry => Conversion cls thry
convImp = convREWR convImp_pth
  where convImp_pth :: TriviaCtxt thry => HOL cls thry HOLThm
        convImp_pth = cacheProof "convImp_pth" ctxtTrivia $
            ruleTAUT [str| a \/ b <=> ~b ==> a |]

convPush :: TriviaCtxt thry => Conversion cls thry
convPush = convGEN_REWRITE convTOP_SWEEP [convPush_pth1, convPush_pth2]
  where convPush_pth1 :: TriviaCtxt thry => HOL cls thry HOLThm
        convPush_pth1 = cacheProof "convPush_pth1" ctxtTrivia $
            ruleTAUT [str| ~(a \/ b) <=> ~a /\ ~b |]

        convPush_pth2 :: TriviaCtxt thry => HOL cls thry HOLThm
        convPush_pth2 = cacheProof "convPush_pth2" ctxtTrivia $
            ruleTAUT "~(~a) <=> a"

convPull :: TriviaCtxt thry => Conversion cls thry
convPull = convGEN_REWRITE convDEPTH [convPull_pth]
  where convPull_pth :: TriviaCtxt thry => HOL cls thry HOLThm
        convPull_pth = cacheProof "convPull_pth" ctxtTrivia $
            ruleTAUT [str| ~a \/ ~b <=> ~(a /\ b) |]

convImf :: TriviaCtxt thry => Conversion cls thry
convImf = convREWR convImf_pth
  where convImf_pth :: TriviaCtxt thry => HOL cls thry HOLThm
        convImf_pth = cacheProof "convImf_pth" ctxtTrivia $
            ruleTAUT "~p <=> p ==> F"


-- translate saved proof back to HOL
holNegate :: HOLTerm -> HOL cls thry HOLTerm
holNegate tm = liftMaybe "holNegate" (destNeg tm) <|> mkNeg tm

mergeInst :: (FOLTerm, Int) -> [(FOLTerm, Int)] -> [(FOLTerm, Int)]
mergeInst (t, x) current =
    let t' = folSubst current t in
      (t', x) : current

finishRule :: TriviaCtxt thry => HOLThm -> HOL cls thry HOLThm
finishRule thm = ruleGEN_REWRITE id [finishRule_pth1, finishRule_pth2]  thm
  where finishRule_pth1 :: TriviaCtxt thry => HOL cls thry HOLThm
        finishRule_pth1 = cacheProof "finishRule_pth1" ctxtTrivia $
            ruleTAUT "(~p ==> p) <=> p"

        finishRule_pth2 :: TriviaCtxt thry => HOL cls thry HOLThm
        finishRule_pth2 = cacheProof "finishRule_pth2" ctxtTrivia $
            ruleTAUT "(p ==> ~p) <=> ~p"
                                
-- create equality axioms

convImpElim :: TriviaCtxt thry => Conversion cls thry
convImpElim = convREWR convImpElim_pth
  where convImpElim_pth :: TriviaCtxt thry => HOL cls thry HOLThm
        convImpElim_pth = cacheProof "convImpElim_pth" ctxtTrivia $
            ruleTAUT [str| (a ==> b) <=> ~a \/ b |]

ruleEqElim :: TriviaCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleEqElim thm = ruleMATCH_MP ruleEqElim_pth thm
  where ruleEqElim_pth :: TriviaCtxt thry => HOL cls thry HOLThm
        ruleEqElim_pth = cacheProof "ruleEqElim_pth" ctxtTrivia $
            ruleTAUT [str| (a <=> b) ==> b \/ ~a |]


createEquivalenceAxioms :: TriviaCtxt thry => (HOLTerm, Int) 
                        -> HOL cls thry [HOLThm]
createEquivalenceAxioms (eq, _) =
    (do ths@(th:_) <- sequence eqThms
        fromJustM $ do veqTm <- rator =<< rator (concl th)
                       tyins <- typeMatch (typeOf veqTm) (typeOf eq) ([], [], [])
                       return $! map (primINST_TYPE_FULL tyins) ths)
    <?> "createEquivalenceAxioms"
  where eqThms :: TriviaCtxt thry => [HOL cls thry HOLThm]
        eqThms = cacheProofs ["eqThms1", "eqThms2"] ctxtTrivia $
            ruleCONJUNCTS =<< 
              prove [str| (x:A = x) /\ (~(x:A = y) \/ ~(x = z) \/ (y = z)) |]
                (tacREWRITE_NIL `_THEN` 
                 tacASM_CASES "x:A = y " `_THEN`
                 tacASM_REWRITE_NIL `_THEN`
                 tacCONV (Conv ruleTAUT))
         

tmConsts :: HOLTerm -> [(HOLTerm, Int)] -> [(HOLTerm, Int)]
tmConsts tm acc =
    let (fn, args) = stripComb tm in
      if null args then acc
      else foldr tmConsts (insert (fn, length args) acc) args

fmConsts :: HOLTerm -> ([(HOLTerm, Int)], [(HOLTerm, Int)]) -> Maybe ([(HOLTerm, Int)], [(HOLTerm, Int)])
fmConsts tm acc@(preds, funs) =
    case destForall tm of
      Just (_, x) -> fmConsts x acc
      Nothing -> 
          case destExists tm of
            Just (_, x) -> fmConsts x acc
            Nothing ->
                case destConj tm of
                  Just (l, r) -> fmConsts l =<< fmConsts r acc
                  Nothing ->
                      case destDisj tm of
                        Just (l, r) -> fmConsts l =<< fmConsts r acc
                        Nothing ->
                            case destImp tm of
                              Just (l, r) -> fmConsts l =<< fmConsts r acc
                              Nothing ->
                                  case destNeg tm of
                                    Just x -> fmConsts x acc
                                    Nothing ->
                                        case destEq tm of
                                          Just (l, r) -> if typeOf l == tyBool
                                                         then fmConsts r =<< fmConsts l acc
                                                         else catchCase tm
                                          Nothing -> catchCase tm
                                              
    where catchCase t = let (p, args) = stripComb t in
                          Just $ if null args then acc
                                 else (insert (p, length args) preds,
                                       foldr tmConsts funs args)

createCongruenceAxiom :: TriviaCtxt thry => Bool -> (HOLTerm, Int) 
                      -> HOL cls thry HOLThm
createCongruenceAxiom pflag (tm, len) =
    let (atys, _) = splitList destFunTy $ typeOf tm in
      (do (ctys, _) <- fromJustM $ chopList len atys
          largs <- mapM genVar ctys
          rargs <- mapM genVar ctys
          let th1 = primREFL tm
          ths <- mapM (\ (x, y) -> do eq <- mkEq x y
                                      fromRightM $ primASSUME eq) (zip largs rargs)
          th2 <- fromRightM $ foldlM primMK_COMB th1 ths
          th3 <- if pflag then ruleEqElim th2 else return th2
          foldrM (\ e th -> ruleCONV convImpElim =<< ruleDISCH e th) th3 (hyp th3))
      <?> "createCongruenceAxiom"

createEqualityAxioms :: TriviaCtxt thry => [HOLTerm] -> HOL cls thry [HOLThm]
createEqualityAxioms tms =
    do (preds, funs) <- liftMaybe "createEqualityAxioms" $ foldrM fmConsts ([], []) tms
       let (eqs0, noneqs) = partition eqPred preds
       if null eqs0 
          then return []
          else do pcongs <- mapM (createCongruenceAxiom True) noneqs
                  fcongs <- mapM (createCongruenceAxiom False) funs
                  (preds1, _) <- liftMaybe "createEqualityAxioms" $ foldrM fmConsts ([], []) $ map concl (pcongs ++ fcongs)
                  let eqs1 = filter eqPred preds1
                      eqs = eqs0 `union` eqs1
                  equivs <- foldrM (\ x ys -> do xs <- createEquivalenceAxioms x
                                                 return $ union xs ys) [] eqs
                  return $! equivs ++ pcongs ++ fcongs
    where eqPred (Const "=" _, _) = True
          eqPred _ = False
    
-- brand's transformation

subtermsIrrefl :: [HOLTerm] -> HOLTerm -> [HOLTerm] -> [HOLTerm]
subtermsIrrefl _ Var{} acc = acc
subtermsIrrefl _ Const{} acc = acc
subtermsIrrefl lconsts tm acc =
    let (_, args) = stripComb tm in
      foldr (subtermsRefl lconsts) acc args

subtermsRefl :: [HOLTerm] -> HOLTerm -> [HOLTerm] -> [HOLTerm]
subtermsRefl lconsts tm@Var{} acc =
    if tm `elem` lconsts then insert tm acc else acc
subtermsRefl _ tm@Const{} acc = insert tm acc
subtermsRefl lconsts tm acc =
    let (_, args) = stripComb tm in
      foldr (subtermsRefl lconsts) (insert tm acc) args

ruleCLAUSIFY :: TriviaCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleCLAUSIFY = ruleCONV (convREWR ruleCLAUSIFY_pth)
  where ruleCLAUSIFY_pth :: TriviaCtxt thry => HOL cls thry HOLThm
        ruleCLAUSIFY_pth = cacheProof "ruleCLAUSIFY_pth" ctxtTrivia $
            ruleTAUT [str| a ==> b <=> ~a \/ b |]


ruleBRAND :: TriviaCtxt thry => [HOLTerm] -> HOLThm -> HOL cls thry HOLThm
ruleBRAND [] th = return th
ruleBRAND (tm:tms) th =
    do gv <- genVar $ typeOf tm
       eq <- mkEq gv tm
       th1 <- fromRightM $ ruleSYM #<< primASSUME eq
       th' <- ruleCLAUSIFY =<< ruleDISCH eq =<< ruleSUBS [th1] th
       tms' <- liftO $ mapM (subst [(tm, gv)]) tms
       ruleBRAND tms' th'

ruleBRAND_CONGS :: TriviaCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleBRAND_CONGS th =
    let lconsts = catFrees $ hyp th
        lits = disjuncts $ concl th
        atoms = map (\ t -> case destNeg t of
                              Just t' -> t'
                              _ -> t) lits
        (eqs, noneqs) = partition partFun atoms
        acc = foldr (subtermsIrrefl lconsts) [] noneqs
        uts = foldr (\ x ys -> foldr (subtermsIrrefl lconsts) ys . snd $ stripComb x) acc eqs
        sts = sort (\ s t -> not $ s `freeIn` t) uts in
      ruleBRAND sts th
    where partFun t = case stripComb t of
                        (Const "=" _, _) -> True
                        _ -> False

ruleBRANDE :: TriviaCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleBRANDE th =
    let tm = concl th in
      (do (l, r) <- fromJustM $ destEq tm
          gv <- genVar $ typeOf l
          eq <- mkEq r gv
          rtm <- fromJustM $ rator tm
          th1 <- fromRightM $ ruleAP_TERM rtm #<< primASSUME eq
          ruleCLAUSIFY =<< ruleDISCH eq =<< fromRightM (primEQ_MP th1 th))
      <?> "ruleBRANDE"

ruleLDISJ_CASES :: BoolCtxt thry => HOLThm -> HOLThm -> HOLThm -> HOL cls thry HOLThm
ruleLDISJ_CASES th lth rth =
    do th1 <- ruleDISJ1 lth $ concl rth
       th2 <- ruleDISJ2 (concl lth) rth
       ruleDISJ_CASES th th1 th2
      
          
ruleASSOCIATE :: TriviaCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleASSOCIATE = ruleCONV (convREWR ruleASSOCIATE_pth)
  where ruleASSOCIATE_pth :: TriviaCtxt thry => HOL cls thry HOLThm
        ruleASSOCIATE_pth = cacheProof "ruleASSOCIATE_pth" ctxtTrivia $
          ruleGSYM thmDISJ_ASSOC


ruleBRAND_TRANS :: TriviaCtxt thry => HOLThm -> HOL cls thry [HOLThm]
ruleBRAND_TRANS th =
    let tm = concl th in
      (case destDisj tm of
         Just (l, r) -> 
             if isEq l 
             then do lth <- fromRightM $ primASSUME l
                     lth1 <- ruleBRANDE lth
                     lth2 <- ruleBRANDE #<< ruleSYM lth
                     rth <- ruleBRAND_TRANS =<< fromRightM (primASSUME r)
                     ls <- mapM (ruleASSOCIATE <=< ruleLDISJ_CASES th lth1) rth
                     rs <- mapM (ruleASSOCIATE <=< ruleLDISJ_CASES th lth2) rth
                     return $! ls ++ rs
             else do rth <- ruleBRAND_TRANS =<< fromRightM (primASSUME r)
                     lth <- fromRightM $ primASSUME l
                     mapM (ruleLDISJ_CASES th lth) rth
         Nothing ->
             if isEq tm
             then sequence [ruleBRANDE th, ruleBRANDE #<< ruleSYM th]
             else return [th])
    <?> "ruleBRAND_TRANS"

findEqs :: HOLTerm -> [HOLTerm]
findEqs = findTerms (\ t -> case t of
                              (Const "=" _) -> True
                              _ -> False)

ruleREFLEXATE :: [HOLThm] -> HOL cls thry [HOLThm]
ruleREFLEXATE ths =
    let eqs = foldr (union . findEqs . concl) [] ths in
      do tys <- liftMaybe "ruleREFLEXATE" $ mapM tyFun eqs
         gvs <- mapM genVar tys
         return $! foldr (\ v acc -> (primREFL v : acc)) ths gvs
    where tyFun (Const _ (TyApp _ (ty:_))) = Just ty
          tyFun _ = Nothing
        
performBrandModification :: TriviaCtxt thry => [HOLThm] -> HOL cls thry [HOLThm]
performBrandModification ths =
    if any (isJust . findTerm isEq . concl) ths
    then do ths' <- mapM ruleBRAND_CONGS ths
            ths'' <- foldrM (\ x ys -> do xs <- ruleBRAND_TRANS x
                                          return $! union' (==) xs ys) [] ths'
            ruleREFLEXATE ths''
    else return ths

grabConstants :: HOLTerm -> [HOLTerm] -> Maybe [HOLTerm]
grabConstants tm acc
    | isForall tm || isExists tm = 
        flip grabConstants acc =<< body =<< rand tm
    | isIff tm || isImp tm || isConj tm || isDisj tm =
        do rtm <- rand tm
           grabConstants rtm =<< flip grabConstants acc =<< lHand tm
    | isNeg tm =
        flip grabConstants acc =<< rand tm
    | otherwise =
        return $! findTerms isConst tm `union` acc

matchConsts :: (HOLTerm, HOLTerm) -> Maybe SubstTrip
matchConsts (Const s1 ty1, Const s2 ty2)
    | s1 == s2 = typeMatch ty1 ty2 ([], [], [])
    | otherwise = Nothing
matchConsts _ = Nothing

polymorph :: [HOLTerm] -> HOLThm -> HOL cls thry [HOLThm]
polymorph mconsts th =
    let tvs = typeVarsInTerm (concl th) \\ (unions . map typeVarsInTerm $ hyp th) in
      if null tvs then return [th]
      else do tyins <- liftMaybe "polymorph" $ 
                         do pconsts <- grabConstants (concl th) []
                            mapFilterM matchConsts $ allpairs (,) pconsts mconsts
              let tyins' = map (`primINST_TYPE_FULL` th) tyins
                  ths' = setify' ((<=) `on` destThm) (==) tyins'
              if null ths'
                 then printDebug "No useful-looking instantiation of lemma" $ return [th]
                 else return ths'

polymorphAll :: [HOLTerm] -> [HOLThm] -> [HOLThm] -> HOL cls thry [HOLThm]
polymorphAll _ [] acc = return acc
polymorphAll mconsts (th:ths) acc =
    do ths' <- polymorph mconsts th
       mconsts' <- liftMaybe "polymorphAll" $ foldrM (grabConstants . concl) mconsts ths'
       polymorphAll mconsts' ths (union' (==) ths' acc)

tacPOLY_ASSUME :: BoolCtxt thry => [HOLThm] -> Tactic cls thry
tacPOLY_ASSUME ths gl@(Goal asl _) =
    do mconsts <- liftMaybe "tacPOLY_ASSUME" $ foldrM (grabConstants . concl . snd) [] asl
       ths' <- polymorphAll mconsts ths []
       _MAP_EVERY tacASSUME ths' gl

tacCONJUNCTS_THEN' :: BoolCtxt thry => ThmTactic cls thry -> ThmTactic cls thry
tacCONJUNCTS_THEN' ttac cth gl =
    do cthl <- ruleCONJUNCT1 cth
       cthr <- ruleCONJUNCT2 cth
       (ttac cthl `_THEN` ttac cthr) gl

tacPURE_MESON :: TriviaCtxt thry => MesonState -> Int -> Int -> Int 
              -> Tactic cls thry
tacPURE_MESON ref minVal maxVal inc goal =
    do resetVars
       resetConsts
       flushCaches
       (_FIRST_ASSUM tacCONTR `_ORELSE`
        (\ g@(Goal asl _) -> do th <- simpleMesonRefute $ map snd asl
                                tacACCEPT th g)) goal

    where 
      simpleMesonRefute :: TriviaCtxt thry => [HOLThm] -> HOL cls thry HOLThm
      simpleMesonRefute ths =
          do dcutin <- liftM cutIn $ readHOLRef ref
             clearContraposCache
             modifyHOLRef ref $ \ st -> st { infs = 0 }
             dflag <- mesonDepth
             bflag <- mesonBrand
             when dflag . modifyHOLRef ref $ \ st -> st { cutIn = 100001 }
             ths' <- if bflag then performBrandModification ths
                     else liftM (ths ++) . createEqualityAxioms $ map concl ths
             rules <- liftM optimizeRules $ folOfHOLClauses ths'
             (proof, (insts, _, _)) <- solveGoal rules dflag inc (1, [])
             modifyHOLRef ref $ \ st -> st { cutIn = dcutin }
             mesonToHOL insts proof
      
      solveGoal :: BoolCtxt thry => [Rule] -> Bool -> Int -> FOLAtom -> HOL cls thry (FOLGoal, Tup)
      solveGoal rules incdepth incsize g = solve minVal (g,[])
          where solve n gl =
                    if n > maxVal then fail "solveGoal: too deep"
                    else do cflag <- mesonChatty
                            _ <- if cflag 
                                 then do is <- liftM infs $ readHOLRef ref
                                         printDebug (show is ++ " inferences so far. " ++
                                                     "Searching with maximum size " ++ show n ++ ".") $ return ()
                                 else do is <- liftM infs $ readHOLRef ref
                                         printDebug (show is ++ "..") $ return ()
                            (do gi <- if incdepth then expandGoal rules gl n 100000 Return1
                                      else expandGoal rules gl 100000 n Return1
                                _ <- if cflag
                                     then do is <- liftM infs $ readHOLRef ref
                                             printDebug ("Goal solved with " ++ show is ++ " inferences.") $ return ()
                                     else do is <- liftM infs $ readHOLRef ref
                                             printDebug ("solved at " ++ show is) $ return ()
                                return gi) <|> solve (n + incsize) gl

      expandGoal :: BoolCtxt thry => [Rule] -> (FOLAtom, [Rule]) -> Int -> Int -> DeCont1 -> HOL cls thry (FOLGoal, Tup)
      expandGoal rules g maxdep maxinf = 
          expandGoalRec rules maxdep (g, ([], 2 * mesonOffInc, maxinf))

      expandGoalRec :: BoolCtxt thry => [Rule] -> Int -> State -> DeCont1 -> HOL cls thry (FOLGoal, Tup)
      expandGoalRec rules depth state@((g, _), (insts, offset, size)) cont =
          if depth < 0 then fail "expandGoal: too deep"
          else mesonExpand rules state
               (\ apprule newstate@(_, (pinsts, _, _)) ->
                    let cont' = cacheconts $ TopRec insts offset pinsts g apprule cont size in
                      expandGoals rules (depth - 1) newstate cont')

      expandGoals :: BoolCtxt thry => [Rule] -> Int -> ([(FOLAtom, [Rule])], Tup) -> DeCont -> HOL cls thry (FOLGoal, Tup)
      expandGoals _ _ ([], tup) cont = deCont cont ([], tup)
      expandGoals rules depth (g:[], tup) cont = expandGoalRec rules depth (g, tup) $ Base cont
      expandGoals rules depth (gl@(g:gs), tup@(insts, offset, size)) cont =
          do dcutin <- liftM cutIn $ readHOLRef ref
             skew <- mesonSkew
             if size >= dcutin
                then let lsize = size `div` skew
                         rsize = size - lsize in
                       do (lgoals, rgoals) <- liftMaybe "expandGoals" $ chopList (length gl `div` 2) gl
                          (let cont' = cacheconts $ Goals1 cont rules depth rgoals rsize in
                             expandGoals rules depth (lgoals, (insts, offset, lsize)) cont')
                            <|> (let cont' = cacheconts $ Goals3 rsize lsize cont rules depth lgoals in
                                  expandGoals rules depth (rgoals, (insts, offset, lsize)) cont')
                else let cont' = cachecont $ Goals11 cont rules depth gs in
                       expandGoalRec rules depth (g, tup) cont'

      mesonExpand :: forall cls thry. BoolCtxt thry => [Rule] -> State -> ((Int, HOLThm) -> ([(FOLAtom, [Rule])], Tup) -> 
                     HOL cls thry (FOLGoal, Tup)) -> HOL cls thry (FOLGoal, Tup)
      mesonExpand rules ((g, ancestors), tup@(insts, offset, size)) cont =
          let pr = fst g in
            do newancestors <- insertan insts g ancestors
               let newstate = ((g, newancestors), tup)
               pflag <- mesonPRefine
               (if pflag && pr > 0 then throwHOL Fail
                else case lookup pr ancestors of
                       Nothing -> throwHOL Fail
                       Just arules -> mesonExpandCont 0 arules newstate cont) `catchHOL` errCase pr newstate
          where errCase :: Int -> State -> MesonErr -> HOL cls thry (FOLGoal, Tup)
                errCase _ _ Cut = fail "mesonExpand"
                errCase pr newstate Fail = 
                    do prule <- liftMaybe "mesonExpand" $ lookup pr rules
                       let crules = filter (\ ((h, _), _) -> length h <= size) prule
                       mesonExpandCont offset crules newstate cont

      mesonExpandCont :: Int -> [(([FOLAtom], FOLAtom), b)] -> State -> 
                         (b -> ([(FOLAtom, [Rule])], Tup) -> HOL cls thry (FOLGoal, Tup)) -> HOL cls thry (FOLGoal, Tup)
      mesonExpandCont loffset rules state cont =
          tryFind (\ r -> cont (snd r) =<< mesonSingleExpand loffset r state) rules 
          <|> throwHOL Fail

      mesonSingleExpand :: Int -> (([FOLAtom], FOLAtom), b) -> State -> HOL cls thry ([(FOLAtom, [Rule])], Tup)
      mesonSingleExpand loffset rule (((_, ftms), ancestors), (insts, offset, size)) =
          let ((hyps, conc), _) = rule in
            do allEnv <- foldl2M (\ c a b -> folUnify loffset a b c) 
                           insts ftms $ snd conc
               let (loc, glob) = separateInsts2 offset insts allEnv
                   mkIHyp h = do h' <- folInstBump offset loc h
                                 an <- checkan insts h' ancestors
                                 return (h', an)
               newhyps <- mapM mkIHyp hyps
               modifyHOLRef ref $ \ st -> st { infs = 1 + infs st }
               return (newhyps, (glob, offset + mesonOffInc, size-length hyps))

      flushCaches :: HOL cls thry ()
      flushCaches =
          modifyHOLRef ref $ \ st -> st { cont1 = [], cont2 = [] }

      replaceMem1 :: DeCont1 -> [(FOLGoal, Tup)] -> HOL cls thry ()
      replaceMem1 f m = 
          modifyHOLRef ref $ \ st -> st { cont1 = replaceMemRec $ cont1 st }
              where replaceMemRec [] = [(f, m)]
                    replaceMemRec (x:xs)
                        | fst x == f = (f, m) : xs
                        | otherwise = x : replaceMemRec xs

      replaceMem :: DeCont -> [([FOLGoal], Tup)] -> HOL cls thry ()
      replaceMem f m = 
          modifyHOLRef ref $ \ st -> st { cont2 = replaceMemRec $ cont2 st }
              where replaceMemRec [] = [(f, m)]
                    replaceMemRec (x:xs)
                        | fst x == f = (f, m) : xs
                        | otherwise = x : replaceMemRec xs

      deCont1 :: BoolCtxt thry => DeCont1 -> ContMem1 cls thry
      deCont1 Return1 x = return x
      deCont1 (Base cont) (g', stup) = deCont cont ([g'], stup)
      deCont1 (Goals11 cont rules depth gs) (g', stup) = 
          let cont' = cacheconts $ Goals5 cont g' in
            expandGoals rules depth (gs, stup) cont'
      deCont1 (Cache1 cont) input@(_, (insts, _, size)) =
          do cache <- liftM cont1 $ readHOLRef ref
             case lookup cont cache of
               Nothing -> 
                 do modifyHOLRef ref $ \ st -> st { cont1 = [(cont, [input])] }
                    deCont1 cont input
               Just m -> 
                 do dflag <- mesonDepth
                    if any (\ (_, (insts', _, size')) -> insts == insts' && (size <= size' || dflag)) m
                       then fail "cacheconts"
                       else do replaceMem1 cont m
                               deCont1 cont input

      deCont :: BoolCtxt thry => DeCont -> ContMemMany cls thry
      deCont (TopRec insts offset pinsts g apprule cont size)
             (gs, (newinsts, newoffset, newsize)) =
          let (locin, globin) = separateInsts2 offset pinsts newinsts
              g' = Subgoal g gs apprule offset locin in
            if globin == insts && null gs
            then deCont1 cont (g', (globin, newoffset, size)) <|> throwHOL Cut
            else deCont1 cont (g', (globin, newoffset, newsize)) <|> throwHOL Fail
      deCont (Goals1 cont rules depth rgoals rsize) (lg', (i, off, n)) =
          let cont' = cacheconts $ Goals2 cont lg' in
            expandGoals rules depth (rgoals, (i, off, n + rsize)) cont'
      deCont (Goals2 cont lg') (rg', ztup) = 
          deCont cont (lg' ++ rg', ztup)
      deCont (Goals3 rsize lsize cont rules depth lgoals) (rg', (i, off, n)) =
          let cont' = cacheconts $ Goals4 n rsize lsize cont rg' in
            expandGoals rules depth (lgoals, (i, off, n + rsize)) cont'
      deCont (Goals4 n rsize lsize cont rg') (lg', ztup@(_, _, fsize)) =
          if n + rsize <= lsize + fsize
          then fail "repetition of demigoal pair"
          else deCont cont (lg' ++ rg', ztup)
      deCont (Goals5 cont g') (gs', ftup) =
          deCont cont (g':gs', ftup)
      deCont (CacheMany cont) input@(_, (insts, _, size)) =
          do cache <- liftM cont2 $ readHOLRef ref
             case lookup cont cache of
               Nothing -> 
                 do modifyHOLRef ref $ \ st -> st { cont2 = [(cont, [input])] }
                    deCont cont input
               Just m -> 
                 do dflag <- mesonDepth
                    if any (\ (_, (insts', _, size')) -> insts == insts' && (size <= size' || dflag)) m
                       then fail "cacheconts"
                       else do replaceMem cont m
                               deCont cont input

      clearContraposCache :: HOL cls thry ()
      clearContraposCache =
          modifyHOLRef ref $ \ st -> st { memory = [] }

      makeHOLContrapos :: TriviaCtxt thry => Int -> HOLThm 
                       -> HOL cls thry HOLThm
      makeHOLContrapos n th =
          let tm = concl th
              key = (n, tm) in
            do m <- liftM memory $ readHOLRef ref
               case lookup key m of
                 Just res -> return res
                 Nothing -> if n < 0 then ruleCONV (convPull `_THEN` convImf) th
                            else let djs = disjuncts tm in
                                   do acth <- if n == 0 then return th
                                              else case chopList n djs of
                                                     Just (ldjs, rdj:rdjs) -> 
                                                       let ndjs = rdj : (ldjs ++ rdjs) in
                                                         do th1 <- runConv convDISJ_AC =<< mkEq tm =<< listMkDisj ndjs
                                                            fromRightM $ primEQ_MP th1 th
                                                     _ -> fail "makeHOLContrapos"
                                      fth <- if length djs == 1 then return acth
                                             else ruleCONV (convImp `_THEN` convPush) acth
                                      modifyHOLRef ref $ \ st -> st { memory = (key, fth) : m }
                                      return fth

      resetVars :: HOL cls thry ()
      resetVars = modifyHOLRef ref $ \ st -> st { vstore = [], gstore = [], vcounter = 0 }

      resetConsts :: TriviaCtxt thry => HOL cls thry ()
      resetConsts = 
          do falseTm <- serve [trivia| F |]
             modifyHOLRef ref $ \ st -> st { cstore = [(falseTm, 1)], ccounter = 2 }

      incVCounter :: HOL cls thry Int
      incVCounter = 
          do n <- liftM vcounter $ readHOLRef ref
             let m = n + 1
             if m >= mesonOffInc 
                then fail "incVCounter: too many variables"
                else do modifyHOLRef ref $ \ st -> st { vcounter = m }
                        return n

      mesonToHOL :: TriviaCtxt thry => [(FOLTerm, Int)] 
                 -> FOLGoal -> HOL cls thry HOLThm
      mesonToHOL insts (Subgoal g gs (n, th) _ locin) =
          let newInsts = foldr mergeInst insts locin
              g' = folInst newInsts g in
            do holG <- holOfLiteral g'
               ths <- mapM (mesonToHOL newInsts) gs
               truthTh <- thmTRUTH
               hth <- if th == truthTh then liftEither "mesonToHOL" $ primASSUME holG
                      else do cth <- makeHOLContrapos n th
                              if null ths 
                                 then return cth
                                 else ruleMATCH_MP cth =<< foldr1M ruleCONJ ths
               ith <- rulePART_MATCH Just hth holG
               tm <- holNegate $ concl ith
               finishRule =<< ruleDISCH tm ith

      folOfHOLClause :: HOLThm -> HOL cls thry [(([FOLAtom], FOLAtom), (Int, HOLThm))]
      folOfHOLClause th =
          let lconsts = catFrees $ hyp th
              tm = concl th
              hlits = disjuncts tm in
            do flits <- mapM (folOfLiteral [] lconsts) hlits
               let basics = mkContraposes 0 th [] flits []
               return $ if all (\ (p, _) -> p < 0) flits
                        then ((map mkNegated flits, (1, [])), (-1, th)):basics
                        else basics

      folOfHOLClauses :: [HOLThm] -> HOL cls thry [Rule]
      folOfHOLClauses thms =
          do rawrules <- foldrM (\ x ys -> do xs <- folOfHOLClause x
                                              return $! union xs ys) [] thms
             let prs = setify $ map (fst . snd . fst) rawrules
                 prules = map (\ t -> (t, filter ((== t) . fst . snd . fst) rawrules)) prs
                 srules = sort (\ (p, _) (q, _) -> abs p <= abs q) prules
             return srules

      holOfTerm :: FOLTerm -> HOL cls thry HOLTerm
      holOfTerm (FVar v) = holOfVar v
      holOfTerm (FNApp f args) =
          do f' <- holOfConst f
             args' <- mapM holOfTerm args
             liftEither "holOfTerm" $ listMkComb f' args'

      folOfTerm :: [HOLTerm] -> [HOLTerm] -> HOLTerm -> HOL cls thry FOLTerm
      folOfTerm env consts tm =
          if isVar tm && (tm `notElem` consts)
          then liftM FVar $ folOfVar tm
          else let (f, args) = stripComb tm in
                 if f `elem` env then fail "folOfTerm: higher order"
                 else do ff <- folOfConst f
                         args' <- mapM (folOfTerm env consts) args
                         return $! FNApp ff args'

      holOfAtom :: FOLAtom -> HOL cls thry HOLTerm
      holOfAtom (p, args) =
          do p' <- holOfConst p
             args' <- mapM holOfTerm args
             liftEither "holOfAtom" $ listMkComb p' args'

      folOfAtom :: [HOLTerm] -> [HOLTerm] -> HOLTerm -> HOL cls thry FOLAtom
      folOfAtom env consts tm =
          let (f, args) = stripComb tm in
            if f `elem` env then fail "folOfAtom: higher order"
            else do ff <- folOfConst f
                    args' <- mapM (folOfTerm env consts) args
                    return (ff, args')

      holOfLiteral :: FOLAtom -> HOL cls thry HOLTerm
      holOfLiteral fa@(p, args)
          | p < 0 = mkNeg =<< holOfAtom (negate p, args)
          | otherwise = holOfAtom fa

      folOfLiteral :: [HOLTerm] -> [HOLTerm] -> HOLTerm -> HOL cls thry FOLAtom
      folOfLiteral env consts tm =
          case destNeg tm of
            Nothing -> folOfAtom env consts tm
            Just tm' -> do (p, a) <- folOfAtom env consts tm'
                           return (negate p, a)

      holOfConst :: Int -> HOL cls thry HOLTerm
      holOfConst c =
          do cs <- liftM cstore $ readHOLRef ref
             case revLookup c cs of
               Nothing -> fail "holOfConst"
               Just x  -> return x

      folOfConst :: HOLTerm -> HOL cls thry Int
      folOfConst c =
          do currentconsts <- liftM cstore $ readHOLRef ref
             case lookup c currentconsts of
               Nothing -> do n <- liftM ccounter $ readHOLRef ref
                             modifyHOLRef ref $ \ st -> st { ccounter = n + 1, cstore = (c, n):currentconsts }
                             return n
               Just x  -> return x

      holOfVar :: Int -> HOL cls thry HOLTerm
      holOfVar v = holOfVar' v <|>
          let v' = v `mod` mesonOffInc in
            do hv' <- holOfVar' v'
               gv <- genVar $ typeOf hv'
               modifyHOLRef ref $ \ st -> st { gstore = (gv, v) : gstore st }
               return gv

      holOfVar' :: Int -> HOL cls thry HOLTerm
      holOfVar' v =
          do vs <- liftM vstore $ readHOLRef ref
             case revLookup v vs of
               Just res -> return res
               Nothing -> do gs <- liftM gstore $ readHOLRef ref
                             case revLookup v gs of
                               Just res -> return res
                               Nothing -> fail "holOfVar"

      folOfVar :: HOLTerm -> HOL cls thry Int
      folOfVar v =
          do currentvars <- liftM vstore $ readHOLRef ref
             case lookup v currentvars of
               Just x  -> return x
               Nothing -> do n <- incVCounter
                             modifyHOLRef ref $ \ st -> st { vstore = (v, n) : currentvars }
                             return n

convQUANT_BOOL :: ClassicCtxt thry => Conversion cls thry
convQUANT_BOOL = 
    convPURE_REWRITE [ thmFORALL_BOOL, thmEXISTS_BOOL, thmCOND_CLAUSES
                     , thmNOT_CLAUSES, thmIMP_CLAUSES, thmAND_CLAUSES
                     , thmOR_CLAUSES, thmEQ_CLAUSES, thmFORALL_SIMP
                     , thmEXISTS_SIMP ]

tacSPLIT :: BoolCtxt thry => Int -> Tactic cls thry
tacSPLIT n =
    (_FIRST_X_ASSUM (tacCONJUNCTS_THEN' tacASSUME) `_THEN` tacSPLIT n) `_ORELSE`
    (if n > 0 then _FIRST_X_ASSUM tacDISJ_CASES `_THEN` tacSPLIT (n-1)
     else _NO) `_ORELSE`
    _ALL

tacGEN_MESON :: (TriviaCtxt thry, HOLThmRep thm cls thry) 
             => Int -> Int -> Int 
             -> [thm] -> Tactic cls thry
tacGEN_MESON minVal maxVal step ths = 
    liftM1 (tacGEN_MESON' minVal maxVal step) $ mapM toHThm ths

tacGEN_MESON' :: TriviaCtxt thry => Int -> Int -> Int 
              -> [HOLThm] -> Tactic cls thry
tacGEN_MESON' minVal maxVal step ths gl =
    do pth <- thmDISJ_ASSOC
       ref <- newHOLRef =<< initializeMeson
       splitLimit <- mesonSplitLimit
       ths' <- mapM ruleGEN_ALL ths
       (tacREFUTE_THEN tacASSUME `_THEN`
        tacPOLY_ASSUME ths' `_THEN`
        (\ g@(Goal asl _) -> _MAP_EVERY (tacUNDISCH . concl . snd) asl g) `_THEN`
        tacSELECT_ELIM `_THEN`
        (\ g@(Goal _ w) -> _MAP_EVERY (\ v -> tacSPEC (v,v)) (frees w) g) `_THEN`
        tacCONV (convPRESIMP `_THEN`
                 convTOP_DEPTH convBETA `_THEN`
                 convLAMBDA_ELIM `_THEN`
                 convCONDS_CELIM `_THEN`
                 convQUANT_BOOL) `_THEN`
        _REPEAT (tacGEN `_ORELSE` tacDISCH) `_THEN`
        tacREFUTE_THEN tacASSUME `_THEN`
        tacRULE_ASSUM (ruleCONV (convNNF `_THEN` convSKOLEM)) `_THEN`
        _REPEAT (_FIRST_X_ASSUM tacCHOOSE) `_THEN`
        tacASM_FOL `_THEN`
        tacSPLIT splitLimit `_THEN`
        tacRULE_ASSUM (ruleCONV (convPRENEX `_THEN` convWEAK_CNF)) `_THEN`
        tacRULE_ASSUM (repeatM (\ th -> case destForall $ concl th of
                                           Just (x, _) -> 
                                               do tm <- genVar $ typeOf x
                                                  ruleSPEC tm th
                                           Nothing -> fail "")) `_THEN`
        _REPEAT (_FIRST_X_ASSUM (tacCONJUNCTS_THEN' tacASSUME)) `_THEN`
        tacRULE_ASSUM (ruleCONV (convASSOC pth)) `_THEN`
        _REPEAT (_FIRST_X_ASSUM tacSUBST_VAR) `_THEN`
        tacPURE_MESON ref minVal maxVal step) gl


-- common meson tactics

tacASM_MESON :: (TriviaCtxt thry, HOLThmRep thm cls thry) 
             => [thm] -> Tactic cls thry
tacASM_MESON = tacGEN_MESON 0 50 1

tacASM_MESON_NIL :: TriviaCtxt thry => Tactic cls thry
tacASM_MESON_NIL = tacGEN_MESON' 0 50 1 []

tacMESON :: (TriviaCtxt thry, HOLThmRep thm cls thry) => [thm] 
         -> Tactic cls thry
tacMESON ths = _POP_ASSUM_LIST (const _ALL) `_THEN` tacASM_MESON ths

tacMESON_NIL :: TriviaCtxt thry => Tactic cls thry
tacMESON_NIL = _POP_ASSUM_LIST (const _ALL) `_THEN` tacASM_MESON_NIL

ruleMESON :: (TriviaCtxt thry, HOLThmRep thm cls thry,
              HOLTermRep tm cls thry) => [thm] -> tm -> HOL cls thry HOLThm
ruleMESON ths tm = prove tm $ tacMESON ths

ruleMESON_NIL :: (TriviaCtxt thry, HOLTermRep tm cls thry) 
              => tm -> HOL cls thry HOLThm
ruleMESON_NIL tm = prove tm tacMESON_NIL
