{-# LANGUAGE ScopedTypeVariables #-}
{-|
  Module:    HaskHOL.Lib.Meson
  Copyright: (c) Evan Austin 2015
  LICENSE:   BSD3

  Maintainer:  e.c.austin@gmail.com
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
    ) where

import HaskHOL.Core
import qualified HaskHOL.Core.Kernel as K (typeOf)

import HaskHOL.Lib.Bool
import HaskHOL.Lib.Canon
import HaskHOL.Lib.Classic
import HaskHOL.Lib.Equal
import HaskHOL.Lib.Theorems
import HaskHOL.Lib.Simp
import HaskHOL.Lib.DRule
import HaskHOL.Lib.Tactics
import HaskHOL.Lib.Trivia


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


-- Cacheable continuations.

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
mesonOffInc, mesonSkew, mesonSplitLimit :: Int
mesonOffInc = 10000
mesonSkew = 3
mesonSplitLimit = 8


-- partitioning utility
qpartition :: forall a. Eq a => (a -> Bool) -> [a] -> [a] -> ([a], [a])
qpartition p m l = tryd ([], l) $ partRec l
  where partRec :: [a] -> Catch ([a], [a])
        partRec [] = fail' "partRec"
        partRec lst@(h:t)
            | lst == m = fail' "partRec"
            | p h = 
                (do (yes, no) <- partRec t
                    return (h:yes, no)) <|> return ([h], t)
            | otherwise = 
                (do (yes, no) <- partRec t
                    return (yes, h:no)) <?> "partRec"


-- nnf substitution functions
folSubst :: [(FOLTerm, Int)] -> FOLTerm -> FOLTerm
folSubst theta tm@(FVar v) = revAssocd v theta tm
folSubst theta (FNApp f args) = FNApp f $ map (folSubst theta) args

folInst :: [(FOLTerm, Int)] -> FOLAtom -> FOLAtom
folInst theta (p, args) = (p, map (folSubst theta) args)

folSubstBump :: Int -> [(FOLTerm, Int)] -> FOLTerm -> FOLTerm
folSubstBump offset theta tm@(FVar v)
    | v < mesonOffInc = 
        let v' = v + offset in
          revAssocd v' theta $ FVar v'
    | otherwise = revAssocd v theta tm
folSubstBump offset theta (FNApp f args) =
    FNApp f $! map (folSubstBump offset theta) args 

folInstBump :: Int -> [(FOLTerm, Int)] -> FOLAtom -> FOLAtom
folInstBump offset theta (p, args) =
    let args' = map (folSubstBump offset theta) args in
      (p, args')


-- main nnf unification functions
isTriv :: MonadThrow m => [(FOLTerm, Int)] -> Int -> FOLTerm -> m Bool
isTriv env x (FVar y)
    | y == x = return True
    | otherwise =
        case runCatch $ revAssoc y env of
          Left{} -> return False
          Right t' -> isTriv env x t'
isTriv env x (FNApp _ args) = 
    do conds <- mapM (isTriv env x) args
       if or conds
          then fail' "isTriv: cyclic"
          else return False

folUnify :: (MonadCatch m, MonadThrow m) => Int -> FOLTerm -> FOLTerm 
         -> [(FOLTerm, Int)] -> m [(FOLTerm, Int)]
folUnify offset (FNApp f fargs) (FNApp g gargs) sofar
    | f /= g = fail' "folUnify"
    | otherwise = foldr2M (folUnify offset) sofar fargs gargs
folUnify offset tm1 (FVar x) sofar =
    case runCatch $ revAssoc x' sofar of
      Right tm2' -> folUnify 0 tm1 tm2' sofar
      Left{} -> do cond <- isTriv sofar x' tm1 <?> "folUnify: cyclic"
                   return $! if cond then sofar else (tm1, x'):sofar
  where x' = x + offset
folUnify offset (FVar x) tm2 sofar =
    case runCatch $ revAssoc x sofar of
      Right tm1' -> folUnify offset tm1' tm2 sofar
      Left{} -> do cond <- isTriv sofar x tm2' <?> "folUnify: cyclic"
                   return $! if cond then sofar else (tm2', x):sofar
  where tm2' = folSubstBump offset [] tm2

-- test for nnf equality
folEq :: [(FOLTerm, Int)] -> FOLTerm -> FOLTerm -> Bool
folEq insts tm1 tm2
    | tm1 == tm2 = True
    | otherwise =
        case (tm1, tm2) of
          (FNApp f fargs, FNApp g gargs) ->
              let conds = zipWith (folEq insts) fargs gargs in
                f == g && and conds
          (_, FVar x) ->
              case runCatch $ revAssoc x insts of
                Right tm2' -> folEq insts tm1 tm2'
                Left{} -> tryd False $ isTriv insts x tm1
          (FVar x, _) ->
              case runCatch $ revAssoc x insts of
                Right tm1' -> folEq insts tm1' tm2
                Left{} -> tryd False $ isTriv insts x tm2

folAtomEq :: [(FOLTerm, Int)] -> FOLAtom -> FOLAtom -> Bool
folAtomEq insts (p1, args1) (p2, args2)
    | p1 /= p2 = False
    | otherwise = and $ zipWith (folEq insts) args1 args2

-- check ancestor list for repetition
checkan :: MonadThrow m => FOLTermEnv -> FOLAtom -> [Rule] -> m [Rule]
checkan insts (p, a) ancestors =
    let p' = negate p
        t' = (p', a) in
      case runCatch $ assoc p' ancestors of
        Left{} -> return ancestors
        Right ours -> 
          if or $ map (folAtomEq insts t' . snd . fst) ours
             then fail' "checkan: loop"
             else return ancestors


-- insert new goal's negation in ancestor clause, given refinement
insertan :: BoolCtxt thry 
         => FOLTermEnv -> FOLAtom -> [Rule] -> HOL cls thry [Rule]
insertan insts (p, a) ancestors =
    let p' = negate p
        t' = (p', a)
        (ourancp, otheranc) = tryd ((p', []), ancestors) $ 
                                remove (\ (pr, _) -> pr ==  p') ancestors
        ouranc = snd ourancp in
      if or $ map (folAtomEq insts t' . snd . fst) ouranc
      then fail "insertan: loop"
      else do th <- thmTRUTH
              return ((p', (([], t'), (0, th)):ouranc):otheranc)
        
        
-- apply a multi-level "graph" instantiation
folSubstPartial :: [(FOLTerm, Int)] -> FOLTerm -> FOLTerm
folSubstPartial insts tm@(FVar v) =
    case runCatch $ revAssoc v insts of
      Left{} -> tm
      Right t -> folSubstPartial insts t
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

mkContraposes :: Int -> HOLThm -> [FOLAtom] -> [FOLAtom] 
              -> [(([FOLAtom], FOLAtom), (Int, HOLThm))]
              -> [(([FOLAtom], FOLAtom), (Int, HOLThm))]
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
            ruleTAUT [txt| a \/ b <=> ~b ==> a |]

convPush :: TriviaCtxt thry => Conversion cls thry
convPush = convGEN_REWRITE convTOP_SWEEP [convPush_pth1, convPush_pth2]
  where convPush_pth1 :: TriviaCtxt thry => HOL cls thry HOLThm
        convPush_pth1 = cacheProof "convPush_pth1" ctxtTrivia $
            ruleTAUT [txt| ~(a \/ b) <=> ~a /\ ~b |]

        convPush_pth2 :: TriviaCtxt thry => HOL cls thry HOLThm
        convPush_pth2 = cacheProof "convPush_pth2" ctxtTrivia $
            ruleTAUT [txt| ~(~a) <=> a |]

convPull :: TriviaCtxt thry => Conversion cls thry
convPull = convGEN_REWRITE convDEPTH [convPull_pth]
  where convPull_pth :: TriviaCtxt thry => HOL cls thry HOLThm
        convPull_pth = cacheProof "convPull_pth" ctxtTrivia $
            ruleTAUT [txt| ~a \/ ~b <=> ~(a /\ b) |]

convImf :: TriviaCtxt thry => Conversion cls thry
convImf = convREWR convImf_pth
  where convImf_pth :: TriviaCtxt thry => HOL cls thry HOLThm
        convImf_pth = cacheProof "convImf_pth" ctxtTrivia $
            ruleTAUT [txt| ~p <=> p ==> F |]


-- translate saved proof back to HOL
holNegate :: HOLTerm -> HOL cls thry HOLTerm
holNegate tm = (destNeg tm <|> mkNeg tm) <?> "holNegate"

mergeInst :: (FOLTerm, Int) -> [(FOLTerm, Int)] -> [(FOLTerm, Int)]
mergeInst (t, x) current =
    let t' = folSubst current t in
      (t', x) : current

finishRule :: TriviaCtxt thry => HOLThm -> HOL cls thry HOLThm
finishRule = ruleGEN_REWRITE id [finishRule_pth1, finishRule_pth2]
  where finishRule_pth1 :: TriviaCtxt thry => HOL cls thry HOLThm
        finishRule_pth1 = cacheProof "finishRule_pth1" ctxtTrivia $
            ruleTAUT [txt| (~p ==> p) <=> p |]

        finishRule_pth2 :: TriviaCtxt thry => HOL cls thry HOLThm
        finishRule_pth2 = cacheProof "finishRule_pth2" ctxtTrivia $
            ruleTAUT [txt| (p ==> ~p) <=> ~p |]
                                
-- create equality axioms

convImpElim :: TriviaCtxt thry => Conversion cls thry
convImpElim = convREWR convImpElim_pth
  where convImpElim_pth :: TriviaCtxt thry => HOL cls thry HOLThm
        convImpElim_pth = cacheProof "convImpElim_pth" ctxtTrivia $
            ruleTAUT [txt| (a ==> b) <=> ~a \/ b |]

ruleEqElim :: TriviaCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleEqElim = ruleMATCH_MP ruleEqElim_pth
  where ruleEqElim_pth :: TriviaCtxt thry => HOL cls thry HOLThm
        ruleEqElim_pth = cacheProof "ruleEqElim_pth" ctxtTrivia $
            ruleTAUT [txt| (a <=> b) ==> b \/ ~a |]


createEquivalenceAxioms :: TriviaCtxt thry => (HOLTerm, Int) 
                        -> HOL cls thry [HOLThm]
createEquivalenceAxioms (eq, _) =
    (do ths@(th:_) <- sequence eqThms
        veqTm <- rator $ rator (concl th)
        tyins <- typeMatch_NIL (typeOf veqTm) (typeOf eq)
        mapM (primINST_TYPE_FULL tyins) ths)
    <?> "createEquivalenceAxioms"
  where eqThms :: TriviaCtxt thry => [HOL cls thry HOLThm]
        eqThms = cacheProofs ["eqThms1", "eqThms2"] ctxtTrivia .
            ruleCONJUNCTS $ 
              prove [txt| (x:A = x) /\ (~(x:A = y) \/ ~(x = z) \/ (y = z)) |]
                (tacREWRITE_NIL `_THEN` 
                 tacASM_CASES [txt| x:A = y |] `_THEN`
                 tacASM_REWRITE_NIL `_THEN`
                 tacCONV (Conv ruleTAUT))
         

tmConsts :: HOLTerm -> [(HOLTerm, Int)] -> [(HOLTerm, Int)]
tmConsts tm acc =
    let (fn, args) = stripComb tm in
      if null args then acc
      else foldr tmConsts (insert (fn, length args) acc) args

fmConsts :: HOLTerm -> ([(HOLTerm, Int)], [(HOLTerm, Int)]) 
         -> ([(HOLTerm, Int)], [(HOLTerm, Int)])
fmConsts (Forall _ x) acc = fmConsts x acc
fmConsts (Exists _ x) acc = fmConsts x acc
fmConsts (l :/\ r) acc = fmConsts l $ fmConsts r acc
fmConsts (l :\/ r) acc = fmConsts l $ fmConsts r acc
fmConsts (l :==> r) acc = fmConsts l $ fmConsts r acc
fmConsts (Neg x) acc = fmConsts x acc
fmConsts tm@(l := r) acc
    | K.typeOf l == tyBool = fmConsts r $ fmConsts l acc
    | otherwise = fmConstsBad tm acc
fmConsts tm acc = fmConstsBad tm acc
                                              
fmConstsBad :: HOLTerm -> ([(HOLTerm, Int)], [(HOLTerm, Int)])
            -> ([(HOLTerm, Int)], [(HOLTerm, Int)])
fmConstsBad tm acc@(preds, funs) =
    let (p, args) = stripComb tm in
      if null args then acc
      else (insert (p, length args) preds, foldr tmConsts funs args)

createCongruenceAxiom :: TriviaCtxt thry => Bool -> (HOLTerm, Int) 
                      -> HOL cls thry HOLThm
createCongruenceAxiom pflag (tm, len) =
    (do (atys, _) <- splitListM destFunTy =<< typeOf tm
        (ctys, _) <- trySplitAt len atys
        largs <- mapM genVar ctys
        rargs <- mapM genVar ctys
        th1 <- primREFL tm
        ths <- mapM (primASSUME <=< uncurry mkEq) $ zip largs rargs
        th2 <- foldlM primMK_COMB th1 ths
        th3@(Thm asl _) <- if pflag then ruleEqElim th2 else return th2
        foldrM (\ e th -> ruleCONV convImpElim $ ruleDISCH e th) th3 asl)
      <?> "createCongruenceAxiom"

createEqualityAxioms :: TriviaCtxt thry => [HOLTerm] -> HOL cls thry [HOLThm]
createEqualityAxioms tms = note "createEqualityAxioms" $
     let (preds, funs) = foldr fmConsts ([], []) tms
         (eqs0, noneqs) = partition eqPred preds in
       if null eqs0 
          then return []
          else do pcongs <- mapM (createCongruenceAxiom True) noneqs
                  fcongs <- mapM (createCongruenceAxiom False) funs
                  let (preds1, _) = foldr fmConsts ([], []) $ 
                                      map concl (pcongs ++ fcongs)
                      eqs1 = filter eqPred preds1
                      eqs = eqs0 `union` eqs1
                  equivs <- foldrM (\ x ys -> do xs <- createEquivalenceAxioms x
                                                 return $ union xs ys) [] eqs
                  return $! equivs ++ pcongs ++ fcongs
    where eqPred :: (HOLTerm, Int) -> Bool
          eqPred (Const "=" _, _) = True
          eqPred _ = False
    
-- polymorph tactic
grabConstants :: HOLTerm -> [HOLTerm] -> [HOLTerm]
grabConstants (Forall _ bod) acc = grabConstants bod acc
grabConstants (Exists _ bod) acc = grabConstants bod acc
grabConstants (l :<=> r) acc = grabConstants r $ grabConstants l acc
grabConstants (l :==> r) acc = grabConstants r $ grabConstants l acc
grabConstants (l :/\ r) acc = grabConstants r $ grabConstants l acc
grabConstants (l :\/ r) acc = grabConstants r $ grabConstants l acc
grabConstants (Neg t) acc = grabConstants t acc
grabConstants tm acc = findTerms isConst tm `union` acc

matchConsts :: (HOLTerm, HOLTerm) -> HOL cls thry SubstTrip
matchConsts (Const s1 ty1, Const s2 ty2)
    | s1 == s2 = typeMatch_NIL ty1 ty2
    | otherwise = fail' "matchConsts: consts of different name"
matchConsts _ = fail' "matchConsts"

polymorph :: [HOLTerm] -> HOLThm -> HOL cls thry [HOLThm]
polymorph mconsts th =
    let tvs = typeVarsInTerm (concl th) \\ 
              (unions . map typeVarsInTerm $ hyp th) in
      if null tvs then return [th]
      else let pconsts = grabConstants (concl th) [] in
             do tyins <- mapFilterM matchConsts $ allpairs (,) pconsts mconsts
                tyins' <- mapM (`primINST_TYPE_FULL` th) tyins
                let ths' = setify' ((<=) `on` destThm) (==) tyins'
                if null ths'
                   then printDebug "No useful-looking instantiation of lemma" $ 
                          return [th]
                   else return ths'

polymorphAll :: [HOLTerm] -> [HOLThm] -> [HOLThm] -> HOL cls thry [HOLThm]
polymorphAll _ [] acc = return acc
polymorphAll mconsts (th:ths) acc =
    do ths' <- polymorph mconsts th
       let mconsts' = foldr (grabConstants . concl) mconsts ths'
       polymorphAll mconsts' ths (union' (==) ths' acc)

tacPOLY_ASSUME :: BoolCtxt thry => [HOLThm] -> Tactic cls thry
tacPOLY_ASSUME ths gl@(Goal asl _) =
    let mconsts = foldr (grabConstants . concl . snd) [] asl in
      do ths' <- polymorphAll mconsts ths []
         _MAP_EVERY tacASSUME ths' gl

tacCONJUNCTS_THEN' :: BoolCtxt thry 
                   => ThmTactic HOLThm cls thry -> ThmTactic HOLThm cls thry
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
             ths' <- liftM (ths ++) . createEqualityAxioms $ map concl ths
             rules <- liftM optimizeRules $ folOfHOLClauses ths'
             (proof, (insts, _, _)) <- solveGoal rules inc (1, [])
             modifyHOLRef ref $ \ st -> st { cutIn = dcutin }
             mesonToHOL insts proof
      
      solveGoal :: BoolCtxt thry 
                => [Rule] -> Int -> FOLAtom -> HOL cls thry (FOLGoal, Tup)
      solveGoal rules incsize g = solve minVal (g,[])
          where solve :: BoolCtxt thry 
                      => Int -> (FOLAtom, [Rule]) -> HOL cls thry (FOLGoal, Tup)
                solve n gl
                    | n > maxVal = fail "solveGoal: too deep"
                    | otherwise = 
                        (do is <- liftM infs $ readHOLRef ref
                            printDebug (show is ++ "..") $ return ()
                            gi <- expandGoal rules gl 100000 n Return1
                            is' <- liftM infs $ readHOLRef ref
                            printDebug ("solved at " ++ show is') $ return ()
                            return gi) <|> solve (n + incsize) gl

      expandGoal :: BoolCtxt thry => [Rule] -> (FOLAtom, [Rule]) -> Int -> Int 
                 -> DeCont1 -> HOL cls thry (FOLGoal, Tup)
      expandGoal rules g maxdep maxinf = 
          expandGoalRec rules maxdep (g, ([], 2 * mesonOffInc, maxinf))

      expandGoalRec :: BoolCtxt thry => [Rule] -> Int -> State -> DeCont1 
                    -> HOL cls thry (FOLGoal, Tup)
      expandGoalRec rules depth state@((g, _), (insts, offset, size)) cont
          | depth < 0 = fail "expandGoal: too deep"
          | otherwise =
              mesonExpand rules state
                (\ apprule newstate@(_, (pinsts, _, _)) ->
                     let cont' = cacheconts $ TopRec insts offset pinsts g 
                                   apprule cont size in
                       expandGoals rules (depth - 1) newstate cont')

      expandGoals :: BoolCtxt thry => [Rule] -> Int 
                  -> ([(FOLAtom, [Rule])], Tup) -> DeCont 
                  -> HOL cls thry (FOLGoal, Tup)
      expandGoals _ _ ([], tup) cont = deCont cont ([], tup)
      expandGoals rules depth ([g], tup) cont = 
          expandGoalRec rules depth (g, tup) $ Base cont
      expandGoals rules depth (gl@(g:gs), tup@(insts, offset, size)) cont =
          do dcutin <- liftM cutIn $ readHOLRef ref
             if size >= dcutin
                then let lsize = size `div` mesonSkew
                         rsize = size - lsize in
                       do (lgoals, rgoals) <- trySplitAt (length gl `div` 2) gl
                          (let cont' = cacheconts $ Goals1 cont rules depth 
                                         rgoals rsize in
                             expandGoals rules depth 
                               (lgoals, (insts, offset, lsize)) cont')
                            <|> (let cont' = cacheconts $ Goals3 rsize lsize 
                                               cont rules depth lgoals in
                                  expandGoals rules depth 
                                    (rgoals, (insts, offset, lsize)) cont')
                else let cont' = cachecont $ Goals11 cont rules depth gs in
                       expandGoalRec rules depth (g, tup) cont'

      mesonExpand :: forall cls thry. BoolCtxt thry => [Rule] -> State 
                  -> ((Int, HOLThm) -> ([(FOLAtom, [Rule])], Tup)
                  -> HOL cls thry (FOLGoal, Tup)) -> HOL cls thry (FOLGoal, Tup)
      mesonExpand rules ((g, ancestors), tup@(insts, offset, size)) cont =
          let pr = fst g in
            do newancestors <- insertan insts g ancestors
               let newstate = ((g, newancestors), tup)
               (if pr > 0 then throwM Fail
                else case lookup pr ancestors of
                       Nothing -> throwM Fail
                       Just arules -> mesonExpandCont 0 arules newstate cont) 
                `catch` errCase pr newstate
          where errCase :: Int -> State -> MesonErr 
                        -> HOL cls thry (FOLGoal, Tup)
                errCase _ _ Cut = fail "mesonExpand"
                errCase pr newstate Fail = 
                    do prule <- assoc pr rules
                       let crules = filter (\ ((h, _), _) -> length h <= size) 
                                      prule
                       mesonExpandCont offset crules newstate cont

      mesonExpandCont :: Int -> [(([FOLAtom], FOLAtom), b)] -> State
                      -> (b -> ([(FOLAtom, [Rule])], Tup) -> 
                                HOL cls thry (FOLGoal, Tup)) 
                      -> HOL cls thry (FOLGoal, Tup)
      mesonExpandCont loffset rules state cont =
          tryFind (\ r -> cont (snd r) =<< 
                            mesonSingleExpand loffset r state) rules 
          <|> throwM Fail

      mesonSingleExpand :: Int -> (([FOLAtom], FOLAtom), b) -> State -> 
                                   HOL cls thry ([(FOLAtom, [Rule])], Tup)
      mesonSingleExpand loffset rule 
                        (((_, ftms), ancestors), (insts, offset, size)) =
          let ((hyps, conc), _) = rule in
            do allEnv <- foldl2M (\ c a b -> folUnify loffset a b c) 
                           insts ftms $ snd conc
               let (loc, glob) = separateInsts2 offset insts allEnv
                   mkIHyp h = let h' = folInstBump offset loc h in
                                do an <- checkan insts h' ancestors
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
                 if any (\ (_, (insts', _, size')) -> insts == insts' && 
                                                      (size <= size')) m
                    then fail "cacheconts"
                    else do replaceMem1 cont m
                            deCont1 cont input

      deCont :: BoolCtxt thry => DeCont -> ContMemMany cls thry
      deCont (TopRec insts offset pinsts g apprule cont size)
             (gs, (newinsts, newoffset, newsize)) =
          let (locin, globin) = separateInsts2 offset pinsts newinsts
              g' = Subgoal g gs apprule offset locin in
            if globin == insts && null gs
            then deCont1 cont (g', (globin, newoffset, size)) <|> throwM Cut
            else deCont1 cont (g', (globin, newoffset, newsize)) <|> throwM Fail
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
                 if any (\ (_, (insts', _, size')) -> insts == insts' && 
                                                      (size <= size')) m
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
               (assoc key m) <|>
                (if n < 0 then ruleCONV (convPull `_THEN` convImf) th
                 else let djs = disjuncts tm in
                        do acth <- if n == 0 then return th
                                   else do (ldjs, rdj:rdjs) <- trySplitAt n djs
                                           let ndjs = rdj : (ldjs ++ rdjs)
                                           th1 <- runConv convDISJ_AC . 
                                                    mkEq tm $ listMkDisj ndjs
                                           primEQ_MP th1 th
                           fth <- if length djs == 1 then return acth
                                  else ruleCONV (convImp `_THEN` convPush) acth
                           modifyHOLRef ref $ \ st -> 
                               st { memory = (key, fth) : m }
                           return fth)

      resetVars :: HOL cls thry ()
      resetVars = modifyHOLRef ref $ \ st -> 
                      st { vstore = [], gstore = [], vcounter = 0 }

      resetConsts :: TriviaCtxt thry => HOL cls thry ()
      resetConsts = 
          do falseTm <- serve [trivia| F |]
             modifyHOLRef ref $ \ st -> 
                 st { cstore = [(falseTm, 1)], ccounter = 2 }

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
               hth <- if th == truthTh then primASSUME holG
                      else do cth <- makeHOLContrapos n th
                              if null ths 
                                 then return cth
                                 else ruleMATCH_MP cth $ foldr1M ruleCONJ ths
               ith <- rulePART_MATCH return hth holG
               tm <- holNegate $ concl ith
               finishRule =<< ruleDISCH tm ith

      folOfHOLClause :: HOLThm 
                     -> HOL cls thry [(([FOLAtom], FOLAtom), (Int, HOLThm))]
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
                 prules = map (\ t -> (t, filter ((== t) . fst . snd . fst) 
                                            rawrules)) prs
                 srules = sort (\ (p, _) (q, _) -> abs p <= abs q) prules
             return srules

      holOfTerm :: FOLTerm -> HOL cls thry HOLTerm
      holOfTerm (FVar v) = holOfVar v
      holOfTerm (FNApp f args) =
          do f' <- holOfConst f
             args' <- mapM holOfTerm args
             listMkComb f' args'

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
             listMkComb p' args'

      folOfAtom :: [HOLTerm] -> [HOLTerm] -> HOLTerm -> HOL cls thry FOLAtom
      folOfAtom env consts tm =
          let (f, args) = stripComb tm in
            if f `elem` env then fail "folOfAtom: higher order"
            else do ff <- folOfConst f
                    args' <- mapM (folOfTerm env consts) args
                    return (ff, args')

      holOfLiteral :: FOLAtom -> HOL cls thry HOLTerm
      holOfLiteral fa@(p, args)
          | p < 0 = mkNeg $ holOfAtom (negate p, args)
          | otherwise = holOfAtom fa

      folOfLiteral :: [HOLTerm] -> [HOLTerm] -> HOLTerm -> HOL cls thry FOLAtom
      folOfLiteral env consts (Neg tm') =
          do (p, a) <- folOfAtom env consts tm'
             return (negate p, a)
      folOfLiteral env consts tm = folOfAtom env consts tm

      holOfConst :: Int -> HOL cls thry HOLTerm
      holOfConst c = note "holOfConst" $
          do cs <- liftM cstore $ readHOLRef ref
             revAssoc c cs

      folOfConst :: HOLTerm -> HOL cls thry Int
      folOfConst c = note "folOfConst" $
          do currentconsts <- liftM cstore $ readHOLRef ref
             (assoc c currentconsts) <|>
              (do n <- liftM ccounter $ readHOLRef ref
                  modifyHOLRef ref $ \ st -> 
                      st { ccounter = n + 1, cstore = (c, n):currentconsts }
                  return n)

      holOfVar :: Int -> HOL cls thry HOLTerm
      holOfVar v = holOfVar' v <|>
          let v' = v `mod` mesonOffInc in
            do hv' <- holOfVar' v'
               gv <- genVar $ typeOf hv'
               modifyHOLRef ref $ \ st -> st { gstore = (gv, v) : gstore st }
               return gv

      holOfVar' :: Int -> HOL cls thry HOLTerm
      holOfVar' v = note "holOfVar" $
          do vs <- liftM vstore $ readHOLRef ref
             (revAssoc v vs) <|>
              (do gs <- liftM gstore $ readHOLRef ref
                  revAssoc v gs)

      folOfVar :: HOLTerm -> HOL cls thry Int
      folOfVar v =
          do currentvars <- liftM vstore $ readHOLRef ref
             case lookup v currentvars of
               Just x  -> return x
               Nothing -> 
                   do n <- incVCounter
                      modifyHOLRef ref $ \ st -> 
                          st { vstore = (v, n) : currentvars }
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
tacGEN_MESON minVal maxVal step ths gl = 
    do val <- initializeMeson
       ref <- newHOLRef val
       ths' <- mapM ruleGEN_ALL ths
       (tacREFUTE_THEN tacASSUME `_THEN`
        tacPOLY_ASSUME ths' `_THEN`
        (\ g@(Goal asl _) -> 
             _MAP_EVERY (tacUNDISCH . concl . snd) asl g) `_THEN`
        tacSELECT_ELIM `_THEN`
        (\ g@(Goal _ w) -> 
             _MAP_EVERY (\ v -> tacSPEC (v,v)) (frees w) g) `_THEN`
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
        tacSPLIT mesonSplitLimit `_THEN`
        tacRULE_ASSUM (ruleCONV (convPRENEX `_THEN` convWEAK_CNF)) `_THEN`
        tacRULE_ASSUM (repeatM (\ th@(Thm _ (Forall x _)) -> 
                                    do tm <- genVar $ typeOf x
                                       ruleSPEC tm th)) `_THEN`
        _REPEAT (_FIRST_X_ASSUM (tacCONJUNCTS_THEN' tacASSUME)) `_THEN`
        tacRULE_ASSUM (ruleCONV (convASSOC thmDISJ_ASSOC)) `_THEN`
        _REPEAT (_FIRST_X_ASSUM tacSUBST_VAR) `_THEN`
        tacPURE_MESON ref minVal maxVal step) gl


-- common meson tactics

tacASM_MESON :: (TriviaCtxt thry, HOLThmRep thm cls thry) 
             => [thm] -> Tactic cls thry
tacASM_MESON = tacGEN_MESON 0 50 1

tacASM_MESON_NIL :: TriviaCtxt thry => Tactic cls thry
tacASM_MESON_NIL = tacASM_MESON ([] :: [HOLThm])

tacMESON :: (TriviaCtxt thry, HOLThmRep thm cls thry) => [thm] 
         -> Tactic cls thry
tacMESON ths = _POP_ASSUM_LIST (const _ALL) `_THEN` tacASM_MESON ths

tacMESON_NIL :: TriviaCtxt thry => Tactic cls thry
tacMESON_NIL = tacMESON ([] :: [HOLThm])

ruleMESON :: (TriviaCtxt thry, HOLThmRep thm cls thry,
              HOLTermRep tm cls thry) => [thm] -> tm -> HOL cls thry HOLThm
ruleMESON ths tm = prove tm $ tacMESON ths

ruleMESON_NIL :: (TriviaCtxt thry, HOLTermRep tm cls thry) 
              => tm -> HOL cls thry HOLThm
ruleMESON_NIL tm = prove tm tacMESON_NIL
