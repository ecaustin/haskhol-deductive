{-# LANGUAGE FlexibleContexts, PatternSynonyms #-}
{-|
  Module:    HaskHOL.Lib.DRule
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.DRule
    ( Instantiation
    , mkThm
    , ruleMK_CONJ
    , ruleMK_DISJ
    , ruleMK_FORALL
    , ruleMK_EXISTS
    , convMP
    , convBETAS
    , instantiate
    , ruleINSTANTIATE
    , ruleINSTANTIATE_ALL
    , termMatch
    , termUnify
    , rulePART_MATCH
    , ruleGEN_PART_MATCH
    , ruleMATCH_MP
    , convHIGHER_REWRITE
    , newDefinition
    , getDefinition
    ) where

import HaskHOL.Core
import HaskHOL.Lib.Bool
import HaskHOL.Lib.Bool.Context
import HaskHOL.Lib.Equal

-- | 'mkThm' can be used to construct an arbitrary 'HOLThm' using 'newAxiom'.
mkThm :: BoolCtxt thry => [HOLTerm] -> HOLTerm -> HOL Theory thry HOLThm
mkThm asl c =
    do n <- tickTermCounter 
       ax <- newAxiom ("mkThm" `append` textShow n) =<< 
               foldrM mkImp c (reverse asl)
       foldlM (\ th t -> ruleMP th #<< primASSUME t) ax $ reverse asl

{-|@
   A |- p \<=\> p'   B |- q \<=\> q'
-----------------------------------
   A U B |- p \/\\ q \<=\> p' \/\\ q'
@

  Throws a 'HOLException' if the conclusions of the provided theorems are not
  both biconditionals.
-}
ruleMK_CONJ :: BoolCtxt thry => HOLThm -> HOLThm -> HOL cls thry HOLThm
ruleMK_CONJ eq1 eq2 =
    (do andtm <- serve [bool| (/\) |]
        liftO $ liftM1 primMK_COMB (ruleAP_TERM andtm eq1) eq2)
     <?> "ruleMK_CONJ"

{-|@
   A |- p \<=\> p'   B |- q \<=\> q'
-----------------------------------
   A U B |- p \\/ q \<=\> p' \\/ q'
@

  Throws a 'HOLException' if the conclusions of the provided theorems are not
  both biconditionals.
-}
ruleMK_DISJ :: BoolCtxt thry => HOLThm -> HOLThm -> HOL cls thry HOLThm
ruleMK_DISJ eq1 eq2 =
    (do ortm <- serve [bool| (\/) |]
        liftO $ liftM1 primMK_COMB (ruleAP_TERM ortm eq1) eq2)
     <?> "ruleMK_DISJ"

{-|@
     v     A |- p \<=\> q    
----------------------------
  A |- (!v. p) \<=\> (!v. q)
@

  Throws a 'HOLException' in the following conditions:

  * The provided term is not a variable.

  * The provided term is free in the hypotheses of the provided theorem.

  * The conclusion of the provided theorem is not a biconditional.
-}
ruleMK_FORALL :: BoolCtxt thry => HOLTerm -> HOLThm -> HOL cls thry HOLThm
ruleMK_FORALL v th =
    (do atm <- serve [bool| (!):(A->bool)->bool |]
        liftO $ ruleAP_TERM (inst [(tyA, typeOf v)] atm) =<< primABS v th)
    <?> "ruleMK_FORALL"

{-|@
     v     A |- p \<=\> q    
----------------------------
  A |- (?v. p) \<=\> (?v. q)
@

  Throws a 'HOLException' in the following conditions:

  * The provided term is not a variable.

  * The provided term is free in the hypotheses of the provided theorem.

  * The conclusion of the provided theorem is not a biconditional.
-}
ruleMK_EXISTS :: BoolCtxt thry => HOLTerm -> HOLThm -> HOL cls thry HOLThm
ruleMK_EXISTS v th =
    (do atm <- serve [bool| (?):(A->bool)->bool |]
        liftO $ ruleAP_TERM (inst [(tyA, typeOf v)] atm) =<< primABS v th)
    <?> "ruleMK_EXISTS"

{-|
  'convMP' applies a provided conversion to a theorem of the form 
  @A |- p ==> q@.  If the conversion returns an intermediate theorem of the form
  @|- p@ or @|- p \<=\> T@ then the final theorem @A |- q@ is returned.  It
  throws a 'HOLException' in the following cases:

  *  The conclusion of the provided theorem is not an implication.

  *  The application of the conversion fails.

  *  The conversion does not solve the antecedent of the implication.
-}
convMP :: BoolCtxt thry => Conversion cls thry -> HOLThm -> HOL cls thry HOLThm
convMP conv th = noteHOL "convMP" $
    do (l, _) <- liftMaybe "conclusion not an implication." . destImp $ concl th
       ath <- runConv conv l <?> "conversion failed."
       (ruleMP th =<< ruleEQT_ELIM ath) <|> ruleMP th ath <?> 
         "antecedent not solved."

{-|
  The 'convBETAS' conversion performs a beta conversion on a application with
  multiple arguments returning a theorem of the form 
  @|- (\ x1 ... xn. t) s1 ... sn = t[s1, ..., sn / x1, ..., xn]@
-}
convBETAS :: Conversion cls thry
convBETAS = Conv $ \ tm ->
    case tm of
      (Comb Abs{} _)  -> runConv convBETA tm
      (Comb Comb{} _) -> 
          runConv (convRATOR convBETAS `_THEN` convBETA) tm
      _ -> fail "convBETAS"

-- instantiation rules
type Instantiation = ([(HOLTerm, Int)], [(HOLTerm, HOLTerm)], SubstTrip)  

{-|
  Applies an 'Instantiation' to a term.  This application should never fail,
  provided the instantiation is correctly constructed.  See 'termMatch' for more
  details.
-}
instantiate :: Instantiation -> HOLTerm -> HOLTerm
instantiate (xs, tmenv, tyenv) x = 
    let itm = if tyenv == ([], [], []) then x else instFull tyenv x in
      if null tmenv then itm
      else fromJust $ do ttm <- varSubst tmenv itm
                         if null xs 
                            then return ttm
                            else hush (hoBetas itm ttm) <|> return ttm
  where betas :: Int -> HOLTerm -> Maybe HOLTerm
        betas n tm =
            do (args, lam) <- funpowM n (\ (l, t) -> 
                                do tRand <- rand t
                                   tRator <- rator t
                                   return (tRand:l, tRator)) ([], tm)
               foldlM (\ l a -> do (v, b) <- destAbs l
                                   varSubst [(v, a)] b) lam args 

        hoBetas :: HOLTerm -> HOLTerm -> Either String HOLTerm
        hoBetas Var{} _ = Left "hoBetas"
        hoBetas Const{} _ = Left "hoBetas"
        hoBetas (Abs _ bod1) (Abs bv bod2) = 
            do th <- hoBetas bod1 bod2
               mkAbs bv th
        hoBetas pat tm =
            let (hop, args) = stripComb pat
                n = length args in
              if lookup hop xs == Just n
              then liftO $ betas n tm
              else case (pat, tm) of
                      (Comb lpat rpat, Comb ltm rtm) -> 
                          do { lth <- hoBetas lpat ltm
                             ; (mkComb lth =<< hoBetas rpat rtm) <|> 
                                 mkComb lth rtm
                             } <|> 
                             (mkComb ltm =<< hoBetas rpat rtm)
                      _ -> Left "hoBetas"

{-|
  The 'ruleINSTANTIATE' rule applies an 'Instantiation' to the conclusion of a
  provided theorem.  It throws a 'HOLException' in the case when instantiation
  fails due to a term or type variable being free in the assumption list.  See
  'termMatch' for more details.
-}
ruleINSTANTIATE :: HOLThmRep thm cls thry => Instantiation -> thm 
                -> HOL cls thry HOLThm
ruleINSTANTIATE (_, [], ([], [], [])) pthm = toHThm pthm
ruleINSTANTIATE (_, [], tyenv) pthm = 
    liftM (primINST_TYPE_FULL tyenv) $ toHThm pthm
ruleINSTANTIATE (bcs, tmenv, tyenv) pthm = noteHOL "ruleINSTANTIATE" $
    do thm <- toHThm pthm
       let ithm = if tyenv == ([], [], []) then thm 
                  else primINST_TYPE_FULL tyenv thm
       tthm <- liftMaybe "instantiation failed." $ primINST tmenv ithm
       if hyp tthm == hyp thm
          then if null bcs then return tthm
               else (do ethm <- ruleHO_BETAS (concl ithm) (concl tthm)
                        liftO $ primEQ_MP ethm tthm)
                    <|> return tthm
          else fail "term or type variable free in assumptions."
  where ruleHO_BETAS :: HOLTerm -> HOLTerm -> HOL cls thry HOLThm 
        ruleHO_BETAS Var{} _ = fail "ruleHO_BETAS"
        ruleHO_BETAS Const{} _ = fail "ruleHO_BETAS"
        ruleHO_BETAS (Abs _ bod1) (Abs bv bod2) =
            do th <- ruleHO_BETAS bod1 bod2
               liftO $ primABS bv th
        ruleHO_BETAS pat tm =
            let (hop, args) = stripComb pat
                n = length args in
              if lookup hop bcs == Just n
              then runConv (betasConv n) tm
              else case (pat, tm) of
                     (Comb lpat rpat, Comb ltm rtm) -> 
                         do { lth <- ruleHO_BETAS lpat ltm
                            ; do { rth <- ruleHO_BETAS rpat rtm
                                 ; liftO (primMK_COMB lth rth)
                                 } <|> liftO (ruleAP_THM lth rtm)
                            } <|> do rth <- ruleHO_BETAS rpat rtm
                                     liftO $ ruleAP_TERM ltm rth
                     _ -> fail "ruleHO_BETAS"
                   
        betasConv :: Int -> Conversion cls thry
        betasConv 1 = _TRY convBETA
        betasConv n = convRATOR (betasConv (n-1)) `_THEN` _TRY convBETA

        
          
{-|
  The 'ruleINSTANTIATE_ALL' rule applies an 'Instantiation' to all parts of a
  provided theorem.  This application should never fail, provided the
  instantiation is correctly constructed.  See 'termMatch' for more details.
-}                     
ruleINSTANTIATE_ALL :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                    => Instantiation -> thm -> HOL cls thry HOLThm
ruleINSTANTIATE_ALL (_, [], ([], [], [])) pthm = toHThm pthm
ruleINSTANTIATE_ALL i@(_, tmenv, (tys, opTys, opOps)) pthm =
    do thm@(Thm hyps _) <- toHThm pthm
       if null hyps
          then ruleINSTANTIATE i pthm
          else let (tyrel, tyiirel) = 
                    if null tys then ([], hyps)
                    else let tvs = foldr (union . tyVars . fst) [] tys in
                           partition (\ tm -> let tvs' = typeVarsInTerm tm in
                                        not(null (tvs `intersect` tvs'))) hyps
                   (oprel, opiirel) = 
                    if null opTys && null opOps then ([], tyiirel)
                    else let tyops = filter isTypeOpVar (map fst opTys ++ 
                                                         map fst opOps) in
                          partition (\ tm -> let tyops' = typeOpVarsInTerm tm in
                                       not(null (tyops `intersect` tyops'))) 
                            tyiirel
                   tmrel = 
                    if null tmenv then []
                    else let vs = foldr (union . frees . fst) [] tmenv in
                           fst $ partition (\ tm -> let vs' = frees tm in
                                              not(null (vs `intersect` vs'))) 
                                   opiirel
                   rhyps = tyrel `union` oprel `union` tmrel in
                 do thm1 <- foldlM (flip ruleDISCH) thm rhyps
                    thm2 <- ruleINSTANTIATE i thm1
                    funpowM (length rhyps) ruleUNDISCH thm2

-- term matching
termMatch :: [HOLTerm] -> HOLTerm -> HOLTerm -> Maybe Instantiation
termMatch lconsts vtm ctm = 
    do pinsts_homs <- termPMatch lconsts [] vtm ctm ([], [])
       tyenv <- getTypeInsts (fst pinsts_homs) ([], [], [])
       insts <- termHOMatch lconsts tyenv pinsts_homs
       separateInsts insts

termPMatch :: [HOLTerm] -> HOLTermEnv -> HOLTerm -> HOLTerm 
           -> (HOLTermEnv, [(HOLTermEnv, HOLTerm, HOLTerm)]) 
           -> Maybe (HOLTermEnv, [(HOLTermEnv, HOLTerm, HOLTerm)])
termPMatch lconsts env vtm@Var{} ctm sofar@(insts, homs) =
    case lookup vtm env of
      Just ctm' -> 
          if ctm' == ctm then return sofar
          else Nothing
      Nothing -> 
          if vtm `elem` lconsts
          then if ctm == vtm then return sofar
               else Nothing
          else do insts' <- safeInsertA (vtm, ctm) insts
                  return (insts', homs)
termPMatch _ _ (Const vname vty) 
               (Const cname cty) sofar@(insts, homs) =
    if vname == cname
    then if vty == cty then return sofar
         else let name = mkDummy in
                do insts' <- safeInsert (mkVar name vty, mkVar name cty) insts
                   return (insts', homs)
    else Nothing
termPMatch lconsts env (Abs vv@(Var _ vty) vbod) 
                       (Abs cv@(Var _ cty) cbod) (insts, homs) =
    let name = mkDummy in
      do insts' <- safeInsert (mkVar name vty, mkVar name cty) insts
         termPMatch lconsts ((vv, cv):env) vbod cbod (insts', homs)
termPMatch lconsts env vtm ctm sofar@(insts, homs) =
    do vhop <- repeatM rator vtm
       if isVar vhop && (vhop `notElem` lconsts) && 
          isNothing (lookup vhop env)
          then let vty = typeOf vtm
                   cty = typeOf ctm in
                 do insts' <- if vty == cty then return insts 
                              else let name = mkDummy in
                                     safeInsert (mkVar name vty, 
                                                 mkVar name cty) insts
                    return (insts', (env, vtm, ctm):homs)
          else case (vtm, ctm) of
                 (Comb lv rv, Comb lc rc) ->
                     do sofar' <- termPMatch lconsts env lv lc sofar
                        termPMatch lconsts env rv rc sofar'
                 (TyAbs tvv tbv, TyAbs tvc tbc) ->
                     termPMatch lconsts env (inst [(tvv, tvc)] tbv) tbc sofar
                 (TyComb tv tyv, TyComb tc tyc) ->
                     if tyv == tyc then termPMatch lconsts env tv tc sofar
                     else do (i, h) <- termPMatch lconsts env tv tc sofar
                             let name = mkDummy
                             i' <- safeInsert (mkVar name tyv, mkVar name tyc) i
                             return (i', h)
                 _ -> Nothing

getTypeInsts :: HOLTermEnv -> SubstTrip -> Maybe SubstTrip
getTypeInsts insts i = 
    foldrM (\ (x, t) sofar -> case x of
                                (Var _ ty) -> 
                                    typeMatch ty (typeOf t) sofar
                                _ -> Nothing) i insts

termHOMatch :: [HOLTerm] -> SubstTrip 
            -> (HOLTermEnv, [(HOLTermEnv, HOLTerm, HOLTerm)]) 
            -> Maybe HOLTermEnv
termHOMatch _ _ (insts, []) = return insts
termHOMatch lconsts tyenv@(tys, opTys, opOps) 
            (insts, homs@((env, vtm, ctm):rest)) = 
    case vtm of
      (Var _ vty) -> 
        if ctm == vtm then termHOMatch lconsts tyenv (insts, rest)
        else do tys' <- safeInsert (vty, typeOf ctm) tys
                let newtyenv = (tys', opTys, opOps)
                    newinsts = (vtm, ctm):insts
                termHOMatch lconsts newtyenv (newinsts, rest)
      _ -> 
        let (vhop, vargs) = stripComb vtm
            afvs = catFrees vargs
            inst_fn = instFull tyenv in
          ((do tmenv <- mapM (\ a -> do a' <- lookup a env <|> 
                                              lookup a insts <|> 
                                              (if a `elem` lconsts 
                                               then return a 
                                               else Nothing)
                                        return (inst_fn a, a')) afvs
               let pats0 = map inst_fn vargs
                   vhop' = inst_fn vhop
               pats <- mapM (varSubst tmenv) pats0
               ni <- let (chop, cargs) = stripComb ctm in
                       if cargs == pats 
                       then if chop == vhop 
                            then return insts
                            else safeInsert (vhop, chop) insts
                       else do ginsts <- mapM (\ p -> 
                                               if isVar p then return (p, p)
                                               else let ty = typeOf p
                                                        p' = unsafeGenVar ty in
                                                      return (p, p')) pats
                               ctm' <- subst ginsts ctm
                               let gvs = map snd ginsts
                               abstm <- hush $ listMkAbs gvs ctm'
                               vinsts <- safeInsertA (vhop, abstm) insts
                               combtm <- hush $ listMkComb vhop' gvs
                               let icpair = (combtm, ctm')
                               return (icpair:vinsts)
               termHOMatch lconsts tyenv (ni, rest))
           <|> (case (ctm, vtm) of
                  (Comb lc rc, Comb lv rv) -> 
                      do pinsts_homs' <- termPMatch lconsts env rv rc (insts, (env, lv, lc):tail homs)
                         tyenv' <- getTypeInsts (fst pinsts_homs') ([], [], [])
                         termHOMatch lconsts tyenv' pinsts_homs'
                  _ -> Nothing))

separateInsts :: HOLTermEnv -> Maybe Instantiation
separateInsts insts = 
    let (realinsts, patterns) = partition (isVar . fst) insts in
      do betacounts <- 
           if null patterns then return []
           else foldrM (\ (p, _) sof -> 
                          let (hop, args) = stripComb p in
                            (safeInsert (hop, length args) sof
                             <|> return sof)) [] patterns
         tyenv <- getTypeInsts realinsts ([], [], [])
         let realinsts' = mapFilter
                          (\ (x, t) -> 
                             case x of
                               (Var xn xty) -> 
                                 let x' = mkVar xn $ typeSubstFull tyenv xty in
                                   if t == x' then Nothing
                                   else Just (x', t)
                               _ -> Nothing) realinsts
         return (betacounts, realinsts', tyenv)

insertByTest :: Eq a => (b -> b -> Bool) -> (a, b) -> [(a, b)] -> Maybe [(a, b)]
insertByTest test n@(x, y) l =
    case lookup x l of
      Nothing -> Just (n:l)
      Just z -> if y `test` z then Just l else Nothing

safeInsert :: (Eq a, Eq b) => (a, b) -> [(a, b)] -> Maybe [(a, b)]
safeInsert = insertByTest (==)

safeInsertA :: (HOLTerm, HOLTerm) -> [(HOLTerm, HOLTerm)] 
            -> Maybe [(HOLTerm, HOLTerm)]
safeInsertA = insertByTest aConv

mkDummy :: Text
mkDummy = 
    let (Var name _) = unsafeGenVar tyA in name




-- first order term unification
augment1 :: HOLTermEnv -> (HOLTerm, HOLTerm) -> Maybe (HOLTerm, HOLTerm)
augment1 sofar (x, s) = 
    do s' <- subst sofar s
       if varFreeIn x s && s /= x 
          then Nothing
          else return (x, s')

rawAugmentInsts :: (HOLTerm, HOLTerm) -> HOLTermEnv -> Maybe HOLTermEnv
rawAugmentInsts p insts = 
    do insts' <- mapM (augment1 [p]) insts
       return $! p:insts'

augmentInsts :: (HOLTerm, HOLTerm) -> HOLTermEnv -> Maybe HOLTermEnv
augmentInsts (v, t) insts = 
    do t' <- varSubst insts t
       if t' == v 
          then return insts
          else if varFreeIn v t' then Nothing
               else rawAugmentInsts (v, t') insts

unify :: [HOLTerm] -> HOLTerm -> HOLTerm -> HOLTermEnv -> Maybe HOLTermEnv
unify vars tm1 tm2 sofar
    | tm1 == tm2 = return sofar
    | isVar tm1 && tm1 `elem` vars =
        case lookup tm1 sofar of
          Just tm1' -> unify vars tm1' tm2 sofar
          Nothing -> augmentInsts (tm1, tm2) sofar
    | isVar tm2 && tm2 `elem` vars =
        case lookup tm2 sofar of
          Just tm2' -> unify vars tm1 tm2' sofar
          Nothing -> augmentInsts (tm2, tm1) sofar
    | otherwise = 
        case (tm1, tm2) of
          (Abs bv1 tm1', Abs bv2 bod) -> 
            do tm2' <- subst [(bv2, bv1)] bod
               unify vars tm1' tm2' sofar
          (Comb l1 r1, Comb l2 r2) -> 
            do sofar' <- unify vars r1 r2 sofar
               unify vars l1 l2 sofar'
          (_, _) -> Nothing

termUnify :: [HOLTerm] -> HOLTerm -> HOLTerm -> Maybe Instantiation
termUnify vars tm1 tm2 = 
    do vars' <- unify vars tm1 tm2 []
       return ([], vars', ([], [], []))

                   
-- modify variables at depth
tryalpha :: HOLTerm -> HOLTerm -> HOLTerm
tryalpha v tm = 
    case alpha v tm <|> alpha (variant (frees tm) v) tm of
      Right res -> res
      _ -> tm


deepAlpha :: [(Text, Text)] -> HOLTerm -> Either String HOLTerm
deepAlpha [] tm = return tm
deepAlpha env tm@(Abs var@(Var vn vty) bod) =
    let catchCase1 = mkAbs var =<< deepAlpha env bod in
      case remove (\ (x, _) -> x == vn) env of
        Just ((_, vn'), newenv) -> 
            case tryalpha (mkVar vn' vty) tm of
                Abs var' ib -> (do ib' <- deepAlpha newenv ib
                                   mkAbs var' ib') <|> catchCase1
                _ -> catchCase1
        Nothing -> catchCase1
deepAlpha env (Comb l r) =
    do  l' <- deepAlpha env l
        r' <- deepAlpha env r
        mkComb l' r'
deepAlpha _ tm = return tm
                                                                        

matchBvs :: HOLTerm -> HOLTerm -> [(Text, Text)] -> [(Text, Text)]
matchBvs (Abs (Var n1 _) b1) 
         (Abs (Var n2 _) b2) acc =
    let newacc = if n1 == n2 then acc else (n2, n1) `insert` acc in
      matchBvs b1 b2 newacc
matchBvs (Comb l1 r1) (Comb l2 r2) acc =
    matchBvs l1 l2 $ matchBvs r1 r2 acc
matchBvs (TyAbs tv1 tb1) (TyAbs tv2 tb2) acc =
    matchBvs (inst [(tv1, tv2)] tb1) tb2 acc
matchBvs (TyComb t1 _) (TyComb t2 _) acc =
    matchBvs t1 t2 acc
matchBvs _ _ acc = acc

partInsts :: (BoolCtxt thry, HOLThmRep thm cls thry) 
          => (HOLTerm -> HOL cls thry HOLTerm) -> thm
          -> HOLTerm -> HOL cls thry (Instantiation, HOLThm, [HOLTerm])
partInsts partfn pthm tm =
    do thm@(Thm asl c) <- toHThm pthm
       sth@(Thm _ bod) <- ruleSPEC_ALL thm
       pbod <- partfn bod
       let lconsts = intersect (frees c) $ catFrees asl
           fvs = frees bod \\ frees pbod \\ lconsts
           bvms = matchBvs tm pbod []
           abod = fromRight $ deepAlpha bvms bod
           ath = fromRight $ liftM1 primEQ_MP (ruleALPHA bod abod) sth
       abod' <- partfn abod
       let insts = fromJust $ termMatch lconsts abod' tm
       return (insts, ath, fvs)

rulePART_MATCH :: (BoolCtxt thry, HOLThmRep thm cls thry) 
               => (HOLTerm -> Maybe HOLTerm) -> thm -> HOLTerm
               -> HOL cls thry HOLThm
rulePART_MATCH partfn thm tm = 
  let partFun = liftMaybe "rulePART_MATCH: parting failed." . partfn in
    do (insts, ath, _) <- partInsts partFun thm tm
       fth <- ruleINSTANTIATE insts ath
       if hyp fth /= hyp ath 
          then fail "rulePART_MATCH: instantiated hyps."
          else do tm' <- partFun $ concl fth
                  if tm' == tm 
                     then return fth
                     else (do alth <- fromRightM $ ruleALPHA tm' tm
                              ruleSUBS [alth] fth) 
                          <?> "rulePART_MATCH: sanity check failure"

ruleGEN_PART_MATCH :: BoolCtxt thry => (HOLTerm -> Maybe HOLTerm) -> HOLThm -> 
                                       HOLTerm -> HOL cls thry HOLThm
ruleGEN_PART_MATCH partfn thm tm = 
  let partFun = liftMaybe "rulePART_MATCH: parting failed." . partfn in
    do (insts, ath, fvs) <- partInsts partFun thm tm
       eth <- ruleINSTANTIATE insts =<< ruleGENL fvs ath
       fth <- foldrM (\ _ th -> liftM snd $ ruleSPEC_VAR th) eth fvs
       if hyp fth /= hyp ath 
          then fail "ruleGEN_PART_MATCH: instantiate hyps"
          else do tm' <- partFun $ concl fth 
                  if tm' == tm 
                     then return fth
                     else (do alth <- fromRightM $ ruleALPHA tm' tm
                              ruleSUBS [alth] fth)
                          <?> "ruleGEN_PART_MATCH: sanity check failure"

ruleMATCH_MP :: (HOLThmRep thm1 cls thry, HOLThmRep thm2 cls thry, 
                 BoolCtxt thry) => thm1 -> thm2 -> HOL cls thry HOLThm
ruleMATCH_MP pith pth = 
    do ith <- toHThm pith
       th <- toHThm pth
       sth <- let tm = concl ith
                  (avs, bod) = stripForall tm in
                case destImp bod of
                  Just (ant, _) -> 
                      (let (svs, pvs) = partition (`varFreeIn` ant) avs in
                         if null pvs then return ith
                         else do th1 <- ruleSPECL avs #<< primASSUME tm
                                 th2 <- ruleGENL svs =<< ruleDISCH ant =<< 
                                          ruleGENL pvs =<< ruleUNDISCH th1
                                 th3 <- ruleDISCH tm th2
                                 ruleMP th3 ith) <?> "ruleMATCH_MP"
                  _ -> fail "ruleMATCH_MP: not an implication"
       let match_fun = rulePART_MATCH (liftM fst . destImp) sth
       thm <- match_fun (concl th) <?> "ruleMATCH_MP: no match"
       ruleMP thm th
       
convHIGHER_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => [thm] -> Bool 
                   -> Conversion cls thry
convHIGHER_REWRITE ths top = Conv $ \ tm ->
    do thl <- mapM (ruleGINST <=< ruleSPEC_ALL) ths
       let concs = map concl thl
           (preds, pats) = fromJust . liftM unzip $ mapM destComb =<< 
                                                      mapM lhs concs
           betaFns = fromJust $ map2 convBETA_VAR preds concs
           asmList = zip pats . zip preds $ zip thl betaFns
           mnet = foldr (\ p n -> netEnter [] (p, p) n) netEmpty pats
           lookFn t = mapFilterM (\ p -> do void $ termMatch [] p t
                                            return p) $ netLookup t mnet
           predFn t = do ts <- liftO $ lookFn t
                         return $! not (null ts) && t `freeIn` tm
       stm <- if top then findTermM predFn tm
              else liftM (head . sort freeIn) $ findTermsM predFn tm
       let pat = head . fromJust $ lookFn stm
           (_, tmenv, _) = fromJust $ termMatch [] pat stm
           (ptm, (th, betaFn)) = fromJust $ pat `lookup` asmList
       gv <- genVar $ typeOf stm
       let tm' = fromJust $ subst [(stm, gv)] tm
           tm'' = fromRight $ mkAbs gv tm'
           (_, tmenv0, tyenv0) = fromJust $ termMatch [] ptm tm''
       ruleCONV betaFn #<< primINST tmenv =<< primINST tmenv0 
         (primINST_TYPE_FULL tyenv0 th)
  where convBETA_VAR :: HOLTerm -> HOLTerm -> Conversion cls thry
        convBETA_VAR v = fromJust . freeBeta v

        freeBeta :: HOLTerm -> HOLTerm -> Maybe (Conversion cls thry)
        freeBeta v (Abs bv bod)
            | v == bv = Nothing
            | otherwise = liftM convABS (freeBeta v bod)
        freeBeta v tm =
            let (op, args) = stripComb tm in
              if null args then Nothing
              else if op == v then return . convBETA_CONVS $ length args
                   else do (l, r) <- destComb tm
                           do { lconv <- freeBeta v l
                              ; do { rconv <- freeBeta v r
                                   ; return (convCOMB2 lconv rconv)
                                   } <|> return (convRATOR lconv)
                              } <|> liftM convRAND (freeBeta v r)

        convBETA_CONVS :: Int -> Conversion cls thry
        convBETA_CONVS 1 = _TRY convBETA
        convBETA_CONVS n = convRATOR (convBETA_CONVS (n - 1)) `_THEN` 
                           _TRY convBETA

        ruleGINST :: HOLThm -> HOL cls thry HOLThm
        ruleGINST th@(Thm asl c) =
            let fvs = frees c \\ catFrees asl in
              do gvs <- mapM (genVar . typeOf) fvs
                 liftMaybe "ruleGINST" $ primINST (zip fvs gvs) th
        ruleGINST _ = error "ruleGINST: exhaustion warning."
        

data TheDefinitions = 
    TheDefinitions !(Map Text HOLThm) deriving Typeable

deriveSafeCopy 0 'base ''TheDefinitions

insertDefinition :: Text -> HOLThm -> Update TheDefinitions ()
insertDefinition lbl thm =
    do TheDefinitions defs <- get
       put (TheDefinitions (mapInsert lbl thm defs))

getDefinitions :: Query TheDefinitions [HOLThm]
getDefinitions =
    do TheDefinitions defs <- ask
       return $! mapElems defs

getADefinition :: Text -> Query TheDefinitions (Maybe HOLThm)
getADefinition name =
    do (TheDefinitions defs) <- ask
       return $! name `mapLookup` defs

makeAcidic ''TheDefinitions 
    ['insertDefinition, 'getDefinitions, 'getADefinition]

newDefinition :: (BoolCtxt thry, HOLTermRep tm Theory thry) => Text -> tm 
              -> HOL Theory thry HOLThm
newDefinition lbl ptm =
    do acid <- openLocalStateHOL (TheDefinitions mapEmpty)
       qth <- queryHOL acid (GetADefinition lbl)
       closeAcidStateHOL acid
       case qth of
         Just th ->
             return th
         Nothing -> 
           do tm <- toHTm ptm
              let (avs, bod) = stripForall tm
              (l, r) <- liftMaybe "newDefinition: Not an equation" $ destEq bod
              let (lv, largs) = stripComb l
              case lv of
                Var name _
                  | name /= lbl ->
                      fail $ "newDefinition: provided label does not match " ++
                             "provided term."
                  | otherwise ->
                      do rtm <- liftEither ("newDefinition: Non-variable " ++
                                  "in LHS pattern.") $ listMkAbs largs r
                         def <- mkEq lv rtm
                         thm1 <- newBasicDefinition lbl def
                         thm2 <- foldlM (\ thm t -> 
                                   do ithm <- fromRightM $ ruleAP_THM thm t
                                      ithm' <- fromJustM . rand $ concl ithm
                                      ithm'' <- runConv convBETA ithm'
                                      fromRightM $ primTRANS ithm ithm''
                                        ) thm1 largs
                         let rvs = filter (not . (`elem` avs)) largs
                         genthm <- foldrM ruleGEN thm2 avs
                         th <- foldrM ruleGEN genthm rvs
                         acid' <- openLocalStateHOL (TheDefinitions mapEmpty)
                         updateHOL acid' (InsertDefinition lbl th)
                         createCheckpointAndCloseHOL acid'
                         return th
                _ -> fail $ "newDefinition: Non-variable constructor in " ++
                             "LHS pattern."

getDefinition :: Text -> HOL cls thry HOLThm
getDefinition lbl =
    do acid <- openLocalStateHOL (TheDefinitions mapEmpty)
       qth <- queryHOL acid (GetADefinition lbl)
       closeAcidStateHOL acid
       liftMaybe ("getDefinition: definition for " ++ show lbl ++ 
                  " not found.") qth
