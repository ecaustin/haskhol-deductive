{-|
  Module:    HaskHOL.Lib.DRule
  Copyright: (c) Evan Austin 2015
  LICENSE:   BSD3

  Maintainer:  e.c.austin@gmail.com
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
    , partInsts
    ) where

import HaskHOL.Core
import qualified HaskHOL.Core.Kernel as K (mkComb)
import qualified HaskHOL.Core.Basics as B (subst)
import HaskHOL.Lib.Bool
import HaskHOL.Lib.Equal

tmAnd, tmOr, tmForall, tmExists :: BoolCtxt thry => HOL cls thry HOLTerm
tmAnd = serve [bool| (/\) |]
tmOr = serve [bool| (\/) |]
tmForall = serve [bool| (!):(A->bool)->bool |]
tmExists = serve [bool| (?):(A->bool)->bool |]

-- | 'mkThm' can be used to construct an arbitrary 'HOLThm' using 'newAxiom'.
mkThm :: BoolCtxt thry => [HOLTerm] -> HOLTerm -> HOL Theory thry HOLThm
mkThm asl c =
    do n <- tickTermCounter 
       thm <- foldrM mkImp c (reverse asl)
       ax <- newAxiom ("mkThm" `append` textShow n, thm)
       foldlM (\ th t -> ruleMP th $ primASSUME t) ax $ reverse asl

{-|@
   A |- p \<=\> p'   B |- q \<=\> q'
-----------------------------------
   A U B |- p \/\\ q \<=\> p' \/\\ q'
@

  Throws a 'HOLException' if the conclusions of the provided theorems are not
  both biconditionals.
-}
ruleMK_CONJ :: (BoolCtxt thry, HOLThmRep thm1 cls thry, HOLThmRep thm2 cls thry)
            => thm1 -> thm2 -> HOL cls thry HOLThm
ruleMK_CONJ eq1 eq2 =
    (primMK_COMB (ruleAP_TERM tmAnd eq1) eq2) <?> "ruleMK_CONJ"

{-|@
   A |- p \<=\> p'   B |- q \<=\> q'
-----------------------------------
   A U B |- p \\/ q \<=\> p' \\/ q'
@

  Throws a 'HOLException' if the conclusions of the provided theorems are not
  both biconditionals.
-}
ruleMK_DISJ :: (BoolCtxt thry, HOLThmRep thm1 cls thry, HOLThmRep thm2 cls thry)
            => thm1 -> thm2 -> HOL cls thry HOLThm
ruleMK_DISJ eq1 eq2 =
    (primMK_COMB (ruleAP_TERM tmOr eq1) eq2) <?> "ruleMK_DISJ"

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
ruleMK_FORALL :: (BoolCtxt thry, HOLTermRep tm cls thry, HOLThmRep thm cls thry)
              => tm -> thm -> HOL cls thry HOLThm
ruleMK_FORALL ptm th =
    (do v <- toHTm ptm
        ruleAP_TERM (liftM (inst [(tyA, typeOf v)]) tmForall) $ primABS v th)
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
ruleMK_EXISTS :: (BoolCtxt thry, HOLTermRep tm cls thry, HOLThmRep thm cls thry)
              => tm -> thm -> HOL cls thry HOLThm
ruleMK_EXISTS ptm th =
    (do v <- toHTm ptm
        ruleAP_TERM (liftM (inst [(tyA, typeOf v)]) tmExists) $ primABS v th)
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
convMP :: (BoolCtxt thry, HOLThmRep thm cls thry) 
       => Conversion cls thry -> thm -> HOL cls thry HOLThm
convMP conv pthm = note "convMP" $
    do thm <- toHThm pthm
       case concl thm of
         (l :==> _) ->
             do ath <- runConv conv l <?> "conversion failed."
                (ruleMP thm $ ruleEQT_ELIM ath) <|> ruleMP thm ath <?> 
                  "antecedent not solved."
         _ -> fail "not an implication."

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
      else let ttm = try' $ varSubst tmenv itm in
             if null xs then ttm
             else case runCatch $ hoBetas itm ttm of
                    Right res -> res
                    _         -> ttm
  where betas :: MonadThrow m => Int -> HOLTerm -> m HOLTerm
        betas n tm =
            do (args, lam) <- funpowM n (\ (ls, t) -> 
                                do (l, r) <- destComb t
                                   return (l:ls, r)) ([], tm)
               foldlM (\ l a -> do (v, b) <- destAbs l
                                   varSubst [(v, a)] b) lam args 

        hoBetas :: HOLTerm -> HOLTerm -> Catch HOLTerm
        hoBetas Var{} _ = fail' "hoBetas"
        hoBetas Const{} _ = fail' "hoBetas"
        hoBetas (Abs _ bod1) (Abs bv bod2) = 
            mkAbs bv =<< hoBetas bod1 bod2 
        hoBetas pat tm =
            let (hop, args) = stripComb pat
                n = length args in
              if lookup hop xs == Just n
              then betas n tm
              else case (pat, tm) of
                      (Comb lpat rpat, Comb ltm rtm) -> 
                          do { lth <- hoBetas lpat ltm
                             ; (K.mkComb lth =<< hoBetas rpat rtm) <|> 
                                 K.mkComb lth rtm
                             } <|> 
                             (K.mkComb ltm =<< hoBetas rpat rtm)
                      _ -> fail' "hoBetas"

{-|
  The 'ruleINSTANTIATE' rule applies an 'Instantiation' to the conclusion of a
  provided theorem.  It throws a 'HOLException' in the case when instantiation
  fails due to a term or type variable being free in the assumption list.  See
  'termMatch' for more details.
-}
ruleINSTANTIATE :: HOLThmRep thm cls thry 
                => Instantiation -> thm -> HOL cls thry HOLThm
ruleINSTANTIATE (_, [], ([], [], [])) pthm = toHThm pthm
ruleINSTANTIATE (_, [], tyenv) pthm = 
    primINST_TYPE_FULL tyenv $ toHThm pthm
ruleINSTANTIATE (bcs, tmenv, tyenv) pthm = note "ruleINSTANTIATE" $
    do thm <- toHThm pthm
       ithm <- if tyenv == ([], [], []) then return thm 
               else primINST_TYPE_FULL tyenv thm
       tthm <- primINST tmenv ithm <?> "instantiation failed."
       if hyp tthm == hyp thm
          then if null bcs then return tthm
               else (do ethm <- ruleHO_BETAS (concl ithm) (concl tthm)
                        primEQ_MP ethm tthm)
                    <|> return tthm
          else fail "term or type variable free in assumptions."
  where ruleHO_BETAS :: HOLTerm -> HOLTerm -> HOL cls thry HOLThm 
        ruleHO_BETAS Var{} _ = fail "ruleHO_BETAS"
        ruleHO_BETAS Const{} _ = fail "ruleHO_BETAS"
        ruleHO_BETAS (Abs _ bod1) (Abs bv bod2) =
            primABS bv $ ruleHO_BETAS bod1 bod2
        ruleHO_BETAS pat tm =
            let (hop, args) = stripComb pat
                n = length args in
              if lookup hop bcs == Just n
              then runConv (betasConv n) tm
              else case (pat, tm) of
                     (Comb lpat rpat, Comb ltm rtm) -> 
                         do { lth <- ruleHO_BETAS lpat ltm
                            ; (primMK_COMB lth $ ruleHO_BETAS rpat rtm) <|>
                                ruleAP_THM lth rtm
                            } <|> (ruleAP_TERM ltm $ ruleHO_BETAS rpat rtm)
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
                 do thm1 <- revItlistM ruleDISCH rhyps thm
                    thm2 <- ruleINSTANTIATE i thm1
                    funpowM (length rhyps) ruleUNDISCH thm2

-- term matching
termMatch :: MonadCatch m => [HOLTerm] -> HOLTerm -> HOLTerm -> m Instantiation
termMatch lconsts vtm ctm = 
    do pinsts_homs <- termPMatch lconsts [] vtm ctm ([], [])
       tyenv <- getTypeInsts (fst pinsts_homs) ([], [], [])
       insts <- termHOMatch lconsts tyenv pinsts_homs
       separateInsts insts

termPMatch :: (MonadCatch m, MonadThrow m) 
           => [HOLTerm] -> HOLTermEnv -> HOLTerm -> HOLTerm 
           -> (HOLTermEnv, [(HOLTermEnv, HOLTerm, HOLTerm)]) 
           -> m (HOLTermEnv, [(HOLTermEnv, HOLTerm, HOLTerm)])
termPMatch lconsts env vtm@Var{} ctm sofar@(insts, homs) =
    case lookup vtm env of
      Just ctm' -> 
          if ctm' == ctm then return sofar
          else fail' "termPMatch"
      Nothing -> 
          if vtm `elem` lconsts
          then if ctm == vtm then return sofar
               else fail' "termPMatch"
          else do insts' <- safeInsertA (vtm, ctm) insts
                  return (insts', homs)
termPMatch _ _ (Const vname vty) (Const cname cty) sofar@(insts, homs) =
    if vname == cname
    then if vty == cty then return sofar
         else let name = mkDummy in
                do insts' <- safeInsert (mkVar name vty, mkVar name cty) insts
                   return (insts', homs)
    else fail' "termPMatch"
termPMatch lconsts env (Abs vv@(Var _ vty) vbod) 
                       (Abs cv@(Var _ cty) cbod) (insts, homs) =
    let name = mkDummy in
      do insts' <- safeInsert (mkVar name vty, mkVar name cty) insts
         termPMatch lconsts ((vv, cv):env) vbod cbod (insts', homs)
termPMatch lconsts env vtm ctm sofar@(insts, homs) =
    do vhop <- repeatM rator vtm
       if isVar vhop && (vhop `notElem` lconsts) && 
          lookup vhop env == Nothing
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
                 _ -> fail' "termPMatch"

getTypeInsts :: (MonadCatch m, MonadThrow m) 
             => HOLTermEnv -> SubstTrip -> m SubstTrip
getTypeInsts insts i = 
    foldrM (\ (x, t) sofar -> case x of
                                (Var _ ty) -> 
                                    typeMatch ty (typeOf t) sofar
                                _ -> fail' "getTypeInsts") i insts

termHOMatch :: MonadCatch m => [HOLTerm] -> SubstTrip  
            -> (HOLTermEnv, [(HOLTermEnv, HOLTerm, HOLTerm)]) 
            -> m HOLTermEnv
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
          ((do tmenv <- mapM (\ a -> do a' <- assoc a env <|> 
                                              assoc a insts <|> 
                                              (if a `elem` lconsts 
                                               then return a 
                                               else fail' "termHOMatch")
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
                               ctm' <- B.subst ginsts ctm
                               let gvs = map snd ginsts
                               abstm <- listMkAbs gvs ctm'
                               vinsts <- safeInsertA (vhop, abstm) insts
                               combtm <- listMkComb vhop' gvs
                               let icpair = (combtm, ctm')
                               return (icpair:vinsts)
               termHOMatch lconsts tyenv (ni, rest))
           <|> (case (ctm, vtm) of
                  (Comb lc rc, Comb lv rv) -> 
                      do pinsts_homs' <- termPMatch lconsts env rv rc 
                                           (insts, (env, lv, lc):tail homs)
                         tyenv' <- getTypeInsts (fst pinsts_homs') ([], [], [])
                         termHOMatch lconsts tyenv' pinsts_homs'
                  _ -> fail' "termHOMatch"))

separateInsts :: (MonadCatch m, MonadThrow m) => HOLTermEnv -> m Instantiation
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
                                   if t == x' then fail' "separateInsts"
                                   else return (x', t)
                               _ -> fail' "separateInsts") realinsts
         return (betacounts, realinsts', tyenv)

insertByTest :: (Eq a, MonadThrow m) 
             => (b -> b -> Bool) -> (a, b) -> [(a, b)] -> m [(a, b)]
insertByTest test n@(x, y) l =
    case lookup x l of
      Nothing -> return (n:l)
      Just z -> if y `test` z then return l else fail' "insertByTest"

safeInsert :: (Eq a, Eq b, MonadThrow m) => (a, b) -> [(a, b)] -> m [(a, b)]
safeInsert = insertByTest (==)

safeInsertA :: MonadThrow m => (HOLTerm, HOLTerm) -> [(HOLTerm, HOLTerm)] 
            -> m [(HOLTerm, HOLTerm)]
safeInsertA = insertByTest aConv

mkDummy :: Text
mkDummy = 
    let (Var name _) = unsafeGenVar tyA in name




-- first order term unification
termUnify :: [HOLTerm] -> HOLTerm -> HOLTerm -> HOL cls thry Instantiation
termUnify vs t1 t2 = 
    do vars' <- unify vs t1 t2 []
       return ([], vars', ([], [], []))
  where unify :: [HOLTerm] -> HOLTerm -> HOLTerm -> HOLTermEnv 
              -> HOL cls thry HOLTermEnv
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
                  (_, _) -> fail "unify"

        augmentInsts :: (HOLTerm, HOLTerm) -> HOLTermEnv 
                     -> HOL cls thry HOLTermEnv
        augmentInsts (v, t) insts = 
            do t' <- varSubst insts t
               if t' == v 
                  then return insts
                  else if varFreeIn v t' then fail "augmentInsts"
                  else rawAugmentInsts (v, t') insts

        rawAugmentInsts :: (HOLTerm, HOLTerm) -> HOLTermEnv 
                        -> HOL cls thry HOLTermEnv
        rawAugmentInsts p insts = (:) p `fmap` mapM (augment1 [p]) insts

        augment1 :: HOLTermEnv -> (HOLTerm, HOLTerm) 
                 -> HOL cls thry (HOLTerm, HOLTerm)
        augment1 sofar (x, s) = 
            do s' <- subst sofar s
               if varFreeIn x s && s /= x 
                  then fail "augment1"
                  else return (x, s')

           
-- modify variables at depth
tryalpha :: HOLTerm -> HOLTerm -> HOLTerm
tryalpha v tm = 
    case runCatch $ alpha v tm <|> alpha (variant (frees tm) v) tm of
      Right res -> res
      _         -> tm


deepAlpha :: [(Text, Text)] -> HOLTerm -> HOL cls thry HOLTerm
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
    mkComb (deepAlpha env l) (deepAlpha env r)
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
       abod <- deepAlpha bvms bod
       ath <- primEQ_MP (ruleALPHA bod abod) sth
       abod' <- partfn abod
       insts <- termMatch lconsts abod' tm
       return (insts, ath, fvs)

rulePART_MATCH :: (BoolCtxt thry, HOLThmRep thm cls thry,
                   HOLTermRep tm cls thry) 
               => (HOLTerm -> HOL cls thry HOLTerm) -> thm -> tm 
               -> HOL cls thry HOLThm
rulePART_MATCH partFun thm ptm = note "rulePART_MATCH" $
  do tm <- toHTm ptm
     (insts, ath, _) <- partInsts partFun thm tm
     fth <- ruleINSTANTIATE insts ath
     if hyp fth /= hyp ath 
        then fail "instantiated hyps."
        else do tm' <- partFun $ concl fth
                if tm' == tm 
                   then return fth
                   else (ruleSUBS [ruleALPHA tm' tm] fth) <?> 
                          "sanity check failure"

ruleGEN_PART_MATCH :: (BoolCtxt thry, HOLThmRep thm cls thry,
                       HOLTermRep tm cls thry) 
                   => (HOLTerm -> HOL cls thry HOLTerm) -> thm -> tm 
                   -> HOL cls thry HOLThm
ruleGEN_PART_MATCH partFun thm ptm = 
  do tm <- toHTm ptm
     (insts, ath, fvs) <- partInsts partFun thm tm
     eth <- ruleINSTANTIATE insts $ ruleGENL fvs ath
     fth <- foldrM (\ _ th -> liftM snd $ ruleSPEC_VAR th) eth fvs
     if hyp fth /= hyp ath 
        then fail "instantiate hyps"
        else do tm' <- partFun $ concl fth 
                if tm' == tm 
                   then return fth
                   else (ruleSUBS [ruleALPHA tm' tm] fth) <?>
                          "sanity check failure"

ruleMATCH_MP :: (BoolCtxt thry, HOLThmRep thm1 cls thry, 
                 HOLThmRep thm2 cls thry) 
             => thm1 -> thm2 -> HOL cls thry HOLThm
ruleMATCH_MP pith pth = 
    do ith <- toHThm pith
       th <- toHThm pth
       sth <- let tm = concl ith
                  (avs, bod) = stripForall tm in
                case destImp bod of
                  Just (ant, _) -> 
                      (let (svs, pvs) = partition (`varFreeIn` ant) avs in
                         if null pvs then return ith
                         else do th1 <- ruleSPECL avs $ primASSUME tm
                                 th2 <- ruleGENL svs . ruleDISCH ant . 
                                          ruleGENL pvs $ ruleUNDISCH th1
                                 th3 <- ruleDISCH tm th2
                                 ruleMP th3 ith) <?> "ruleMATCH_MP"
                  _ -> fail "ruleMATCH_MP: not an implication"
       thm <- (rulePART_MATCH (liftM fst . destImp) sth $ concl th) <?> 
                "ruleMATCH_MP: no match"
       ruleMP thm th
       
convHIGHER_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                   => [thm] -> Bool -> Conversion cls thry
convHIGHER_REWRITE ths top = Conv $ \ tm ->
    do thl <- mapM (ruleGINST . ruleSPEC_ALL) ths
       let concs = map concl thl
       (preds, pats) <- liftM unzip $ mapM destComb =<< mapM lhs concs
       betaFns <- map2 convBETA_VAR preds concs
       let asmList = zip pats . zip preds $ zip thl betaFns
           mnet = foldr (\ p n -> netEnter [] (p, p) n) netEmpty pats
           lookFn t = mapFilterM (\ p -> do void $ termMatch [] p t
                                            return p) $ netLookup t mnet
           predFn t = do ts <- lookFn t
                         return $! not (null ts) && t `freeIn` tm
       stm <- if top then findTermM predFn tm
              else liftM (head . sort freeIn) $ findTermsM predFn tm
       pat <- liftM head $ lookFn stm
       (_, tmenv, _) <- termMatch [] pat stm
       (ptm, (th, betaFn)) <- pat `assoc` asmList
       gv <- genVar $ typeOf stm
       tm' <- subst [(stm, gv)] tm
       tm'' <- mkAbs gv tm'
       (_, tmenv0, tyenv0) <- termMatch [] ptm tm''
       ruleCONV betaFn . primINST tmenv . primINST tmenv0 $
         primINST_TYPE_FULL tyenv0 th
  where convBETA_VAR :: HOLTerm -> HOLTerm -> Conversion cls thry
        convBETA_VAR v tm =
            case runCatch $ freeBeta v tm of
              Right res -> res
              _         -> _FAIL "convBETA_VAR"

        freeBeta :: HOLTerm -> HOLTerm -> Catch (Conversion cls thry)
        freeBeta v (Abs bv bod)
            | v == bv = fail' "freeBeta"
            | otherwise = liftM convABS (freeBeta v bod)
        freeBeta v tm =
            let (op, args) = stripComb tm in
              if null args then fail' "freeBeta"
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

        ruleGINST :: HOLThmRep thm cls thry => thm -> HOL cls thry HOLThm
        ruleGINST pthm =
            (do thm@(Thm asl c) <- toHThm pthm
                let fvs = frees c \\ catFrees asl
                gvs <- mapM (genVar . typeOf) fvs
                primINST (zip fvs gvs) thm) <?> "ruleGINST"
        

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

getADefinition' :: Text -> Query TheDefinitions (Maybe HOLThm)
getADefinition' name =
    do (TheDefinitions defs) <- ask
       return $! name `mapAssoc` defs

makeAcidic ''TheDefinitions 
    ['insertDefinition, 'getDefinitions, 'getADefinition']

getADefinition :: Text -> HOL cls thry (Maybe HOLThm)
getADefinition lbl = 
    do acid <- openLocalStateHOL (TheDefinitions mapEmpty)
       qth <- queryHOL acid (GetADefinition' lbl)
       closeAcidStateHOL acid
       return qth

newDefinition :: (BoolCtxt thry, HOLTermRep tm Theory thry) 
              => (Text, tm) -> HOL Theory thry HOLThm
newDefinition (lbl, ptm) = note "newDefinition" $
    do qth <- getADefinition lbl
       case qth of
         Just th ->
             return th
         Nothing -> 
           do tm <- toHTm ptm
              let (avs, bod) = stripForall tm
              (l, r) <- destEq bod <?> "not an equation."
              let (lv, largs) = stripComb l
              case lv of
                Var name _
                  | name /= lbl ->
                      fail $ "provided label does not match provided term."
                  | otherwise ->
                      do rtm <- listMkAbs largs r <?> 
                                  "Non-variable in LHS pattern."
                         def <- mkEq lv rtm
                         thm1 <- newBasicDefinition (lbl, def)
                         thm2 <- foldlM (\ thm t -> 
                                   do ithm <- ruleAP_THM thm t
                                      ithm' <- rand $ concl ithm
                                      ithm'' <- runConv convBETA ithm'
                                      primTRANS ithm ithm'') thm1 largs
                         let rvs = filter (not . (`elem` avs)) largs
                         genthm <- foldrM ruleGEN thm2 avs
                         th <- foldrM ruleGEN genthm rvs
                         acid' <- openLocalStateHOL (TheDefinitions mapEmpty)
                         updateHOL acid' (InsertDefinition lbl th)
                         closeAcidStateHOL acid'
                         return th
                _ -> fail $ "Non-variable constructor in LHS pattern."

getDefinition :: Text -> HOL cls thry HOLThm
getDefinition lbl =
    do qth <- getADefinition lbl
       case qth of
         Just res -> return res
         _ -> fail $ "getDefinition: definition for " ++ show lbl ++ 
                     " not found."
