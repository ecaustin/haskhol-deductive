{-# LANGUAGE FlexibleContexts, FlexibleInstances, PatternSynonyms, 
             ScopedTypeVariables, TypeSynonymInstances #-}
{-|
  Module:    HaskHOL.Lib.Simp
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Simp
       ( GConversion
       , convREWR
       , convIMP_REWR
       , convORDERED_REWR
       , convORDERED_IMP_REWR
       , termOrder
       , netOfThm
       , netOfConv
       , netOfCong
       , mkRewrites
       , convREWRITES
       , Prover
       , mkProver
       , augment
       , applyProver
       , Simpset
       , Strategy
       , basicProver
       , ssOfThms
       , ssOfConv
       , ssOfCongs
       , ssOfProver
       , ssOfProvers
       , ssOfMaker
       , ruleAUGMENT_SIMPSET
       , setBasicRewrites
       , extendBasicRewrites
       , basicRewrites
       , setBasicConvs
       , extendBasicConvs
       , basicConvs
       , basicNet
       , setBasicCongs
       , extendBasicCongs
       , basicCongs
       , convGENERAL_REWRITE
       , convGEN_REWRITE
       , convPURE_REWRITE
       , convREWRITE
       , convREWRITE_NIL
       , convPURE_ONCE_REWRITE
       , convONCE_REWRITE
       , ruleGEN_REWRITE
       , rulePURE_REWRITE
       , ruleREWRITE
       , ruleREWRITE_NIL
       , rulePURE_ONCE_REWRITE
       , ruleONCE_REWRITE
       , rulePURE_ASM_REWRITE
       , ruleASM_REWRITE
       , rulePURE_ONCE_ASM_REWRITE
       , ruleONCE_ASM_REWRITE
       , tacGEN_REWRITE
       , tacPURE_REWRITE
       , tacREWRITE
       , tacREWRITE_NIL
       , tacPURE_ONCE_REWRITE
       , tacONCE_REWRITE
       , tacPURE_ASM_REWRITE
       , tacPURE_ASM_REWRITE_NIL
       , tacASM_REWRITE
       , tacASM_REWRITE_NIL
       , tacPURE_ONCE_ASM_REWRITE
       , tacONCE_ASM_REWRITE
       , convGEN_SIMPLIFY
       , convONCE_SIMPLIFY
       , convSIMPLIFY
       , emptySS
       , basicSS
       , convSIMP
       , convPURE_SIMP
       , convONCE_SIMP
       , ruleSIMP
       , rulePURE_SIMP
       , ruleONCE_SIMP
       , tacSIMP
       , tacPURE_SIMP
       , tacONCE_SIMP
       , tacASM_SIMP
       , tacPURE_ASM_SIMP
       , tacONCE_ASM_SIMP
       , tacABBREV
       , tacEXPAND
       , thmEQ_REFL
       , thmIMP_CLAUSES
       ) where

import HaskHOL.Core

import HaskHOL.Lib.Bool
import HaskHOL.Lib.Bool.Context
import HaskHOL.Lib.Equal
import HaskHOL.Lib.Itab
import HaskHOL.Lib.DRule
import HaskHOL.Lib.Tactics

import System.IO.Unsafe (unsafePerformIO)
import Data.IORef

data BasicConvs = 
    BasicConvs ![(Text, (HOLTerm, (String, [String])))] deriving Typeable

deriveSafeCopy 0 'base ''BasicConvs

getConvs :: Query BasicConvs [(Text, (HOLTerm, (String, [String])))]
getConvs =
    do (BasicConvs convs) <- ask
       return convs

putConvs :: [(Text, (HOLTerm, (String, [String])))] -> Update BasicConvs ()
putConvs convs = put (BasicConvs convs)

addConv :: (Text, (HOLTerm, (String, [String]))) -> Update BasicConvs ()
addConv (name, patcong) =
    do (BasicConvs convs) <- get
       put (BasicConvs $ (name, patcong) : 
                         filter (\ (name', _) -> name /= name') convs)

makeAcidic ''BasicConvs ['getConvs, 'putConvs, 'addConv]

{-# NOINLINE conversionNet #-}
conversionNet :: HOLRef (Maybe (Net (GConversion cls thry)))
conversionNet = unsafePerformIO $ newIORef Nothing

type GConversion cls thry = (Int, Conversion cls thry)

-- primitive rewriting conversionals
convREWR :: (BoolCtxt thry, HOLThmRep thm cls thry) => thm 
         -> Conversion cls thry
convREWR th = Conv $ \ tm -> 
    do th' <- toHThm th
       rulePART_MATCH lhs th' tm

convIMP_REWR :: BoolCtxt thry => HOLThm -> Conversion cls thry
convIMP_REWR th = Conv $ \ tm -> 
    rulePART_MATCH (lhs <=< liftM snd . destImp) th tm

-- ordered rewriting conversionals
convORDERED_REWR :: (BoolCtxt thry, HOLThmRep thm cls thry) => 
                    (HOLTerm -> HOLTerm -> HOL cls thry Bool) -> thm -> 
                    Conversion cls thry
convORDERED_REWR ord th = Conv $ \ tm ->
    let basic_conv = convREWR th in
      do thm <- runConv basic_conv tm
         case destEq $ concl thm of
           Just (l, r) -> do cond <- ord l r
                             if cond
                                then return thm
                                else fail "convORDERED_REWR: wrong orientation"
           _ -> fail "convORDERED_IMP_REWR"

convORDERED_IMP_REWR :: BoolCtxt thry 
                     => (HOLTerm -> HOLTerm -> HOL cls thry Bool) -> HOLThm 
                     -> Conversion cls thry
convORDERED_IMP_REWR ord th = Conv $ \ tm -> 
    let basic_conv = convIMP_REWR th in
      do thm <- runConv basic_conv tm
         case destEq <=< rand $ concl thm of
           Just (l, r) -> do cond <- ord l r
                             if cond
                                then return thm
                                else fail "convORDERED_IMP_REWR: wrong orientation"
           _ -> fail "convORDERED_IMP_REWR"

-- alpha conversion compatible term ordering
lexify :: (HOLTerm -> HOLTerm -> Bool) -> [HOLTerm] -> [HOLTerm] -> Bool
lexify _ [] _ = False
lexify _ _ [] = True
lexify ord (a:as) (b:bs) = 
    ord a b || (a == b && lexify ord as bs)

dyn_order :: HOLTerm -> HOLTerm -> HOLTerm -> Bool
dyn_order top tm1 tm2 = 
    let (f1, args1) = stripComb tm1
        (f2, args2) = stripComb tm2 in
      if f1 == f2 then lexify (dyn_order f1) args1 args2
      else (f2 /= top) && ((f1 == top) || (f1 > f2))

termOrder :: BoolCtxt thry => HOLTerm -> HOLTerm -> HOL cls thry Bool
termOrder tm1 tm2 = 
    do tm <- serve [bool| T |]
       return $! dyn_order tm tm1 tm2

-- create a net for a theorem
netOfThm :: BoolCtxt thry => Bool -> HOLThm 
         -> Net (GConversion cls thry) 
         -> Maybe (Net (GConversion cls thry))
netOfThm rep th net = 
  let tm = concl th
      lconsts = catFrees $ hyp th
      matchable x y = (termMatch lconsts x y >> return True) <|> return False in
    case tm of
      (l@(Abs x (Comb v@Var{} x')) := v') ->
          if x' == x && v' == v && x /= v
          then return $! netEnter lconsts 
                           (l, (1, convBASEABS v th)) net
          else Nothing
      (l := r) ->
          if rep && l `freeIn` r
          then return $! 
                 netEnter lconsts (l, (1,
                   Conv $ \ x -> do th' <- ruleEQT_INTRO th
                                    runConv (convREWR th') x)) net
          else do cond1 <- matchable l r
                  cond2 <- matchable r l
                  if rep && cond1 && cond2
                    then return $! netEnter lconsts 
                                     (l, (1, convORDERED_REWR termOrder th)) net
                    else return $! netEnter lconsts 
                                     (l, (1, convREWR th)) net
      (Comb (Comb _ t) (l := r)) ->
            if rep && l `freeIn` r
            then return $! netEnter lconsts 
                   (l, (3, Conv $ \ x -> do th' <- ruleDISCH t =<< 
                                                     ruleEQT_INTRO =<< 
                                                       ruleUNDISCH th
                                            runConv (convIMP_REWR th') x)) net
            else do cond1 <- matchable l r
                    cond2 <- matchable r l
                    if rep && cond1 && cond2
                      then return $! netEnter lconsts 
                             (l, (3, convORDERED_IMP_REWR termOrder th)) net
                      else return $! netEnter lconsts 
                                     (l, (3, convIMP_REWR th)) net
      _ -> Nothing
  where convBASEABS :: HOLTerm -> HOLThm -> Conversion cls thry
        convBASEABS v thm = Conv $ \ tm ->
            case tm of
              (Abs y (Comb t y')) ->
                  if y == y' && not (y `freeIn` t)
                  then do t' <- liftO $ termMatch [] v t
                          ruleINSTANTIATE t' thm
                  else fail "convREWR (axETA special case)"
              _ -> fail "convREWR (axETA special case)"

-- create a net for a gconversion using "defunctionalized" conversions
-- safe conversion of phantom variables, as guarded by context
netOfConv :: Ord a => HOLTerm -> a -> Net (Int, a) -> (Net (Int, a))
netOfConv tm conv net = 
    netEnter [] (tm, (2, conv)) net

netOfCong :: BoolCtxt thry => HOLThm 
          -> Net (GConversion cls thry) 
          -> Maybe (Net (GConversion cls thry))
netOfCong th sofar = 
    do (pat, n) <- do (conc, n) <- repeatM (\ (tm, m) -> 
                                            case destImp tm of
                                              Just (_, x) -> Just (x, m+1)
                                              _ -> Nothing) (concl th, 0)
                      if n == 0 
                         then Nothing
                         else do pat <- lHand conc
                                 return (pat, n)
       return $! netEnter [] (pat, (4, convBASE n th)) sofar
  where convBASE :: BoolCtxt thry => Int -> HOLThm -> Conversion cls thry
        convBASE n thm = Conv $ \ tm ->
            ruleGEN_PART_MATCH (lHand <=< funpowM n rand) thm tm

-- rewrite maker
convIMP_CONJ :: BoolCtxt thry => Conversion cls thry
convIMP_CONJ = convREWR convIMP_CONJ_pth
  where convIMP_CONJ_pth :: BoolCtxt thry => HOL cls thry HOLThm
        convIMP_CONJ_pth = cacheProof "convIMP_CONJ_pth" ctxtBool $
            ruleITAUT [str| p ==> q ==> r <=> p /\ q ==> r |] 

ruleIMP_EXISTS :: BoolCtxt thry => HOLTerm -> HOLThm -> HOL cls thry HOLThm
ruleIMP_EXISTS v th = 
    ruleCONV (convREWR ruleIMP_EXISTS_pth) =<< ruleGEN v th
  where ruleIMP_EXISTS_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleIMP_EXISTS_pth = cacheProof "ruleIMP_EXISTS_pth" ctxtBool $
            ruleITAUT "(!x. P x ==> Q) <=> (?x . P x) ==> Q"

collect_condition :: BoolCtxt thry => [HOLTerm] -> HOLThm -> HOL cls thry HOLThm
collect_condition oldhyps th =
    let conds = hyp th \\ oldhyps in
      if null conds then return th
      else do jth <- foldrM ruleDISCH th conds
              kth <- ruleCONV (_REPEAT convIMP_CONJ) jth
              case destImp $ concl kth of
                Just (cond, eqn) -> let fvs = (frees cond \\ frees eqn) \\ catFrees oldhyps in
                                      foldrM ruleIMP_EXISTS kth fvs
                _ -> fail "collect_condition"

split_rewrites :: BoolCtxt thry => [HOLTerm] -> Bool -> HOLThm -> [HOLThm] 
               -> HOL cls thry [HOLThm]
split_rewrites oldhyps cf th sofar =
    let tm = concl th in
      if isForall tm
      then do th' <- ruleSPEC_ALL th
              split_rewrites oldhyps cf th' sofar
      else if isConj tm
           then do th1 <- ruleCONJUNCT1 th
                   th2 <- ruleCONJUNCT2 th
                   sofar' <- split_rewrites oldhyps cf th2 sofar
                   split_rewrites oldhyps cf th1 sofar'
      else if isImp tm && cf
           then do th' <- ruleUNDISCH th
                   split_rewrites oldhyps cf th' sofar
      else if isEq tm
           then if cf then do th' <- collect_condition oldhyps th
                              return $! th':sofar
                else return $! th:sofar
      else case destNeg tm of
             Just tm' -> do th' <- ruleEQF_INTRO th
                            ths <- split_rewrites oldhyps cf th' sofar
                            if isEq tm'
                               then do th'' <- ruleEQF_INTRO =<< ruleGSYM th
                                       split_rewrites oldhyps cf th'' ths
                               else return ths
             _ -> do th' <- ruleEQT_INTRO th
                     split_rewrites oldhyps cf th' sofar

mkRewrites :: (BoolCtxt thry, HOLThmRep thm cls thry) => Bool -> thm 
           -> [HOLThm] -> HOL cls thry [HOLThm]
mkRewrites cf pth ths = 
    do th <- toHThm pth
       split_rewrites (hyp th) cf th ths

convREWRITES :: BoolCtxt thry => Net (GConversion cls thry) 
             -> Conversion cls thry
convREWRITES net = Conv $ \ tm ->
    let pconvs = netLookup tm net in
      tryFind (\ (_, cnv) -> runConv cnv tm) pconvs
      <?> "convREWRITES"

-- provers
-- provers
data Prover cls thry = 
    Prover (Conversion cls thry) ([HOLThm] -> Prover cls thry)

mkProver :: forall cls thry. (HOLTerm -> Conversion cls thry) 
         -> (HOLTerm -> [HOLThm] -> HOLTerm) 
         -> HOLTerm -> Prover cls thry
mkProver applicator augmentor = mkProverRec
  where mkProverRec :: HOLTerm -> Prover cls thry
        mkProverRec state =
            let app = applicator state
                aug thms = mkProverRec $ augmentor state thms in
              Prover app aug

augment :: Prover cls thry -> [HOLThm] -> Prover cls thry
augment (Prover _ aug) = aug

applyProver :: Prover cls thry -> HOLTerm -> HOL cls thry HOLThm
applyProver (Prover conv _ ) = runConv conv

-- simpsets
data Simpset cls thry = Simpset (Net (GConversion cls thry))
                        (Strategy cls thry -> Strategy cls thry)
                        [Prover cls thry]
                        (HOLThm -> [HOLThm] -> HOL cls thry [HOLThm])

type Strategy cls thry = Simpset cls thry -> Int -> Conversion cls thry

-- basic prover - recursively simplify then try provers
basicProver :: BoolCtxt thry => Strategy cls thry -> Strategy cls thry
basicProver strat ss@(Simpset _ _ provers _) lev = Conv $ \ tm ->
    do sth <- runConv (strat ss lev) tm <|> (return $! primREFL tm)
       ruleEQT_ELIM sth <|> 
         (do tth <- tryFind (\ pr -> case rand $ concl sth of
                                       Just stm -> applyProver pr stm
                                       _ -> fail "") provers
             fromRightM $ liftM1 primEQ_MP (ruleSYM sth) tth)

ssOfThms :: BoolCtxt thry => [HOLThm] 
         -> Simpset cls thry
         -> HOL cls thry (Simpset cls thry)
ssOfThms thms (Simpset net prover provers rewmaker) =
    do cthms <- foldrM rewmaker [] thms
       net' <- liftO $ foldrM (netOfThm True) net cthms
       return $! Simpset net' prover provers rewmaker

ssOfConv :: HOLTerm -> Conversion cls thry -> Simpset cls thry 
         -> Simpset cls thry
ssOfConv keytm conv (Simpset net prover provers rewmaker) =
    Simpset (netOfConv keytm conv net) prover provers rewmaker

ssOfCongs :: BoolCtxt thry => [HOLThm] 
          -> Simpset cls thry
          -> Maybe (Simpset cls thry)
ssOfCongs thms (Simpset net prover provers rewmaker) =
   do net' <- foldrM netOfCong net thms
      return $! Simpset net' prover provers rewmaker

ssOfProver :: (Strategy cls thry -> Strategy cls thry) -> Simpset cls thry
           -> Simpset cls thry
ssOfProver newprover (Simpset net _ provers rewmaker) =
    Simpset net newprover provers rewmaker

ssOfProvers :: [Prover cls thry] -> Simpset cls thry -> Simpset cls thry
ssOfProvers newprovers (Simpset net prover provers rewmaker) =
    Simpset net prover (newprovers ++ provers) rewmaker

ssOfMaker :: (HOLThm -> [HOLThm] -> HOL cls thry [HOLThm]) -> Simpset cls thry
          -> Simpset cls thry
ssOfMaker newmaker (Simpset net prover provers _) =
    Simpset net prover provers newmaker

ruleAUGMENT_SIMPSET :: BoolCtxt thry => HOLThmRep thm cls thry => thm 
                    -> Simpset cls thry
                    -> HOL cls thry (Simpset cls thry)
ruleAUGMENT_SIMPSET pth (Simpset net prover provers rewmaker) =
    do cth <- toHThm pth
       let provers' = map (`augment` [cth]) provers
       cthms <- rewmaker cth []
       net' <- liftO $ foldrM (netOfThm True) net cthms
       return $ Simpset net' prover provers' rewmaker

-- sqconvs
convIMP_REWRITES :: BoolCtxt thry => Strategy cls thry
                 -> Simpset cls thry
                 -> Int -> [GConversion cls thry] -> Conversion cls thry
convIMP_REWRITES strat ss@(Simpset _ prover _ _) lev pconvs = Conv $ \ tm ->
    tryFind (\ (n, cnv) -> 
             if n >= 4 then fail "fail"
             else do th <- runConv cnv tm
                     let etm = concl th
                     if isEq etm 
                        then return th
                        else if lev <= 0 then fail "convIMP_REWRITES: too deep"
                             else case lHand etm of
                                    Just etm' -> 
                                      do cth <- runConv (prover strat ss (lev-1)) etm'
                                         ruleMP th cth
                                    _ -> fail "") pconvs

convGEN_SUB :: BoolCtxt thry => Strategy cls thry
            -> Simpset cls thry -> Int
            -> [GConversion cls thry] 
            -> Conversion cls thry
convGEN_SUB strat ss lev pconvs = Conv $ \ tm ->
    tryFind (\ (n, cnv) -> if n < 4 then fail "fail"
                           else do th <- runConv cnv tm
                                   cRUN_SUB_CONV strat ss lev True th) pconvs
    <|> (case tm of
            (Comb l r) -> (do th1 <- runConv (strat ss lev) l
                              (do th2 <- runConv (strat ss lev) r
                                  fromRightM $ primMK_COMB th1 th2)
                                <|> fromRightM (ruleAP_THM th1 r))
                          <|> (do rth <- runConv (strat ss lev) r
                                  fromRightM $ ruleAP_TERM l rth)
            (Abs v bod) -> (do th <- runConv (strat ss lev) bod
                               fromRightM $ primABS v th) 
                           <|> (do gv <- genVar $ typeOf v
                                   let gbod = fromJust $ varSubst [(gv, v)] bod
                                   gbodth <- runConv (strat ss lev) gbod
                                   gth <- fromRightM $ primABS gv gbodth
                                   let gtm = concl gth
                                   case destEq gtm of
                                     Just (l, r) -> let v' = variant (frees gtm) v in
                                                      do (l', r') <- liftEither "convGEN_SUB: alpha" $ 
                                                                     pairMapM (alpha v') (l, r)
                                                         eq <- mkEq l' r'
                                                         th <- fromRightM $ ruleALPHA gtm eq
                                                         fromRightM $ primEQ_MP th gth
                                     _ -> fail "convGEN_SUB")
            _ -> fail "convGEN_SUB")

cRUN_SUB_CONV :: BoolCtxt thry => Strategy cls thry
              -> Simpset cls thry
              -> Int -> Bool -> HOLThm -> HOL cls thry HOLThm
cRUN_SUB_CONV strat ss lev triv th =
    let tm = concl th in
      (case destImp tm of
         Just (subtm, _) -> 
             let (avs, bod) = stripForall subtm in
               do ((t, t'), ss', mk_fun) <- fromJustM (do ts <- destEq bod
                                                          return (ts, ss, return))
                                            <|> (do (c, deq) <- fromJustM $ destImp bod
                                                    cTh <- fromRightM $ primASSUME c
                                                    ssth' <- ruleAUGMENT_SIMPSET cTh ss
                                                    x <- fromJustM $ destEq deq
                                                    return (x, ssth', ruleDISCH c))
                  (eth, triv') <- (do x <- runConv (strat ss' lev) t
                                      return (x, False))
                                  <|> return (primREFL t, triv)
                  eth' <- ruleGENL avs =<< mk_fun eth
                  th' <- case t' of
                           Var{} -> do t'' <- fromJustM . rand $ concl eth
                                       liftO $! primINST [(t', t'')] th
                           _ -> ruleGEN_PART_MATCH lHand th (concl eth')
                  th'' <- ruleMP th' eth'
                  cRUN_SUB_CONV strat ss lev triv' th''
         _ -> if triv then fail ""
              else return th)
      <?> "cRUN_SUB_CONV"

sqconvTOP_DEPTH :: BoolCtxt thry 
                => Strategy cls thry
sqconvTOP_DEPTH ss@(Simpset net _ _ _) lev = Conv $ \ tm ->
    let pconvs = netLookup tm net in
      do th1 <- runConv (convIMP_REWRITES sqconvTOP_DEPTH ss lev pconvs) tm 
                <|> runConv (convGEN_SUB sqconvTOP_DEPTH ss lev pconvs) tm
         case rand $ concl th1 of
             Just t -> (do th2 <- runConv (sqconvTOP_DEPTH ss lev) t
                           fromRightM $ primTRANS th1 th2) <|> return th1
             _ -> return th1

sqconvONCE_DEPTH :: BoolCtxt thry => Strategy cls thry
sqconvONCE_DEPTH ss@(Simpset net _ _ _) lev = Conv $ \ tm ->
    let pconvs = netLookup tm net in
      runConv (convIMP_REWRITES sqconvONCE_DEPTH ss lev pconvs) tm <|>
      runConv (convGEN_SUB sqconvONCE_DEPTH ss lev pconvs) tm

-- keeping track of rewrites and gconversional nets
data Rewrites = Rewrites ![HOLThm] deriving Typeable

deriveSafeCopy 0 'base ''Rewrites

putRewrites :: [HOLThm] -> Update Rewrites ()
putRewrites ths =
    put (Rewrites ths)

addRewrites :: [HOLThm] -> Update Rewrites ()
addRewrites ths =
    do (Rewrites xs) <- get
       put (Rewrites (ths++xs))

getRewrites :: Query Rewrites [HOLThm]
getRewrites =
    do (Rewrites ths) <- ask
       return ths

makeAcidic ''Rewrites ['putRewrites, 'addRewrites, 'getRewrites]


setBasicRewrites :: BoolCtxt thry => [HOLThm] -> HOL Theory thry ()
setBasicRewrites thl =
    do canonThl <- foldrM (mkRewrites False) [] thl
       acid <- openLocalStateHOL (Rewrites [])
       updateHOL acid (PutRewrites canonThl)
       createCheckpointAndCloseHOL acid
       rehashConvnet

extendBasicRewrites :: BoolCtxt thry => [HOLThm] -> HOL Theory thry ()
extendBasicRewrites thl = 
    do canonThl <- foldrM (mkRewrites False) [] thl
       acid <- openLocalStateHOL (Rewrites [])
       updateHOL acid (AddRewrites canonThl)
       createCheckpointAndCloseHOL acid
       rehashConvnet

basicRewrites :: HOL cls thry [HOLThm]
basicRewrites =
    do acid <- openLocalStateHOL (Rewrites [])
       ths <- queryHOL acid GetRewrites
       closeAcidStateHOL acid
       return ths

setBasicConvs :: BoolCtxt thry => [(Text, (HOLTerm, (String, [String])))] 
              -> HOL Theory thry ()
setBasicConvs cnvs =
    do acid <- openLocalStateHOL (BasicConvs [])
       updateHOL acid (PutConvs cnvs)
       createCheckpointAndCloseHOL acid
       rehashConvnet

extendBasicConvs :: (BoolCtxt thry, HOLTermRep tm Theory thry) 
                 => (Text, (tm, (String, [String]))) -> HOL Theory thry ()
extendBasicConvs (name, (ptm, conv)) = 
    do tm <- toHTm ptm
       acid <- openLocalStateHOL (BasicConvs [])
       updateHOL acid (AddConv (name, (tm, conv)))
       createCheckpointAndCloseHOL acid
       rehashConvnet

-- Interpreted code must be of type HOL Proof thry, so we need to
-- build the entire `runConv conv tm` rather than just recalling conv by name
basicConvs :: CtxtName thry 
           => HOL cls thry [(Text, (HOLTerm, Conversion cls thry))]
basicConvs =
    do acid <- openLocalStateHOL (BasicConvs [])
       convs <- queryHOL acid GetConvs
       closeAcidStateHOL acid
       return $! map (\ (x, (y, (m, mods))) -> (x, (y, Conv $ \ tm -> 
                        do tm' <- showHOL tm
                           let tm'' = "[str| " ++ tm' ++ " |]"
                               expr = "runConv " ++ m ++ " =<< toHTm " ++ tm''
                           runHOLHint expr ("HaskHOL.Lib.Equal":mods)))) convs

basicNet :: BoolCtxt thry => HOL cls thry (Net (GConversion cls thry))
basicNet =
    do net <- readHOLRef conversionNet
       case net of
         Just net' -> return net'
         Nothing -> do rehashConvnet
                       basicNet

rehashConvnet :: BoolCtxt thry => HOL cls thry ()
rehashConvnet =
  do rewrites <- basicRewrites
     cnvs <- liftM (map snd) basicConvs
     let convs = foldr (uncurry netOfConv) netEmpty cnvs
     net <- liftO $ foldrM (netOfThm True) convs rewrites
     writeHOLRef conversionNet (Just net)


-- default congruences
data Congruences = Congruences ![HOLThm] deriving Typeable

deriveSafeCopy 0 'base ''Congruences

putCongruences :: [HOLThm] -> Update Congruences ()
putCongruences ths =
    put (Congruences ths)

addCongruences :: [HOLThm] -> Update Congruences ()
addCongruences ths =
    do (Congruences xs) <- get
       put (Congruences (ths `union` xs))

getCongruences :: Query Congruences [HOLThm]
getCongruences =
    do (Congruences xs) <- ask
       return xs

makeAcidic ''Congruences ['putCongruences, 'addCongruences, 'getCongruences]


setBasicCongs :: [HOLThm] -> HOL Theory thry ()
setBasicCongs thl =
    do acid <- openLocalStateHOL (Congruences [])
       updateHOL acid (PutCongruences thl)
       createCheckpointAndCloseHOL acid

extendBasicCongs :: [HOLThm] -> HOL Theory thry ()
extendBasicCongs thl = 
    do acid <- openLocalStateHOL (Congruences [])
       updateHOL acid (AddCongruences thl)
       createCheckpointAndCloseHOL acid

basicCongs :: HOL cls thry [HOLThm]
basicCongs =
    do acid <- openLocalStateHOL (Congruences [])
       congs <- queryHOL acid GetCongruences
       closeAcidStateHOL acid
       return congs

-- main rewriting conversions
convGENERAL_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => Bool 
                    -> (Conversion cls thry -> Conversion cls thry) 
                    -> Net (GConversion cls thry) -> [thm] 
                    -> Conversion cls thry
convGENERAL_REWRITE f c n pths = Conv $ \ tm ->
    do pths' <- mapM toHThm pths
       runConv (convGENERAL_REWRITE' f c n pths') tm

convGENERAL_REWRITE' :: BoolCtxt thry => Bool 
                     -> (Conversion cls thry -> Conversion cls thry) 
                     -> Net (GConversion cls thry) -> [HOLThm] 
                     -> Conversion cls thry
convGENERAL_REWRITE' rep cnvl builtin_net ths = Conv $ \ tm ->
    do ths_canon <- foldrM (mkRewrites False) [] ths
       final_net <- liftO $ foldrM (netOfThm rep) builtin_net ths_canon
       runConv (cnvl (convREWRITES final_net)) tm

convGEN_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry)
                => (Conversion cls thry -> Conversion cls thry) -> [thm] 
                -> Conversion cls thry
convGEN_REWRITE cnvl = convGENERAL_REWRITE False cnvl netEmpty

convPURE_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => [thm] 
                 -> Conversion cls thry
convPURE_REWRITE = convGENERAL_REWRITE True convTOP_DEPTH netEmpty

convREWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => [thm]
            -> Conversion cls thry
convREWRITE thl = Conv $ \ tm ->
    do net <- basicNet
       runConv (convGENERAL_REWRITE True convTOP_DEPTH net thl) tm

convREWRITE_NIL :: BoolCtxt thry => Conversion cls thry
convREWRITE_NIL = Conv $ \ tm ->
    do net <- basicNet
       runConv (convGENERAL_REWRITE' True convTOP_DEPTH net []) tm

convPURE_ONCE_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => [thm] 
                      -> Conversion cls thry
convPURE_ONCE_REWRITE = 
    convGENERAL_REWRITE False convONCE_DEPTH netEmpty

convONCE_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                 => [thm] -> Conversion cls thry
convONCE_REWRITE thl = Conv $ \ tm ->
    do net <- basicNet
       runConv (convGENERAL_REWRITE False convONCE_DEPTH net thl) tm

-- rewriting rules and tactics
ruleGEN_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry)
                => (Conversion cls thry -> Conversion cls thry) -> [thm] 
                -> HOLThm -> HOL cls thry HOLThm
ruleGEN_REWRITE cnvl thl = ruleCONV (convGEN_REWRITE cnvl thl)

rulePURE_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry,
                     HOLThmRep thm2 cls thry) => [thm] -> thm2 
                 -> HOL cls thry HOLThm
rulePURE_REWRITE thl = ruleCONV (convPURE_REWRITE thl)

ruleREWRITE :: (BoolCtxt thry, HOLThmRep thm1 cls thry,
                HOLThmRep thm2 cls thry) => [thm1] -> thm2 
            -> HOL cls thry HOLThm
ruleREWRITE thl = ruleCONV (convREWRITE thl)

ruleREWRITE_NIL :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                => thm -> HOL cls thry HOLThm
ruleREWRITE_NIL = ruleCONV convREWRITE_NIL

rulePURE_ONCE_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => [thm]
                      -> HOLThm -> HOL cls thry HOLThm
rulePURE_ONCE_REWRITE thl = ruleCONV (convPURE_ONCE_REWRITE thl)

ruleONCE_REWRITE :: (BoolCtxt thry, HOLThmRep thm1 cls thry,
                     HOLThmRep thm2 cls thry) => [thm1] -> thm2
                 -> HOL cls thry HOLThm
ruleONCE_REWRITE thl = ruleCONV (convONCE_REWRITE thl)

rulePURE_ASM_REWRITE :: (BoolCtxt thry, HOLThmRep thm1 cls thry,
                         HOLThmRep thm2 cls thry) => [thm1] -> thm2
                     -> HOL cls thry HOLThm
rulePURE_ASM_REWRITE pthl pth =
    do th <- toHThm pth
       thl <- mapM toHThm pthl
       rulePURE_REWRITE (map (fromRight . primASSUME) (hyp th) ++ thl) th

ruleASM_REWRITE :: (BoolCtxt thry, HOLThmRep thm1 cls thry,
                    HOLThmRep thm2 cls thry) => [thm1] -> thm2
                -> HOL cls thry HOLThm
ruleASM_REWRITE pthl pth =
    do th <- toHThm pth
       thl <- mapM toHThm pthl
       ruleREWRITE (map (fromRight . primASSUME) (hyp th) ++ thl) th

rulePURE_ONCE_ASM_REWRITE :: (BoolCtxt thry, HOLThmRep thm1 cls thry,
                              HOLThmRep thm2 cls thry) => [thm1] -> thm2
                          -> HOL cls thry HOLThm 
rulePURE_ONCE_ASM_REWRITE pthl pth =
    do th <- toHThm pth
       thl <- mapM toHThm pthl
       rulePURE_ONCE_REWRITE (map (fromRight . primASSUME) (hyp th) ++ thl) th

ruleONCE_ASM_REWRITE :: (BoolCtxt thry
                        ,HOLThmRep thm1 cls thry
                        ,HOLThmRep thm2 cls thry) => [thm1] -> thm2
                     -> HOL cls thry HOLThm 
ruleONCE_ASM_REWRITE pthl pth =
    do th <- toHThm pth
       thl <- mapM toHThm pthl
       ruleONCE_REWRITE (map (fromRight . primASSUME) (hyp th) ++ thl) th

tacGEN_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => 
                  (Conversion cls thry -> Conversion cls thry) ->
                  [thm] -> Tactic cls thry
tacGEN_REWRITE cnvl thl = tacCONV (convGEN_REWRITE cnvl thl)

tacPURE_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => [thm]
                -> Tactic cls thry
tacPURE_REWRITE thl = tacCONV (convPURE_REWRITE thl)

tacREWRITE' :: BoolCtxt thry => [HOLThm] -> Tactic cls thry
tacREWRITE' thl = tacCONV (convREWRITE thl)

tacREWRITE_NIL :: BoolCtxt thry => Tactic cls thry
tacREWRITE_NIL = tacREWRITE' []

tacREWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => 
              [thm] -> Tactic cls thry
tacREWRITE pthl = liftM1 tacREWRITE' (mapM toHThm pthl)

tacPURE_ONCE_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => [thm] 
                     -> Tactic cls thry
tacPURE_ONCE_REWRITE thl = tacCONV (convPURE_ONCE_REWRITE thl)

tacONCE_REWRITE' :: BoolCtxt thry => [HOLThm] -> Tactic cls thry
tacONCE_REWRITE' thl = tacCONV (convONCE_REWRITE thl)

tacONCE_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => 
                   [thm] -> Tactic cls thry
tacONCE_REWRITE pthl = liftM1 tacONCE_REWRITE' (mapM toHThm pthl)

tacPURE_ASM_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => 
                       [thm] -> Tactic cls thry 
tacPURE_ASM_REWRITE = tacASM tacPURE_REWRITE

tacPURE_ASM_REWRITE_NIL :: BoolCtxt thry => Tactic cls thry 
tacPURE_ASM_REWRITE_NIL = tacASM tacPURE_REWRITE ([]::[HOLThm])

tacASM_REWRITE' :: BoolCtxt thry => [HOLThm] -> Tactic cls thry
tacASM_REWRITE' = tacASM tacREWRITE

tacASM_REWRITE_NIL :: BoolCtxt thry => Tactic cls thry
tacASM_REWRITE_NIL = tacASM_REWRITE' []

tacASM_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) 
               => [thm] -> Tactic cls thry
tacASM_REWRITE pthl = liftM1 tacASM_REWRITE' (mapM toHThm pthl)

tacPURE_ONCE_ASM_REWRITE :: BoolCtxt thry => [HOLThm] -> Tactic cls thry
tacPURE_ONCE_ASM_REWRITE = tacASM tacPURE_ONCE_REWRITE

tacONCE_ASM_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                    => [thm] -> Tactic cls thry 
tacONCE_ASM_REWRITE = tacASM tacONCE_REWRITE

-- simplification stuff

convGEN_SIMPLIFY :: BoolCtxt thry => HOLThmRep thm cls thry => Strategy cls thry
                 -> Simpset cls thry -> Int -> [thm] 
                 -> Conversion cls thry
convGEN_SIMPLIFY strat ss lev thl = Conv $ \ tm ->
    do ss' <- foldrM ruleAUGMENT_SIMPSET ss thl
       runConv (_TRY (strat ss' lev)) tm

convONCE_SIMPLIFY :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                  => Simpset cls thry
                  -> [thm] -> Conversion cls thry
convONCE_SIMPLIFY ss = convGEN_SIMPLIFY sqconvONCE_DEPTH ss 1

convSIMPLIFY :: (BoolCtxt thry, HOLThmRep thm cls thry) => Simpset cls thry 
             -> [thm] -> Conversion cls thry
convSIMPLIFY ss = convGEN_SIMPLIFY sqconvTOP_DEPTH ss 3

emptySS :: BoolCtxt thry => Simpset cls thry
emptySS = Simpset netEmpty basicProver [] $ mkRewrites True

basicSS :: BoolCtxt thry => [HOLThm] -> HOL cls thry (Simpset cls thry)
basicSS thl = 
    let rewmaker = mkRewrites True in
      do cthms <- foldrM rewmaker [] thl
         b_net <- basicNet
         net' <- liftO $ foldrM (netOfThm True) b_net cthms
         congs <- basicCongs
         net'' <- liftO $ foldrM netOfCong net' congs
         return $ Simpset net'' basicProver [] rewmaker

convSIMP :: (BoolCtxt thry, HOLThmRep thm cls thry) => [thm] 
         -> Conversion cls thry
convSIMP thl = Conv $ \ tm -> 
    do ss <- basicSS []
       runConv (convSIMPLIFY ss thl) tm

convPURE_SIMP :: (BoolCtxt thry, HOLThmRep thm cls thry) => [thm] 
              -> Conversion cls thry
convPURE_SIMP = convSIMPLIFY emptySS

convONCE_SIMP :: (BoolCtxt thry, HOLThmRep thm cls thry) 
              => [thm] -> Conversion cls thry
convONCE_SIMP thl = Conv $ \ tm ->
    do ss <- basicSS []
       runConv (convONCE_SIMPLIFY ss thl) tm

ruleSIMP :: (BoolCtxt thry, HOLThmRep thm cls thry) => [thm] 
         -> HOLThm -> HOL cls thry HOLThm
ruleSIMP thl = ruleCONV (convSIMP thl)

rulePURE_SIMP :: (BoolCtxt thry, HOLThmRep thm cls thry) => [thm] 
              -> HOLThm -> HOL cls thry HOLThm
rulePURE_SIMP thl = ruleCONV (convPURE_SIMP thl)

ruleONCE_SIMP :: (BoolCtxt thry, HOLThmRep thm cls thry) 
              => [thm] -> HOLThm -> HOL cls thry HOLThm
ruleONCE_SIMP thl = ruleCONV (convONCE_SIMP thl)

tacSIMP :: (BoolCtxt thry, HOLThmRep thm cls thry) => [thm] 
        -> Tactic cls thry
tacSIMP thl = tacCONV (convSIMP thl)

tacPURE_SIMP :: (BoolCtxt thry, HOLThmRep thm cls thry) => [thm] 
             -> Tactic cls thry
tacPURE_SIMP thl = tacCONV (convPURE_SIMP thl)

tacONCE_SIMP :: (BoolCtxt thry, HOLThmRep thm cls thry) 
             => [thm] -> Tactic cls thry
tacONCE_SIMP thl = tacCONV (convONCE_SIMP thl)

tacASM_SIMP :: (BoolCtxt thry, HOLThmRep thm cls thry) => [thm]
            -> Tactic cls thry
tacASM_SIMP = tacASM tacSIMP

tacPURE_ASM_SIMP :: (BoolCtxt thry, HOLThmRep thm cls thry) => [thm] 
                 -> Tactic cls thry
tacPURE_ASM_SIMP = tacASM tacPURE_SIMP

tacONCE_ASM_SIMP :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                 => [thm] -> Tactic cls thry
tacONCE_ASM_SIMP = tacASM tacONCE_SIMP

tacABBREV :: (BoolCtxt thry, HOLTermRep tm cls thry) => tm -> Tactic cls thry
tacABBREV ptm gl@(Goal asl w) =
    do tm <- toHTm ptm
       let (cvs, t) = fromJust $ destEq tm
           (v, vs) = stripComb cvs
           rs = fromRight $ listMkAbs vs t
       eq <- mkEq rs v
       th1 <- foldrM (\ v' th -> ruleCONV (convLAND convBETA) #<< 
                                   ruleAP_THM th v') 
                (fromRight $ primASSUME eq) $ reverse vs
       th2 <- ruleSIMPLE_CHOOSE v =<< ruleSIMPLE_EXISTS v =<< ruleGENL vs th1
       tm' <- mkExists v eq
       th3 <- ruleEXISTS tm' rs (primREFL rs)
       let th4 = rulePROVE_HYP th3 th2
           avoids = foldr (union . frees . concl . snd) (frees w) asl
       if v `elem` avoids
          then fail "tacABBREVL variable already used."
          else _CHOOSE_THEN 
                 (\ th -> tacRULE_ASSUM (rulePURE_ONCE_REWRITE [th]) `_THEN`
                          tacPURE_ONCE_REWRITE [th] `_THEN`
                          tacASSUME th) th4 gl

tacEXPAND :: BoolCtxt thry => Text -> Tactic cls thry
tacEXPAND s =
    _FIRST_ASSUM (\ th -> do (s', _) <- liftO $ destVar =<< rhs (concl th)
                             if s' == s
                                then tacSUBST1 #<< ruleSYM th
                                else fail "tacEXPAND") `_THEN` 
    tacBETA

-- Equality Proofs From Thereoms here for staging purposes
thmEQ_REFL :: BoolCtxt thry => HOL cls thry HOLThm
thmEQ_REFL = cacheProof "thmEQ_REFL" ctxtBool $
    prove "!x:A. x = x" $ tacGEN `_THEN` tacREFL

thmIMP_CLAUSES :: BoolCtxt thry => HOL cls thry HOLThm
thmIMP_CLAUSES = cacheProof "thmIMP_CLAUSES" ctxtBool $
    prove [str| !t. (T ==> t <=> t) /\ 
                    (t ==> T <=> T) /\ 
                    (F ==> t <=> T) /\
                    (t ==> t <=> T) /\ 
                    (t ==> F <=> ~t) |] tacITAUT
