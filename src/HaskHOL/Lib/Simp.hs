{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, TypeSynonymInstances #-}
{-|
  Module:    HaskHOL.Lib.Simp
  Copyright: (c) Evan Austin 2015
  LICENSE:   BSD3

  Maintainer:  e.c.austin@gmail.com
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Simp
       ( GConversion
       , CConv(..)
       , convREWR
       , convIMP_REWR
       , convORDERED_REWR
       , convORDERED_IMP_REWR
       , termOrder
       , netOfThm
       , netOfConv
       , netOfCong
       , mkRewrites
       , convREWRITES_PRIM
       , convREWRITES
       , gconvREWRITES
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
       , convCACHED_GENERAL_REWRITE
       , convCACHED_REWRITE
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
       , tacPURE_ONCE_ASM_REWRITE_NIL
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
import HaskHOL.Lib.Equal
import HaskHOL.Lib.Itab
import HaskHOL.Lib.DRule
import HaskHOL.Lib.Tactics

-- Cacheable Conversions
data CConv
    = BASEABS HOLTerm HOLThm
    | EQT_REWR HOLThm
    | ORD_REWR HOLThm
    | REWR HOLThm
    | IMP_REWR (Maybe HOLTerm) HOLThm
    | ORD_IMP_REWR HOLThm
    | CONG Int HOLThm
    | HINT String String deriving Typeable

deriveSafeCopy 0 'base ''CConv

instance Eq CConv where
    _ == _ = False
        
instance Ord CConv where        
    compare _ _ = GT
    _ <= _ = False
    _ < _ = False

data BasicConvs = 
    BasicConvs ![(Text, (HOLTerm, CConv))] deriving Typeable

deriveSafeCopy 0 'base ''BasicConvs

getConvs :: Query BasicConvs [(Text, (HOLTerm, CConv))]
getConvs =
    do (BasicConvs convs) <- ask
       return convs

putConvs :: [(Text, (HOLTerm, CConv))] -> Update BasicConvs ()
putConvs convs = put (BasicConvs convs)

addConv :: (Text, (HOLTerm, CConv)) -> Update BasicConvs ()
addConv (name, patcong) =
    do (BasicConvs convs) <- get
       put (BasicConvs $ (name, patcong) : 
                         filter (\ (name', _) -> name /= name') convs)

makeAcidic ''BasicConvs ['getConvs, 'putConvs, 'addConv]

type GConversion = (Int, CConv)

data ConversionNet = ConversionNet !(Net GConversion) deriving Typeable

deriveSafeCopy 0 'base ''ConversionNet

getNet :: Query ConversionNet (Net GConversion)
getNet =
    do (ConversionNet net) <- ask
       return net

putNet :: Net GConversion -> Update ConversionNet ()
putNet net = put (ConversionNet net)

makeAcidic ''ConversionNet ['getNet, 'putNet]


-- Interpreted code must be of type HOL Proof thry, so we need to
-- generalize it when we recall it.
mkConvGeneral :: Conversion Proof thry -> Conversion cls thry
mkConvGeneral cnv = Conv $ \ tm -> mkProofGeneral $ runConv cnv tm

unCConv :: (Typeable thry, BoolCtxt thry) => CConv -> Conversion cls thry
unCConv (HINT c m) = mkConvGeneral . Conv $ \ tm ->
    do cnv <- runHOLHint ("return " ++ c) ("HaskHOL.Lib.Equal":[m])
       runConv cnv tm
unCConv (BASEABS v th) = Conv $ \ tm ->
    case tm of
      (Abs y (Comb t y'))
          | y == y' && not (y `freeIn` t) ->
                do env <- termMatch [] v t
                   ruleINSTANTIATE env th
          | otherwise -> fail "convREWR (axETA special case)"
      _ -> fail "convREWR (axETA special case)"
unCConv (EQT_REWR th) = Conv $ \ tm ->
    do th' <- ruleEQT_INTRO th
       runConv (convREWR th') tm
unCConv (ORD_REWR th) = convORDERED_REWR termOrder th
unCConv (REWR th) = convREWR th
unCConv (IMP_REWR (Just t) th) = Conv $ \ tm ->
    do th' <- ruleDISCH t . ruleEQT_INTRO $ ruleUNDISCH th
       runConv (convIMP_REWR th') tm
unCConv (IMP_REWR Nothing th) = convIMP_REWR th
unCConv (ORD_IMP_REWR th) = convORDERED_IMP_REWR termOrder th
unCConv (CONG n th) = Conv $ \ tm ->
    ruleGEN_PART_MATCH (lHand <=< funpowM n rand) th tm

-- primitive rewriting conversionals
convREWR :: (BoolCtxt thry, HOLThmRep thm cls thry) 
         => thm -> Conversion cls thry
convREWR th = Conv $ \ tm -> 
    rulePART_MATCH lhs th tm

convIMP_REWR :: (BoolCtxt thry, HOLThmRep thm cls thry) 
             => thm -> Conversion cls thry
convIMP_REWR th = Conv $ \ tm -> 
    rulePART_MATCH (lhs <=< liftM snd . destImp) th tm

-- ordered rewriting conversionals
convORDERED_REWR :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                 => (HOLTerm -> HOLTerm -> Bool) -> thm 
                 -> Conversion cls thry
convORDERED_REWR ord th = Conv $ \ tm -> note "convORDERED_REWR" $
    do thm <- runConv (convREWR th) tm
       case concl thm of
         (l := r)
             | ord l r -> return thm
             | otherwise -> fail "wrong orientation."
         _ -> fail "not an equation."

convORDERED_IMP_REWR :: (BoolCtxt thry, HOLThmRep thm cls thry)
                     => (HOLTerm -> HOLTerm -> Bool) -> thm 
                     -> Conversion cls thry
convORDERED_IMP_REWR ord th = Conv $ \ tm -> note "convORDERED_IMP_REWR" $
    do thm <- runConv (convIMP_REWR th) tm
       case concl thm of
           (Comb _ (l := r))
               | ord l r -> return thm
               | otherwise -> fail "wrong orientation."
           _ -> fail "not an equation."

{-
  Using 'Maybe' with patterns saves us from having to parse "T", 
  letting us keep this function pure.
-}
termOrder :: HOLTerm -> HOLTerm -> Bool
termOrder = dynOrder Nothing
  where dynOrder :: Maybe HOLTerm -> HOLTerm -> HOLTerm -> Bool
        dynOrder top tm1 tm2 = 
            let (f1, args1) = stripComb tm1
                (f2, args2) = stripComb tm2 in
              if f1 == f2 then lexify (dynOrder (Just f1)) args1 args2
              else case top of
                     Nothing -> case (f1, f2) of
                                  (T, _) -> False
                                  (_, T) -> True
                                  (_, _) -> f1 > f2
                     Just top' -> (f2 /= top') && ((f1 == top') || (f1 > f2))
       
        lexify :: (HOLTerm -> HOLTerm -> Bool) -> [HOLTerm] -> [HOLTerm] -> Bool
        lexify _ [] _ = False
        lexify _ _ [] = True
        lexify ord (a:as) (b:bs) = 
            ord a b || (a == b && lexify ord as bs)

-- create a net for a theorem
netOfThm :: Bool -> HOLThm -> Net GConversion -> HOL cls thry (Net GConversion)
netOfThm rep th@(Thm asl tm) net = 
  let lconsts = catFrees asl
      matchable x = can (termMatch lconsts x) in
    case tm of
      (l@(Abs x (Comb v@Var{} x')) := v')
          | x' == x && v' == v && x /= v ->
                return $! netEnter lconsts (l, (1, BASEABS v th)) net
          | otherwise -> fail "netOfThm"
      (l := r)
          | rep && l `freeIn` r ->
                return $! netEnter lconsts (l, (1, EQT_REWR th)) net
          | otherwise -> 
                do cond1 <- matchable l r
                   cond2 <- matchable r l
                   if rep && cond1 && cond2
                      then return $! netEnter lconsts (l, (1, ORD_REWR th)) net
                      else return $! netEnter lconsts (l, (1, REWR th)) net
      (Comb (Comb _ t) (l := r))
          | rep && l `freeIn` r ->
                return $! netEnter lconsts (l, (3, IMP_REWR (Just t) th)) net
          | otherwise -> 
                do cond1 <- matchable l r
                   cond2 <- matchable r l
                   if rep && cond1 && cond2
                      then return $! netEnter lconsts 
                                       (l, (3, ORD_IMP_REWR th)) net
                      else return $! netEnter lconsts 
                                       (l, (3, IMP_REWR Nothing th)) net
      _ -> fail "netOfThm"
netOfThm _ _ _ = throwM $ HOLExhaustiveWarning "netOfThm"

-- This is kept polymorphic for re-use in later libraries
netOfConv :: Ord a => HOLTerm -> a -> Net (Int, a) -> Net (Int, a)
netOfConv tm conv = netEnter [] (tm, (2, conv))

netOfCong :: HOLThm -> Net GConversion -> HOL cls thry (Net GConversion)
netOfCong th sofar = 
    do (conc, n) <- repeatM (\ (tm, m) -> 
                      do (_, x) <- destImp tm
                         return (x, m+1)) (concl th, 0)
       if n == 0 
          then fail "netOfCong"
          else do pat <- lHand conc
                  return $! netEnter [] (pat, (4, CONG n th)) sofar

-- rewrite maker
convIMP_CONJ :: BoolCtxt thry => Conversion cls thry
convIMP_CONJ = convREWR convIMP_CONJ_pth
  where convIMP_CONJ_pth :: BoolCtxt thry => HOL cls thry HOLThm
        convIMP_CONJ_pth = cacheProof "convIMP_CONJ_pth" ctxtBool $
            ruleITAUT [txt| p ==> q ==> r <=> p /\ q ==> r |] 

ruleIMP_EXISTS :: (BoolCtxt thry, HOLTermRep tm cls thry, 
                   HOLThmRep thm cls thry) 
               => tm -> thm -> HOL cls thry HOLThm
ruleIMP_EXISTS v th = 
    ruleCONV (convREWR ruleIMP_EXISTS_pth) $ ruleGEN v th
  where ruleIMP_EXISTS_pth :: BoolCtxt thry => HOL cls thry HOLThm
        ruleIMP_EXISTS_pth = cacheProof "ruleIMP_EXISTS_pth" ctxtBool $
            ruleITAUT [txt| (!x. P x ==> Q) <=> (?x . P x) ==> Q |]

mkRewrites :: (BoolCtxt thry, HOLThmRep thm1 cls thry, HOLThmRep thm2 cls thry) 
           => Bool -> thm1 -> [thm2] -> HOL cls thry [HOLThm]
mkRewrites cf pth pths = 
    do th@(Thm asl _) <- toHThm pth
       ths <- mapM toHThm pths
       splitRewrites asl th ths
  where splitRewrites :: BoolCtxt thry => [HOLTerm] -> HOLThm 
                      -> [HOLThm] -> HOL cls thry [HOLThm]
        splitRewrites oldhyps th@(Thm _ tm) sofar
            | isForall tm =
                  do th' <- ruleSPEC_ALL th
                     splitRewrites oldhyps th' sofar
            | isConj tm =
                  do th1 <- ruleCONJUNCT1 th
                     th2 <- ruleCONJUNCT2 th
                     sofar' <- splitRewrites oldhyps th2 sofar
                     splitRewrites oldhyps th1 sofar'
            | isImp tm && cf =
                  do th' <- ruleUNDISCH th
                     splitRewrites oldhyps th' sofar
            | isEq tm && cf =
                  do th' <- collectCondition oldhyps th
                     return $! th':sofar
            | isEq tm = return $! th:sofar
            | isNeg tm =
                  let (Neg tm') = tm in
                    do th' <- ruleEQF_INTRO th
                       ths <- splitRewrites oldhyps th' sofar
                       if isEq tm'
                          then do th'' <- ruleEQF_INTRO $ ruleGSYM th
                                  splitRewrites oldhyps th'' ths
                          else return ths
            | otherwise = 
                  do th' <- ruleEQT_INTRO th
                     splitRewrites oldhyps th' sofar
        splitRewrites _ _ _ = throwM $ HOLExhaustiveWarning "splitRewrites"

        collectCondition :: BoolCtxt thry => [HOLTerm] -> HOLThm 
                         -> HOL cls thry HOLThm
        collectCondition oldhyps th =
            let conds = hyp th \\ oldhyps in
              if null conds then return th
              else do jth <- foldrM ruleDISCH th conds
                      kth <- ruleCONV (_REPEAT convIMP_CONJ) jth
                      case concl kth of
                        (cond :==> eqn) -> 
                            let fvs = (frees cond \\ frees eqn) \\ 
                                      catFrees oldhyps in
                              foldrM ruleIMP_EXISTS kth fvs
                        _ -> fail "collectCondition"

convREWRITES_PRIM :: Net (Int, a) -> (a -> HOLTerm -> HOL cls thry b) 
                  -> HOLTerm -> HOL cls thry b
convREWRITES_PRIM net f tm =
    let pconvs = netLookup tm net in
      tryFind (\ (_, cnv) -> f cnv tm) pconvs <?> "convREWRITES'"

convREWRITES :: Net (Int, Conversion cls thry) -> Conversion cls thry
convREWRITES net = Conv $ \ tm -> note "convREWRITES" $
    convREWRITES_PRIM net (\ cnv x -> runConv cnv x) tm

gconvREWRITES :: BoolCtxt thry => Net GConversion -> Conversion cls thry
gconvREWRITES net = Conv $ \ tm -> note "gconvREWRITES" $
    convREWRITES_PRIM net (\ cnv x -> runConv (unCConv cnv) x) tm

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

augment :: HOLThmRep thm cls thry 
        => Prover cls thry -> [thm] -> HOL cls thry (Prover cls thry)
augment (Prover _ aug) thms = liftM aug $ mapM toHThm thms

applyProver :: HOLTermRep tm cls thry 
            => Prover cls thry -> tm -> HOL cls thry HOLThm
applyProver (Prover conv _ ) = runConv conv

-- simpsets
data Simpset cls thry = Simpset (Net GConversion)
                        (Strategy cls thry -> Strategy cls thry)
                        [Prover cls thry]
                        (HOLThm -> [HOLThm] -> HOL cls thry [HOLThm])

type Strategy cls thry = Simpset cls thry -> Int -> Conversion cls thry

-- basic prover - recursively simplify then try provers
basicProver :: BoolCtxt thry => Strategy cls thry -> Strategy cls thry
basicProver strat ss@(Simpset _ _ provers _) lev = Conv $ \ tm ->
    do sth@(Thm _ c) <- runConv (strat ss lev) tm <|> primREFL tm
       ruleEQT_ELIM sth <|> 
         (do tth <- tryFind (\ pr -> do c' <- rand c
                                        applyProver pr c') provers
             primEQ_MP (ruleSYM sth) tth)

ssOfThms :: BoolCtxt thry => [HOLThm] -> Simpset cls thry 
         -> HOL cls thry (Simpset cls thry)
ssOfThms thms (Simpset net prover provers rewmaker) =
    do cthms <- foldrM rewmaker [] thms
       net' <- foldrM (netOfThm True) net cthms
       return $! Simpset net' prover provers rewmaker

ssOfConv :: HOLTerm -> CConv -> Simpset cls thry -> Simpset cls thry
ssOfConv keytm conv (Simpset net prover provers rewmaker) =
    Simpset (netOfConv keytm conv net) prover provers rewmaker

ssOfCongs :: BoolCtxt thry => [HOLThm] -> Simpset cls thry 
          -> HOL cls thry (Simpset cls thry)
ssOfCongs thms (Simpset net prover provers rewmaker) =
   do net' <- foldrM netOfCong net thms
      return $! Simpset net' prover provers rewmaker

ssOfProver :: (Strategy cls thry -> Strategy cls thry) 
           -> Simpset cls thry -> Simpset cls thry
ssOfProver newprover (Simpset net _ provers rewmaker) =
    Simpset net newprover provers rewmaker

ssOfProvers :: [Prover cls thry] -> Simpset cls thry -> Simpset cls thry
ssOfProvers newprovers (Simpset net prover provers rewmaker) =
    Simpset net prover (newprovers ++ provers) rewmaker

ssOfMaker :: (HOLThm -> [HOLThm] -> HOL cls thry [HOLThm]) 
          -> Simpset cls thry -> Simpset cls thry
ssOfMaker newmaker (Simpset net prover provers _) =
    Simpset net prover provers newmaker

ruleAUGMENT_SIMPSET :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                    => thm -> Simpset cls thry 
                    -> HOL cls thry (Simpset cls thry)
ruleAUGMENT_SIMPSET pth (Simpset net prover provers rewmaker) =
    do cth <- toHThm pth
       provers' <- mapM (`augment` [cth]) provers
       cthms <- rewmaker cth []
       net' <- foldrM (netOfThm True) net cthms
       return $ Simpset net' prover provers' rewmaker

-- sqconvs
convIMP_REWRITES :: BoolCtxt thry => Strategy cls thry
                 -> Simpset cls thry -> Int -> [GConversion] 
                 -> Conversion cls thry
convIMP_REWRITES strat ss@(Simpset _ prover _ _) lev pconvs = 
    Conv $ \ tm -> note "convIMP_REWRITES" $ tryFind (\ (n, cnv) -> 
      if n >= 4 then fail ""
      else do th@(Thm _ etm) <- runConv (unCConv cnv) tm
              if isEq etm 
                 then return th
                 else if lev <= 0 
                      then fail "convIMP_REWRITES: too deep"
                      else ruleMP th . runConv (prover strat ss (lev-1)) $ 
                             lHand etm) pconvs

convGEN_SUB :: BoolCtxt thry => Strategy cls thry
            -> Simpset cls thry -> Int -> [GConversion] 
            -> Conversion cls thry
convGEN_SUB strat ss lev pconvs = Conv $ \ tm -> note "convGEN_SUB" $ 
    tryFind (\ (n, cnv) -> 
      if n < 4 then fail "fail"
      else do th <- runConv (unCConv cnv) tm
              convRUN_SUB strat ss lev True th) pconvs
    <|> (case tm of
            (Comb l r) -> 
                do { th1 <- runConv (strat ss lev) l
                   ; do { th2 <- runConv (strat ss lev) r
                        ; primMK_COMB th1 th2
                        } <|> ruleAP_THM th1 r
                   } <|>
                do { rth <- runConv (strat ss lev) r
                   ;   ruleAP_TERM l rth
                   }
            (Abs v bod) -> 
                (do th <- runConv (strat ss lev) bod
                    primABS v th) 
                <|> (do gv <- genVar $ typeOf v
                        gbod <- varSubst [(gv, v)] bod
                        gbodth <- runConv (strat ss lev) gbod
                        gth@(Thm _ gtm) <- primABS gv gbodth
                        let (l := r) = gtm
                            v' = variant (frees gtm) v
                        (l', r') <- pairMapM (alpha v') (l, r)
                        eq <- mkEq l' r'
                        th <- ruleALPHA gtm eq
                        primEQ_MP th gth)
            _ -> fail "not a combination or abstraction.")

convRUN_SUB :: (BoolCtxt thry, HOLThmRep thm cls thry) 
            => Strategy cls thry -> Simpset cls thry -> Int -> Bool -> thm 
            -> HOL cls thry HOLThm
convRUN_SUB strat ss lev triv pth = note "convRUN_SUB" $
    do th <- toHThm pth
       case concl th of
         (subtm :==> _) -> 
           let (avs, bod) = stripForall subtm in
             do ((t, t'), ss', mkFun) <-
                    case bod of
                      (t := t') -> return ((t, t'), ss, return)
                      (c :==> deq) ->
                        do ssth' <- ruleAUGMENT_SIMPSET (primASSUME c) ss
                           x <- destEq deq
                           return (x, ssth', ruleDISCH c)
                      _ -> fail "not an equation or implication."
                (eth, triv') <- (do x <- runConv (strat ss' lev) t
                                    return (x, False))
                                <|> (do tth <- primREFL t
                                        return (tth, triv))
                eth' <- ruleGENL avs $ mkFun eth
                th' <- case t' of
                         Var{} -> do t'' <- rand $ concl eth
                                     primINST [(t', t'')] th
                         _ -> ruleGEN_PART_MATCH lHand th (concl eth')
                th'' <- ruleMP th' eth'
                convRUN_SUB strat ss lev triv' th''
         _ -> if triv then fail "trivial non-implication." else return th

sqconvTOP_DEPTH :: BoolCtxt thry => Strategy cls thry
sqconvTOP_DEPTH ss@(Simpset net _ _ _) lev = Conv $ \ tm ->
    let pconvs = netLookup tm net in
      do th1 <- runConv (convIMP_REWRITES sqconvTOP_DEPTH ss lev pconvs) tm 
                <|> runConv (convGEN_SUB sqconvTOP_DEPTH ss lev pconvs) tm
         case concl th1 of
             (Comb _ t) -> 
                 (do th2 <- runConv (sqconvTOP_DEPTH ss lev) t
                     primTRANS th1 th2) <|> return th1
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
       put (Rewrites (ths ++ xs))

getRewrites :: Query Rewrites [HOLThm]
getRewrites =
    do (Rewrites ths) <- ask
       return ths

makeAcidic ''Rewrites ['putRewrites, 'addRewrites, 'getRewrites]


setBasicRewrites :: (BoolCtxt thry, HOLThmRep thm Theory thry) 
                 => [thm] -> HOL Theory thry ()
setBasicRewrites thl =
    do canonThl <- foldrM (mkRewrites False) [] thl
       acid <- openLocalStateHOL (Rewrites [])
       updateHOL acid (PutRewrites canonThl)
       closeAcidStateHOL acid
       rehashConvnet

extendBasicRewrites :: (BoolCtxt thry, HOLThmRep thm Theory thry) 
                    => [thm] -> HOL Theory thry ()
extendBasicRewrites [] = return ()
extendBasicRewrites (th:ths) = 
    do canonThs <- mkRewrites False th ([] :: [HOLThm])
       acid <- openLocalStateHOL (Rewrites [])
       updateHOL acid (AddRewrites canonThs)
       closeAcidStateHOL acid
       rehashConvnet
       extendBasicRewrites ths

basicRewrites :: HOL cls thry [HOLThm]
basicRewrites =
    do acid <- openLocalStateHOL (Rewrites [])
       ths <- queryHOL acid GetRewrites
       closeAcidStateHOL acid
       return ths

setBasicConvs :: (BoolCtxt thry, HOLTermRep tm Theory thry) 
              => [(Text, (tm, String))] -> HOL Theory thry ()
setBasicConvs cnvs =
    do acid <- openLocalStateHOL (BasicConvs [])
       cnvs' <- mapM (\ (x, (tm, m)) -> 
                         do tm' <- toHTm tm
                            return (x, (tm', HINT (unpack x) m))) cnvs
       updateHOL acid $ PutConvs cnvs'
       closeAcidStateHOL acid
       rehashConvnet

extendBasicConvs :: (BoolCtxt thry, HOLTermRep tm Theory thry) 
                 => [(Text, (tm, String))] -> HOL Theory thry ()
extendBasicConvs [] = return ()
extendBasicConvs ((name, (ptm, m)):cnvs) = 
    do tm <- toHTm ptm
       acid <- openLocalStateHOL (BasicConvs [])
       updateHOL acid (AddConv (name, (tm, HINT (unpack name) m)))
       closeAcidStateHOL acid
       rehashConvnet
       extendBasicConvs cnvs

basicConvs :: Typeable thry => HOL cls thry [(Text, (HOLTerm, CConv))]
basicConvs =
    do acid <- openLocalStateHOL (BasicConvs [])
       convs <- queryHOL acid GetConvs
       closeAcidStateHOL acid
       return convs

basicNet :: BoolCtxt thry => HOL cls thry (Net GConversion)
basicNet =
    do acid <- openLocalStateHOL (ConversionNet netEmpty)
       net <- queryHOL acid GetNet
       closeAcidStateHOL acid
       return net

rehashConvnet :: BoolCtxt thry => HOL Theory thry ()
rehashConvnet =
  do rewrites <- basicRewrites
     cnvs <- liftM (map snd) basicConvs
     let convs = foldr (uncurry netOfConv) netEmpty cnvs
     net <- foldrM (netOfThm True) convs rewrites
     acid <- openLocalStateHOL (ConversionNet netEmpty)
     updateHOL acid (PutNet net)
     closeAcidStateHOL acid

-- default congruences
data Congruences = Congruences ![HOLThm] deriving Typeable

deriveSafeCopy 0 'base ''Congruences

putCongruences :: [HOLThm] -> Update Congruences ()
putCongruences ths =
    put (Congruences ths)

addCongruence :: HOLThm -> Update Congruences ()
addCongruence th =
    do (Congruences xs) <- get
       put (Congruences (th `insert` xs))

getCongruences :: Query Congruences [HOLThm]
getCongruences =
    do (Congruences xs) <- ask
       return xs

makeAcidic ''Congruences ['putCongruences, 'addCongruence, 'getCongruences]

setBasicCongs :: HOLThmRep thm Theory thry => [thm] -> HOL Theory thry ()
setBasicCongs pthl =
    do thl <- mapM toHThm pthl
       acid <- openLocalStateHOL (Congruences [])
       updateHOL acid (PutCongruences thl)
       closeAcidStateHOL acid

extendBasicCongs :: HOLThmRep thm Theory thry => [thm] -> HOL Theory thry ()
extendBasicCongs [] = return ()
extendBasicCongs (th:ths) = 
    do th' <- toHThm th
       acid <- openLocalStateHOL (Congruences [])
       updateHOL acid (AddCongruence th')
       closeAcidStateHOL acid
       extendBasicCongs ths

basicCongs :: HOL cls thry [HOLThm]
basicCongs =
    do acid <- openLocalStateHOL (Congruences [])
       congs <- queryHOL acid GetCongruences
       closeAcidStateHOL acid
       return congs

-- main rewriting conversions
convCACHED_GENERAL_REWRITE :: forall thm cls thry. 
                              (BoolCtxt thry, HOLThmRep thm cls thry) 
                           => Bool -> Bool
                           -> (Conversion cls thry -> Conversion cls thry) 
                           -> Net GConversion -> [thm] 
                           -> Conversion cls thry
convCACHED_GENERAL_REWRITE cache rep cnvl builtin_net pths = Conv $ \ tm ->
    do ths <- mapM toHThm pths
       final_net <- if not cache then mkProofGeneral $ buildNet ths
                    else cacheNet ths buildNet
       let fun :: HOLTerm -> HOL cls thry HOLThm
           fun = convREWRITES_PRIM final_net $ \ cnv x -> 
                   runConv (mkConvGeneral cnv) x
       runConv (cnvl $ Conv fun) tm
 where buildNet :: BoolCtxt thry 
                => [HOLThm] -> HOL Proof thry (Net (Int, Conversion Proof thry))
       buildNet ths =
         do ths_canon <- foldrM (mkRewrites False) [] ths
            net <- foldrM (netOfThm rep) builtin_net ths_canon
            return $! netMap (\ (x, cnv) -> (x, unCConv cnv)) net

convCACHED_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry)
                   => (Conversion cls thry -> Conversion cls thry) -> [thm] 
                   -> Conversion cls thry
convCACHED_REWRITE cnvl = convCACHED_GENERAL_REWRITE True False cnvl netEmpty

convGEN_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry)
                => (Conversion cls thry -> Conversion cls thry) -> [thm] 
                -> Conversion cls thry
convGEN_REWRITE cnvl = convCACHED_GENERAL_REWRITE False False cnvl netEmpty

convPURE_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => [thm] 
                 -> Conversion cls thry
convPURE_REWRITE = convCACHED_GENERAL_REWRITE False True convTOP_DEPTH netEmpty

convREWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => [thm]
            -> Conversion cls thry
convREWRITE thl = Conv $ \ tm ->
    do net <- basicNet
       runConv (convCACHED_GENERAL_REWRITE False True convTOP_DEPTH net thl) tm

convREWRITE_NIL :: BoolCtxt thry => Conversion cls thry
convREWRITE_NIL = convREWRITE ([] :: [HOLThm])

convPURE_ONCE_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => [thm] 
                      -> Conversion cls thry
convPURE_ONCE_REWRITE = 
    convCACHED_GENERAL_REWRITE False False convONCE_DEPTH netEmpty

convONCE_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                 => [thm] -> Conversion cls thry
convONCE_REWRITE thl = Conv $ \ tm ->
    do net <- basicNet
       runConv (convCACHED_GENERAL_REWRITE False False convONCE_DEPTH net thl) tm

-- rewriting rules and tactics
ruleGEN_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry, 
                    HOLThmRep thm2 cls thry)
                => (Conversion cls thry -> Conversion cls thry) -> [thm] 
                -> thm2 -> HOL cls thry HOLThm
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

rulePURE_ONCE_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry, 
                          HOLThmRep thm2 cls thry) 
                      => [thm] -> thm2 -> HOL cls thry HOLThm
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
       hyps <- mapM primASSUME $ hyp th
       thl <- mapM toHThm pthl
       rulePURE_REWRITE (hyps ++ thl) th

ruleASM_REWRITE :: (BoolCtxt thry, HOLThmRep thm1 cls thry,
                    HOLThmRep thm2 cls thry) => [thm1] -> thm2
                -> HOL cls thry HOLThm
ruleASM_REWRITE pthl pth =
    do th <- toHThm pth
       hyps <- mapM primASSUME $ hyp th
       thl <- mapM toHThm pthl
       ruleREWRITE (hyps ++ thl) th

rulePURE_ONCE_ASM_REWRITE :: (BoolCtxt thry, HOLThmRep thm1 cls thry,
                              HOLThmRep thm2 cls thry) => [thm1] -> thm2
                          -> HOL cls thry HOLThm 
rulePURE_ONCE_ASM_REWRITE pthl pth =
    do th <- toHThm pth
       hyps <- mapM primASSUME $ hyp th
       thl <- mapM toHThm pthl
       rulePURE_ONCE_REWRITE (hyps ++ thl) th

ruleONCE_ASM_REWRITE :: (BoolCtxt thry
                        ,HOLThmRep thm1 cls thry
                        ,HOLThmRep thm2 cls thry) => [thm1] -> thm2
                     -> HOL cls thry HOLThm 
ruleONCE_ASM_REWRITE pthl pth =
    do th <- toHThm pth
       hyps <- mapM primASSUME $ hyp th
       thl <- mapM toHThm pthl
       ruleONCE_REWRITE (hyps ++ thl) th

tacGEN_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => 
                  (Conversion cls thry -> Conversion cls thry) ->
                  [thm] -> Tactic cls thry
tacGEN_REWRITE cnvl thl = tacCONV (convGEN_REWRITE cnvl thl)


tacPURE_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => [thm]
                -> Tactic cls thry
tacPURE_REWRITE thl = tacCONV (convPURE_REWRITE thl)


tacREWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => 
              [thm] -> Tactic cls thry
tacREWRITE thl = tacCONV (convREWRITE thl)

tacREWRITE_NIL :: BoolCtxt thry => Tactic cls thry
tacREWRITE_NIL = tacREWRITE ([] :: [HOLThm])


tacPURE_ONCE_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => [thm] 
                     -> Tactic cls thry
tacPURE_ONCE_REWRITE thl = tacCONV (convPURE_ONCE_REWRITE thl)

tacONCE_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => 
                   [thm] -> Tactic cls thry
tacONCE_REWRITE thl = tacCONV (convONCE_REWRITE thl)

tacPURE_ASM_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) => 
                       [thm] -> Tactic cls thry 
tacPURE_ASM_REWRITE = tacASM tacPURE_REWRITE

tacPURE_ASM_REWRITE_NIL :: BoolCtxt thry => Tactic cls thry 
tacPURE_ASM_REWRITE_NIL = tacPURE_ASM_REWRITE ([] :: [HOLThm])


tacASM_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) 
               => [thm] -> Tactic cls thry
tacASM_REWRITE = tacASM tacREWRITE

tacASM_REWRITE_NIL :: BoolCtxt thry => Tactic cls thry
tacASM_REWRITE_NIL = tacASM_REWRITE ([] :: [HOLThm])


tacPURE_ONCE_ASM_REWRITE :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                         => [thm] -> Tactic cls thry
tacPURE_ONCE_ASM_REWRITE = tacASM tacPURE_ONCE_REWRITE

tacPURE_ONCE_ASM_REWRITE_NIL :: BoolCtxt thry => Tactic cls thry
tacPURE_ONCE_ASM_REWRITE_NIL = tacPURE_ONCE_ASM_REWRITE ([] :: [HOLThm])


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
         net <- basicNet
         net' <- foldrM (netOfThm True) net cthms
         congs <- basicCongs
         net'' <- foldrM netOfCong net' congs
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
tacABBREV ptm gl@(Goal asl w) = note "tacABBREV" $
    do tm <- toHTm ptm
       (cvs, t) <- destEq tm
       let (v, vs) = stripComb cvs
       rs <- listMkAbs vs t
       eq <- mkEq rs v
       eqth <- primASSUME eq
       th1 <- foldrM (\ v' th -> ruleCONV (convLAND convBETA) $ 
                                   ruleAP_THM th v') eqth $ reverse vs
       th2 <- ruleSIMPLE_CHOOSE v . ruleSIMPLE_EXISTS v $ ruleGENL vs th1
       tm' <- mkExists v eq
       th3 <- ruleEXISTS tm' rs (primREFL rs)
       th4 <- rulePROVE_HYP th3 th2
       let avoids = foldr (union . frees . concl . snd) (frees w) asl
       if v `elem` avoids
          then fail "variable already used."
          else _CHOOSE_THEN 
                 (\ th -> tacRULE_ASSUM (rulePURE_ONCE_REWRITE [th]) `_THEN`
                          tacPURE_ONCE_REWRITE [th] `_THEN`
                          tacASSUME th) th4 gl

tacEXPAND :: BoolCtxt thry => Text -> Tactic cls thry
tacEXPAND s =
    _FIRST_ASSUM (\ th -> case concl th of
                            (_ := Var s' _)
                                | s == s' ->
                                      tacSUBST1 $ ruleSYM th
                                | otherwise -> fail "tacEXPAND: name mismatch."
                            _ -> fail "tacEXPAND: not an equation.") `_THEN` 
    tacBETA

-- Equality Proofs From Thereoms here for staging purposes
thmEQ_REFL :: BoolCtxt thry => HOL cls thry HOLThm
thmEQ_REFL = cacheProof "thmEQ_REFL" ctxtBool $
    prove [txt| !x:A. x = x |] $ tacGEN `_THEN` tacREFL

thmIMP_CLAUSES :: BoolCtxt thry => HOL cls thry HOLThm
thmIMP_CLAUSES = cacheProof "thmIMP_CLAUSES" ctxtBool $
    prove [txt| !t. (T ==> t <=> t) /\ 
                    (t ==> T <=> T) /\ 
                    (F ==> t <=> T) /\
                    (t ==> t <=> T) /\ 
                    (t ==> F <=> ~t) |] tacITAUT
