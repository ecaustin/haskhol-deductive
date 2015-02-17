{-# LANGUAGE PatternSynonyms, ScopedTypeVariables #-}

{-|
  Module:    HaskHOL.Lib.Equal
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown

  This module implements the equality logic library for HaskHOL.  Most notably,
  it defines 'Conversion's.
  It has no associated theory context, instead relying only on the context of 
  the logical kernel.
-}
module HaskHOL.Lib.Equal
    ( -- * Derived Syntax
      lHand 
    , lhs
    , rhs
    , mkPrimedVar
      -- * Derived Equality Rules
    , ruleAP_TERM 
    , ruleAP_THM 
    , ruleSYM 
    , ruleALPHA
    , ruleMK_BINOP 
      -- * Conversions
    , Conversion(..)
       -- ** Subterm Conversions
    , convRATOR 
    , convRAND
    , convLAND
    , convCOMB2
    , convCOMB
    , convABS
    , convTYAPP
    , convTYABS
    , convBINDER
    , convSUB
    , convBINOP
       -- ** Equality Conversions
    , convALPHA
    , convTYALPHA
    , convGEN_ALPHA
    , convGEN_TYALPHA
    , convSYM
       -- ** Beta Conversions
    , convBETA
    , convTYBETA
       -- ** Depth Conversions
    , convONCE_DEPTH
    , convDEPTH
    , convREDEPTH
    , convTOP_DEPTH
    , convTOP_SWEEP
       -- ** Traversal Conversions
    , convDEPTH_BINOP
    , convPATH
    , convPAT
       -- ** Substituation Conversion
    , convSUBS
      -- * Other Derived Rules
    , ruleCONV 
    , ruleBETA 
    , ruleTYBETA
    , ruleGSYM
    , ruleSUBS
    ) where

import HaskHOL.Core

-- Syntax for equality

{-| 
  Returns the left hand side of a binary operator combination.  Equivalent to 
  the composition of
 
  > rand <=< rator

  Fails with 'Maybe' if the term is not a combination of adequate structure.
-}
lHand :: HOLTerm -> Maybe HOLTerm
lHand = rand <=< rator

{-|
  Returns the left hand side of an equation.  Fails with 'Maybe' if the term
  is not equational.
-}
lhs :: HOLTerm -> Maybe HOLTerm
lhs = liftM fst . destEq

{-|
  Returns the right hand side of an equation.  Fails with 'Maybe' if the term
  is not equational.
-}
rhs :: HOLTerm -> Maybe HOLTerm
rhs = liftM snd . destEq

-- Basic Constructors for Equality

{-|
  The 'mkPrimedVar' function renames a variable to avoid conflicts with a 
  provided list of variables and constants.  Throws a 'HOLException' in the
  following cases:

  * The term to be renamed is not a variable.
-}
mkPrimedVar :: [HOLTerm] -> HOLTerm -> HOL cls thry HOLTerm
mkPrimedVar avoid (Var s ty) =
    do s' <- primedRec (mapFilter varName avoid) s
       return $! mkVar s' ty
  where varName :: HOLTerm -> Maybe Text
        varName (Var x _) = Just x
        varName _ = Nothing
          
        primedRec :: [Text] -> Text -> HOL cls thry Text
        primedRec avd x
            | x `elem` avd = primedRec avd (x `snoc` '\'')
            | otherwise = 
                do cond <- do cnd <- can getConstType x
                              hid <- getHidden
                              return $! cnd && (x `notElem` hid)
                   if cond
                      then primedRec avd (x `snoc` '\'')
                      else return x
mkPrimedVar _ _ = fail "mkPrimedVar"

--derived equality rules
{-|@
 f   A |- x = y
----------------
 A |- f x = f y
@

  Fails with 'Left' in the following cases:

  * The theorem conclusion is not an equation.

  * The type of the function term does not agree with theorem argument types.
-}
ruleAP_TERM :: HOLTerm -> HOLThm -> Either String HOLThm
ruleAP_TERM tm thm =
    primMK_COMB (primREFL tm) thm
    <?> "ruleAP_TERM"

{-|@
 A |- f = g   x
----------------
 A |- f x = g x
@

  Fails with 'Left' in the following cases:

  * The theorem conclusion is not an equation.
  
  * The type of the argument term does not agree with theorem function types.
-}
ruleAP_THM :: HOLThm -> HOLTerm -> Either String HOLThm
ruleAP_THM thm tm =
    primMK_COMB thm (primREFL tm) <?> "ruleAP_THM"

{-|@
 A |- t1 = t2
--------------
 A |- t2 = t1
@

  Fails with 'Left' if the theorem conclusion is not an equation.
-}
ruleSYM :: HOLThm -> Either String HOLThm
ruleSYM thm@(Thm _ c) = 
    do (l, _) <- note "ruleSYM: not an equation" $ destEq c
       let lth = primREFL l
           eqTm = fromJust $ rator =<< rator c
       liftO $ do th1 <- ruleAP_TERM eqTm thm
                  th2 <- primMK_COMB th1 lth
                  primEQ_MP th2 lth
ruleSYM _ = error "ruleSYM: exhaustive warning."

{-|@
  t1   t1'  
-------------
 |- t1 = t1'
@

  Fails with 'Left' if the terms are not alpha equivalent.
-}
ruleALPHA :: HOLTerm -> HOLTerm -> Either String HOLThm
ruleALPHA tm1 tm2 = 
    primTRANS (primREFL tm1) (primREFL tm2) <?> "ruleALPHA"

{-|@
 op   |- l1 = l2   |- r1 = r2       
------------------------------
    |- l1 op r1 = l2 op r2
@

  Fails with 'Left' if the argument types of the two theorems do not agree.  
-}
ruleMK_BINOP :: HOLTerm -> HOLThm -> HOLThm -> Either String HOLThm
ruleMK_BINOP op lthm rthm = 
    liftM1 primMK_COMB (ruleAP_TERM op lthm) rthm
    <?> "ruleMK_BINOP"


 -- Conversions and combinator type classes

{-|
  The 'Conversion' type is a special class of derived rules that accepts a
  term and returns a theorem proving its equation with an equivalent term.
-}
newtype Conversion cls thry = Conv { runConv :: HOLTerm -> HOL cls thry HOLThm }
  deriving Typeable

instance Eq (Conversion cls thry) where
    _ == _ = False
        
instance Ord (Conversion cls thry) where        
    compare _ _ = GT
    _ <= _ = False
    _ < _ = False

-- conversion combinators
instance Lang (Conversion cls thry) where
    _FAIL = convFAIL
    _NO = convNO
    _ALL = convALL
    _ORELSE = convORELSE
    _FIRST = convFIRST
    _CHANGED = convCHANGED
    _TRY = convTRY
    _NOTE = convNOTE

instance LangSeq (Conversion cls thry) where
    _THEN = convTHEN
    _REPEAT = convREPEAT
    _EVERY = convEVERY

convFAIL :: String -> Conversion cls thry
convFAIL s = Conv $ \ _ -> fail s

convNO :: Conversion cls thry
convNO = convFAIL "convNO"

convALL :: Conversion cls thry
convALL = Conv $ \ tm -> return $! primREFL tm

convTHEN :: Conversion cls thry -> Conversion cls thry -> Conversion cls thry
convTHEN c1 c2 = Conv $ \ tm ->
    do th1@(Thm _ tm') <- runConv c1 tm
       th2 <- runConv c2 #<< rand tm'
       liftEither "convTHEN: bad sequence" $ primTRANS th1 th2

convORELSE :: Conversion cls thry -> Conversion cls thry -> Conversion cls thry
convORELSE c1 c2 = Conv $ \ tm -> runConv c1 tm <|> runConv c2 tm

-- fails when given an empty list
convFIRST :: [Conversion cls thry] -> Conversion cls thry
convFIRST [] = convFAIL "convFIRST: empty list"
convFIRST xs = foldr1 _ORELSE xs

convEVERY :: [Conversion cls thry] -> Conversion cls thry
convEVERY = foldr _THEN convALL

convREPEAT :: Conversion cls thry -> Conversion cls thry
convREPEAT conv = 
    (conv `_THEN` convREPEAT conv) `_ORELSE` convALL

-- fails if resultant equation has alpha-equivalent sides
convCHANGED :: Conversion cls thry -> Conversion cls thry
convCHANGED conv = Conv $ \ tm ->
    do th@(Thm _ tm') <- runConv conv tm
       let (l, r) = fromJust $ destEq tm'
       if l `aConv` r 
          then fail "convCHANGED: no change"
          else return th

convTRY :: Conversion cls thry -> Conversion cls thry
convTRY conv = conv `_ORELSE` _ALL

convNOTE :: String -> Conversion cls thry -> Conversion cls thry
convNOTE err conv = Conv $ \ tm ->
    noteHOL err $ runConv conv tm

-- subterm conversions

{-|
  The 'convRATOR' conversional applies a given conversion to the operator of a
  combination, returning a theorem of the form @|- (t1 t2) = (t1' t2)@.
  It throws a 'HOLException' in the following cases:

  * The term the resultant conversion is applied to is not a combination.
 
  * The original conversion fails.
-}
convRATOR :: Conversion cls thry -> Conversion cls thry
convRATOR conv = Conv $ \ tm -> 
    case tm of
       Comb l r -> 
         do th <- runConv conv l <?> "convRATOR: conversion failed."
            liftO $ ruleAP_THM th r
       _ -> fail "convRATOR: not a combination"

{-|
  The 'convRAND' conversional applies a given conversion to the operand of a
  combination, returning a theorem of the form @|- (t1 t2) = (t1 t2')@.
  It throws a 'HOLException' in the following cases:

  * The term the resultant conversion is applied to is not a combination.
 
  * The original conversion fails.
-}
convRAND :: Conversion cls thry -> Conversion cls thry
convRAND conv = Conv $ \ tm ->
    case tm of
       Comb l r -> 
           do th <- runConv conv r <?> "convRAND: conversion failed."
              liftO $ ruleAP_TERM l th
       _ -> fail "convRAND: not a combination"

{-|
  The 'convLAND' conversional applies a given conversion to the left hand side 
  of a binary operator combination, returning a theorem of the form 
  @|- l op r = l' op r@.  It is functionally equivalent to 

  > convRATOR . convRAND

  , failing accordingly.
-} 
convLAND :: Conversion cls thry -> Conversion cls thry
convLAND = _NOTE "convLAND" . convRATOR . convRAND

{-|
  The 'convCOMB2' conversional applies two different conversions to the operator
  and operand of a combination accordingly, returning a theorem of the form 
  @|- (t1 t2) = (t1' t2')@.  It throws a 'HOLException' in the following cases:

  * The term the resultant conversion is applied to is not a combination.

  * Either of the original conversions fail.
-}
convCOMB2 :: Conversion cls thry -> Conversion cls thry -> Conversion cls thry
convCOMB2 lconv rconv = Conv $ \ tm -> 
    case tm of
      Comb l r -> 
         do lth <- runConv lconv l <?> "convCOMB2: left conversion failed."
            rth <- runConv rconv r <?> "convCOMB2: right conversion failed."
            liftO $ primMK_COMB lth rth
      _ -> fail "convCOMB2: not a combination"

{-|
  The 'convCOMB' conversional applies a conversion to both the operator and 
  operand of a combination.  It is functionally equivalent to
 
  > \ x -> convCOMB2 x x

  , failing accordingly.
-}
convCOMB :: Conversion cls thry -> Conversion cls thry
convCOMB conv = _NOTE "convCOMB" $ convCOMB2 conv conv

{-|
  The 'convABS' conversional applies a given conversion to the body of an 
  abstraction, returning a theorem of the form @|- (\ x . t) = (\ x . t')@.  
  It throws a 'HOLException' in the following cases:

  * The term the resultant conversion is applied to is not an abstraction.
 
  * The original conversion fails.
-}
convABS :: Conversion cls thry -> Conversion cls thry
convABS conv = Conv $ \ tm ->
    case tm of
      Abs v@(Var _ ty) bod ->
          do th <- runConv conv bod <?> "convABS: conversion failed."
             liftO (primABS v th) <|> 
               do gv <- genVar ty
                  gbod <- runConv conv #<< varSubst [(v, gv)] bod
                  let gth = fromRight $ primABS gv gbod
                      gtm = concl gth
                      v' = variant (frees gtm) v
                      (l, r) = fromRight (pairMapM (alpha v') #<< destEq gtm)
                  tm' <- mkEq l r
                  liftO $ liftM1 primEQ_MP (ruleALPHA gtm tm') gth
      _ -> fail "convABS: not an abstraction."

{-|
  The 'convTYAPP' conversional applies a given conversions to the body of a
  type combination, returning a theorem of the form @|- (t ty) = (t' ty)@.  It 
  throws a 'HOLException' in the following cases:

  * The term the resultant conversion is applied to is not a type combination.

  * The original conversion fails.
-}
convTYAPP :: Conversion cls thry -> Conversion cls thry
convTYAPP conv = Conv $ \ tm ->
    case tm of
      TyComb t ty -> 
          do th <- runConv conv t <?> "convTYAPP: conversion failed."
             liftO $ primTYAPP ty th
      _ -> fail "convTYAPP: not a type combination."

{-|
  The 'convTYABS' conversional applies a given conversions to the body of a
  type abstraction, returning a theorem of the form 
  @|- (\\ tv. tm) = (\\ tv. tm)@.  It throws a 'HOLException' in the following 
  cases:

  * The term the resultant conversion is applied to is not a type abstraction.

  * The original conversion fails.
-}
convTYABS :: Conversion cls thry -> Conversion cls thry
convTYABS conv = Conv $ \ tm ->
    case tm of
      TyAbs tv t -> 
          do th <- runConv conv t <?> "convTYABS: conversion failed."
             liftO (primTYABS tv th) <|> 
               do gv <- genSmallTyVar
                  gbod <- runConv conv $ inst [(tv, gv)] t
                  let gth = fromRight $ primTYABS gv gbod
                      gtm = concl gth
                      v' = variantTyVar (typeVarsInTerm gtm) tv
                      (l, r) = fromRight (pairMapM (alphaTyabs v') #<< 
                                            destEq gtm)
                  tm' <- mkEq l r
                  liftO $ liftM1 primEQ_MP (ruleALPHA gtm tm') gth
      _ -> fail "convTYABS: not an abstraction."

{-|
  The 'convBINDER' conversional applies a given conversion to the body of a term
  with a binder returning a theorem of the form @|- b x . t = b x . t'@   In the
  case of a basic abstraction terms, it is functionally equivalent to 'convABS' 
  or 'convTYABS', failing accordingly.  It throws a 'HOLException' in the 
  following cases:

  * The term the resultant conversion is applied to is not a term with a binder.

  * The original conversion fails.
-}
convBINDER :: Conversion cls thry -> Conversion cls thry
convBINDER conv = Conv $ \ tm -> noteHOL "convBINDER" $
    case tm of
      Abs{} -> runConv (convABS conv) tm
      TyAbs{} -> runConv (convTYABS conv) tm
      Bind{} -> 
          runConv (convRAND $ convABS conv) tm
      TyBind{} -> 
          runConv (convRAND $ convTYABS conv) tm
      _ -> fail "not a binder term."

{-|
  The 'convSUB' conversional applies a given conversion to the subterms of a 
  term.  For variable and constant terms it is functionally equivalent to 
  'convALL'.
-}
convSUB :: Conversion cls thry -> Conversion cls thry
convSUB conv = Conv $ \ tm -> noteHOL "convSUB" $
    case tm of
      Comb{} -> runConv (convCOMB conv) tm
      Abs{}  -> runConv (convABS conv) tm
      TyComb{} -> runConv (convTYAPP conv) tm
      TyAbs{} -> runConv (convTYABS conv) tm
      _ -> return $! primREFL tm

{-|
  The 'convBINOP' conversional applies a given conversion to both the left and 
  right hand sides of a binary operator combination, returning a theorem of the
  form @|- l op r = l' op r'@.  It throws a 'HOLException' in the following 
  cases:

  * The term the resultant conversion is applied to is not a binary operator
    combination.

  * The original conversion fails.

-}
convBINOP :: Conversion cls thry -> Conversion cls thry
convBINOP conv = Conv $ \ tm ->
    case tm of
      (Comb (Comb op l) r) -> 
          do lth <- runConv conv l <?> 
                      "convBINOP: conversion failed on left sub-term."
             rth <- runConv conv r <?>
                      "convBINOP: conversion failed on right sub-term."
             liftO $ liftM1 primMK_COMB (ruleAP_TERM op lth) rth
      _-> fail "convBINOP: not a binary operator combination."

-- Equality Conversions

{-|
  The 'convALPHA' conversion converts the bound variable of lambda abstraction 
  to a provided one, returning a theorem of the form @|- (\ x . t) = (\ v . t)@.
  It throws a 'HOLException' in the following cases:

  * The provided term is not a variable.

  * Alpha conversion fails for the term this conversion is applied to.
-}
convALPHA :: HOLTerm -> Conversion cls thry
convALPHA v@Var{} = Conv $ \ tm ->
    liftEither "convALPHA" $ ruleALPHA tm =<< alpha v tm
convALPHA _ = _FAIL "convALPHA: provided term not a variable."

{-|
  The 'convTYALPHA' conversion converts the bound variable of type abstraction 
  to a provided one, returning a theorem of the form 
  @|- (\\ x . t) = (\\ v . t)@.  It throws a 'HOLException' in the following 
  cases:

  * The provided type is not a small variable.

  * Alpha conversion fails for the term this conversion is applied to.
-}
convTYALPHA :: HOLType -> Conversion cls thry
convTYALPHA v@(TyVar True _) = Conv $ \ tm ->
    liftEither "convTYALPHA" $ ruleALPHA tm =<< alphaTyabs v tm
convTYALPHA _ = _FAIL "convTYALPHA: provided type not a small variable."

{-|
  The 'convGEN_ALPHA' conversion converts the bound variable of a term with a 
  binder to a provided one.  In the case of a basic lambda term it is 
  functionally equivalent to 'convALPHA', failing accordingly.  In other cases
  it returns a theorem of the form @|- b x . t = b v . t@. It throws a 
  'HOLException' in the following cases:

  * The provided term is not a variable.

  * The term the conversion is applied to does not have a binder. 
-}
convGEN_ALPHA:: HOLTerm -> Conversion cls thry
convGEN_ALPHA v@Var{} = Conv $ \ tm ->
    case tm of
      Abs{} -> runConv (convALPHA v) tm
      (Comb b@Const{} ab@Abs{}) ->
          do abth <- runConv (convALPHA v) ab
             liftO $ ruleAP_TERM b abth
      _ -> fail "convGEN_ALPHA: not a binder term."
convGEN_ALPHA _ = _FAIL "convGEN_ALPHA: provided term not a variable"

{-|
  The 'convGEN_TYALPHA' conversion converts the bound type variable of a term 
  with a type binder to a provided one.  In the case of a basic type abstraction
  it is functionally equivalent to 'convTYALPHA', failing accordingly.  In other  cases it returns a theorem of the form @|- b x . t = b v . t@. It throws a 
  'HOLException' in the following cases:

  * The provided type is not a small variable.

  * The term the conversion is applied to does not have a type binder. 
-}
convGEN_TYALPHA:: HOLType -> Conversion cls thry
convGEN_TYALPHA v@(TyVar True _) = Conv $ \ tm ->
    case tm of
      TyAbs{} -> runConv (convTYALPHA v) tm
      (Comb b@Const{} ab@TyAbs{}) ->
          do abth <- runConv (convTYALPHA v) ab
             liftO $ ruleAP_TERM b abth
      _ -> fail "convGEN_TYALPHA: not a type binder term."
convGEN_TYALPHA _ = _FAIL "convGEN_TYALPHA: provided type not a small variable."

{-|
  The 'convSYM' conversion performs a symmetry conversion on an equational 
  term, returning a theorem of the form @|- (l = r) = (r = l)@.
  It throws a 'HOLException' if the term provided to the conversion is not an 
  equational term.
-}
convSYM :: Conversion cls thry
convSYM = Conv $ \ tm -> liftEither "convSYM" $
    do th1 <- ruleSYM =<< primASSUME tm
       th2 <- ruleSYM =<< primASSUME (concl th1)
       return $! primDEDUCT_ANTISYM th2 th1


-- Beta Conversions 
{-|
  The 'convBETA' conversion performs a beta reduction, returning a theorem of 
  the form @|- (\ x . t) v = t [v/x]@.  In the case where the argument term is 
  the same as the bound variable, the primitive rule 'primBETA' is used for 
  efficiency. It throws a 'HOLException' if the term the conversion is applied 
  to is not a valid redex.
-}
convBETA :: Conversion cls thry
convBETA = Conv $ \ tm -> liftEither "convBETA" $
    case tm of
        (Comb f@(Abs v _) arg)
            | v == arg -> primBETA tm
            | otherwise -> 
                  do th <- primBETA =<< mkComb f v
                     liftO $ primINST [(v, arg)] th
        _ -> Left "not a beta-redex."

{-|
  The 'convTYBETA' conversion performs a type beta reduction, returning a 
  theorem of the form @|- (\\ x . t) [: tv] = t [tv/x]@.  In the case where the 
  argument type is the same as the bound variable, the primitive rule 
  'primTYBETA' is used for efficiency. It throws a 'HOLException' if the term 
  the conversion is applied to is not a valid type redex.
-}
convTYBETA :: Conversion cls thry
convTYBETA = Conv $ \ tm -> liftEither "convTYBETA" $
    case tm of
      (TyComb t@(TyAbs tv _) ty)
          | tv == ty -> primTYBETA tm
          | otherwise ->
                liftM (primINST_TYPE [(tv, ty)]) $ primTYBETA =<< mkTyComb t tv
      _ -> Left "not a type beta-redex."


-- depth conversions

{-|
  The 'convONCE_DEPTH' conversional applies a given conversion to the first set
  of subterms that it succeeds on from a top-down search.  It does not fail 
  given that its implementation is wrapped in a use of '_TRY'.
-}
convONCE_DEPTH :: Conversion cls thry -> Conversion cls thry
convONCE_DEPTH = _TRY . onceDepthQConv
  where onceDepthQConv :: Conversion cls thry -> Conversion cls thry
        onceDepthQConv conv = conv `_ORELSE` subQConv (onceDepthQConv conv)

{-|
  The 'convDEPTH' conversional repeatedly applies a given conversion to all 
  subterms in a bottom-up manner until it fails.  The overall conversion does 
  not fail given that its implementation is wrapped in a use of '_TRY', however,  it can loop infinitely if provided with a conversion that itself never fails.
-}
convDEPTH :: Conversion cls thry -> Conversion cls thry
convDEPTH = _TRY . depthQConv
  where depthQConv :: Conversion cls thry -> Conversion cls thry
        depthQConv conv = subQConv (depthQConv conv) `thenqc`
                          repeatqc conv

{-|
  The 'convREDEPTH' conversional repeatedly applies a given conversion to all 
  subterms in a bottom-up manner, retraversing any that are changed.  
  Its behavior is similar to 'convDEPTH' in that it cannot fail, but it can 
  loop infinitely.
-}
convREDEPTH :: Conversion cls thry -> Conversion cls thry
convREDEPTH = _TRY . redepthQConv
  where redepthQConv :: Conversion cls thry -> Conversion cls thry
        redepthQConv conv = subQConv (redepthQConv conv) `thenqc`
                             (conv `thencqc` redepthQConv conv)

{-|
  The 'convTOP_DEPTH' conversional has idententical behavior to that of 
  'convREDEPTH', with the exception that the traversal is top-down instead of 
  bottom-up.
-}
convTOP_DEPTH :: Conversion cls thry -> Conversion cls thry
convTOP_DEPTH = _TRY . topDepthQConv
  where topDepthQConv :: Conversion cls thry -> Conversion cls thry
        topDepthQConv conv = repeatqc conv `thenqc`
                               (subQConv (topDepthQConv conv) `thencqc`
                                 (conv `thencqc` topDepthQConv conv))

{-|
  The 'convTOP_SWEEP' conversional has identical behavior to that of 
  'convDEPTH', with the exception that the the traversal is top-down instead of
  bottom-up.
-}
convTOP_SWEEP :: Conversion cls thry -> Conversion cls thry
convTOP_SWEEP = _TRY . topSweepQConv
  where topSweepQConv :: Conversion cls thry -> Conversion cls thry
        topSweepQConv conv = repeatqc conv `thenqc`
                             subQConv (topSweepQConv conv)

-- depth sub-conversions
-- tries to sequence, then tries conv1, finally conv2
thenqc :: Conversion cls thry -> Conversion cls thry -> Conversion cls thry
thenqc conv1 conv2 = Conv $ \ tm ->
    (do th@(Thm _ tm') <- runConv conv1 tm      
        (do tmth <- runConv conv2 . fromJust $ rand tm'
            liftO $ primTRANS th tmth)
          <|> return th)
    <|> runConv conv2 tm

-- tries to sequence, then tries conv1, conv2 not tried
thencqc :: Conversion cls thry -> Conversion cls thry -> Conversion cls thry
thencqc conv1 conv2 = Conv $ \ tm ->
    do th@(Thm _ tm') <- runConv conv1 tm       
       (do tmth <- runConv conv2 . fromJust $ rand tm'
           liftO $ primTRANS th tmth)
         <|> return th

{- 
  depth conversion for combinations, tries converting l and r, then just l,
  then just r, then fails.
-}
combQConv :: Conversion cls thry -> Conversion cls thry
combQConv conv = Conv $ \ tm ->
    case tm of
      (Comb l r) -> 
          (do th <- runConv conv l
              (do rth <- runConv conv r
                  liftO $ primMK_COMB th rth)
                <|> liftO (ruleAP_THM th r))
          <|> (do rth <- runConv conv r
                  liftO $ ruleAP_TERM l rth)
      _ -> fail "combQConv"

repeatqc :: Conversion cls thry -> Conversion cls thry
repeatqc conv = conv `thencqc` repeatqc conv

-- depth sub conversion.  indirectly fails for variables and constants.
subQConv :: Conversion cls thry -> Conversion cls thry
subQConv conv = Conv $ \ tm ->
    case tm of
      Abs{} -> runConv (convABS conv) tm
      TyAbs{} -> runConv (convTYABS conv) tm
      TyComb{} -> runConv (convTYAPP conv) tm
      _ -> runConv (combQConv conv) tm


-- traversal conversions

{-|
  The 'convDEPTH_BINOP' conversional applies a given conversion to the left 
  and right subterms of a binary operator combination whenever that operator 
  matches the one provided. If the combination is complex with many instances of
  the operator then all subterms will be converted.  It fails if the original 
  conversion fails on a subterm.
-}
convDEPTH_BINOP :: HOLTermRep tm cls thry => tm -> Conversion cls thry 
                -> Conversion cls thry
convDEPTH_BINOP pop conv = Conv $ \ tm -> noteHOL "convDEPTH_BINOP" $
    case tm of
      (Comb (Comb op' l) r) ->
          do op <- toHTm pop
             if op' == op
                then do lth <- runConv (convDEPTH_BINOP pop conv) l
                        rth <- runConv (convDEPTH_BINOP pop conv) r
                        liftO $ liftM1 primMK_COMB (ruleAP_TERM op' lth) rth
                else runConv conv tm
      _ -> runConv conv tm

{-|
  The 'convPATH' conversional applies a given conversion in a path specified 
  by the user.  The path is specified as a 'String' as defined below:  

  * @\'b\'@ -> traverse the body of a term abstraction -> 'convABS'

  * @\'t\'@ -> traverse the body of a type abstraction -> 'convTYABS'

  * @\'l\'@ -> traverse the operator of a combination -> 'convRATOR'

  * @\'r\'@ -> traverse the operand of a combination -> 'convRAND'

  * @\'c\'@ -> traverse the body of a type combination -> 'convTYAPP'
  
  It throws a 'HOLException' in the following cases:

  * An invalid path string is provided.

  * The structure of the term is not traversable by the pattern.

  * The original conversion fails on any of the subterms.
-}
convPATH :: forall cls thry. 
            String -> Conversion cls thry -> Conversion cls thry
convPATH pth conv = _NOTE "convPATH" $ cnvsl pth
  where cnvsl :: String -> Conversion cls thry
        cnvsl [] = conv
        cnvsl ('b':t) = convABS (cnvsl t)
        cnvsl ('t':t) = convTYABS (cnvsl t)
        cnvsl ('l':t) = convRATOR (cnvsl t)
        cnvsl ('r':t) = convRAND (cnvsl t)
        cnvsl ('c':t) = convTYAPP (cnvsl t)
        cnvsl _ = convFAIL "invalid path."

{-|
  The 'convPAT' conversional applies a given conversion following a pattern 
  specified by the user. The pattern is given in the form of a lambda 
  abstraction where the conversion is applied everywhere there is an instance of
  the bound variable in the body of the abstraction.  For example, 

  > convPAT (\ x. x a)

  is functionally equivalent to 'convRATOR'.  It fails when the original 
  conversion fails on a targetted subterm.
-}
convPAT :: forall cls thry. 
           HOLTerm -> Conversion cls thry -> Conversion cls thry
convPAT p conv = Conv $ \ t -> noteHOL "convPAT" $
    let (xs, pbod) = stripAbs p in
      runConv (pconv xs pbod) t
    where pconv :: [HOLTerm] -> HOLTerm -> Conversion cls thry 
          pconv xs pat
              | pat `elem` xs = conv
              | not (any (`freeIn` pat) xs) = convALL
              | otherwise = 
                  case pat of
                    (Comb l r) -> 
                        convCOMB2 (pconv xs l) (pconv xs r)
                    (Abs _ bod) -> 
                        convABS (pconv xs bod)
                    _ -> convFAIL "bad pattern."


{-|
  The 'convSUBS' conversion accepts a list of equational theorems, deconstructs 
  them into a substitution list, and performs the substitution over a term, 
  replacing any instance of the left hand side of an equation with the right 
  hand side. It fails when the list of theorems are not in the correct form.
-}
convSUBS :: HOLThmRep thm cls thry => [thm] -> Conversion cls thry
convSUBS [] = convALL
convSUBS pths = Conv $ \ tm -> noteHOL "convSUBS" $
    do ths <- mapM toHThm pths
       lfts <- liftMaybe "not an equational theorem." $
                 mapM (lHand . concl) ths
       gvs <- mapM (genVar . typeOf) lfts
       let pat = fromJust $ subst (zip lfts gvs) tm
       let abTh = primREFL . fromRight $ listMkAbs gvs pat
       th@(Thm _ tm') <- foldlM (\ x y -> ruleCONV
                                 (convRAND convBETA `_THEN` convLAND convBETA)
                                 (fromRight $ primMK_COMB x y)) abTh ths
       if rand tm' == Just tm 
          then return $! primREFL tm
          else return th

-- other derived rules
{-|@
 conv   A |- t 
---------------
 A U A' |- t'
@

  Applies a conversion to the conclusion of a theorem, unifying any newly
  introduced assumptions.  Throws a 'HOLException' when the conversion fails.
-}
ruleCONV :: HOLThmRep thm cls thry => Conversion cls thry -> thm 
         -> HOL cls thry HOLThm
ruleCONV conv pthm = noteHOL "ruleCONV" $
    do thm <- toHThm pthm
       thm' <- runConv conv $ concl thm
       liftO $ primEQ_MP thm' thm

{-|@
 A |- (\ x1 ... xn . t) s1 ... sn
-----------------------------------
 A |- (t[s1, ..., sn/x1, ..., xn])    
@

  Never fails, but may have no effect.
-}
ruleBETA :: HOLThm -> HOL cls thry HOLThm
ruleBETA = noteHOL "ruleBETA" . ruleCONV (convREDEPTH convBETA)

{-|@
 A |- (\\ x1 ... xn . t) [: s1 ... sn]
---------------------------------------
 A |- (t[s1, ..., sn/x1, ..., xn])    
@

  Never fails, but may have no effect.
-}
ruleTYBETA :: HOLThm -> HOL cls thry HOLThm
ruleTYBETA = noteHOL "ruleTYBETA" . ruleCONV (convREDEPTH convTYBETA)

{-|@
 A |- (l1 = r1) ... (l2 = r2)
------------------------------
 A |- (r1 = l1) ... (r2 = l2)
@

  Never fails, but may have no effect.
-}
ruleGSYM :: HOLThmRep thm cls thry => thm -> HOL cls thry HOLThm
ruleGSYM = ruleGSYM' <=< toHThm
  where ruleGSYM' :: HOLThm -> HOL cls thry HOLThm
        ruleGSYM' = noteHOL "ruleGSYM" . ruleCONV (convONCE_DEPTH convSYM)

{-|@
 [A1 |- l1 = r1, ..., An |- ln = rn]    A |-t
----------------------------------------------
 A1 U ... U An U A |- t[r1, ..., rn\/l1, ..., ln]
@

  The rule version of 'convSUBS'.  Throws a 'HOLException' if each theorem in
  the provided list is not equational.
-}
ruleSUBS :: HOLThmRep thm cls thry => [thm] -> HOLThm -> HOL cls thry HOLThm
ruleSUBS thms = noteHOL "ruleSUBS" . ruleCONV (convSUBS thms)
