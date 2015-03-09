module HaskHOL.Lib.Trivia.A.Base where

import HaskHOL.Core

import HaskHOL.Lib.Bool
import HaskHOL.Lib.Classic
import HaskHOL.Lib.Classic.Context
import HaskHOL.Lib.DRule
import HaskHOL.Lib.Tactics

thmEXISTS_ONE_REP :: ClassicCtxt thry => HOL cls thry HOLThm
thmEXISTS_ONE_REP = cacheProof "thmEXISTS_ONE_REP" ctxtClassic $
    prove "?b:bool . b" $
      tacEXISTS "T" `_THEN`
      tacBETA `_THEN`
      tacACCEPT thmTRUTH



defO' :: BoolCtxt thry => HOL Theory thry HOLThm
defO' = newDefinition "o"
    [str| (o) (f:B->C) g = \x:A. f(g(x)) |]

defI' :: BoolCtxt thry => HOL Theory thry HOLThm
defI' = newDefinition "I"
    [str| I = \x:A. x |]

tyDefOne' :: ClassicCtxt thry => HOL Theory thry HOLThm
tyDefOne' = newTypeDefinition "1" "one_ABS" "one_REP" thmEXISTS_ONE_REP

defONE' :: BoolCtxt thry => HOL Theory thry HOLThm
defONE' = newDefinition "one" "one = @x:1. T"  
