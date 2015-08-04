module HaskHOL.Lib.Bool.PQ where

import HaskHOL.Core
import HaskHOL.Lib.Bool.Context

-- Lift Parse Context and define quasi-quoter
pcBool :: ParseContext
pcBool = $(liftParseContext ctxtBool)

bool :: QuasiQuoter
bool = baseQuoter ctxtBool pcBool
