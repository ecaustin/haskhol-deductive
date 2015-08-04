module HaskHOL.Lib.Classic.PQ where

import HaskHOL.Core
import HaskHOL.Lib.Classic.Context

-- Lift Parse Context and define quasi-quoter
pcClassic :: ParseContext
pcClassic = $(liftParseContext ctxtClassic)

classic :: QuasiQuoter
classic = baseQuoter ctxtClassic pcClassic
