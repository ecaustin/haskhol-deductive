module HaskHOL.Lib.Theorems.PQ where

import HaskHOL.Core
import HaskHOL.Lib.Theorems.Context

-- Lift Parse Context and define quasi-quoter
pcTheorems :: ParseContext
pcTheorems = $(liftParseContext ctxtTheorems)

theorems :: QuasiQuoter
theorems = baseQuoter ctxtTheorems pcTheorems
