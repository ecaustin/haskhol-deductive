module HaskHOL.Lib.IndDefs.PQ where

import HaskHOL.Core
import HaskHOL.Lib.IndDefs.Context

-- Lift Parse Context and define quasi-quoter
pcIndDefs :: ParseContext
pcIndDefs = $(liftParseContext ctxtIndDefs)

indDefs :: QuasiQuoter
indDefs = baseQuoter ctxtIndDefs pcIndDefs
