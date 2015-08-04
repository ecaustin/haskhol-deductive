module HaskHOL.Lib.TypeQuant.PQ where

import HaskHOL.Core
import HaskHOL.Lib.TypeQuant.Context

-- Lift Parse Context and define quasi-quoter
pcTypeQuant :: ParseContext
pcTypeQuant = $(liftParseContext ctxtTypeQuant)

typeQuant :: QuasiQuoter
typeQuant = baseQuoter ctxtTypeQuant pcTypeQuant
