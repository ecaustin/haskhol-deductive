module HaskHOL.Lib.Trivia.PQ where

import HaskHOL.Core
import HaskHOL.Lib.Trivia.Context

-- Lift Parse Context and define quasi-quoter
pcTrivia :: ParseContext
pcTrivia = $(liftParseContext ctxtTrivia)

trivia :: QuasiQuoter
trivia = baseQuoter ctxtTrivia pcTrivia
