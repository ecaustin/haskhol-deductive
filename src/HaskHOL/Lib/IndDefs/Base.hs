{-# LANGUAGE FlexibleContexts #-}
module HaskHOL.Lib.IndDefs.Base where

import HaskHOL.Core

data MonoThms = MonoThms ![HOLThm] deriving Typeable

deriveSafeCopy 0 'base ''MonoThms

addMono :: HOLThm -> Update MonoThms ()
addMono th =
    do (MonoThms ths) <- get
       put (MonoThms (th:ths))

getMonos :: Query MonoThms [HOLThm]
getMonos =
    do (MonoThms ths) <- ask
       return ths

makeAcidic ''MonoThms ['addMono, 'getMonos]

addMonoThm :: HOLThmRep thm Theory thry => thm -> HOL Theory thry ()
addMonoThm pthm =
    do mthm <- toHThm pthm
       acid <- openLocalStateHOL (MonoThms [])
       updateHOL acid (AddMono mthm)
       closeAcidStateHOL acid
