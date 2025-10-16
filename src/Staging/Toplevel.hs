{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -ddump-splices #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Staging.Toplevel where
import Prelude hiding (fail)
import Staging.Direct
import Eval (SearchTree)
import FD.OvertonFD (OvertonFD)
import Solver (Solver, run)
import qualified Staging.Optimised as Opt


dfsS :: (Solver solver) => (SearchTree solver a -> solver [a]) -> SearchTree solver a -> [a]
dfsS search = run . search 

bbLdsRandStaged :: SearchTree OvertonFD a -> OvertonFD [a] 
-- seed discrepancy
bbLdsRandStaged = $$(bbLdsRandCode 123 5000) []

bbLdsRandStagedNew :: SearchTree OvertonFD a -> OvertonFD [a] 
-- seed discrepancy
bbLdsRandStagedNew = $$(bbLdsRandCodeNew 123 5000) []

bbLdsRandStagedOld :: SearchTree OvertonFD a -> OvertonFD [a]
bbLdsRandStagedOld = $$(bbLdsRandCodeOld 123 5000) []

justBBStaged :: SearchTree OvertonFD a -> OvertonFD [a]  
justBBStaged = $$justBBCode []

justBBOptimised :: SearchTree OvertonFD a -> OvertonFD [a]
justBBOptimised = $$(Opt.justBBCode) []

bbLdsRandOptimised :: SearchTree OvertonFD a -> OvertonFD [a]
bbLdsRandOptimised = $$(Opt.bbLdsRandCode 123 5000) []

