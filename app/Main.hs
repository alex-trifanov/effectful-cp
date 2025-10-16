{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import Staging.Toplevel as Staging
import System.Environment (getArgs)
import BranchAndBound (gmodel)
import BranchAndBound (bb)
import Transformers
import BranchAndBound (newBound)
import Eval


bbLdsRand = it . (bb newBound) . (lds 5000) . (rand 123)

main :: IO ()
main = do
  arg <- head <$> getArgs
  let graph = gmodel 60
      sols = case arg of
        "bb_lds_rand_staged" -> dfsS bbLdsRandStaged graph
        "bb_lds_rand_staged_old" -> dfsS bbLdsRandStagedOld graph
        "bb_lds_rand_staged_new" -> dfsS bbLdsRandStagedNew graph
        "bb_lds_rand" -> dfs bbLdsRand graph
        "bb_lds_rand_old" -> dfsO bbLdsRand graph
        "bb_lds_rand_opt" -> dfsS bbLdsRandOptimised graph
        _ -> []
  print $ sols
