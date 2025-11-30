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
import Queens (nqueens)


bbLdsRand = it . (bb newBound) . (lds 5000) . (rand 123)
queensT = it . nbs 150000 . rand 300 . dbs 30

main :: IO ()
main = do
  arg <- head <$> getArgs
  let graph = gmodel 50
      queens = nqueens 11
      sols = case arg of
        "graph_staged" -> [dfsS bbLdsRandStaged graph]
        "graph" -> [dfs bbLdsRand graph]
        "queens" -> dfs queensT queens
        "queens_staged" -> dfsS queensTransStaged queens
        _ -> []
  print $ sols
