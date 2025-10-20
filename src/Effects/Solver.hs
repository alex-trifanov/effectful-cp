{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Effects.Solver where
import Control.Monad.Free (Free (..))
import Effects.Core (Sub(..), project, inject)
import Solver(Solver(..))
import Effects.Algebra
import Control.Monad (join)

data SolverE solver a where 
  RunSolver' :: solver a -> SolverE solver a 

instance (Solver solver) => Functor (SolverE solver) where
  fmap :: Solver solver => (a -> b) -> SolverE solver a -> SolverE solver b
  fmap f (RunSolver' a) = RunSolver' (f <$> a) 

pattern Solver a <- (project -> (Just (RunSolver' a)))

solve' :: forall solver a sig. (Solver solver, SolverE solver `Sub` sig) => solver (Free sig a) -> Free sig a
solve' = inject . RunSolver'

solve :: (Solver solver, Sub (SolverE solver) sig) => solver a -> Free sig a
solve a = solve' $ pure <$> a

runSolver :: Solver solver => Free (SolverE solver) a -> solver a 
runSolver (Pure a) = pure a
runSolver (Solver a) = a >>= runSolver

runSolverAlg :: Solver solver => Free (SolverE solver) a -> solver a 
runSolverAlg = handle (\(RunSolver' s) -> join s) pure

algSolver :: (Solver solver) => SolverE solver (solver a) -> solver a
algSolver (RunSolver' s) = join s
