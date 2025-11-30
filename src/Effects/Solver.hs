{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-missing-pattern-synonym-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Effects.Solver where

import Control.Monad (join)
import Control.Monad.Free (Free (..))
import Effects.Algebra
import Effects.Core (Sub (..), inject, project)
import Effects.NonDet (NonDet, fail)
import FD.OvertonFD
import Solver (Solver (..))
import Prelude hiding (fail)

data SolverE solver a where
  RunSolver' :: solver a -> SolverE solver a

instance (Solver solver) => Functor (SolverE solver) where
  fmap :: (Solver solver) => (a -> b) -> SolverE solver a -> SolverE solver b
  fmap f (RunSolver' a) = RunSolver' (f <$> a)

pattern Solver a <- (project -> (Just (RunSolver' a)))

dynamic :: forall solver a sig. (Solver solver, SolverE solver `Sub` sig) => solver a -> Free sig a
dynamic = solve

solve :: (Solver solver, Sub (SolverE solver) sig) => solver a -> Free sig a
solve a = (inject . RunSolver') $ pure <$> a

runSolver :: (Solver solver) => Free (SolverE solver) a -> solver a
runSolver (Pure a) = pure a
runSolver (Solver a) = a >>= runSolver

runSolverAlg :: (Solver solver) => Free (SolverE solver) a -> solver a
runSolverAlg = handle (\(RunSolver' s) -> join s) pure

algSolver :: (Solver solver) => SolverE solver (solver a) -> solver a
algSolver (RunSolver' s) = join s

--------- sugar

-- exists :: forall solver sig a. (Solver solver, CPOps solver `Sub` sig) =>
--   (Term solver -> Free sig a) -> Free sig a
-- exists = inject . NewVar'

-- add :: forall solver sig. (Solver solver, CPOps solver `Sub` sig) =>
--   Constraint solver -> Free sig ()
-- add c = inject (Add' c (pure ()))

newVar ::
  (Solver solver, SolverE solver `Sub` sig) =>
  Free sig (Term solver)
newVar = solve newvar

exists ::
  (Solver solver, SolverE solver `Sub` sig) =>
  (Term solver -> Free sig a) -> Free sig a
exists = (newVar >>=)

add ::
  (Solver solver, NonDet `Sub` sig, SolverE solver `Sub` sig) =>
  Constraint solver -> Free sig ()
add c = do
  success <- solve $ addCons c
  if success then pure () else fail

-- | Generates `n` new solver variables.
exist ::
  forall solver sig a.
  (Solver solver, SolverE solver `Sub` sig) =>
  Int -> ([Term solver] -> Free sig a) -> Free sig a
exist n k = go n $ pure []
 where
  go :: Int -> Free sig [Term solver] -> Free sig a
  go 0 acc = acc >>= k
  go n' acc = do
    v <- newVar
    go (n' - 1) ((v :) <$> acc)

in_domain ::
  (SolverE OvertonFD `Sub` sig, NonDet `Sub` sig) =>
  Term OvertonFD -> (Int, Int) -> Free sig ()
v `in_domain` r = add (OInDom v r)

(@=) :: (SolverE OvertonFD `Sub` sig, NonDet `Sub` sig) => Term OvertonFD -> Int -> Free sig ()
v @= n = add (OHasValue v n)

(@+) :: Term OvertonFD -> Int -> OPlus
(@+) = (:+)

(@\=) ::
  (SolverE OvertonFD `Sub` sig, NonDet `Sub` sig) =>
  Term OvertonFD -> Term OvertonFD -> Free sig ()
v1 @\= v2 = add (ODiff v1 v2)

(@<) :: (SolverE OvertonFD `Sub` sig, NonDet `Sub` sig) => Term OvertonFD -> Int -> Free sig ()
v1 @< v2 = add (OLtConst v1 v2)

(@>) :: (SolverE OvertonFD `Sub` sig, NonDet `Sub` sig) => Term OvertonFD -> Int -> Free sig ()
v1 @> v2 = add (OGtConst v1 v2)

(@\==) :: (SolverE OvertonFD `Sub` sig, NonDet `Sub` sig) => Term OvertonFD -> OPlus -> Free sig ()
v1 @\== (v2 :+ n) = do
  n' <- newVar
  t2 <- newVar
  add (OHasValue n' n)
  add (OAdd t2 v2 n')
  add (ODiff t2 v1)

addSum ::
  (SolverE OvertonFD `Sub` sig, NonDet `Sub` sig) =>
  Term OvertonFD -> Term OvertonFD -> Term OvertonFD -> Free sig ()
addSum a b c = add @OvertonFD (OAdd a b c)

prime :: (SolverE OvertonFD `Sub` sig, NonDet `Sub` sig) => Term OvertonFD -> Free sig ()
prime a = add @OvertonFD (OPrime a)