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
module Effects.CPOps (
  CPOps(..)
, newVar
, exists
, add
, exist
, in_domain
, (@=)
, (@+)
, (@\=)
, (@\==)
, addSum
, (@<)
, (@>)
, prime) where
import Control.Monad.Free (Free (..))
import Effects.Core (Sub(..), inject)
import FD.OvertonFD (OvertonFD, OPlus ((:+)), OConstraint (..))
import Solver(Solver(..))

data CPOps solver a where
  NewVar'  :: (Term solver -> a) -> CPOps solver a
  Add'     :: (Constraint solver) -> a -> CPOps solver a
  deriving Functor

newVar :: forall solver sig. (Solver solver, CPOps solver `Sub` sig) =>
  Free sig (Term solver)
newVar = inject (NewVar' pure)

exists :: forall solver sig a. (Solver solver, CPOps solver `Sub` sig) =>
  (Term solver -> Free sig a) -> Free sig a
exists = inject . NewVar'

add :: forall solver sig. (Solver solver, CPOps solver `Sub` sig) =>
  Constraint solver -> Free sig ()
add c = inject (Add' c (pure ()))

-- --------------| Sugar |--------------

-- | Generates `n` new solver variables.
exist :: forall solver sig a. (Solver solver, CPOps solver `Sub` sig) =>
  Int -> ([Term solver] -> Free sig a) -> Free sig a
exist n k = go n $ pure []
  where
    go :: Int -> Free sig [Term solver] -> Free sig a
    go 0 acc = acc >>= k
    go n' acc = do
      v <- newVar
      go (n' - 1) ((v :) <$> acc)

in_domain :: (CPOps OvertonFD `Sub` sig) => Term OvertonFD -> (Int, Int) -> Free sig ()
v `in_domain` r = add (OInDom v r)

(@=) :: (CPOps OvertonFD `Sub` sig) => Term OvertonFD -> Int -> Free sig ()
v @= n = add (OHasValue v n)

(@+) :: Term OvertonFD -> Int -> OPlus
(@+) = (:+)

(@\=) :: (CPOps OvertonFD `Sub` sig) => Term OvertonFD -> Term OvertonFD -> Free sig ()
v1 @\= v2 = add (ODiff v1 v2)

(@<) :: (CPOps OvertonFD `Sub` sig) => Term OvertonFD -> Int -> Free sig ()
v1 @< v2 = add (OLtConst v1 v2)

(@>) :: (CPOps OvertonFD `Sub` sig) => Term OvertonFD -> Int -> Free sig ()
v1 @> v2 = add (OGtConst v1 v2)

(@\==) :: (CPOps OvertonFD `Sub` sig) => Term OvertonFD -> OPlus -> Free sig ()
v1 @\== (v2 :+ n) = do
  n' <- newVar
  t2 <- newVar
  add (OHasValue n' n)
  add (OAdd t2 v2 n')
  add (ODiff t2 v1)

addSum :: (CPOps OvertonFD `Sub` sig) => Term OvertonFD -> Term OvertonFD -> Term OvertonFD -> Free sig ()
addSum a b c = add @OvertonFD (OAdd a b c)

prime :: (CPOps OvertonFD `Sub` sig) => Term OvertonFD -> Free sig ()
prime a = add @OvertonFD (OPrime a)
