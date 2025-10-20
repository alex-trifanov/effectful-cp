{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- {-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Transformers where

import Control.Monad.Free (Free (Free), MonadFree (wrap))
import Effects.Algebra
import Effects.Core (Sub, (:+:) (..))
import Effects.NonDet (NonDet, fail, try, pattern (:|:))
import Effects.Solver (SolverE)
import Effects.Transformer (TransformerE (..), initS, initT, leftS, leftT, nextS, nextT, rightS, rightT, solS, solT)
import Eval
import Solver (Solver (..))
import System.Random
import Prelude hiding (fail)

type Transformer ts es solver a =
  forall ts' es'.
  TransformerTree (ts, ts') (es, es') solver a [a] ->
  TransformerTree ts' es' solver a [a]

type Transformer' ts es solver a =
  TransformerTree ts es solver a [a] -> Free (SolverE solver) [a]

makeTEff ::
  forall ts es ts' es' solver a.
  (Solver solver) =>
  ts ->
  es ->
  (es -> TransformerTree ts' es' solver a es) ->
  (ts -> TransformerTree ts' es' solver a ts) ->
  (ts -> TransformerTree ts' es' solver a ts) ->
  (SearchTree solver a -> ts -> es -> (SearchTree solver a, ts, es)) ->
  TransformerTree (ts, ts') (es, es') solver a [a] ->
  TransformerTree ts' es' solver a [a]
makeTEff tsInit esInit esSol tsLeft tsRight nextState = handle (alg <| wrap . Inr) pure
 where
  alg ::
    TransformerE
      (ts, ts')
      (es, es')
      (SearchTree solver a)
      (TransformerTree ts' es' solver a [a]) ->
    TransformerTree ts' es' solver a [a]
  alg (InitT' k) = do
    (tsRest, esRest) <- initS
    k (tsInit, tsRest) (esInit, esRest)
  alg (SolT' (es, esRest) k) = do
    esRest' <- solS esRest
    es' <- esSol es
    k (es', esRest')
  alg (LeftT' (ts, tsRest) k) = do
    tsRest' <- leftS tsRest
    ts' <- tsLeft ts
    k (ts', tsRest')
  alg (RightT' (ts, tsRest) k) = do
    tsRest' <- rightS tsRest
    ts' <- tsRight ts
    k (ts', tsRest')
  alg (NextT' tree (ts, tsRest) (es, esRest) k) = do
    let (tree', ts', es') = nextState tree ts es
    (tree'', tsRest', esRest') <- nextS tree' tsRest esRest
    k tree'' (ts', tsRest') (es', esRest')

makeTransNC ::
  forall ts es solver a.
  (Solver solver) =>
  ts ->
  es ->
  (es -> Free (SolverE solver) es) ->
  (ts -> Free (SolverE solver) ts) ->
  (ts -> Free (SolverE solver) ts) ->
  (SearchTree solver a -> ts -> es -> (SearchTree solver a, ts, es)) ->
  Transformer' ts es solver a
makeTransNC tsInit esInit esSol tsLeft tsRight nextState = handle (alg <| Free) pure
 where
  alg (InitT' k) = do
    k tsInit esInit
  alg (LeftT' ts k) = do
    ts' <- tsLeft ts
    k ts'
  alg (RightT' ts k) = do
    ts' <- tsRight ts
    k ts'
  alg (SolT' es k) = do
    es' <- esSol es
    k es'
  alg (NextT' tree ts es k) = do
    let (tree', ts', es') = nextState tree ts es
    k tree' ts' es'

dbsNC :: (Solver solver) => Int -> Transformer' Int () solver a
dbsNC depthLimit = makeTransNC 0 () pure (pure . succ) (pure . succ) $
  \tree depth u -> (if depth <= depthLimit then tree else fail, depth, u)

nbsNC :: (Solver solver) => Int -> Transformer' () Int solver a
nbsNC nodeLimit = makeTransNC () 0 pure pure pure $
  \tree u nodes -> (if nodes <= nodeLimit then tree else fail, u, nodes + 1)

dbsAndNbsNC :: (Solver solver) => Int -> Int -> Transformer' Int Int solver a 
dbsAndNbsNC depthLimit nodeLimit = makeTransNC 0 0 pure (pure . succ) (pure . succ) $
  \tree depth nodes -> (if depth <= depthLimit && nodes <= nodeLimit then tree else fail, depth, nodes + 1)

dbs :: (Solver solver) => Int -> Transformer Int () solver a
dbs depthLimit = makeTEff 0 () pure (pure . succ) (pure . succ) $
  \tree depth u -> (if depth <= depthLimit then tree else fail, depth, u)

nbs :: (Solver solver) => Int -> Transformer () Int solver a
nbs nodeLimit = makeTEff () 0 pure pure pure $
  \tree u nodes -> (if nodes <= nodeLimit then tree else fail, u, nodes + 1)

flipT :: (NonDet `Sub` sig) => Free sig a -> Free sig a
flipT (l :|: r) = try r l
flipT other = other

rand :: (Solver solver) => Int -> Transformer () [Bool] solver a
rand seed = makeTEff
  ()
  (randoms $ mkStdGen seed)
  pure
  pure
  pure
  $ \tree u coins -> (if head coins then flipT tree else tree, u, tail coins)

lds :: (Solver solver) => Int -> Transformer Int () solver a
lds discrepancyLimit = makeTEff 0 () pure pure (pure . succ) $
  \tree disc u -> (if disc <= discrepancyLimit then tree else fail, disc, u)

it :: forall solver a. (Solver solver) => Transformer' () () solver a
it = handle (alg <| wrap) pure
 where
  alg ::
    TransformerE () () (SearchTree solver a) (Free (SolverE solver) [a]) ->
    Free (SolverE solver) [a]
  alg (InitT' k) = k () ()
  alg (LeftT' _ k) = k ()
  alg (RightT' _ k) = k ()
  alg (SolT' _ k) = k ()
  alg (NextT' tree _ _ k) = k tree () ()
