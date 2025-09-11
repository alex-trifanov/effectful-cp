{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Staging.Old.Direct where

import Control.Monad.Free
import Effects.Core
import Language.Haskell.TH 
import Effects.NonDet
import Queues
import Prelude hiding (fail)
import System.Random
import Transformers (flipT)

codeCurry :: (CodeQ a -> CodeQ b) -> CodeQ (a -> b)
codeCurry f = [||\a -> $$(f [||a||])||]

data SearchTransformer ts es = SearchTransformer
  { tsInit :: Code Q ts,
    esInit :: Code Q es,
    solEs :: Code Q es -> Code Q es,
    leftTs :: Code Q ts -> Code Q ts,
    rightTs :: Code Q ts -> Code Q ts,
    nextState :: forall a.
      Code Q ts -> Code Q es -> Code Q (Free (NonDet :+: Void) a) ->
        (Code Q ts, Code Q es, Code Q (Free (NonDet :+: Void) a))
  }

idTrans :: SearchTransformer () ()
idTrans = SearchTransformer 
  { tsInit = [|| () ||]
  , esInit = [|| () ||]
  , solEs = id 
  , leftTs = id 
  , rightTs = id 
  , nextState = \ts es model -> (ts, es, model)
  }

dbsTrans :: Int -> SearchTransformer Int ()
dbsTrans depthLimit =
  SearchTransformer
    { tsInit = [||0||],
      esInit = [||()||],
      solEs = id,
      leftTs = \ts -> [|| $$ts + 1 ||],
      rightTs = \ts -> [|| $$ts + 1 ||],
      nextState = \ts es model -> (ts, es, [|| if $$ts <= depthLimit then $$model else fail||])
    }

nbsTrans :: Int -> SearchTransformer () Int 
nbsTrans nodeLimit = 
  SearchTransformer
    { tsInit = [|| () ||]
    , esInit = [|| 0 ||]
    , solEs = id
    , leftTs = id
    , rightTs = id
    , nextState = \ts es model -> (ts, [|| $$es + 1 ||], [||if $$es <= nodeLimit then $$model else fail||])
    }

ldsTrans :: Int -> SearchTransformer Int ()
ldsTrans discLimit = 
  SearchTransformer
  { tsInit = [|| 0 ||]
  , esInit = [|| () ||]
  , solEs = id
  , leftTs = id
  , rightTs = id
  , nextState = \ts es model -> (ts, es, [|| if $$ts <= discLimit then $$model else fail ||])
  }

randTrans :: Int -> SearchTransformer () [Bool]
randTrans seed = 
  SearchTransformer
  { tsInit = [|| () ||]
  , esInit = [|| randoms $ mkStdGen seed  ||]
  , solEs = id
  , leftTs = id
  , rightTs = id
  , nextState = \ts es model ->
    (ts, [|| tail $$es ||], [|| let tree = $$model in if head $$es then flipT tree else tree ||])
  }

dbsTrans25 :: SearchTransformer Int ()
dbsTrans25 = dbsTrans 25

nbsTrans500000 :: SearchTransformer () Int 
nbsTrans500000 = nbsTrans 500000

ldsTrans5000000 :: SearchTransformer Int ()
ldsTrans5000000 = ldsTrans 5000000

randTrans2801 :: SearchTransformer () [Bool]
randTrans2801 = randTrans 2801


stagedRand :: Code Q ( [((), Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
stagedRand = stage1 randTrans2801

dbsRandTrans :: SearchTransformer (Int, ()) ((), [Bool])
dbsRandTrans = composeTrans dbsTrans25 randTrans2801

stagedDbsRand :: Code Q ( [((Int, ()), Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
stagedDbsRand = stage1 dbsRandTrans

dbsNbsTrans :: SearchTransformer (Int, ()) ((), Int)
dbsNbsTrans = composeTrans dbsTrans25 nbsTrans500000

dbsNbsLdsTrans :: SearchTransformer ((Int, ()), Int) (((), Int), ())
dbsNbsLdsTrans = composeTrans dbsNbsTrans ldsTrans5000000

stagedDbs25 :: Code Q ([(Int, Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
stagedDbs25 = stage1 dbsTrans25 

stagedDbs15 :: Code Q ([(Int, Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
stagedDbs15 = stage1 (dbsTrans 15)

stagedDbsNbs :: Code Q ([((Int, ()), Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
stagedDbsNbs = stage1 dbsNbsTrans

stagedDbsNbsLds :: Code Q ( [( ((Int, ()), Int) , Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a] )
stagedDbsNbsLds = stage1 dbsNbsLdsTrans

stage1 :: forall q ts es a. (Queue q, Elem q ~ (ts, Free (NonDet :+: Void) a)) =>
  SearchTransformer ts es -> 
  Code Q (q -> Free (NonDet :+: Void) a -> Free Void [a])
stage1 (SearchTransformer tsInit esInit solEs leftTs rightTs nextState) = rec2 
  (\(_, continue) ->  
    [||
    \ts es q tree -> case tree of 
      Pure a -> (a:) <$> $$continue $$(solEs [|| es ||]) q
      l :|: r -> $$continue es (pushQ ($$(leftTs [|| ts ||]), l) $ pushQ ($$(rightTs [|| ts ||]), r) q) 
      Fail -> $$continue es q
    ||]
    )
  (\(go, _) -> [||
    \es q -> if nullQ q then pure [] else
      let ((ts, tree),q') = popQ q in
        $$(
          let (ts', es', tree') = nextState [||ts||] [||es||] [||tree||] in
          [||$$go $$ts' $$es' q' $$tree'||]
          )
  ||])
  (\(go, _) -> [|| $$go $$tsInit $$esInit ||])

composeTrans :: SearchTransformer ts1 es1 -> SearchTransformer ts2 es2 -> SearchTransformer (ts1, ts2) (es1, es2)
composeTrans t1 t2 =
  SearchTransformer {
    tsInit = [|| ($$(tsInit t1), $$(tsInit t2)) ||]

  , esInit = [|| ($$(esInit t1), $$(esInit t2)) ||] 

  , solEs = \esc -> [|| ($$(solEs t1 [|| fst $$esc ||]), $$(solEs t2 [|| snd $$esc ||])) ||]

  , leftTs = \ts -> let ts1 = [|| fst $$ts ||]
                        ts2 = [|| snd $$ts ||]
                      in [|| ($$(leftTs t1 ts1), $$(leftTs t2 ts2)) ||]

  , rightTs = \ts -> let ts1 = [|| fst $$ts ||]
                         ts2 = [|| snd $$ts ||]
                      in [|| ($$(rightTs t1 ts1), $$(rightTs t2 ts2)) ||]

  , nextState = \ts es tree -> let ts1 = [|| fst $$ts ||]
                                   ts2 = [|| snd $$ts ||]
                                   es1 = [|| fst $$es ||]
                                   es2 = [|| snd $$es ||]
                                   (ts1', es1', tree') = nextState t1 ts1 es1 tree
                                   (ts2', es2', tree'') = nextState t2 ts2 es2 tree'
                                  in  
                                   ([|| ($$ts1', $$ts2') ||], [|| ($$es1', $$es2') ||], tree'')
}

-- ------------------------------------------

exampleTrans :: SearchTransformer ((Int, ()), ()) (((), [Bool]), Int)
exampleTrans = composeTrans (composeTrans (dbsTrans 15) (randTrans 300)) (nbsTrans 1500)

stagedExample :: Code Q ([(((Int, ()), ()), Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
stagedExample = stage1 exampleTrans

exampleBigTrans :: SearchTransformer ((Int, ()), ()) (((), [Bool]), Int)
exampleBigTrans = composeTrans (composeTrans (dbsTrans 25) (randTrans 300)) (nbsTrans 18000)

stagedBigExample :: Code Q ([(((Int, ()), ()), Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
stagedBigExample = stage1 exampleBigTrans

exampleVeryBigTrans :: SearchTransformer ((Int, ()), ()) (((), [Bool]), Int)
exampleVeryBigTrans = composeTrans (composeTrans (dbsTrans 32) (randTrans 300)) (nbsTrans 320000)

stagedVeryBigExample :: Code Q ([(((Int, ()), ()), Free (NonDet :+: Void) a)] -> Free (NonDet :+: Void) a -> Free Void [a])
stagedVeryBigExample = stage1 exampleVeryBigTrans
-- ------------------------------------------

type Mk1 a b = Code Q a -> Code Q b
type Mk2 a b c = (Code Q a, Code Q b) -> Code Q c
type Mk4 a b c d e = (Code Q a, Code Q b, Code Q c, Code Q d) -> Code Q e

rec2 :: Mk2 a b a -> Mk2 a b b -> Mk2 a b c -> Code Q c
rec2 mk1 mk2 mkk = [|| let f = $$(mk1 ([|| f ||], [|| g ||]))
                           g = $$(mk2 ([|| f ||], [|| g ||]))
                          in $$(mkk ([|| f ||], [|| g ||])) ||]

rec :: Mk1 a a -> Code Q a 
rec mk1 = [|| let f = $$(mk1 [|| f ||]) in f ||]
