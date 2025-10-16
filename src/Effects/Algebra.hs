{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Effects.Algebra where

import Control.Monad.Free (Free (..))
import Effects.Core ((:+:) (..))

handle :: (Functor f) => (f b -> b) -> (a -> b) -> Free f a -> b
handle _alg gen (Pure x) = gen x
handle alg gen (Free op) = alg $ (handle alg gen) <$> op

handlePara :: (Functor f) => (f (Free f a, b) -> b) -> (a -> b) -> Free f a -> b
handlePara _alg gen (Pure x) = gen x
handlePara alg gen (Free op) = alg $ (\fa -> (fa, handlePara alg gen fa)) <$> op

handle2 :: (Functor f) => 
  ((Free f a -> b) -> f (Free f a, b) -> b) -> ((Free f a -> b) -> a -> b) -> Free f a -> b 
handle2 alg gen (Pure x) = gen (handle2 alg gen) x
handle2 alg gen (Free op) = alg (handle2 alg gen) $ (\fa -> (fa, handle2 alg gen fa)) <$> op

(<|) :: (f a -> b) -> (g a -> b) -> (f :+: g) a -> b
(<|) algF _algG (Inl s) = algF s
(<|) _algF algG (Inr s) = algG s
infixr 6 <|

(<|$) :: (c -> f a -> b) -> (c -> g a -> b) -> (c -> (f :+: g) a -> b)
(<|$) algF _algG cont (Inl s) = algF cont s 
(<|$) _algF algG cont (Inr s) = algG cont s
infixr 6 <|$

liftPara :: (Functor f) => (f b -> b) -> (f (c, b) -> b)
liftPara alg = alg . (snd <$>)

-- type Sigma = NonDet :+: State Int :+: Void -- global state
-- type SigmaLocal = State Int :+: NonDet :+: Void -- local state
