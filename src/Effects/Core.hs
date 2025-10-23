{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Effects.Core (
  inject,
  project,
  runEffects,
  pattern Other,
  Sub (..),
  (:+:) (..),
  Void,
  getL,
  putL,
  -- wrapF,
  wrapFree,
  liftR,
  pattern Other2
)
where

import Control.Monad.Free (Free (..), MonadFree (wrap))

data (sig1 :+: sig2) a = Inl (sig1 a) | Inr (sig2 a)
infixr 7 :+:

instance (Functor sig1, Functor sig2) => Functor (sig1 :+: sig2) where
  fmap f (Inl s1) = Inl (fmap f s1)
  fmap f (Inr s2) = Inr (fmap f s2)

instance (Foldable sig1, Foldable sig2) => Foldable (sig1 :+: sig2) where
  foldMap ::
    (Foldable sig1, Foldable sig2, Monoid m) =>
    (a -> m) -> (:+:) sig1 sig2 a -> m
  foldMap f (Inl s1) = foldMap f s1
  foldMap f (Inr s2) = foldMap f s2

instance (Traversable sig1, Traversable sig2) => Traversable (sig1 :+: sig2) where
  traverse ::
    (Traversable sig1, Traversable sig2, Applicative f) =>
    (a -> f b) -> (:+:) sig1 sig2 a -> f ((:+:) sig1 sig2 b)
  traverse f (Inl s1) = Inl <$> traverse f s1
  traverse f (Inr s2) = Inr <$> traverse f s2

class (Functor sub, Functor sup) => sub `Sub` sup where
  inj :: sub a -> sup a
  prj :: sup a -> Maybe (sub a)

instance {-# OVERLAPPING #-} (Functor sig) => sig `Sub` sig where
  inj = id
  prj = Just

instance {-# OVERLAPS #-} (Functor sig1, Functor sig2) => sig1 `Sub` (sig1 :+: sig2) where
  inj = Inl
  prj (Inl fa) = Just fa
  prj _ = Nothing

instance {-# INCOHERENT #-} (Functor (f a), Functor sig2, a ~ b) => f b `Sub` (f (a :: k) :+: sig2) where
  inj = Inl
  prj (Inl fa) = Just fa
  prj _ = Nothing

instance {-# INCOHERENT #-} (Functor (f a b c), Functor sig2, a ~ x, b ~ y, c ~ z) => f x y z `Sub` (f a b c :+: sig2) where
  inj = Inl
  prj (Inl fa) = Just fa
  prj _ = Nothing

instance {-# OVERLAPPABLE #-} (Functor sig1, sig `Sub` sig2) => sig `Sub` (sig1 :+: sig2) where
  inj = Inr . inj
  prj (Inr ga) = prj ga
  prj _ = Nothing

inject :: (sub `Sub` sup) => sub (Free sup a) -> Free sup a
inject = Free . inj

project :: (sub `Sub` sup) => Free sup a -> Maybe (sub (Free sup a))
project (Free s) = prj s
project _ = Nothing

-- wrapF :: (sub `Sub` sup) => sub a -> Free sup a
-- wrapF = Free . inj . (pure <$>)

getL :: Free (sig1 :+: sig2) a -> Maybe (sig1 (Free (sig1 :+: sig2) a))
getL (Free (Inl a)) = Just a
getL _ = Nothing

putL :: sig1 (Free (sig1 :+: sig2) a) -> Free (sig1 :+: sig2) a
putL = Free . Inl

data Void cnt deriving (Functor, Foldable, Traversable)

runEffects :: Free Void a -> a
runEffects (Pure x) = x
runEffects _ = error "impossible???"

-- wrapF :: m `Sub` sig => m a -> Free sig a
-- wrapF m = wrap . inj $ pure <$> m

wrapFree :: forall sub sup a. (sub `Sub` sup) => sub (Free sup a) -> Free sup a
wrapFree msig = wrap $ inj @sub @sup msig

pattern Other :: sig2 (Free (sig1 :+: sig2) a) -> Free (sig1 :+: sig2) a
pattern Other s = Free (Inr s)

pattern Other2 :: sig3 (Free (sig1 :+: sig2 :+: sig3) a) -> Free (sig1 :+: sig2 :+: sig3) a
pattern Other2 s = Free (Inr (Inr s))

liftR :: (Functor sig1, Functor sig2) => Free sig1 a -> Free (sig2 :+: sig1) a
liftR (Pure a) = Pure a
liftR (Free f) = Free $ Inr (liftR <$> f)
