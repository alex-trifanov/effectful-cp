{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
module Effects.NonDet (fail, pattern (:|:), try, NonDet(..), pattern Fail) where 
import Control.Monad.Free (Free(..))
import Effects.Core (Sub, project, inject)
import Prelude hiding (fail)
import Effects.Algebra (handle)
  
data NonDet a where
  Try'  :: a -> a -> NonDet a
  Fail' :: NonDet a
  deriving Functor

instance Foldable NonDet where 
  foldMap :: Monoid m => (a -> m) -> NonDet a -> m
  foldMap f (Try' l r) = f l <> f r
  foldMap _ Fail' = mempty

instance Traversable NonDet where 
  traverse :: Applicative f => (a -> f b) -> NonDet a -> f (NonDet b)
  traverse f (Try' l r) = (Try' <$> f l) <*> f r
  traverse _ Fail' = pure Fail'

pattern Fail :: Sub NonDet sup => Free sup a
pattern Fail <- (project -> Just Fail')
fail :: (NonDet `Sub` sig) => Free sig a 
fail = inject Fail'

pattern (:|:) :: Sub NonDet sup => Free sup a -> Free sup a -> Free sup a
pattern p :|: q <- (project -> Just (Try' p q))
try :: (NonDet `Sub` sig) => Free sig a -> Free sig a -> Free sig a 
try p q = inject (Try' p q)

data Coin = Heads | Tails deriving Show 
flip :: Free NonDet Coin 
flip = Free (Try' (Pure Heads) (Pure Tails))

allLeaves :: Free NonDet a -> [a]
allLeaves = handle alg (\a -> [a])
  where 
    alg Fail' = []
    alg (Try' l r) = l ++ r

flip' :: (NonDet `Sub` sig) => Free sig Coin 
flip' = try (Pure Heads) (Pure Tails)
