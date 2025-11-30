
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# LANGUAGE TransformListComp #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Queens where 
import Prelude hiding (fail)
import Data.List (tails)
import FD.OvertonFD as OvertonFD
import FD.Domain as Domain
import GHC.Exts (sortWith)
import Effects.Core ((:+:), Void, Sub)
import Effects.CPOps (exist, in_domain, (@\=), (@\==), (@+), (@=))
import Effects.Solver (dynamic)
import Control.Monad.Free (Free)
import Effects.NonDet (try, fail, NonDet)
import Eval (CSP)

nqueens :: Int -> CSP [Int]
nqueens n = exist n $ \queens -> model queens n /\ enumerate queens /\ assignments queens

model :: [FDVar] -> Int -> CSP ()
model queens n = queens `allin` (1,n) /\ alldifferent queens /\ diagonals queens

allin :: [FDVar] -> (Int, Int) -> CSP ()
allin queens range = conj [q `in_domain` range | q <- queens]

alldifferent :: [FDVar] -> CSP ()
alldifferent queens = conj [qi @\= qj | qi : qjs <- tails queens, qj <- qjs]

diagonals :: [FDVar] -> CSP ()
diagonals queens = conj [ (qi @\== (qj @+ d)) /\ (qj @\== (qi @+ d)) | qi : qjs <- tails queens, (qj, d) <- zip qjs [1..]]
-- enumerate queens values = conj [ enum queen values | queen <- queens]

enum :: FDVar -> [Int] -> CSP ()
enum var values = disj [ var @= value | value <- values ]

(\/) :: (NonDet `Sub` sig) => Free sig a -> Free sig a -> Free sig a
(\/) = try
infixl 2 \/

(/\) :: (NonDet `Sub` sig) => Free sig a -> Free sig b -> Free sig b
(/\) = (>>)
infixl 3 /\

false :: (NonDet `Sub` sig) => Free sig a
false = fail

true :: (Functor sig) => Free sig ()
true = pure ()

disj :: (NonDet `Sub` sig) => [Free sig a] -> Free sig a
disj = foldl (\/) false

conj :: (NonDet `Sub` sig) => [Free sig ()] -> Free sig ()
conj = foldl (/\) true


-- -----------------------| Labelling |------------------------

enumerate vs = label firstfail id vs

label :: ([FDVar] -> OvertonFD [FDVar]) -> ([Int] -> [Int]) ->
  [FDVar] -> CSP ()
label varsel valsel vs = do
  vs' <- dynamic $ varsel vs
  label' vs'
  where
    label' [] = pure $ ()
    label' (v:vs) = do
      -- d <- valsel $ Domain.elems $ OvertonFD.lookup v
      d <- dynamic $ fd_domain v
      let d' = valsel d
      enum v d' /\ (label varsel valsel vs)

firstfail :: [FDVar] -> OvertonFD [FDVar]
firstfail vs = do
  ds <- mapM OvertonFD.lookup vs
  return [v | (d,v) <- zip ds vs, then sortWith by Domain.size d]

middleout :: [a] -> [a]
middleout l = let n = length l `div` 2 in
  interleave (drop n l) (reverse $ take n l)

interleave :: [a] -> [a] -> [a]
interleave [] ys = ys
interleave (x:xs) ys = x:interleave ys xs

-- ----------------------| Assignment |----------------------

assignments :: [FDVar] -> CSP [Int]
assignments = mapM assignment 
assignment q = dynamic $ do 
  d <- fd_domain q
  let v = head d
  pure v

-- ----------------------| Knapsack |------------------------

knapsack :: Int -> [Int] -> Free (NonDet :+: Void) [Int]
knapsack w vs
  | w < 0  = fail
  | w == 0 = pure []
  | otherwise  = do
    v <- select vs
    vs' <- knapsack (w-v) vs
    pure (v:vs')
  where
    select = foldr (try . pure) fail
