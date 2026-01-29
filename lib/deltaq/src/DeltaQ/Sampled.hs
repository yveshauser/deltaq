{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}

module DeltaQ.Sampled (
  -- * Type
  DQ
) where

import Data.Function (on)
import Data.List (groupBy, sortBy)
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)
import Data.Ord (comparing)
import DeltaQ.Class (
  DeltaQ (..),
  Eventually (..),
  Outcome (..),
  ProbabilisticOutcome (..),
 )

type PMF a = [(a, Rational)] -- (value, probability)
type CDF a = [(a, Rational)] -- (value, cumulative probability)

-- Probability distribution, PMF & CDF
data Dist a = Dist
  { pmf :: !(PMF a)
  , cdf :: !(CDF a)
  }
  deriving (Show)

-- Create distribution from PMF
fromPMF :: Ord a => PMF a -> Dist a
fromPMF f =
  let pmf = sortBy (comparing fst) f
      cdf = scanl1 (\(_, cp) (v, p) -> (v, cp + p)) pmf
   in Dist{..}

-- Quantile function
quantile' :: Rational -> Dist a -> Maybe a
quantile' p Dist{..} = fmap fst $ find (\(_, cp) -> cp >= p) cdf
 where
  find x = listToMaybe . filter x

-- Convolve two distributions
convolve :: (Ord a, Num a) => Dist a -> Dist a -> Dist a
convolve d1 d2 =
  let products = [(x + y, p1 * p2) | (x, p1) <- pmf d1, (y, p2) <- pmf d2]
      grouped = groupBy ((==) `on` fst) $ sortBy (comparing fst) products
      combined = [(v, sum [p | (_, p) <- grp]) | grp@((v, _) : _) <- grouped]
   in fromPMF combined

-- Uniform over a list of values
fromList :: Ord a => [a] -> Dist a
fromList xs =
  let n = length xs
      p = 1.0 / fromIntegral n
      m = [(x, p) | x <- xs]
   in fromPMF m

-- Uniform over a range (for Enum types like Int)
uniform' :: Rational -> Rational -> Dist Rational
uniform' a b = fromList [a, (a + 0.01) .. b]

-- Evaluate CDF at a specific value: P(X <= x)
cdfAt :: Ord a => a -> Dist a -> Rational
cdfAt x Dist{..} =
  case filter (\(v, _) -> v <= x) cdf of
    [] -> 0.0
    ps -> snd $ last ps -- take the cumulative probability at largest value <= x

maxCDF :: Ord a => Dist a -> Dist a -> Dist a
maxCDF d1 d2 =
  let values = Map.keys $ Map.union (Map.fromList $ cdf d1) (Map.fromList $ cdf d2)
      cdf' = sortBy (comparing fst) [(x, cdfAt x d1 * cdfAt x d2) | x <- values]
      pmf' = zipWith (\(v, cp) prev_cp -> (v, cp - prev_cp)) cdf' (0.0 : map snd cdf')
   in fromPMF pmf'

-- For minimum instead: 1 - (1 - F₁(x))(1 - F₂(x))
minCDF :: Ord a => Dist a -> Dist a -> Dist a
minCDF d1 d2 =
  let values = Map.keys $ Map.union (Map.fromList $ cdf d1) (Map.fromList $ cdf d2)
      cdf' = sortBy (comparing fst) [(x, 1 - (1 - cdfAt x d1) * (1 - cdfAt x d2)) | x <- values]
      pmf' = zipWith (\(v, cp) prev_cp -> (v, cp - prev_cp)) cdf' (0.0 : map snd cdf')
   in fromPMF pmf'

mixture' :: Ord a => Rational -> Rational -> Dist a -> Dist a -> Dist a
mixture' threshold w d1 d2
  | w < 0 || w > 1 = error "Weight must be between 0 and 1"
  | otherwise =
      let
        map1 = Map.fromList [(x, w * p) | (x, p) <- pmf d1, w * p >= threshold]
        resultMap =
          foldl'
            ( \m (x, p) ->
                let !prob = (1 - w) * p
                 in if prob >= threshold
                      then Map.insertWith (+) x prob m
                      else m
            )
            map1
            (pmf d2)
        total = Map.foldl' (+) 0 resultMap
        normalized = Map.map (/ total) resultMap
       in
        fromPMF (Map.toList normalized)

mixture :: Ord a => Rational -> Dist a -> Dist a -> Dist a
mixture = mixture' 0.01

data DQ = DQ (Dist Rational)
  deriving (Show)

instance Outcome DQ where
  type Duration DQ = Rational

  never = DQ (Dist [] [])

  wait t = DQ (Dist [(t, 1)] [(t, 1)])

  sequentially (DQ a) (DQ b) = DQ $ convolve a b

  firstToFinish (DQ a) (DQ b) = DQ $ minCDF a b

  lastToFinish (DQ a) (DQ b) = DQ $ maxCDF a b

instance ProbabilisticOutcome DQ where
  type Probability DQ = Rational

  choice p (DQ a) (DQ b) = DQ $ mixture p a b

instance DeltaQ DQ where
  uniform a b = DQ $ uniform' a b

  successWithin (DQ l) d = cdfAt d l

  failure (DQ (Dist _ l)) =
    case reverse l of
      ((_, p) : _) -> 1.0 - p
      [] -> 1.0

  quantile (DQ l) p =
    case quantile' p l of
      Just q -> Occurs q
      Nothing -> Abandoned

  earliest (DQ (Dist _ l)) =
    case l of
      ((a, _) : _) -> Occurs a
      [] -> Abandoned

  deadline (DQ (Dist _ l)) =
    case reverse l of
      ((a, _) : _) -> Occurs a
      [] -> Abandoned
