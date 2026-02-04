{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}

module DeltaQ.Sampled
    ( -- * Type
      DQ
    ) where

import Data.Function (on)
import Data.List (groupBy, sortBy, union)
import Data.Maybe (listToMaybe)
import Data.Ord (comparing)
import DeltaQ.Class
    ( DeltaQ (..)
    , Outcome (..)
    , ProbabilisticOutcome (..)
    , eventuallyFromMaybe
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
        cdf = scanl1 (\(_, p') (v, p) -> (v, p' + p)) pmf
    in  Dist{..}

-- Create distribution from CDF
fromCDF :: Ord a => CDF a -> Dist a
fromCDF cdf =
    let pmf = zipWith (\(v, p) p' -> (v, p - p')) cdf (0.0 : map snd cdf)
    in  Dist{..}

-- Quantile function
quantile' :: Rational -> Dist a -> Maybe a
quantile' q Dist{..} = fmap fst $ find (\(_, p) -> p >= q) cdf
  where
    find x = listToMaybe . filter x

-- Convolve two distributions
convolve :: (Ord a, Num a) => Dist a -> Dist a -> Dist a
convolve d1 d2 =
    let products = [(x + y, p1 * p2) | (x, p1) <- pmf d1, (y, p2) <- pmf d2]
        grouped = groupBy ((==) `on` fst) $ sortBy (comparing fst) products
        combined = [(v, sum [p | (_, p) <- g]) | g@((v, _) : _) <- grouped]
    in  fromPMF combined

-- Uniform over a list of values
fromList :: Ord a => [a] -> Dist a
fromList xs =
    let n = length xs
        p = 1.0 / fromIntegral n
        m = [(x, p) | x <- xs]
    in  fromPMF m

-- Uniform over a range with constant step size
uniform' :: Rational -> Rational -> Dist Rational
uniform' a b = fromList [a, (a + stepSize) .. b]
  where
    stepSize = 0.01

-- Evaluate CDF at a specific value: P(X <= x)
cdfAt :: Ord a => a -> Dist a -> Rational
cdfAt x Dist{..} =
    case filter (\(v, _) -> v <= x) cdf of
        [] -> 0.0
        ps -> snd $ last ps -- the cumulative probability at largest value <= x

-- Last to finish: F₁(x)F₂(x)
lastToFinish' :: Ord a => Dist a -> Dist a -> Dist a
lastToFinish' d1 d2 =
    let values = union (map fst (cdf d1)) (map fst (cdf d2))
        cdf' = sortBy (comparing fst) [(v, cdfAt v d1 * cdfAt v d2) | v <- values]
    in  fromCDF cdf'

-- First to finish: 1 - (1 - F₁(x))(1 - F₂(x))
firstToFinish' :: Ord a => Dist a -> Dist a -> Dist a
firstToFinish' d1 d2 =
    let values = union (map fst (cdf d1)) (map fst (cdf d2))
        cdf' =
            sortBy
                (comparing fst)
                [(v, 1 - (1 - cdfAt v d1) * (1 - cdfAt v d2)) | v <- values]
    in  fromCDF cdf'

-- Mixture distribution, dropping values with a probability below the treshold
mixture' :: Ord a => Rational -> Rational -> Dist a -> Dist a -> Dist a
mixture' t w d1 d2
    | w < 0 || w > 1 = error "Weight must be between 0 and 1"
    | otherwise =
        let pmf1' = [(x, w * p) | (x, p) <- pmf d1, w * p >= t]
            pmf2' = [(x, (1 - w) * p) | (x, p) <- pmf d2, (1 - w) * p >= t]
            combined = pmf1' ++ pmf2'
            grouped = groupBy ((==) `on` fst) $ sortBy (comparing fst) combined
            merged = [(v, sum [p | (_, p) <- g]) | g@((v, _) : _) <- grouped]
            total = sum $ map snd merged
            normalized = map (\(v, p) -> (v, p / total)) merged
        in  fromPMF normalized

mixture :: Ord a => Rational -> Dist a -> Dist a -> Dist a
mixture = mixture' threshold
  where
    threshold = 0.01

data DQ = DQ (Dist Rational)
    deriving (Show)

instance Outcome DQ where
    type Duration DQ = Rational

    never = DQ (Dist [] [])

    wait t = DQ (Dist [(t, 1)] [(t, 1)])

    sequentially (DQ a) (DQ b) = DQ $ convolve a b

    firstToFinish (DQ a) (DQ b) = DQ $ firstToFinish' a b

    lastToFinish (DQ a) (DQ b) = DQ $ lastToFinish' a b

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
        eventuallyFromMaybe
            $ quantile' p l

    earliest (DQ (Dist _ l)) =
        eventuallyFromMaybe
            $ fst <$> listToMaybe l

    deadline (DQ (Dist _ l)) =
        eventuallyFromMaybe
            $ fst <$> listToMaybe (reverse l)
