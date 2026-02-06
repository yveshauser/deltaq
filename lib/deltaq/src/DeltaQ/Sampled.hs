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

import Control.Monad.ST (runST)
import qualified Data.Vector.Algorithms.Intro as VA
import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM
import DeltaQ.Class
    ( DeltaQ (..)
    , Outcome (..)
    , ProbabilisticOutcome (..)
    , eventuallyFromMaybe
    )

-- Maximum number of points to keep in a distribution
maxDistributionSize :: Int
maxDistributionSize = 10000

-- Using unboxed vectors for maximum performance
-- Sorted by value for binary search
data Dist = Dist
    { values :: !(Vector Double) -- sorted values
    , probabilities :: !(Vector Double) -- corresponding probabilities (PMF)
    , cumulative :: !(Vector Double) -- cumulative probabilities (CDF)
    }
    deriving (Show)

emptyDist :: Dist
emptyDist = Dist VU.empty VU.empty VU.empty

-- Create distribution from value-probability pairs with automatic size limiting
fromPairs :: [(Double, Double)] -> Dist
fromPairs pairs
    | null pairs = emptyDist
    | otherwise =
        let sorted = sort pairs
            final =
                if VU.length sorted > maxDistributionSize
                    then coalesceToSize maxDistributionSize sorted
                    else sorted
            values = VU.map fst final
            probabilities = VU.map snd final
            cumulative = VU.scanl1' (+) probabilities
        in  Dist{..}
  where
    sort :: [(Double, Double)] -> Vector (Double, Double)
    sort xs = runST $ do
        let vec = VU.fromList xs
        mvec <- VU.thaw vec
        VA.sortBy (\(v1, _) (v2, _) -> compare v1 v2) mvec
        sorted <- VU.unsafeFreeze mvec
        return sorted

-- Coalesce distribution to target size by merging nearby points
-- Uses adaptive binning based on probability density
coalesceToSize :: Int -> Vector (Double, Double) -> Vector (Double, Double)
coalesceToSize targetSize vec
    | VU.length vec <= targetSize = vec
    | targetSize <= 0 = VU.empty
    | otherwise = runST $ do
        -- Calculate how many points to merge into each bin
        let n = VU.length vec
            binSize = (n + targetSize - 1) `div` targetSize

        -- Create result vector
        result <- VUM.new targetSize

        -- Merge points into bins
        let fillBins !outIdx !inIdx
                | outIdx >= targetSize = return outIdx
                | inIdx >= n = return outIdx
                | otherwise = do
                    let endIdx = min n (inIdx + binSize)
                        binPoints = VU.slice inIdx (endIdx - inIdx) vec
                        merged = mergeBin binPoints
                    VUM.write result outIdx merged
                    fillBins (outIdx + 1) endIdx

        finalSize <- fillBins 0 0
        VU.unsafeFreeze (VUM.take finalSize result)
  where
    mergeBin :: Vector (Double, Double) -> (Double, Double)
    mergeBin bin =
        let !totalProb = VU.sum (VU.map snd bin)
            !weightedSum = VU.sum (VU.zipWith (\(v, p) _ -> v * p) bin bin)
            !avgValue = weightedSum / totalProb
        in  (avgValue, totalProb)

-- Keep high probability values
importanceSample :: Int -> Vector (Double, Double) -> Vector (Double, Double)
importanceSample targetSize vec
    | VU.length vec <= targetSize = vec
    | otherwise =
        let sorted = runST $ do
                mvec <- VU.thaw vec
                VA.sortBy (\(_, p1) (_, p2) -> compare p2 p1) mvec
                VU.unsafeFreeze mvec
            (important, _) = VU.foldl' takeUntilThreshold (VU.empty, 0.0) sorted
        in  if VU.length important > targetSize
                then VU.take targetSize important
                else important
  where
    threshold = 0.95
    takeUntilThreshold (acc, !cumProb) point@(_, p)
        | cumProb >= threshold = (acc, cumProb)
        | otherwise = (VU.snoc acc point, cumProb + p)

-- Binary search for index where value <= x
binarySearchLE :: Double -> Vector Double -> Maybe Int
binarySearchLE x vec
    | VU.null vec = Nothing
    | otherwise = go 0 (VU.length vec - 1)
  where
    go !lo !hi
        | lo > hi = if lo == 0 then Nothing else Just (lo - 1)
        | otherwise =
            let !mid = (lo + hi) `div` 2
                !midVal = VU.unsafeIndex vec mid
            in  if midVal <= x
                    then
                        if mid == VU.length vec - 1 || VU.unsafeIndex vec (mid + 1) > x
                            then Just mid
                            else go (mid + 1) hi
                    else go lo (mid - 1)

-- Evaluate CDF at a specific value: P(X <= x)
cdfAt :: Double -> Dist -> Double
cdfAt x Dist{..} =
    case binarySearchLE x values of
        Nothing -> 0.0
        Just idx -> VU.unsafeIndex cumulative idx

-- Quantile function
quantile' :: Double -> Dist -> Maybe Double
quantile' q Dist{..} =
    case VU.findIndex (>= q) cumulative of
        Nothing -> Nothing
        Just idx -> Just (VU.unsafeIndex values idx)

-- Convolve two distributions
convolve :: Dist -> Dist -> Dist
convolve d1 d2 =
    let n1 = VU.length (values d1)
        n2 = VU.length (values d2)
        totalPoints = n1 * n2
    in  if totalPoints <= maxDistributionSize
            then convolveExact d1 d2
            else convolveSampled d1 d2

-- Exact convolution
convolveExact :: Dist -> Dist -> Dist
convolveExact d1 d2 =
    let products =
            [ ( VU.unsafeIndex (values d1) i + VU.unsafeIndex (values d2) j
              , VU.unsafeIndex (probabilities d1) i * VU.unsafeIndex (probabilities d2) j
              )
            | i <- [0 .. VU.length (values d1) - 1]
            , j <- [0 .. VU.length (values d2) - 1]
            ]
    in  fromPairs products

-- Sampled convolution
convolveSampled :: Dist -> Dist -> Dist
convolveSampled d1 d2 =
    let n1 = VU.length (values d1)
        n2 = VU.length (values d2)
        sampleSize = floor (sqrt (fromIntegral maxDistributionSize :: Double))
        sampled1 = if n1 > sampleSize then sampleDist sampleSize d1 else d1
        sampled2 = if n2 > sampleSize then sampleDist sampleSize d2 else d2
    in  convolveExact sampled1 sampled2

-- Sample distribution
sampleDist :: Int -> Dist -> Dist
sampleDist n Dist{..} =
    let pairs = VU.zip values probabilities
        sampled = importanceSample n pairs
        probs = VU.map snd sampled
        total = VU.sum probs
        normalized = VU.map (/ total) probs
    in  Dist
            { values = VU.map fst sampled
            , probabilities = normalized
            , cumulative = VU.scanl1' (+) normalized
            }

-- Uniform over a list of values
fromList :: [Double] -> Dist
fromList xs =
    let !n = length xs
        !p = 1.0 / fromIntegral n
    in  fromPairs [(x, p) | x <- xs]

-- Uniform over a range with constant step size
uniform' :: Double -> Double -> Dist
uniform' a b = fromList [a, (a + stepSize) .. b]
  where
    stepSize = 0.01

-- Get all unique values from both distributions (sampled if too large)
unionValues :: Dist -> Dist -> [Double]
unionValues d1 d2 =
    let v1 = VU.toList (values d1)
        v2 = VU.toList (values d2)
    in  mergeUnique v1 v2
  where
    mergeUnique [] ys = ys
    mergeUnique xs [] = xs
    mergeUnique (x : xs) (y : ys)
        | x < y = x : mergeUnique xs (y : ys)
        | x > y = y : mergeUnique (x : xs) ys
        | otherwise = x : mergeUnique xs ys

-- Build a distribution from the CDF
fromCDF :: [(Double, Double)] -> Dist
fromCDF [] = emptyDist
fromCDF pairs@((v0, p0) : rest) =
    let pmfPairs = (v0, p0) : zipWith (\(v, p) (_, p') -> (v, p - p')) rest pairs
    in  fromPairs pmfPairs

-- Last to finish: F₁(x)F₂(x)
lastToFinish' :: Dist -> Dist -> Dist
lastToFinish' d1 d2 =
    let vals = unionValues d1 d2
        pairs = [(v, cdfAt v d1 * cdfAt v d2) | v <- vals]
    in  fromCDF pairs

-- First to finish: 1 - (1 - F₁(x))(1 - F₂(x))
firstToFinish' :: Dist -> Dist -> Dist
firstToFinish' d1 d2 =
    let vals = unionValues d1 d2
        pairs = [(v, 1 - (1 - cdfAt v d1) * (1 - cdfAt v d2)) | v <- vals]
    in  fromCDF pairs

-- Mixture distribution
mixture :: Double -> Dist -> Dist -> Dist
mixture w d1 d2
    | w < 0 || w > 1 = error "Weight must be between 0 and 1"
    | otherwise =
        let n1 = VU.length (values d1)
            n2 = VU.length (values d2)
            pairs1 =
                [ (VU.unsafeIndex (values d1) i, w * VU.unsafeIndex (probabilities d1) i)
                | i <- [0 .. n1 - 1]
                ]
            pairs2 =
                [ (VU.unsafeIndex (values d2) i, (1 - w) * VU.unsafeIndex (probabilities d2) i)
                | i <- [0 .. n2 - 1]
                ]
        in  fromPairs (pairs1 ++ pairs2)

data DQ = DQ Dist
    deriving (Show)

instance Outcome DQ where
    type Duration DQ = Double

    never = DQ emptyDist

    wait t = DQ (fromPairs [(t, 1.0)])

    sequentially (DQ a) (DQ b) = DQ $ convolve a b

    firstToFinish (DQ a) (DQ b) = DQ $ firstToFinish' a b

    lastToFinish (DQ a) (DQ b) = DQ $ lastToFinish' a b

instance ProbabilisticOutcome DQ where
    type Probability DQ = Double

    choice p (DQ a) (DQ b) = DQ $ mixture p a b

instance DeltaQ DQ where
    uniform a b = DQ $ uniform' a b

    successWithin (DQ l) d = cdfAt d l

    failure (DQ (Dist _ _ cum)) =
        if VU.null cum
            then 1.0
            else 1.0 - VU.last cum

    quantile (DQ l) p =
        eventuallyFromMaybe
            $ quantile' p l

    earliest (DQ (Dist vals _ _)) =
        eventuallyFromMaybe
            $ if VU.null vals then Nothing else Just (VU.head vals)

    deadline (DQ (Dist vals _ _)) =
        eventuallyFromMaybe
            $ if VU.null vals then Nothing else Just (VU.last vals)
