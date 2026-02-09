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
import DeltaQ.Class
    ( DeltaQ (..)
    , Outcome (..)
    , ProbabilisticOutcome (..)
    , eventuallyFromMaybe
    )

-- Max size of a distribution (see also stepSize below)
maxDistributionSize :: Int
maxDistributionSize = 10000

-- A probability distribution
data Dist = Dist
    { values :: !(Vector Double) -- sorted values
    , probabilities :: !(Vector Double) -- corresponding probabilities (PMF)
    , cumulative :: !(Vector Double) -- cumulative probabilities (CDF)
    }
    deriving (Show)

-- Empty is an improper distribution
emptyDist :: Dist
emptyDist = Dist VU.empty VU.empty VU.empty

-- Sorting by values
-- Create distribution from (value, probability) pairs
fromPairs :: Vector (Double, Double) -> Dist
fromPairs pairs
    | VU.null pairs = emptyDist
    | otherwise =
        let sorted = sort pairs
            sampled =
                if VU.length sorted > maxDistributionSize
                    then reduceSize maxDistributionSize sorted
                    else sorted
            normalized = normalize sampled
            values = VU.map fst normalized
            probabilities = VU.map snd normalized
            cumulative = VU.scanl1' (+) probabilities
        in  Dist{..}
  where
    sort vec = runST $ do
        mvec <- VU.thaw vec
        VA.sortBy (\(v1, _) (v2, _) -> compare v1 v2) mvec
        VU.unsafeFreeze mvec

-- Normalize
normalize :: Vector (Double, Double) -> Vector (Double, Double)
normalize values =
    let !total = VU.foldl' (\x (_, y) -> x + y) 0.0 values
    in  VU.map (\(v, p) -> (v, p / total)) values

-- Reduce size of distribution
reduceSize :: Int -> Vector (Double, Double) -> Vector (Double, Double)
reduceSize targetSize v
    | VU.length v <= targetSize = v
    | otherwise = VU.take targetSize (sort v)
  where
    sort vec = runST $ do
        mvec <- VU.thaw vec
        VA.sortBy (\(_, p1) (_, p2) -> compare p2 p1) mvec
        VU.unsafeFreeze mvec

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
    fromPairs
        $ VU.concatMap
            ( \(i, p_i) ->
                VU.map (\(j, p_j) -> (i + j, p_i * p_j)) (VU.zip (values d2) (probabilities d2))
            )
        $ VU.zip (values d1) (probabilities d1)

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
        sampled = reduceSize n pairs
        normalized = normalize sampled
        probs = VU.map snd normalized
    in  Dist
            { values = VU.map fst normalized
            , probabilities = probs
            , cumulative = VU.scanl1' (+) probs
            }

-- Uniform over a range with constant step size
uniform' :: Double -> Double -> Dist
uniform' a b = fromPairs $ VU.generate n (\i -> (a + (fromIntegral i) * stepSize, 1))
  where
    stepSize = 0.01
    n = ceiling $ ((b - a) / stepSize)

-- Get all unique values from both distributions
unionValues :: Dist -> Dist -> Vector Double
unionValues d1 d2 =
    let v1 = VU.toList (values d1)
        v2 = VU.toList (values d2)
    in  VU.fromList $ mergeUnique v1 v2
  where
    mergeUnique [] ys = ys
    mergeUnique xs [] = xs
    mergeUnique (x : xs) (y : ys)
        | x < y = x : mergeUnique xs (y : ys)
        | x > y = y : mergeUnique (x : xs) ys
        | otherwise = x : mergeUnique xs ys

-- Build a distribution from the CDF
fromCDF :: Vector (Double, Double) -> Dist
fromCDF vec | VU.null vec = emptyDist
fromCDF vec
    | otherwise =
        let h = VU.head vec
            r = VU.tail vec
        in  fromPairs $ VU.cons h (VU.zipWith (\(v, p) (_, p') -> (v, p - p')) r vec)

-- Last to finish: F₁(x)F₂(x)
lastToFinish' :: Dist -> Dist -> Dist
lastToFinish' d1 d2 =
    let vals = unionValues d1 d2
        pairs = VU.map (\v -> (v, cdfAt v d1 * cdfAt v d2)) vals
    in  fromCDF pairs

-- First to finish: 1 - (1 - F₁(x))(1 - F₂(x))
firstToFinish' :: Dist -> Dist -> Dist
firstToFinish' d1 d2 =
    let vals = unionValues d1 d2
        pairs = VU.map (\v -> (v, 1 - (1 - cdfAt v d1) * (1 - cdfAt v d2))) vals
    in  fromCDF pairs

-- Mixture distribution
mixture :: Double -> Dist -> Dist -> Dist
mixture w d1 d2
    | w < 0 || w > 1 = error "Weight must be between 0 and 1"
    | otherwise =
        let p1 = VU.map (w *) (probabilities d1)
            p2 = VU.map ((1 - w) *) (probabilities d2)
        in  fromPairs $ (VU.zip (values d1) p1) VU.++ (VU.zip (values d2) p2)

data DQ = DQ Dist
    deriving (Show)

instance Outcome DQ where
    type Duration DQ = Double

    never = DQ emptyDist

    wait t = DQ (Dist (VU.singleton t) (VU.singleton 1.0) (VU.singleton 1.0))

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
