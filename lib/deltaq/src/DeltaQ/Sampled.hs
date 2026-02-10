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
import Data.Vector (Vector)
import qualified Data.Vector as V
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
    { values :: !(Vector Rational) -- sorted values
    , probabilities :: !(Vector Rational) -- corresponding probabilities (PMF)
    , cumulative :: !(Vector Rational) -- cumulative probabilities (CDF)
    }
    deriving (Eq)

instance Show Dist where
  show Dist {..} = "Dist"

-- Empty is an improper distribution
emptyDist :: Dist
emptyDist = Dist V.empty V.empty V.empty

-- Create distribution from (value, probability) pairs
fromPairs :: Vector (Rational, Rational) -> Dist
fromPairs pairs
    | V.null pairs = emptyDist
    | otherwise =
        let sorted = sort pairs
            sampled =
                if V.length sorted > maxDistributionSize
                    then reduceSize maxDistributionSize sorted
                    else sorted
            normalized = normalize sampled
            values = V.map fst normalized
            probabilities = V.map snd normalized
            cumulative = V.scanl1' (+) probabilities
        in  Dist{..}
  where
    sort vec = runST $ do
        mvec <- V.thaw vec
        VA.sortBy (\(v1, _) (v2, _) -> compare v1 v2) mvec
        V.unsafeFreeze mvec

-- Normalize
normalize :: Vector (Rational, Rational) -> Vector (Rational, Rational)
normalize values =
    let !total = V.foldl' (\x (_, y) -> x + y) 0.0 values
    in  V.map (\(v, p) -> (v, p / total)) values

-- Reduce size of distribution
reduceSize :: Int -> Vector (Rational, Rational) -> Vector (Rational, Rational)
reduceSize targetSize v
    | V.length v <= targetSize = v
    | otherwise = V.take targetSize (sort v)
  where
    sort vec = runST $ do
        mvec <- V.thaw vec
        VA.sortBy (\(_, p1) (_, p2) -> compare p2 p1) mvec
        V.unsafeFreeze mvec

-- Binary search for index where value <= x
binarySearchLE :: Rational -> Vector Rational -> Maybe Int
binarySearchLE x vec
    | V.null vec = Nothing
    | otherwise = go 0 (V.length vec - 1)
  where
    go !lo !hi
        | lo > hi = if lo == 0 then Nothing else Just (lo - 1)
        | otherwise =
            let !mid = (lo + hi) `div` 2
                !midVal = V.unsafeIndex vec mid
            in  if midVal <= x
                    then
                        if mid == V.length vec - 1 || V.unsafeIndex vec (mid + 1) > x
                            then Just mid
                            else go (mid + 1) hi
                    else go lo (mid - 1)

-- Evaluate CDF at a specific value: P(X <= x)
cdfAt :: Rational -> Dist -> Rational
cdfAt x Dist{..} =
    case binarySearchLE x values of
        Nothing -> 0.0
        Just idx -> V.unsafeIndex cumulative idx

-- Quantile function
quantile' :: Rational -> Dist -> Maybe Rational
quantile' q Dist{..} =
    case V.findIndex (>= q) cumulative of
        Nothing -> Nothing
        Just idx -> Just (V.unsafeIndex values idx)

-- Convolve two distributions
convolve :: Dist -> Dist -> Dist
convolve d1 d2 =
    let n1 = V.length (values d1)
        n2 = V.length (values d2)
        totalPoints = n1 * n2
    in  if totalPoints == 0 then emptyDist
        else if totalPoints <= maxDistributionSize then convolveExact d1 d2
        else convolveSampled d1 d2

-- Exact convolution
convolveExact :: Dist -> Dist -> Dist
convolveExact d1 d2 =
    fromPairs
        $ V.concatMap
            ( \(i, p_i) ->
                V.map (\(j, p_j) -> (i + j, p_i * p_j)) (V.zip (values d2) (probabilities d2))
            )
        $ V.zip (values d1) (probabilities d1)

-- Sampled convolution
convolveSampled :: Dist -> Dist -> Dist
convolveSampled d1 d2 =
    let n1 = V.length (values d1)
        n2 = V.length (values d2)
        sampleSize = floor (sqrt (fromIntegral maxDistributionSize) :: Double)
        sampled1 = if n1 > sampleSize then sampleDist sampleSize d1 else d1
        sampled2 = if n2 > sampleSize then sampleDist sampleSize d2 else d2
    in  convolveExact sampled1 sampled2

-- Sample distribution
sampleDist :: Int -> Dist -> Dist
sampleDist n Dist{..} =
    let pairs = V.zip values probabilities
        sampled = reduceSize n pairs
        normalized = normalize sampled
        probs = V.map snd normalized
    in  Dist
            { values = V.map fst normalized
            , probabilities = probs
            , cumulative = V.scanl1' (+) probs
            }

-- Uniform over a range with constant step size
uniform' :: Rational -> Rational -> Dist
uniform' a b | a >= b = emptyDist
uniform' a b | otherwise = fromPairs $ 
  V.generate n (\i -> (a + (fromIntegral i) * stepSize, 1))
  where
    n = 100
    stepSize = (b - a) / fromIntegral n

-- Get all unique values from both distributions
unionValues :: Dist -> Dist -> Vector Rational
unionValues d1 d2 =
    let v1 = V.toList (values d1)
        v2 = V.toList (values d2)
    in  V.fromList $ mergeUnique v1 v2
  where
    mergeUnique [] ys = ys
    mergeUnique xs [] = xs
    mergeUnique (x : xs) (y : ys)
        | x < y = x : mergeUnique xs (y : ys)
        | x > y = y : mergeUnique (x : xs) ys
        | otherwise = x : mergeUnique xs ys

-- Build a distribution from the CDF
fromCDF :: Vector (Rational, Rational) -> Dist
fromCDF vec | V.null vec = emptyDist
fromCDF vec
    | otherwise =
        let h = V.head vec
            r = V.tail vec
        in  fromPairs $ V.cons h (V.zipWith (\(v, p) (_, p') -> (v, p - p')) r vec)

-- Last to finish: F₁(x)F₂(x)
lastToFinish' :: Dist -> Dist -> Dist
lastToFinish' d1 d2 =
    let vals = unionValues d1 d2
        pairs = V.map (\v -> (v, cdfAt v d1 * cdfAt v d2)) vals
    in  fromCDF pairs

-- First to finish: 1 - (1 - F₁(x))(1 - F₂(x))
firstToFinish' :: Dist -> Dist -> Dist
firstToFinish' d1 d2 =
    let vals = unionValues d1 d2
        pairs = V.map (\v -> (v, 1 - (1 - cdfAt v d1) * (1 - cdfAt v d2))) vals
    in  fromCDF pairs

-- Mixture distribution
mixture :: Rational -> Dist -> Dist -> Dist
mixture w d1 d2
    | w < 0 || w > 1 = error "Weight must be between 0 and 1"
    | otherwise =
        let p1 = V.map (w *) (probabilities d1)
            p2 = V.map ((1 - w) *) (probabilities d2)
        in  fromPairs $ (V.zip (values d1) p1) V.++ (V.zip (values d2) p2)

data DQ = DQ Dist
    deriving (Eq, Show)

instance Outcome DQ where
    type Duration DQ = Rational

    never = DQ emptyDist

    wait t = DQ (Dist (V.singleton t) (V.singleton 1.0) (V.singleton 1.0))

    sequentially (DQ a) (DQ b) = DQ $ convolve a b

    firstToFinish (DQ a) (DQ b) = DQ $ firstToFinish' a b

    lastToFinish (DQ a) (DQ b) = DQ $ lastToFinish' a b

instance ProbabilisticOutcome DQ where
    type Probability DQ = Rational

    choice p (DQ a) (DQ b) = DQ $ mixture p a b

instance DeltaQ DQ where
    uniform a b = DQ $ uniform' a b

    successWithin (DQ l) d = cdfAt d l

    failure (DQ (Dist _ _ cum)) =
        if V.null cum
            then 1.0
            else 1.0 - V.last cum

    quantile (DQ l) p =
        eventuallyFromMaybe
            $ quantile' p l

    earliest (DQ (Dist vals _ _)) =
        eventuallyFromMaybe
            $ if V.null vals then Nothing else Just (V.head vals)

    deadline (DQ (Dist vals _ _)) =
        eventuallyFromMaybe
            $ if V.null vals then Nothing else Just (V.last vals)
