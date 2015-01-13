{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module Data.Interval (
  -- * Intervals
  -- * Creating intervals
  Interval(..)
  , interval
  , unsafeInterval
  , asInterval
  , point
    -- * Working with intervals
  , intersects
  , overlaps
  , dominates
  , contains
  , disjoins
  , intersection
  , union
  , span
  , gapBetween
  , isPoint
    -- * Interval arithmetic
    --
    -- There is no 'Num' instance provided, because it would be a bit
    -- incomplete.
  , extent
  , add
  , subtr
  , multiply
  , divide
  , neg
  ) where

import Prelude hiding (span)

import GHC.Generics (Generic)
import Data.Data (Data)
import Data.Typeable (Typeable)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Control.DeepSeq.Generics

import Test.QuickCheck

data Interval a = Interval { low :: !a
                           , high :: !a
                           }
                deriving (Show, Read, Eq, Ord,
                          Generic, Data, Typeable,
                          Functor, Foldable, Traversable)

instance (Ord a, Arbitrary a) => Arbitrary (Interval a) where
  arbitrary = do
    lo <- arbitrary
    hi <- arbitrary `suchThat` (>= lo)
    return $ Interval lo hi

instance NFData a => NFData (Interval a) where rnf = genericRnf

-- |
--
-- >>> interval 22 33
-- Just (Interval {low = 22, high = 33})
--
-- >>> interval 33 22
-- Nothing
interval :: Ord a => a -> a -> Maybe (Interval a)
interval a b
  | b >= a    = Just (Interval a b)
  | otherwise = Nothing

-- |
--
-- >>> point 22
-- Interval {low = 22, high = 22}
point :: a -> Interval a
point x = Interval x x

isPoint :: Eq a => Interval a -> Bool
isPoint (Interval a b) = a == b

-- |
--
-- >>> unsafeInterval 22 33
-- Interval {low = 22, high = 33}
--
-- >>> unsafeInterval 33 22
-- *** Exception: Data.FingerTree.IntervalTree.unsafeInterval: invalid interval (a > b)
unsafeInterval :: Ord a => a -> a -> Interval a
unsafeInterval a b
  | b >= a = Interval a b
  | otherwise = error "Data.FingerTree.IntervalTree.unsafeInterval: invalid interval (a > b)"

-- |
--
-- >>> asInterval 22 33
-- Interval {low = 22, high = 33}
--
-- >>> asInterval 33 22
-- Interval {low = 22, high = 33}
asInterval :: Ord a => a -> a -> Interval a
asInterval a b
  | a > b     = Interval b a
  | otherwise = Interval a b


-- | An interval dominates another if it strictly contains it: the
-- dominator's bounds must be smaller and larger than those of the
-- dominatee, respectively.
--
-- >>> Interval 10 20 `dominates` Interval 12 18
-- True
--
-- >>> Interval 12 18 `dominates` Interval 10 20
-- False
--
-- prop> not (a `dominates` a)
dominates :: Ord v => Interval v -> Interval v -> Bool
dominates a b = high a > high b && low a < low b

-- |
--
-- >>> Interval 10 20 `contains` Interval 12 18
-- True
--
-- >>> Interval 10 20 `contains` Interval 10 20
-- True
--
-- >>> Interval 10 20 `contains` Interval 8 22
-- False
--
-- prop> a `contains` a
-- prop> a `dominates` b ==> a `contains` b
contains :: Ord v => Interval v -> Interval v -> Bool
contains a b = high a >= high b && low a <= low b

-- | An interval intersects another if there is any overlap, including
-- at the bounaries.
--
-- >>> Interval 10 20 `intersects` Interval 15 25
-- True
--
-- >>> Interval 15 20 `intersects` Interval 10 15
-- True
--
-- >>> Interval 10 20 `intersects` Interval 30 40
-- False
--
-- prop> a `intersects` b ==> b `intersects` a
intersects :: Ord v => Interval v -> Interval v -> Bool
intersects a b = not $ high a < low b || low a > high b

-- | An interval overlaps another only if there is overlap beyond
-- identical boundaries.
--
-- >>> Interval 10 20 `overlaps` Interval 15 25
-- True
--
-- >>> Interval 15 20 `overlaps` Interval 10 15
-- False
--
-- >>> Interval 10 20 `overlaps` Interval 30 40
-- False
--
-- prop> a `overlaps` b ==> b `overlaps` a
overlaps :: Ord v => Interval v -> Interval v -> Bool
overlaps a b = not $ high a <= low b || low a >= high b

-- | The inverse of overlap.
disjoins :: Ord v => Interval v -> Interval v -> Bool
disjoins a b = not $ a `intersects` b

intersection :: Ord v => Interval v -> Interval v -> Maybe (Interval v)
intersection a b
  | a `disjoins` b = Nothing
  | otherwise = Just $ Interval (max (low b) (low a)) (min (high b) (high a))

union :: Ord v => Interval v -> Interval v -> Maybe (Interval v)
union a b
  | a `disjoins` b = Nothing
  | otherwise = Just $ span a b

span :: Ord v => Interval v -> Interval v -> Interval v
span a b = Interval (min (low b) (low a)) (max (high b) (high a))

gapBetween :: Ord v => Interval v -> Interval v -> Maybe (Interval v)
gapBetween a b
  | a `intersects` b = Nothing
  | high a < low b   = Just (Interval (high a) (low b))
  | high b < low a   = Just (Interval (high b) (low a))
  | otherwise = error "Data.FingerTree.IntervalTree: 'gapBetween' hit a nonsensical case!"

extent :: Num a => Interval a -> a
extent (Interval l h) = h - l

add :: Num a => Interval a -> Interval a -> Interval a
add (Interval la ha) (Interval lb hb) = Interval (la + lb) (ha + hb)

subtr :: Num a => Interval a -> Interval a -> Interval a
subtr (Interval la ha) (Interval lb hb) = Interval (la - hb) (ha - lb)

multiply :: (Ord a, Num a) => Interval a -> Interval a -> Interval a
multiply (Interval la ha) (Interval lb hb) = Interval (minimum options) (maximum options)
  where
    options = [la * lb, la * hb, ha * lb, ha * hb]

divide :: (Ord a, Fractional a) => Interval a -> Interval a -> Interval a
divide (Interval _ _) (Interval _ 0) = error "Data.Interval.divide: divide by 0!"
divide (Interval _ _) (Interval 0 _) = error "Data.Interval.divide: divide by 0!"
divide (Interval la ha) (Interval lb hb) = Interval (minimum options) (maximum options)
  where
    options = [la / lb, la / hb, ha / lb, ha / hb]

neg :: Num a => Interval a -> Interval a
neg (Interval l h) = Interval (negate h) (negate l)
