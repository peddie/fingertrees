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

module Data.FingerTree.IntervalTree where

import GHC.Generics (Generic)
import Data.Data (Data)
import Data.Typeable (Typeable)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import Data.Monoid (Monoid(..), (<>))

import Data.FingerTree

data Interval a = Interval { low :: !a
                           , high :: !a
                           }
                deriving (Show, Read, Eq, Ord,
                          Generic, Data, Typeable,
                          Functor, Foldable, Traversable)

dominates a b = high a > high b && low a < low b
intersects a b = not $ high a < low b || low a > high b

-- | The 'maxInterval' part keeps track of the ordering of
-- 'Interval's, sorted by lower bound first.  The 'maxHigh' part keeps
-- track of the upper bound of the 'Interval's contained.  Between the
-- two, we can split by whether intersection is possible on the high
-- end (using 'maxHigh') or the low end (using 'maxInterval').
data Key v = NoKey
           | Key { maxInterval :: !(Interval v)
                 , maxHigh :: !v
                 }
           deriving (Show, Read, Eq, Ord,
                     Generic, Data, Typeable,
                     Functor, Foldable, Traversable)

instance Ord v => Monoid (Key v) where
  mempty = NoKey
  NoKey `mappend` k = k
  k `mappend` NoKey = k
  (Key _ a) `mappend` (Key ib b) = Key ib (max a b)

instance Measured (Interval v) where
  type Measure (Interval v) = Key v
  measure = intervalToKey

instance Ord v => Measured (Interval v, a) where
  type Measure (Interval v, a) = Key v
  measure = intervalToKey . fst

intervalToKey :: Interval v -> Key v
intervalToKey i = Key i (high i)
{-# INLINE intervalToKey #-}

dominates' a b = (fst a) `dominates` (fst b)
intersects' a b = (fst a) `intersects` (fst b)

newtype IntervalTree v a = IntervalTree {
  getIntervalTree :: FingerTree (Key v) (Interval v, a)
  } deriving (Show, Eq, Ord)

insert :: Ord v => IntervalTree v a -> Interval v -> a -> IntervalTree v a
insert (IntervalTree tree) i x = IntervalTree $ leq <> ((i, x) <| gt)
  where
    (leq, gt) = split (> intervalToKey i) tree

insertWith :: Ord v => (a -> Interval v) -> IntervalTree v a -> a -> IntervalTree v a
insertWith f tree x = insert tree (f x) x

atLeast :: Ord v => Interval v -> Key v -> Bool
atLeast v (Key i _) = measure v < measure i

greaterThan v (Key _ mx) = measure v > mx

search :: Ord v => IntervalTree v a -> Interval v -> Maybe a
search (IntervalTree tree) i = searchAtFinger (viewL geq)
  where
    (lt, geq) = split (>= intervalToKey i) tree
    searchAtFinger EmptyL = Nothing
    searchAtFinger (a :< as)
      | ai == i          = Just (snd a)
      | high i < high ai = searchAtFinger (viewL as)
      | otherwise        = Nothing
      where
        ai = fst a
