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

import Data.FingerTree as FT

import Test.QuickCheck

data Interval a = Interval { low :: a
                           , high :: a
                           }
                deriving (Show, Read, Eq, Ord,
                          Generic, Data, Typeable,
                          Functor, Foldable, Traversable)

instance (Ord a, Arbitrary a) => Arbitrary (Interval a) where
  arbitrary = do
    lo <- arbitrary
    hi <- arbitrary `suchThat` (>= lo)
    return $ Interval lo hi

-- |
--
-- >>> Interval 10 20 `dominates` Interval 12 18
-- True
--
-- >>> Interval 12 18 `dominates` Interval 10 20
-- False
--
-- prop> a `dominates` b && b `dominates` a ==> b == a
dominates :: Ord v => Interval v -> Interval v -> Bool
dominates a b = high a > high b && low a < low b

-- |
-- >>> Interval 10 20 `intersects` Interval 15 25
-- True
--
-- >>> Interval 10 20 `intersects` Interval 30 40
-- False
--
-- prop> a `intersects` b ==> b `intersects` a
intersects :: Ord v => Interval v -> Interval v -> Bool
intersects a b = not $ high a < low b || low a > high b

-- | The 'maxInterval' part keeps track of the ordering of
-- 'Interval's, sorted by lower bound first.  The 'maxHigh' part keeps
-- track of the upper bound of the 'Interval's contained.  Between the
-- two, we can split by whether intersection is possible on the high
-- end (using 'maxHigh') or the low end (using 'maxInterval').
data Key v = NoKey
           | Key { maxInterval :: (Interval v)
                 , maxHigh :: v
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
  measure = measure . fst

intervalToKey :: Interval v -> Key v
intervalToKey i = Key i (high i)

dominates', intersects' :: Ord v => (Interval v, a) -> (Interval v, b) -> Bool
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

atLeast :: Ord v => Key v -> v -> Bool
atLeast NoKey      _ = False
atLeast (Key _ mx) v = mx >= v

greaterThan :: Ord v => Key v -> v -> Bool
greaterThan NoKey     _ = False
greaterThan (Key i _) v = low i > v

atMost :: Ord v => Key v -> v -> Bool
atMost NoKey _ = True
atMost (Key _ mx) v = mx <= v

lessThan :: Ord v => Key v -> v -> Bool
lessThan NoKey _ = True
lessThan (Key i _) v = low i < v

search :: Ord v => IntervalTree v a -> Interval v -> Maybe a
search (IntervalTree tree) i = searchAtFinger (viewL geq)
  where
    (_, geq) = split (>= intervalToKey i) tree
    searchAtFinger EmptyL = Nothing
    searchAtFinger (a :< as)
      | ai == i          = Just (snd a)
      | high i < high ai = searchAtFinger (viewL as)
      | otherwise        = Nothing
      where
        ai = fst a

inRange :: Ord v => IntervalTree v a -> v -> v -> [(Interval v, a)]
inRange (IntervalTree tree) lo hi = pickem beginning
  where
    beginning = FT.takeUntil (`greaterThan` hi) tree
    pickem x = case viewL $ FT.dropUntil (`atLeast` lo) x of
      EmptyL -> []
      a :< xs -> a : pickem xs
    -- TODO(MP): can you define a split "from the right" and search
    -- more efficiently?  At some point, the subtrees' 'maxHigh' will
    -- be lower than the interval's 'low', at which point we can stop
    -- the search.  In this code, we traverse the whole first part of
    -- the sequence again.

intersections :: Ord v => IntervalTree v a -> Interval v -> [(Interval v, a)]
intersections tree (Interval lo hi) = inRange tree lo hi

dominators :: Ord v => IntervalTree v a -> Interval v -> [(Interval v, a)]
dominators tree (Interval lo hi) = inRange tree hi lo

withinRange :: Ord v => IntervalTree v a -> v -> v -> [(Interval v, a)]
withinRange (IntervalTree tree) lo hi = pickem beginning
  where
    beginning = FT.dropWhile (`lessThan` lo) tree
    pickem x = case viewL $ FT.dropUntil (`atMost` hi) x of
      EmptyL -> []
      a :< xs -> a : pickem xs

contents :: Ord v => IntervalTree v a -> Interval v -> [(Interval v, a)]
contents tree (Interval lo hi) = withinRange tree lo hi
