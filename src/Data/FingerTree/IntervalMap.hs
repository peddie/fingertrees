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

module Data.FingerTree.IntervalMap (
    -- * Interval trees
  IntervalMap
    -- ** Creating interval trees
  , empty
  , singleton
  , insert
  , insert'
  , insertWith
  , fromFoldable
    -- ** Working with interval trees
  , toList
  , union
    -- ** Querying interval trees
  , search
  , intersections
  , dominators
  , contents
  , extractIntersections
  , extractDominators
  , extractContents
    -- ** Working with interval tree key-value pairs
  , intersects'
  , dominates'
  , contains'
  , disjoins'
  ) where

import GHC.Generics (Generic)
import Data.Data (Data)
import Data.Typeable (Typeable)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Control.DeepSeq.Generics

import qualified Data.Foldable as F

import Data.Monoid (Monoid(..), (<>))
import Control.Monad (replicateM)

import Data.FingerTree as FT
import Data.Interval hiding (union, intersection)

import Test.QuickCheck

-- | The 'maxInterval' part keeps track of the ordering of
-- 'Interval's, sorted by lower bound first.  The 'maxHigh' part keeps
-- track of the upper bound of the 'Interval's contained.  Between the
-- two, we can split by whether intersection is possible on the high
-- end (using 'maxHigh') or the low end (using 'maxInterval').
data Key v = NoKey
           | Key !(Interval v)
                 !v
           deriving (Show, Read, Eq, Ord,
                     Generic, Data, Typeable,
                     Functor, Foldable, Traversable)

instance NFData a => NFData (Key a) where rnf = genericRnf

instance Ord v => Monoid (Key v) where
  mempty = NoKey
  NoKey `mappend` k = k
  k `mappend` NoKey = k
  (Key _ a) `mappend` (Key ib b) = Key ib (max a b)

{-

Ran into trouble trying to come up with the Monoid instance for this
structure.  The problem is that any 'Gap' constructor would have to
store all the gaps below it, so that in the case of 'NoGap a'
@`mappend`@ 'Gap z c', if @a@ contains @z@, we can't turn it into a
'NoGap' -- we're only tracking the highest gap in values.

data Gap v = NullGap
           | NoGap (Interval v)
           | Gap (Interval v) (Interval v)
           deriving (Show, Read, Eq, Ord,
                     Generic, Data, Typeable,
                     Functor, Foldable, Traversable)

instance Ord v => Monoid (Gap v) where
  mempty = NullGap
  NullGap `mappend` v = v
  v `mappend` NullGap = v
  (NoGap a) `mappend` (NoGap b)
    | a == b           = NoGap a
    | a `intersects` b = NoGap (Interval (min (low a) (low b)) (max (high a) (high b)))
    | high a < low b   = Gap (Interval (high a) (low b)) (Interval (low a) (high b))
    | high b < low a   = Gap (Interval (high b) (low a)) (Interval (low b) (high a))
  (NoGap a) `mappend` (Gap z c)
    | a `contains` z = NoGap (min (low a) (low c)) (max (high a) (high c))
    | a `intersects` z =

Perhaps a Gap Tree can be implemented by

 * an operation to transform any contents/intersections/dominators and
   re-insert them in the tree

 * filling the Gap Tree with the initial interval in question and use
   the transform operation to truncate anything overlapping with incoming
   intervals.

-}

instance Measured (Interval v) where
  type Measure (Interval v) = Key v
  measure = intervalToKey

instance Ord v => Measured (Interval v, a) where
  type Measure (Interval v, a) = Key v
  measure = measure . fst

intervalToKey :: Interval v -> Key v
intervalToKey i = Key i (high i)

dominates', intersects', contains', disjoins' :: Ord v => (Interval v, a) -> (Interval v, b) -> Bool
dominates' a b = (fst a) `dominates` (fst b)
intersects' a b = (fst a) `intersects` (fst b)
contains' a b = (fst a) `contains` (fst b)
disjoins' a b = (fst a) `disjoins` (fst b)

newtype IntervalMap v a = IntervalMap {
  getIntervalMap :: FingerTree (Key v) (Interval v, a)
  } deriving (Eq, Ord)

instance (NFData v, NFData a) => NFData (IntervalMap v a) where
  rnf = rnf . getIntervalMap

instance (Arbitrary a, Arbitrary v, Ord v) => Arbitrary (IntervalMap v a) where
  arbitrary = do
    sz <- fmap abs arbitrarySizedBoundedIntegral
    intervals <- replicateM sz arbitrary
    values <- replicateM sz arbitrary
    return . fromFoldable $ zip intervals values

empty :: IntervalMap v a
empty = IntervalMap Empty

singleton :: Ord v => Interval v -> a -> IntervalMap v a
singleton i v = insert empty i v

-- TODO(MP): Make safe and unsafe variants.
insert :: Ord v => IntervalMap v a -> Interval v -> a -> IntervalMap v a
insert (IntervalMap tree) i x = IntervalMap $ leq <> ((i, x) <| gt)
  where
    (leq, gt) = split (> intervalToKey i) tree

insert' :: Ord v => IntervalMap v a -> (Interval v, a) -> IntervalMap v a
insert' t (i, x) = insert t i x

insertWith :: Ord v => (a -> Interval v) -> IntervalMap v a -> a -> IntervalMap v a
insertWith f tree x = insert tree (f x) x

fromFoldable :: (Foldable f, Ord v) => f (Interval v, a) -> IntervalMap v a
fromFoldable = F.foldl' (\tree (i, a) -> insert tree i a) empty

toList :: IntervalMap v a -> [(Interval v, a)]
toList = F.foldr' (:) [] . getIntervalMap

instance (Show v, Show a) => Show (IntervalMap v a) where
  show x = "fromList " ++ show (toList x)

atLeast :: Ord v => Key v -> v -> Bool
atLeast NoKey      _ = False
atLeast (Key _ mx) v = mx >= v

greaterThan :: Ord v => Key v -> v -> Bool
greaterThan NoKey     _ = False
greaterThan (Key i _) v = low i > v

search :: Ord v => IntervalMap v a -> Interval v -> Maybe a
search (IntervalMap tree) i = searchAtFinger (viewL geq)
  where
    (_, geq) = split (>= intervalToKey i) tree
    searchAtFinger EmptyL = Nothing
    searchAtFinger (a :< as)
      | ai == i          = Just (snd a)
      | high i < high ai = searchAtFinger (viewL as)
      | otherwise        = Nothing
      where
        ai = fst a

inRange :: Ord v => IntervalMap v a -> v -> v -> (IntervalMap v a, [(Interval v, a)])
inRange (IntervalMap tree) lo hi = (IntervalMap $ beginning' <> end, res)
  where
    (beginning, end) = split (`greaterThan` hi) tree
    (beginning', res) = pickem beginning
    pickem x = let (drp, check) = split (`atLeast` lo) x in
      case viewL check of
       EmptyL -> (Empty, [])
       a :< xs -> let (moar, px) = pickem xs
                  in (drp <> moar, a : px)
    -- TODO(MP): can you define a split "from the right" and search
    -- more efficiently?  At some point, the subtrees' 'maxHigh' will
    -- be lower than the interval's 'low', at which point we can stop
    -- the search.  In this code, we traverse the whole first part of
    -- the sequence again.

-- |
--
-- >>> let test = fromFoldable [(Interval 20 22, "butts"), (Interval 30 31, "poop"), (Interval 21 28, "cats")]
-- >>> fst $ extractIntersections test (Interval 22 23)
-- fromList [(Interval {low = 30, high = 31},"poop")]
extractIntersections :: Ord v => IntervalMap v a -> Interval v
                     -> (IntervalMap v a, [(Interval v, a)])
extractIntersections tree (Interval lo hi) = inRange tree lo hi

-- |
--
-- >>> let test = fromFoldable [(Interval 20 22, "butts"), (Interval 30 31, "poop"), (Interval 21 28, "cats")]
-- >>> intersections test (Interval 22 23)
-- [(Interval {low = 20, high = 22},"butts"),(Interval {low = 21, high = 28},"cats")]
intersections :: Ord v => IntervalMap v a -> Interval v -> [(Interval v, a)]
intersections tree = snd . extractIntersections tree

-- |
--
-- >>> let test = fromFoldable [(Interval 20 22, "butts"), (Interval 30 31, "poop"), (Interval 21 28, "cats")]
-- >>> fst $ extractDominators test (Interval 22 23)
-- fromList [(Interval {low = 20, high = 22},"butts"),(Interval {low = 30, high = 31},"poop")]
extractDominators :: Ord v => IntervalMap v a -> Interval v
                  -> (IntervalMap v a, [(Interval v, a)])
extractDominators tree (Interval lo hi) = inRange tree hi lo

-- |
--
-- >>> let test = fromFoldable [(Interval 20 22, "butts"), (Interval 30 31, "poop"), (Interval 21 28, "cats")]
-- >>> dominators test (Interval 22 23)
-- [(Interval {low = 21, high = 28},"cats")]
dominators :: Ord v => IntervalMap v a -> Interval v -> [(Interval v, a)]
dominators tree = snd . extractDominators tree

above :: Ord v => Key v -> v -> Bool
above NoKey _ = True
above (Key _ mx) v = mx > v

greaterThanEq :: Ord v => Key v -> v -> Bool
greaterThanEq NoKey _ = True
greaterThanEq (Key i _) v = low i >= v

withinRange :: Ord v => IntervalMap v a -> v -> v
            -> (IntervalMap v a, [(Interval v, a)])
withinRange (IntervalMap tree) lo hi = (IntervalMap $ beginning <> end', toList $ IntervalMap res)
  where
    (beginning, end) = split (`greaterThanEq` lo) tree
    (res, end') = split (`above` hi) end

-- |
--
-- >>> let test = fromFoldable [(Interval 20 22, "butts"), (Interval 30 31, "poop"), (Interval 21 28, "cats")]
-- >>> fst $ extractContents test (Interval 20 29)
-- fromList [(Interval {low = 30, high = 31},"poop")]
extractContents :: Ord v => IntervalMap v a -> Interval v
                -> (IntervalMap v a, [(Interval v, a)])
extractContents tree (Interval lo hi) = withinRange tree lo hi

-- |
--
-- >>> let test = fromFoldable [(Interval 20 22, "butts"), (Interval 30 31, "poop"), (Interval 21 28, "cats")]
-- >>> contents test (Interval 20 29)
-- [(Interval {low = 20, high = 22},"butts"),(Interval {low = 21, high = 28},"cats")]
-- >>> contents test (Interval 21 28)
-- [(Interval {low = 21, high = 28},"cats")]
contents :: Ord v => IntervalMap v a -> Interval v -> [(Interval v, a)]
contents tree = snd . extractContents tree

-- TODO(MP): locate, modify and reinsert for intersections,
-- dominators, contents (probably only makes sense for interval trees,
-- rather than interval maps).  Perhaps provide a zipper?
-- TODO(MP): intersection, disunion

union :: Ord v => IntervalMap v a -> IntervalMap v a -> IntervalMap v a
union (IntervalMap ta) (IntervalMap tb) = IntervalMap $ go ta tb
  where
    go as bs = case viewL bs of
      EmptyL -> as
      b :< lst -> let (lt, gt) = split (measure b <) as in
        lt <> (b <| go lst gt)
