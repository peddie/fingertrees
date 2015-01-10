{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE TypeFamilies #-}

module Data.FingerTree.Sequence where

import Data.Monoid (Monoid(..), (<>))
import Data.Word (Word64)

import Data.FingerTree

type Index = Word64

newtype Size = Size { getSize :: Word64 } deriving (Eq, Show, Ord)

instance Monoid Size where
  mempty = Size 0
  (Size a) `mappend` (Size b) = Size $ a + b

newtype Element a = Element { getElement :: a } deriving (Eq, Ord)

instance Measured (Element a) where
  type Measure (Element a) = Size
  measure (Element _) = Size 1

newtype Sequence a = Sequence { getSequence :: (FingerTree Size (Element a)) }
                   deriving (Eq, Ord)

instance Monoid (Sequence a) where
  mempty = Sequence mempty
  (Sequence a) `mappend` (Sequence b) = Sequence $ a <> b

length :: Sequence a -> Index
length = getSize . measure . getSequence

(!) :: Sequence a -> Index -> a
(Sequence s) ! i = getElement x
  where
    Split _ x _ = splitTree (Size i <) (Size 0) s

splitAt :: Sequence a -> Index -> (Sequence a, Sequence a)
splitAt (Sequence x) i = (Sequence a, Sequence b)
  where
    (a, b) = split (Size i <) x
