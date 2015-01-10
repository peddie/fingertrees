{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE TypeFamilies #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module Data.FingerTree.PriorityQueue where

import GHC.Generics (Generic)
import Data.Data (Data)
import Data.Typeable (Typeable)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import Data.Monoid (Monoid(..), (<>))

import Data.FingerTree

data Prio a = Min
            | Prio a
            deriving (Eq, Ord, Show, Read,
                      Generic, Data, Typeable,
                      Functor, Foldable, Traversable)

newtype Element a = Element { getElement :: a } deriving (Eq, Ord)

instance Ord a => Monoid (Prio a) where
  mempty = Min
  Min `mappend` p = p
  p `mappend` Min = p
  (Prio a) `mappend` (Prio b) = Prio $ max a b

instance Ord a => Measured (Element a) where
  type Measure (Element a) = Prio a
  measure (Element a) = Prio a

newtype PQueue a = PQueue { getPQueue :: FingerTree (Prio a) (Element a) }
                 deriving (Eq, Ord)

instance Ord a => Monoid (PQueue a) where
  mempty = PQueue mempty
  (PQueue a) `mappend` (PQueue b) = PQueue $ a <> b

extract :: Ord a => (Prio a -> Bool) -> PQueue a -> Maybe (a, PQueue a)
extract _    (PQueue Empty) = Nothing
extract test (PQueue tree) = Just (getElement x, PQueue $ l <> r)
  where
    Split l x r = splitTree test mempty tree

extractMax :: Ord a => PQueue a -> Maybe (a, PQueue a)
extractMax (PQueue tree) = extract (measure tree <=) (PQueue tree)

extractGT :: Ord a => PQueue a -> a -> Maybe (a, PQueue a)
extractGT (PQueue tree) k = extract (Prio k <) (PQueue tree)

-- TODO(MP): extractAllGT
