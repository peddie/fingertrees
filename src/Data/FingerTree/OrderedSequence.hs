{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE TypeFamilies #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module Data.FingerTree.OrderedSequence where

import GHC.Generics (Generic)
import Data.Data (Data)
import Data.Typeable (Typeable)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import Data.Monoid (Monoid(..), (<>))

import Data.FingerTree

data Key a = NoKey
           | Key a
           deriving (Eq, Ord, Show, Read,
                     Generic, Data, Typeable,
                     Functor, Foldable, Traversable)

newtype Element a = Element { getElement :: a } deriving (Eq, Ord)

instance Monoid (Key a) where
  mempty = NoKey
  NoKey `mappend` k = k
  k `mappend` NoKey = k
  _ `mappend` k = k

instance Measured (Element a) where
  type Measure (Element a) = Key a
  measure (Element a) = Key a

newtype OSeq a = OSeq { getOSeq :: FingerTree (Key a) (Element a) }
               deriving (Eq, Ord)

instance Ord a => Monoid (OSeq a) where
  mempty = OSeq mempty
  mappend = merge

partition :: Ord a => OSeq a -> a -> (OSeq a, OSeq a)
partition (OSeq tree) k = (OSeq a, OSeq b)
  where
    (a, b) = split (>= Key k) tree

insert :: Ord a => OSeq a -> a -> OSeq a
insert (OSeq tree) v = (OSeq $ lt <> (Element v <| gt))
  where
    (lt, gt) = split (> Key v) tree

deleteAll :: Ord a => OSeq a -> a -> OSeq a
deleteAll (OSeq tree) v = OSeq $ lt <> gt
  where
    (lt, geq) = split (>= Key v) tree
    gt = snd $ split (> Key v) geq

merge :: Ord a => OSeq a -> OSeq a -> OSeq a
merge (OSeq a') (OSeq b') = OSeq $ a' `go` b'
  where
    go as bs = case viewL bs of
      EmptyL -> as
      (Element a) :< lst -> let (lt, gt) = split (Key a >) lst
                            in lt <> (Element a <| go bs gt)
