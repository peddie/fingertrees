{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE TypeFamilies #-}

module Data.FingerTree.Sequence where

import Data.Monoid (Monoid(..), (<>))

import Control.DeepSeq.Generics
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import Data.FingerTree (FingerTree, Measured(..), Split(..))
import qualified Data.FingerTree as FT

type Index = Int

newtype Size = Size { getSize :: Index } deriving (Eq, Show, Ord)

instance NFData Size where
  rnf = rnf . getSize

instance Monoid Size where
  mempty = Size 0
  {-# INLINE mappend #-}
  (Size a) `mappend` (Size b) = Size $ a + b

newtype Element a = Element { getElement :: a } deriving (Eq, Ord)

instance NFData a => NFData (Element a) where
  rnf = rnf . getElement

instance Measured (Element a) where
  type Measure (Element a) = Size
  {-# INLINE measure #-}
  measure (Element _) = Size 1

newtype Sequence a = Sequence { getSequence :: (FingerTree Size (Element a)) }
                   deriving (Eq, Ord)

instance NFData a => NFData (Sequence a) where
  rnf = rnf . getSequence

instance Monoid (Sequence a) where
  mempty = Sequence mempty
  (Sequence a) `mappend` (Sequence b) = Sequence $ a <> b

empty :: Sequence a
empty = Sequence FT.Empty

(<|) :: a -> Sequence a -> Sequence a
a <| sq = Sequence $ (Element a) FT.<| (getSequence sq)

(|>) :: Sequence a -> a -> Sequence a
sq |> a = Sequence $ (getSequence sq) FT.|> (Element a)

fromFoldable :: Foldable f => f a -> Sequence a
fromFoldable = F.foldr' (<|) empty

length :: Sequence a -> Index
length = getSize . measure . getSequence

(!) :: Sequence a -> Index -> a
(Sequence s) ! i = getElement x
  where
    Split _ x _ = FT.splitTree (Size i <) (Size 0) s

splitAt :: Index -> Sequence a -> (Sequence a, Sequence a)
splitAt i (Sequence x) = (Sequence a, Sequence b)
  where
    (a, b) = FT.split (Size i <) x

viewL :: Sequence a -> FT.ViewL Sequence a
viewL (Sequence s) = case FT.viewL s of
  FT.EmptyL -> FT.EmptyL
  (Element a) FT.:< tree -> a FT.:< Sequence tree

viewR :: Sequence a -> FT.ViewR Sequence a
viewR (Sequence s) = case FT.viewR s of
  FT.EmptyR -> FT.EmptyR
  tree FT.:> (Element a) -> Sequence tree FT.:> a

drop :: Index -> Sequence a -> Sequence a
drop n = Sequence . snd . FT.split (Size n <) . getSequence

take :: Index -> Sequence a -> Sequence a
take n = Sequence . fst . FT.split (Size n <) . getSequence
