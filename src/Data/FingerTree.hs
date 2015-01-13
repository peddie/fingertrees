{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}

module Data.FingerTree where

import qualified Prelude as P
import Prelude ( Functor(..), Show(..), Read(..), Eq(..), Ord(..)
               , (.), otherwise
               , flip, Bool(..), Maybe(..), error)

import GHC.Generics (Generic)
import Data.Data (Data)
import Data.Typeable (Typeable)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.Monoid (Monoid(..), (<>))
import Control.DeepSeq.Generics

import qualified Data.Foldable as F
import Data.Maybe (fromMaybe)

data Digit a = One a
             | Two a a
             | Three a a a
             | Four a a a a
             deriving (Show, Read, Eq, Ord,
                       Generic, Data, Typeable,
                       Functor, Foldable, Traversable)

data Node v a = Node2 !v a a
              | Node3 !v a a a
              deriving (Show, Read, Eq, Ord,
                        Generic, Data, Typeable,
                        Functor, Foldable, Traversable)

data FingerTree v a = Empty
                    | Single a
                    | Deep !v !(Digit a) (FingerTree v (Node v a)) !(Digit a)
                    deriving (Show, Read, Eq, Ord,
                              Generic, Data, Typeable,
                              Functor, Foldable, Traversable)

instance NFData a => NFData (Digit a) where rnf = genericRnf
instance (NFData v, NFData a) => NFData (Node v a) where rnf = genericRnf
instance (NFData v, NFData a) => NFData (FingerTree v a) where rnf = genericRnf

infixr 5 <|
{-# INLINE (<|) #-}
(<|) :: Meas a v => a -> FingerTree v a -> FingerTree v a
lft <| Empty                      = Single lft
lft <| Single v                   = deep' (One lft) Empty (One v)
lft <| Deep v (One a) mid rd        = Deep (measure lft <> v) (Two lft a) mid rd
lft <| Deep v (Two a b) mid rd      = Deep (measure lft <> v) (Three lft a b) mid rd
lft <| Deep v (Three a b c) mid rd  = Deep (measure lft <> v) (Four lft a b c) mid rd
-- TODO(MP): What do the next 3 lines imply?  Do they simply allow the
-- tree to fill out one level entirely before moving on to the next?
-- Does it affect bounds?  Prove.  Experimentally it seems to hurt massively.
-- lft <| Deep _ (Four a b c d) Empty (One z) = deep' (Four lft a b c) Empty (Two d z)
-- lft <| Deep _ (Four a b c d) Empty (Two y z) = deep' (Four lft a b c) Empty (Three d y z)
-- lft <| Deep _ (Four a b c d) Empty (Three x y z) = deep' (Four lft a b c) Empty (Four d x y z)
lft <| Deep v (Four a b c d) mid rd = mid' `P.seq` Deep (measure lft <> v) (Two lft a) mid' rd
  where
    mid' = node3' b c d <| mid

infixl 5 |>
{-# INLINE (|>) #-}
(|>) :: Meas a v => FingerTree v a -> a -> FingerTree v a
Empty                      |> rgt = Single rgt
Single v                   |> rgt = deep' (One v) Empty (One rgt)
Deep v ld mid (One a)        |> rgt = Deep (v <> measure rgt) ld mid (Two a rgt)
Deep v ld mid (Two a b)      |> rgt = Deep (v <> measure rgt) ld mid (Three a b rgt)
Deep v ld mid (Three a b c)  |> rgt = Deep (v <> measure rgt) ld mid (Four a b c rgt)
-- See comments in <| for some thoughts.
-- Deep _ (One a) Empty (Four w x y z) |> rgt = deep' (Two a w) Empty (Four x y z rgt)
-- Deep _ (Two a b) Empty (Four w x y z) |> rgt = deep' (Three a b w) Empty (Four x y z rgt)
-- Deep _ (Three a b c) Empty (Four w x y z) |> rgt = deep' (Four a b c w) Empty (Four x y z rgt)
Deep v ld mid (Four a b c d) |> rgt = mid' `P.seq` Deep (v <> measure rgt) ld mid' (Two d rgt)
  where
    mid' = mid |> node3' a b c

infixl 6 <<|
(<<|) :: (Meas a v, Foldable f) =>
         f a -> FingerTree v a -> FingerTree v a
lst <<| tr = F.foldr' (<|) tr lst

infixl 6 |>>
(|>>) :: (Meas a v, Foldable f) =>
         FingerTree v a -> f a -> FingerTree v a
tr |>> lst = F.foldl' (|>) tr lst

toTreeL :: (Meas a v, Foldable f) =>
           f a -> FingerTree v a
toTreeL lst = lst <<| Empty

toTreeR :: (Meas a v, Foldable f) =>
           f a -> FingerTree v a
toTreeR lst = Empty |>> lst

nodeToDigit :: Node v a -> Digit a
nodeToDigit (Node2 _ a b) = Two a b
nodeToDigit (Node3 _ a b c) = Three a b c

deepL :: Meas a v => FingerTree v (Node v a) -> Digit a -> FingerTree v a
deepL mid rd = case viewL mid of
  EmptyL -> toTreeR rd
  (n :< mid') -> deep' (nodeToDigit n) mid' rd
{-# INLINE deepL #-}

deepR :: Meas a v => Digit a -> FingerTree v (Node v a) -> FingerTree v a
deepR ld mid = case viewR mid of
  EmptyR -> toTreeL ld
  (mid' :> n)   -> deep' ld mid' (nodeToDigit n)
{-# INLINE deepR #-}

data ViewL f a = EmptyL
               | a :< f a
               deriving (Show, Read, Eq, Ord,
                         Generic, Data, Typeable,
                         Functor, Foldable, Traversable)

viewL :: Meas a v => FingerTree v a -> ViewL (FingerTree v) a
viewL Empty = EmptyL
viewL (Single a) = a :< Empty
viewL (Deep _ (One a) mid rd) = a :< deepL mid rd
viewL (Deep _ (Two a b) mid rd)      = a :< deep' (One b) mid rd
viewL (Deep _ (Three a b c) mid rd)  = a :< deep' (Two b c) mid rd
viewL (Deep _ (Four a b c d) mid rd) = a :< deep' (Three b c d) mid rd

data ViewR f a = EmptyR
               | f a :> a
               deriving (Show, Read, Eq, Ord,
                         Generic, Data, Typeable,
                         Functor, Foldable, Traversable)

viewR :: Meas a v => FingerTree v a -> ViewR (FingerTree v) a
viewR Empty = EmptyR
viewR (Single a) = Empty :> a
viewR (Deep _ ld mid (One a)) = deepR ld mid :> a
viewR (Deep _ ld mid (Two a b))      = deep' ld mid (One a) :> b
viewR (Deep _ ld mid (Three a b c))  = deep' ld mid (Two a b) :> c
viewR (Deep _ ld mid (Four a b c d)) = deep' ld mid (Three a b c) :> d

null :: FingerTree v a -> Bool
null Empty = True
null _     = False

head :: Meas a v => FingerTree v a -> Maybe a
head t = case viewL t of
  (a :< _) -> Just a
  _        -> Nothing

tail :: Meas a v => FingerTree v a -> FingerTree v a
tail t = case viewL t of
  (_ :< tl) -> tl
  _         -> Empty

last :: Meas a v => FingerTree v a -> Maybe a
last t = case viewR t of
  (_ :> a) -> Just a
  _        -> Nothing

inits :: Meas a v => FingerTree v a -> FingerTree v a
inits t = case viewR t of
  (it :> _) -> it
  _         -> Empty

head' :: Meas a v => FingerTree v a -> a
head' = fromMaybe (error "Data.FingerTree.head': empty tree!") . head

last' :: Meas a v => FingerTree v a -> a
last' = fromMaybe (error "Data.FingerTree.last': empty tree!") . last

digitToList :: Digit a -> [a]
digitToList = F.foldl' (flip (:)) []

node2' :: Meas a v => a -> a -> Node v a
node2' x y = Node2 (measure x <> measure y) x y
{-# INLINE node2' #-}

node3' :: Meas a v => a -> a -> a -> Node v a
node3' x y z = Node3 (measure x <> measure y <> measure z) x y z
{-# INLINE node3' #-}

instance Meas a v => Monoid (FingerTree v a) where
  mempty = Empty
  mappend = combine

class Measured a where
  type Measure a :: *
  measure :: Monoid (Measure a) => a -> Measure a

type Meas a v = (Measured a, Monoid v, v ~ Measure a)

instance Measured a => Measured (Digit a) where
  type Measure (Digit a) = Measure a
  {-# INLINE measure #-}
  measure = F.foldl' (\a x -> a <> measure x) mempty

instance Monoid v => Measured (Node v a) where
  type Measure (Node v a) = v
  {-# INLINE measure #-}
  measure (Node2 v _ _) = v
  measure (Node3 v _ _ _) = v

instance Meas a v => Measured (FingerTree v a) where
  type Measure (FingerTree v a) = v
  measure Empty = mempty
  measure (Single x) = measure x
  measure (Deep v _ _ _) = v

deep' :: Meas a v => Digit a -> FingerTree v (Node v a) -> Digit a
      -> FingerTree v a
deep' ld mid rd = Deep summ ld mid rd
  where
    summ = measure ld <> measure mid <> measure rd

data Split v a = Split (v a) a (v a)
               deriving (Show, Read, Eq, Ord,
                         Generic, Data, Typeable,
                         Functor, Foldable, Traversable)

splitDigit :: Meas a v => (v -> Bool) -> v -> Digit a
           -> (Maybe (Digit a), a, Maybe (Digit a))
splitDigit _    _ (One a) = (Nothing, a, Nothing)
splitDigit test z (Two a b)
  | test za   = (Nothing, a, j1 b)
  | otherwise = (j1 a, b, Nothing)
  where
    za = z <> measure a
    j1 x = Just (One x)
splitDigit test z (Three a b c)
  | test za   = (Nothing, a, j2 b c)
  | test zb   = (j1 a, b, j1 c)
  | otherwise = (j2 a b, c, Nothing)
  where
    za = z <> measure a
    zb = za <> measure b
    j1 x = Just (One x)
    j2 x y = Just (Two x y)
splitDigit test z (Four a b c d)
  | test za   = (Nothing, a, j3 b c d)
  | test zb   = (j1 a, b, j2 c d)
  | test zc   = (j2 a b, c, j1 d)
  | otherwise = (j3 a b c, d, Nothing)
  where
    za = z <> measure a
    zb = za <> measure b
    zc = zb <> measure c
    j1 x = Just (One x)
    j2 x y = Just (Two x y)
    j3 w x y = Just (Three w x y)

splitTree :: Meas a v =>
             (v -> Bool) -> v -> FingerTree v a
          -> Split (FingerTree v) a
splitTree _ _ Empty =
  error "Data.FingerTree.splitTree: busted invariant: 'splitTree' called on empty tree"
splitTree _ _ (Single v) = Split Empty v Empty
splitTree test z (Deep _ ld mid rd)
  | test summl = let (pre, x, po) = splitDigit test z ld
                 in Split (mttL pre) x (mttLT po mid rd)
  | test summm = let Split mpre mx mpo = splitTree test summl mid
                     (pre, x, po) = splitDigit test (summl <> measure mpre) (nodeToDigit mx)
                 in Split (mttRT ld mpre pre) x (mttLT po mpo rd)
  | otherwise  = let (pre, x, po) = splitDigit test summm rd
                 in Split (mttRT ld mid pre) x (mttR po)
  where
    mttL Nothing = Empty
    mttL (Just p) = toTreeL p
    mttR Nothing = Empty
    mttR (Just p) = toTreeR p
    mttRT ld' mid' Nothing = deepR ld' mid'
    mttRT ld' mid' (Just rd') = deep' ld' mid' rd'
    mttLT Nothing mid' rd' = deepL mid' rd'
    mttLT (Just ld') mid' rd' = deep' ld' mid' rd'
    summl = z <> measure ld
    summm = summl <> measure mid

split :: Meas a v => (v -> Bool) -> FingerTree v a
      -> (FingerTree v a, FingerTree v a)
split _ Empty = (Empty, Empty)
split test tree
  | test (measure tree) = let Split l x r = splitTree test mempty tree
                          in (l, x <| r)
  | otherwise           = (tree, Empty)

lookupTree :: Meas a v => (v -> Bool) -> v -> FingerTree v a -> Maybe (v, a)
lookupTree _ _ Empty = Nothing
lookupTree test z tree = Just (z <> measure l, x)
  where
    Split l x _ = splitTree test z tree

takeUntil :: Meas a v => (v -> Bool) -> FingerTree v a -> FingerTree v a
takeUntil test = P.fst . split test

dropUntil :: Meas a v => (v -> Bool) -> FingerTree v a -> FingerTree v a
dropUntil test = P.snd . split test

takeWhile :: Meas a v => (v -> Bool) -> FingerTree v a -> FingerTree v a
takeWhile test = takeUntil (P.not . test)

dropWhile :: Meas a v => (v -> Bool) -> FingerTree v a -> FingerTree v a
dropWhile test = dropUntil (P.not . test)

-- | @O(n)@ version of 'delete' that doesn't require an 'Ord' instance
-- for @v@.
deleteEq :: (Eq a, Meas a v) => FingerTree v a -> a -> FingerTree v a
deleteEq tree = go Empty tree
  where
    go done togo x = case viewL togo of
      EmptyL  -> done
      a :< as -> if a == x
                 then done <> as
                 else go (done |> a) as x

-- | @O(n)@ version of 'deleteAll' that doesn't require an 'Ord'
-- instance for @v@.
deleteAllEq :: (Eq a, Meas a v) => FingerTree v a -> a -> FingerTree v a
deleteAllEq tree = go Empty tree
  where
    go done togo x = case viewL togo of
      EmptyL  -> done
      a :< as -> if a == x
                 then go done as x
                 else go (done |> a) as x

delete :: (Eq a, Ord v, Meas a v) => FingerTree v a -> a -> FingerTree v a
delete tree x = case split (> measure x) tree of
  (_, Empty) -> tree
  (pre,   t) -> pre <> deleteIfHead (viewL t)
    where
      deleteIfHead EmptyL = Empty
      deleteIfHead (a :< as)
        | a == x = as
        | measure a == measure x = deleteIfHead (viewL as)
        | otherwise = a <| as

deleteAll :: (Eq a, Ord v, Meas a v) => FingerTree v a -> a -> FingerTree v a
deleteAll tree x = case split (> measure x) tree of
  (_, Empty) -> tree
  (pre,   t) -> pre <> deleteIfHead (viewL t)
    where
      deleteIfHead EmptyL = Empty
      deleteIfHead (a :< as)
        | a == x = deleteIfHead (viewL as)
        | measure a == measure x = deleteIfHead (viewL as)
        | otherwise = a <| as

-- All the code below here is autogenerated by invoking the function
-- 'generate' in @src/Data/FingerTree/Generate.hs@.  This function
-- will output a standalone module containing the following code plus
-- the necessary imports and language extensions.  It is recommended
-- to modify that program instead of this.

combine :: Meas a v => FingerTree v a -> FingerTree v a -> FingerTree v a
combine = build0

build0 :: Meas a v => FingerTree v a -> FingerTree v a -> FingerTree v a
build0 Empty a = a
build0 a Empty = a
build0 (Single a) b = a <| b
build0 a (Single b) = a |> b
build0 (Deep va la ma ra) (Deep vb lb mb rb) = Deep (va <> vb) la (combine0 ma ra lb mb) rb


build1 :: Meas a v => FingerTree v a -> a -> FingerTree v a -> FingerTree v a
build1 Empty a b = a <| b
build1 a b Empty = a |> b
build1 (Single a) b c = a <| b <| c
build1 a b (Single c) = a |> b |> c
build1 (Deep va la ma ra) b (Deep vc lc mc rc) = Deep (va <> measure b <> vc) la (combine1 ma ra b lc mc) rc


build2 :: Meas a v => FingerTree v a -> a -> a -> FingerTree v a -> FingerTree v a
build2 Empty a b c = a <| b <| c
build2 a b c Empty = a |> b |> c
build2 (Single a) b c d = a <| b <| c <| d
build2 a b c (Single d) = a |> b |> c |> d
build2 (Deep va la ma ra) b c (Deep vd ld md rd) = Deep (va <> measure b <> measure c <> vd) la (combine2 ma ra b c ld md) rd


build3 :: Meas a v => FingerTree v a -> a -> a -> a -> FingerTree v a -> FingerTree v a
build3 Empty a b c d = a <| b <| c <| d
build3 a b c d Empty = a |> b |> c |> d
build3 (Single a) b c d e = a <| b <| c <| d <| e
build3 a b c d (Single e) = a |> b |> c |> d |> e
build3 (Deep va la ma ra) b c d (Deep ve le me re) = Deep (va <> measure b <> measure c <> measure d <> ve) la (combine3 ma ra b c d le me) re


build4 :: Meas a v => FingerTree v a -> a -> a -> a -> a -> FingerTree v a -> FingerTree v a
build4 Empty a b c d e = a <| b <| c <| d <| e
build4 a b c d e Empty = a |> b |> c |> d |> e
build4 (Single a) b c d e f = a <| b <| c <| d <| e <| f
build4 a b c d e (Single f) = a |> b |> c |> d |> e |> f
build4 (Deep va la ma ra) b c d e (Deep vf lf mf rf) = Deep (va <> measure b <> measure c <> measure d <> measure e <> vf) la (combine4 ma ra b c d e lf mf) rf


build5 :: Meas a v => FingerTree v a -> a -> a -> a -> a -> a -> FingerTree v a -> FingerTree v a
build5 Empty a b c d e f = a <| b <| c <| d <| e <| f
build5 a b c d e f Empty = a |> b |> c |> d |> e |> f
build5 (Single a) b c d e f g = a <| b <| c <| d <| e <| f <| g
build5 a b c d e f (Single g) = a |> b |> c |> d |> e |> f |> g
build5 (Deep va la ma ra) b c d e f (Deep vg lg mg rg) = Deep (va <> measure b <> measure c <> measure d <> measure e <> measure f <> vg) la (combine5 ma ra b c d e f lg mg) rg


combine0 :: Meas a v => FingerTree v (Node v a) -> Digit a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
combine0 tree1 (One a) (One b) tree2 = build1 tree1 (node2' a b) tree2
combine0 tree1 (One a) (Two b c) tree2 = build1 tree1 (node3' a b c) tree2
combine0 tree1 (One a) (Three b c d) tree2 = build2 tree1 (node2' a b) (node2' c d) tree2
combine0 tree1 (One a) (Four b c d e) tree2 = build2 tree1 (node3' a b c) (node2' d e) tree2
combine0 tree1 (Two a b) (One c) tree2 = build1 tree1 (node3' a b c) tree2
combine0 tree1 (Two a b) (Two c d) tree2 = build2 tree1 (node2' a b) (node2' c d) tree2
combine0 tree1 (Two a b) (Three c d e) tree2 = build2 tree1 (node3' a b c) (node2' d e) tree2
combine0 tree1 (Two a b) (Four c d e f) tree2 = build2 tree1 (node3' a b c) (node3' d e f) tree2
combine0 tree1 (Three a b c) (One d) tree2 = build2 tree1 (node2' a b) (node2' c d) tree2
combine0 tree1 (Three a b c) (Two d e) tree2 = build2 tree1 (node3' a b c) (node2' d e) tree2
combine0 tree1 (Three a b c) (Three d e f) tree2 = build2 tree1 (node3' a b c) (node3' d e f) tree2
combine0 tree1 (Three a b c) (Four d e f g) tree2 = build3 tree1 (node2' a b) (node3' c d e) (node2' f g) tree2
combine0 tree1 (Four a b c d) (One e) tree2 = build2 tree1 (node3' a b c) (node2' d e) tree2
combine0 tree1 (Four a b c d) (Two e f) tree2 = build2 tree1 (node3' a b c) (node3' d e f) tree2
combine0 tree1 (Four a b c d) (Three e f g) tree2 = build3 tree1 (node2' a b) (node3' c d e) (node2' f g) tree2
combine0 tree1 (Four a b c d) (Four e f g h) tree2 = build3 tree1 (node3' a b c) (node2' d e) (node3' f g h) tree2


combine1 :: Meas a v => FingerTree v (Node v a) -> Digit a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
combine1 tree1 (One a) b (One c) tree2 = build1 tree1 (node3' a b c) tree2
combine1 tree1 (One a) b (Two c d) tree2 = build2 tree1 (node2' a b) (node2' c d) tree2
combine1 tree1 (One a) b (Three c d e) tree2 = build2 tree1 (node3' a b c) (node2' d e) tree2
combine1 tree1 (One a) b (Four c d e f) tree2 = build2 tree1 (node3' a b c) (node3' d e f) tree2
combine1 tree1 (Two a b) c (One d) tree2 = build2 tree1 (node2' a b) (node2' c d) tree2
combine1 tree1 (Two a b) c (Two d e) tree2 = build2 tree1 (node3' a b c) (node2' d e) tree2
combine1 tree1 (Two a b) c (Three d e f) tree2 = build2 tree1 (node3' a b c) (node3' d e f) tree2
combine1 tree1 (Two a b) c (Four d e f g) tree2 = build3 tree1 (node2' a b) (node3' c d e) (node2' f g) tree2
combine1 tree1 (Three a b c) d (One e) tree2 = build2 tree1 (node3' a b c) (node2' d e) tree2
combine1 tree1 (Three a b c) d (Two e f) tree2 = build2 tree1 (node3' a b c) (node3' d e f) tree2
combine1 tree1 (Three a b c) d (Three e f g) tree2 = build3 tree1 (node2' a b) (node3' c d e) (node2' f g) tree2
combine1 tree1 (Three a b c) d (Four e f g h) tree2 = build3 tree1 (node3' a b c) (node2' d e) (node3' f g h) tree2
combine1 tree1 (Four a b c d) e (One f) tree2 = build2 tree1 (node3' a b c) (node3' d e f) tree2
combine1 tree1 (Four a b c d) e (Two f g) tree2 = build3 tree1 (node2' a b) (node3' c d e) (node2' f g) tree2
combine1 tree1 (Four a b c d) e (Three f g h) tree2 = build3 tree1 (node3' a b c) (node2' d e) (node3' f g h) tree2
combine1 tree1 (Four a b c d) e (Four f g h i) tree2 = build3 tree1 (node3' a b c) (node3' d e f) (node3' g h i) tree2


combine2 :: Meas a v => FingerTree v (Node v a) -> Digit a -> a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
combine2 tree1 (One a) b c (One d) tree2 = build2 tree1 (node2' a b) (node2' c d) tree2
combine2 tree1 (One a) b c (Two d e) tree2 = build2 tree1 (node3' a b c) (node2' d e) tree2
combine2 tree1 (One a) b c (Three d e f) tree2 = build2 tree1 (node3' a b c) (node3' d e f) tree2
combine2 tree1 (One a) b c (Four d e f g) tree2 = build3 tree1 (node2' a b) (node3' c d e) (node2' f g) tree2
combine2 tree1 (Two a b) c d (One e) tree2 = build2 tree1 (node3' a b c) (node2' d e) tree2
combine2 tree1 (Two a b) c d (Two e f) tree2 = build2 tree1 (node3' a b c) (node3' d e f) tree2
combine2 tree1 (Two a b) c d (Three e f g) tree2 = build3 tree1 (node2' a b) (node3' c d e) (node2' f g) tree2
combine2 tree1 (Two a b) c d (Four e f g h) tree2 = build3 tree1 (node3' a b c) (node2' d e) (node3' f g h) tree2
combine2 tree1 (Three a b c) d e (One f) tree2 = build2 tree1 (node3' a b c) (node3' d e f) tree2
combine2 tree1 (Three a b c) d e (Two f g) tree2 = build3 tree1 (node2' a b) (node3' c d e) (node2' f g) tree2
combine2 tree1 (Three a b c) d e (Three f g h) tree2 = build3 tree1 (node3' a b c) (node2' d e) (node3' f g h) tree2
combine2 tree1 (Three a b c) d e (Four f g h i) tree2 = build3 tree1 (node3' a b c) (node3' d e f) (node3' g h i) tree2
combine2 tree1 (Four a b c d) e f (One g) tree2 = build3 tree1 (node2' a b) (node3' c d e) (node2' f g) tree2
combine2 tree1 (Four a b c d) e f (Two g h) tree2 = build3 tree1 (node3' a b c) (node2' d e) (node3' f g h) tree2
combine2 tree1 (Four a b c d) e f (Three g h i) tree2 = build3 tree1 (node3' a b c) (node3' d e f) (node3' g h i) tree2
combine2 tree1 (Four a b c d) e f (Four g h i j) tree2 = build4 tree1 (node3' a b c) (node2' d e) (node2' f g) (node3' h i j) tree2


combine3 :: Meas a v => FingerTree v (Node v a) -> Digit a -> a -> a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
combine3 tree1 (One a) b c d (One e) tree2 = build2 tree1 (node3' a b c) (node2' d e) tree2
combine3 tree1 (One a) b c d (Two e f) tree2 = build2 tree1 (node3' a b c) (node3' d e f) tree2
combine3 tree1 (One a) b c d (Three e f g) tree2 = build3 tree1 (node2' a b) (node3' c d e) (node2' f g) tree2
combine3 tree1 (One a) b c d (Four e f g h) tree2 = build3 tree1 (node3' a b c) (node2' d e) (node3' f g h) tree2
combine3 tree1 (Two a b) c d e (One f) tree2 = build2 tree1 (node3' a b c) (node3' d e f) tree2
combine3 tree1 (Two a b) c d e (Two f g) tree2 = build3 tree1 (node2' a b) (node3' c d e) (node2' f g) tree2
combine3 tree1 (Two a b) c d e (Three f g h) tree2 = build3 tree1 (node3' a b c) (node2' d e) (node3' f g h) tree2
combine3 tree1 (Two a b) c d e (Four f g h i) tree2 = build3 tree1 (node3' a b c) (node3' d e f) (node3' g h i) tree2
combine3 tree1 (Three a b c) d e f (One g) tree2 = build3 tree1 (node2' a b) (node3' c d e) (node2' f g) tree2
combine3 tree1 (Three a b c) d e f (Two g h) tree2 = build3 tree1 (node3' a b c) (node2' d e) (node3' f g h) tree2
combine3 tree1 (Three a b c) d e f (Three g h i) tree2 = build3 tree1 (node3' a b c) (node3' d e f) (node3' g h i) tree2
combine3 tree1 (Three a b c) d e f (Four g h i j) tree2 = build4 tree1 (node3' a b c) (node2' d e) (node2' f g) (node3' h i j) tree2
combine3 tree1 (Four a b c d) e f g (One h) tree2 = build3 tree1 (node3' a b c) (node2' d e) (node3' f g h) tree2
combine3 tree1 (Four a b c d) e f g (Two h i) tree2 = build3 tree1 (node3' a b c) (node3' d e f) (node3' g h i) tree2
combine3 tree1 (Four a b c d) e f g (Three h i j) tree2 = build4 tree1 (node3' a b c) (node2' d e) (node2' f g) (node3' h i j) tree2
combine3 tree1 (Four a b c d) e f g (Four h i j k) tree2 = build5 tree1 (node2' a b) (node2' c d) (node3' e f g) (node2' h i) (node2' j k) tree2


combine4 :: Meas a v => FingerTree v (Node v a) -> Digit a -> a -> a -> a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
combine4 tree1 (One a) b c d e (One f) tree2 = build2 tree1 (node3' a b c) (node3' d e f) tree2
combine4 tree1 (One a) b c d e (Two f g) tree2 = build3 tree1 (node2' a b) (node3' c d e) (node2' f g) tree2
combine4 tree1 (One a) b c d e (Three f g h) tree2 = build3 tree1 (node3' a b c) (node2' d e) (node3' f g h) tree2
combine4 tree1 (One a) b c d e (Four f g h i) tree2 = build3 tree1 (node3' a b c) (node3' d e f) (node3' g h i) tree2
combine4 tree1 (Two a b) c d e f (One g) tree2 = build3 tree1 (node2' a b) (node3' c d e) (node2' f g) tree2
combine4 tree1 (Two a b) c d e f (Two g h) tree2 = build3 tree1 (node3' a b c) (node2' d e) (node3' f g h) tree2
combine4 tree1 (Two a b) c d e f (Three g h i) tree2 = build3 tree1 (node3' a b c) (node3' d e f) (node3' g h i) tree2
combine4 tree1 (Two a b) c d e f (Four g h i j) tree2 = build4 tree1 (node3' a b c) (node2' d e) (node2' f g) (node3' h i j) tree2
combine4 tree1 (Three a b c) d e f g (One h) tree2 = build3 tree1 (node3' a b c) (node2' d e) (node3' f g h) tree2
combine4 tree1 (Three a b c) d e f g (Two h i) tree2 = build3 tree1 (node3' a b c) (node3' d e f) (node3' g h i) tree2
combine4 tree1 (Three a b c) d e f g (Three h i j) tree2 = build4 tree1 (node3' a b c) (node2' d e) (node2' f g) (node3' h i j) tree2
combine4 tree1 (Three a b c) d e f g (Four h i j k) tree2 = build5 tree1 (node2' a b) (node2' c d) (node3' e f g) (node2' h i) (node2' j k) tree2
combine4 tree1 (Four a b c d) e f g h (One i) tree2 = build3 tree1 (node3' a b c) (node3' d e f) (node3' g h i) tree2
combine4 tree1 (Four a b c d) e f g h (Two i j) tree2 = build4 tree1 (node3' a b c) (node2' d e) (node2' f g) (node3' h i j) tree2
combine4 tree1 (Four a b c d) e f g h (Three i j k) tree2 = build5 tree1 (node2' a b) (node2' c d) (node3' e f g) (node2' h i) (node2' j k) tree2
combine4 tree1 (Four a b c d) e f g h (Four i j k l) tree2 = build4 tree1 (node3' a b c) (node3' d e f) (node3' g h i) (node3' j k l) tree2


combine5 :: Meas a v => FingerTree v (Node v a) -> Digit a -> a -> a -> a -> a -> a -> Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)
combine5 tree1 (One a) b c d e f (One g) tree2 = build3 tree1 (node2' a b) (node3' c d e) (node2' f g) tree2
combine5 tree1 (One a) b c d e f (Two g h) tree2 = build3 tree1 (node3' a b c) (node2' d e) (node3' f g h) tree2
combine5 tree1 (One a) b c d e f (Three g h i) tree2 = build3 tree1 (node3' a b c) (node3' d e f) (node3' g h i) tree2
combine5 tree1 (One a) b c d e f (Four g h i j) tree2 = build4 tree1 (node3' a b c) (node2' d e) (node2' f g) (node3' h i j) tree2
combine5 tree1 (Two a b) c d e f g (One h) tree2 = build3 tree1 (node3' a b c) (node2' d e) (node3' f g h) tree2
combine5 tree1 (Two a b) c d e f g (Two h i) tree2 = build3 tree1 (node3' a b c) (node3' d e f) (node3' g h i) tree2
combine5 tree1 (Two a b) c d e f g (Three h i j) tree2 = build4 tree1 (node3' a b c) (node2' d e) (node2' f g) (node3' h i j) tree2
combine5 tree1 (Two a b) c d e f g (Four h i j k) tree2 = build5 tree1 (node2' a b) (node2' c d) (node3' e f g) (node2' h i) (node2' j k) tree2
combine5 tree1 (Three a b c) d e f g h (One i) tree2 = build3 tree1 (node3' a b c) (node3' d e f) (node3' g h i) tree2
combine5 tree1 (Three a b c) d e f g h (Two i j) tree2 = build4 tree1 (node3' a b c) (node2' d e) (node2' f g) (node3' h i j) tree2
combine5 tree1 (Three a b c) d e f g h (Three i j k) tree2 = build5 tree1 (node2' a b) (node2' c d) (node3' e f g) (node2' h i) (node2' j k) tree2
combine5 tree1 (Three a b c) d e f g h (Four i j k l) tree2 = build4 tree1 (node3' a b c) (node3' d e f) (node3' g h i) (node3' j k l) tree2
combine5 tree1 (Four a b c d) e f g h i (One j) tree2 = build4 tree1 (node3' a b c) (node2' d e) (node2' f g) (node3' h i j) tree2
combine5 tree1 (Four a b c d) e f g h i (Two j k) tree2 = build5 tree1 (node2' a b) (node2' c d) (node3' e f g) (node2' h i) (node2' j k) tree2
combine5 tree1 (Four a b c d) e f g h i (Three j k l) tree2 = build4 tree1 (node3' a b c) (node3' d e f) (node3' g h i) (node3' j k l) tree2
combine5 tree1 (Four a b c d) e f g h i (Four j k l m) tree2 = build5 tree1 (node3' a b c) (node2' d e) (node3' f g h) (node2' i j) (node3' k l m) tree2
