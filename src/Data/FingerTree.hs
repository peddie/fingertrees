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
               , (.), (++), ($), otherwise
               , flip, Bool(..), Maybe(..), error)

import Data.Maybe (fromMaybe)

import GHC.Generics (Generic)
import Data.Data (Data)
import Data.Typeable (Typeable)
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import Data.Traversable (Traversable)
import Data.Monoid (Monoid(..), (<>))

data Digit a = One a
             | Two a a
             | Three a a a
             | Four a a a a
             deriving (Show, Read, Eq, Ord,
                       Generic, Data, Typeable,
                       Functor, Foldable, Traversable)

data Node v a = Node2 v a a
              | Node3 v a a a
              deriving (Show, Read, Eq, Ord,
                        Generic, Data, Typeable,
                        Functor, Foldable, Traversable)

data FingerTree v a = Empty
                    | Single a
                    | Deep v (Digit a) (FingerTree v (Node v a)) (Digit a)
                    deriving (Show, Read, Eq, Ord,
                              Generic, Data, Typeable,
                              Functor, Foldable, Traversable)

type Meas a v = (Measured a, Monoid v, v ~ Measure a)

infixr 5 <|

(<|) :: Meas a v => a -> FingerTree v a -> FingerTree v a
lft <| Empty                      = Single lft
lft <| Single v                   = deep' (One lft) Empty (One v)
lft <| Deep _ (One a) mid rd        = deep' (Two lft a) mid rd
lft <| Deep _ (Two a b) mid rd      = deep' (Three lft a b) mid rd
lft <| Deep _ (Three a b c) mid rd  = deep' (Four lft a b c) mid rd
lft <| Deep _ (Four a b c d) mid rd = deep' (Two lft a) mid' rd
  where
    mid' = node3' b c d <| mid

infixl 5 |>
(|>) :: Meas a v => FingerTree v a -> a -> FingerTree v a
Empty                      |> rgt = Single rgt
Single v                   |> rgt = deep' (One v) Empty (One rgt)
Deep _ ld mid (One a)        |> rgt = deep' ld mid (Two a rgt)
Deep _ ld mid (Two a b)      |> rgt = deep' ld mid (Three a b rgt)
Deep _ ld mid (Three a b c)  |> rgt = deep' ld mid (Four a b c rgt)
Deep _ ld mid (Four a b c d) |> rgt = deep' ld mid' (Two d rgt)
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

deepR :: Meas a v => Digit a -> FingerTree v (Node v a) -> FingerTree v a
deepR ld mid = case viewR mid of
  EmptyR -> toTreeL ld
  (mid' :> n)   -> deep' ld mid' (nodeToDigit n)

data ViewL v a = EmptyL
               | a :< FingerTree v a
               deriving (Show, Read, Eq, Ord,
                         Generic, Data, Typeable,
                         Functor, Foldable, Traversable)

viewL :: Meas a v => FingerTree v a -> ViewL v a
viewL Empty = EmptyL
viewL (Single a) = a :< Empty
viewL (Deep _ (One a) mid rd) = a :< deepL mid rd
viewL (Deep _ (Two a b) mid rd)      = a :< deep' (One b) mid rd
viewL (Deep _ (Three a b c) mid rd)  = a :< deep' (Two b c) mid rd
viewL (Deep _ (Four a b c d) mid rd) = a :< deep' (Three b c d) mid rd

data ViewR v a = EmptyR
               | FingerTree v a :> a
               deriving (Show, Read, Eq, Ord,
                         Generic, Data, Typeable,
                         Functor, Foldable, Traversable)

viewR :: Meas a v => FingerTree v a -> ViewR v a
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

node3' :: Meas a v => a -> a -> a -> Node v a
node3' x y z = Node3 (measure x <> measure y <> measure z) x y z

listToNodes :: Meas a v => [a] -> [Node v a]
listToNodes [] = error "Data.FingerTree.listToNodes: empty argument!"
listToNodes [_] = error "Data.FingerTree.listToNodes: singleton argument!"
listToNodes [x, y] = [node2' x y]
listToNodes [x, y, z] = [node3' x y z]
listToNodes [w, x, y, z] = [node2' w x, node2' y z]
listToNodes [v, w, x, y, z] = [node3' v w x, node2' y z]
listToNodes [u, v, w, x, y, z] = [node3' u v w, node3' x y z]
listToNodes [t, u, v, w, x, y, z] = [node3' t u v, node2' w x, node2' y z]
listToNodes [s, t, u, v, w, x, y, z] = [node3' s t u, node2' v w, node3' x y z]
listToNodes [r, s, t, u, v, w, x, y, z] = [node3' r s t, node3' u v w, node3' x y z]
listToNodes [q, r, s, t, u, v, w, x, y, z] = [node3' q r s, node2' t u, node2' v w, node3' x y z]
listToNodes [p, q, r, s, t, u, v, w, x, y, z] = [node3' p q r, node3' s t u, node2' v w, node3' x y z]
listToNodes [o, p, q, r, s, t, u, v, w, x, y, z] = [node3' o p q, node3' r s t, node3' u v w, node3' x y z]
listToNodes [n, o, p, q, r, s, t, u, v, w, x, y, z] = [node3' n o p, node2' q r, node3' s t u, node2' v w, node3' x y z]
listToNodes [m, n, o, p, q, r, s, t, u, v, w, x, y, z] = [node3' m n o, node3' p q r, node2' s t, node3' u v w, node3' x y z]
listToNodes [l, m, n, o, p, q, r, s, t, u, v, w, x, y, z] = [node3' l m n, node3' o p q, node3' r s t, node3' u v w, node3' x y z]
listToNodes [k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z] = [node3' k l m, node3' n o p, node2' q r, node2' s t, node3' u v w, node3' x y z]
-- There is no way we can have more than 16 arguments here.
--
-- * On the first iteration, we could have as many as 8 elements just
-- from the digits.
--
-- * On the second iteration, we could have up to 16 elements total.
-- We group these 16 elements into nodes, and they could form as many
-- as 6 nodes.  These will be passed to the next iteration, but they
-- are already fewer than 8, so that that iteration can form only 5
-- nodes.
--
-- * This is the stable point: with 5 nodes recursively and 8 more at
-- the next level, 14 elements get mapped to 5 nodes again.
listToNodes _ = error "Data.FingerTree.listToNodes: excessively large (>16) argument!"

combine' :: Meas a v => FingerTree v a -> [a] -> FingerTree v a -> FingerTree v a
combine' Empty nds m2 = nds <<| m2
combine' m1 nds Empty = m1 |>> nds
combine' (Single a) nds m2 = a <| nds <<| m2
combine' m1 nds (Single z) = m1 |>> nds |> z
combine' (Deep _ l1 md1 r1) nds (Deep _ l2 md2 r2) = deep' l1 moar r2
  where
    moar = combine' md1 (listToNodes $ digitToList r1 ++ nds ++ digitToList l2) md2

combine :: Meas a v => FingerTree v a -> FingerTree v a -> FingerTree v a
combine Empty x = x
combine x Empty = x
combine (Single a) x = a <| x
combine x (Single a) = x |> a
combine x y = combine' x [] y

instance Meas a v => Monoid (FingerTree v a) where
  mempty = Empty
  mappend = combine

class Measured a where
  type Measure a :: *
  measure :: Monoid (Measure a) => a -> Measure a

-- instance (Measured a, Foldable f) => Measured (f a) where
--   type Measure (f a) = Measure a
--   measure = F.foldl' (\a x -> a <> measure x) mempty

instance Measured a => Measured (Digit a) where
  type Measure (Digit a) = Measure a
  measure = F.foldl' (\a x -> a <> measure x) mempty

instance Monoid v => Measured (Node v a) where
  type Measure (Node v a) = v
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
    summm = z <> measure mid

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
