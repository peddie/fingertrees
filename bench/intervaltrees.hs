{-# OPTIONS_GHC -Wall #-}

module Main where

import Criterion.Types
import Criterion.Main

import Control.DeepSeq.Generics
import Data.Monoid((<>))
import Data.List (foldl')
import System.Random

import qualified Data.Foldable as Fold

import qualified Data.FingerTree as F
import qualified Data.Interval as I
import qualified Data.FingerTree.IntervalMap as I

myConfig = defaultConfig {
             -- Always GC between runs.
             forceGC = True
             , timeLimit = 30.0
           }

benchLS :: NFData b => String -> (a -> b) -> a -> [Benchmark]
benchLS lbl v x = [
  bench ("nf-" ++ lbl) $ nf v x
  , bench ("lazy-" ++ lbl) $ whnf v x
  ]

-- benchN :: Show a => (String -> (v -> Benchmarkable) -> v -> [Benchmark])
--        -> String -> (v -> Benchmarkable) -> (a -> v) -> a -> [Benchmark]
benchN f lbl v i n = f name v (i n)
  where
    name = lbl ++ "(" ++ show n ++ ")"

benchS :: NFData b => String -> (a -> b) -> a -> [Benchmark]
benchS lbl v x = [bench lbl $ nf v x]

benchL :: NFData b => String -> (a -> b) -> a -> [Benchmark]
benchL lbl v x = [bench lbl $ whnf v x]

main = do
  putStr "Creating test structures . . . "
  let g = mkStdGen 22
  let rlist n = map (`mod` (n+1)) (take 10000 (randoms g)) :: [Int]
      r10 = rlist 10
      r100 = rlist 100
      r1000 = rlist 1000
  rnf [r10, r100, r1000] `seq` return ()
  putStr "random lists ready . . . "
  let tops n = map (abs . (`mod` (n+1))) (take 22000 (randoms (mkStdGen 22))) :: [Int]
      bottoms = take 22000 (randoms (mkStdGen 222))
      randintervals n = zipWith (\t b -> I.Interval (b `mod` (t + 1)) t) (tops n) bottoms
      i0 = I.fromFoldable . flip zip [1..] $ take 1000 $ randintervals 1000 :: I.IntervalMap Int Int
      idense = I.fromFoldable . flip zip [1..] $ take 1000 $ randintervals 100
      isparse = I.fromFoldable . flip zip [1..] $ take 100 $ randintervals 10000
      ri100 = getRandIntervals $ rlist 100 :: [I.Interval Int]
      ri1000 = getRandIntervals $ rlist 1000
      ri10000 = getRandIntervals $ rlist 10000
  rnf [i0, idense, isparse] `seq` return ()
  rnf [ri100, ri1000, ri10000] `seq` return ()
  putStr "random intervals ready . . . "
  putStrLn "done!"

  defaultMainWith myConfig [
    bgroup "insertion" (
       benchN benchLS "fromFoldable" I.fromFoldable listchar 100
       <> benchN benchLS "fromFoldable" I.fromFoldable listchar 1000
       <> benchN benchLS "fromFoldable" I.fromFoldable listchar 10000
       )
    , bgroup "intersections, 1k q" [
       bench "100 in [0, 10000]" $
       nf (map (I.intersections isparse)) (take 1000 ri10000)
       , bench "1000 in [0, 1000]" $
         nf (map (I.intersections i0)) (take 1000 ri1000)
       , bench "1000 in [0, 100]" $
         nf (map (I.intersections idense)) (take 1000 ri100)
       ]
    , bgroup "dominators, 1k q" [
       bench "100 in [0, 10000]" $
       nf (map (I.dominators isparse)) (take 1000 ri10000)
       , bench "1000 in [0, 1000]" $
         nf (map (I.dominators i0)) (take 1000 ri1000)
       , bench "1000 in [0, 100]" $
         nf (map (I.dominators idense)) (take 1000 ri100)
       ]
    , bgroup "contents, 1k q" [
       bench "100 in [0, 10000]" $
       nf (map (I.contents isparse)) (take 1000 ri10000)
       , bench "1000 in [0, 1000]" $
         nf (map (I.contents i0)) (take 1000 ri1000)
       , bench "1000 in [0, 100]" $
         nf (map (I.contents idense)) (take 1000 ri100)
       ]
    ]
  where
    getRandIntervals :: Ord a => [a] -> [I.Interval a]
    getRandIntervals lst = go [] lst
      where
        go acc (x:y:xs)
          | x > y     = go (I.Interval y x : acc) xs
          | otherwise = go (I.Interval x y : acc) xs
        go acc _ = acc
    intervalsUpTo n = do
      x <- [1..n]
      y <- [x..2 * n]
      return $ I.Interval x y
    listchar :: Int -> [(I.Interval Int, Char)]
    listchar n = force $ zip (intervalsUpTo n) (cycle ['a'..'z'])
