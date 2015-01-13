{-# OPTIONS_GHC -Wall #-}

module Main where

import Criterion.Types
import Criterion.Main

import Control.DeepSeq.Generics
import Data.Monoid((<>))
import Data.List (foldl')
import System.Random

import qualified Data.Sequence as S
import qualified Data.Foldable as Fold

import qualified Data.FingerTree as F
import qualified Data.FingerTree.Sequence as FS

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
  let s10 = S.fromList [1..10] :: S.Seq Int
      s100 = S.fromList [1..100] :: S.Seq Int
      s1000 = S.fromList [1..1000] :: S.Seq Int
      fs10 = FS.fromFoldable [1..10] :: FS.Sequence Int
      fs100 = FS.fromFoldable [1..100]
      fs1000 = FS.fromFoldable [1..1000]
  rnf [s10, s100, s1000] `seq` return ()
  rnf [fs10, fs100, fs1000] `seq` return ()
  putStr "sequences ready . . . "
  let g = mkStdGen 22
  let rlist n = map (`mod` (n+1)) (take 10000 (randoms g)) :: [Int]
      r10 = rlist 10
      r100 = rlist 100
      r1000 = rlist 1000
  rnf [r10, r100, r1000] `seq` return ()
  putStr "random lists ready . . . "
  putStrLn "done!"

  defaultMainWith myConfig [
    bgroup "shuffle" (
     benchN benchS "MP" (shuffleFS r10) (const fs10) 10
     <> benchN benchS "MP" (shuffleFS r100) (const fs100) 100
     <> benchN benchS "containers" (shuffle r10) (const s10) 10
     <> benchN benchS "containers" (shuffle r100) (const s100) 100
     )
    ]

shuffle :: [Int] -> S.Seq Int -> Int
shuffle ps s = case S.viewl (S.drop (S.length s `div` 2) (foldl' cut s ps)) of
    x S.:< _ -> x
  where cut xs p = let (front, back) = S.splitAt p xs in back S.>< front

shuffleFS :: [Int] -> FS.Sequence Int -> Int
shuffleFS ps s = case FS.viewL (FS.drop (FS.length s `div` 2) (foldl' cut s ps)) of
    x F.:< _ -> x
  where
    cut :: FS.Sequence Int -> Int -> FS.Sequence Int
    cut xs p = let (front, back) = FS.splitAt p xs in back <> front
