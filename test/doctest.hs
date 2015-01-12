module Main where

import Test.DocTest

main :: IO ()
main = doctest [ "src/Data/FingerTree.hs"
               , "src/Data/FingerTree/Sequence.hs"
               , "src/Data/FingerTree/PriorityQueue.hs"
               , "src/Data/FingerTree/OrderedSequence.hs"
               , "src/Data/FingerTree/IntervalTree.hs"
               ]
