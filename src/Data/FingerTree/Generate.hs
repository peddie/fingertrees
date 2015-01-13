module Data.FingerTree.Generate where


import Prelude hiding (print)
import Data.List
import Control.Applicative
import Control.Monad (replicateM, guard, when)
import qualified Data.Traversable as Trav
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Class

data Digit = One | Two | Three | Four deriving (Eq, Ord, Show, Enum, Bounded)

indices = [(One, 1), (Two, 2), (Three, 3), (Four, 4)]

globalNames = ['a'..]

print x = lift $ tell [x]
-- printN = lift . tell

-- renderMatch :: Digit -> StateT String (Writer [String]) ()
-- renderMatch c = do
--   print "("
--   render c
--   print ")"

renderD :: Digit -> StateT String (Writer [String]) Int
renderD c = do
  names <- replicateM count getName
  print $ "(" ++ intercalate " " (show c : names) ++ ")"
  return count
  where
    count = case lookup c indices of Just x -> x

getName :: StateT String (Writer [String]) String
getName = do
  names <- get
  put (tail names)
  return $ [head names]

printName :: StateT String (Writer [String]) ()
printName = getName >>= print

firstTree = print "tree1"
secondTree = print "tree2"

eval prog = intercalate " " . execWriter $ runStateT prog globalNames

data Node = Node3 | Node2 deriving (Eq, Ord, Show, Enum, Bounded)

nodeIndices = [(Node3, 3), (Node2, 2)]

renderN c = do
  names <- replicateM count getName
  print $ "(" ++ intercalate " " (funName : names) ++ ")"
  where
    count = case lookup c nodeIndices of Just x -> x
    funName = "node" ++ show count ++ "'"

generateNodes n
  | n == 11 = Node2 : Node2 : Node3 : Node2 : [Node2]
  | n > 7 = Node3 : generateNodes (n - 6) ++ [Node3]
  | n > 6 = Node2 : generateNodes (n - 4) ++ [Node2]
  | n > 4 = Node3 : generateNodes (n - 3)
  | n == 4 = Node2 : [Node2]
  | n == 3 = [Node3]
  | n == 2 = [Node2]

data Tree = Empty | Single | Deep deriving (Eq, Ord, Show, Enum, Bounded)

renderT Empty _ = do
  print $ show Empty
  return 0
renderT Single nm = do
  print $ "(" ++ show Single ++ " " ++ nm ++ ")"
  return 1
renderT Deep nm = do
  print $ parens (intercalate " " $ [show Deep, 'v':nm, 'l':nm, 'm':nm, 'r':nm])
  return 1

matchTemplate n d1 d2 = do
  print $ "combine" ++ show n
  firstTree
  da <- renderD d1
  replicateM n printName
  db <- renderD d2
  secondTree
  return $ da + n + db

callTemplate nval = do
  print $ "build" ++ show nnodes
  firstTree
  mapM_ renderN nodes
  secondTree
  where
    nodes = generateNodes nval
    nnodes = length nodes

lineTemplate n d1 d2 = do
  nval <- matchTemplate n d1 d2
  put globalNames
  print "="
  callTemplate nval

templatesCombine' n = do
  d1 <- [minBound..maxBound]
  d2 <- [minBound..maxBound]
  return . eval $ lineTemplate n d1 d2

combineTypeTemplate n = do
  print $ "combine" ++ show n ++ " ::"
  print "Meas a v => FingerTree v (Node v a) -> Digit a ->"
  replicateM n $ print "a ->"
  print "Digit a -> FingerTree v (Node v a) -> FingerTree v (Node v a)"

templatesCombine = do
  n <- [0..5]
  let ty = eval $ combineTypeTemplate n
      terms = templatesCombine' n
  return $ "\n" : ty : terms

parens str = "(" ++ str ++ ")"

treeTemplate n Empty _ = do
  ns <- replicateM (n + 1) getName
  print $ show Empty
  mapM_ print ns
  print "="
  print $ intercalate " <| " ns
treeTemplate n _ Empty = do
  ns <- replicateM (n + 1) getName
  mapM_ print ns
  print $ show Empty
  print "="
  print $ intercalate " |> " ns
treeTemplate n Single _ = do
  ns <- replicateM (n + 2) getName
  renderT Single (head ns)
  mapM_ print (tail ns)
  print "="
  print $ intercalate " <| " ns
treeTemplate n _ Single = do
  ns <- replicateM (n + 2) getName
  mapM_ print (init ns)
  renderT Single (last ns)
  print "="
  print $ intercalate " |> " ns
treeTemplate n Deep Deep = do
  ns <- replicateM (n + 2) getName
  let taname = head ns
      tbname = last ns
      nodes = take n $ tail ns
      mid = middle taname nodes tbname
      val = value taname nodes tbname
  renderT Deep taname
  mapM_ print (init $ tail ns)
  renderT Deep tbname
  print "="
  print $ intercalate " " $ ["Deep", val, 'l':taname, mid, 'r':tbname]
  where
    middle taname nodes tbname = let n = length nodes in
      parens $ intercalate " " $
      ["combine" ++ show n, 'm':taname, 'r':taname] ++
      nodes ++
      ['l':tbname, 'm':tbname]
    value taname nodes tbname = parens $ intercalate " <> " $ ['v':taname] ++ map ("measure " ++) nodes ++ ['v':tbname]

treeTypeTemplate n = do
  print $ "build" ++ show n ++ " ::"
  print "Meas a v => FingerTree v a ->"
  replicateM n $ print "a ->"
  print "FingerTree v a -> FingerTree v a"

templatesTree' n = do
  t1 <- [minBound..maxBound]
  t2 <- [minBound..maxBound]
  return . eval $ print ("build" ++ show n) >> treeTemplate n t1 t2

templatesTree = do
  n <- [0..5]
  let ty = eval $ treeTypeTemplate n
      terms = templatesTree' n
  return $ "\n" : ty : nub terms

header = [ "{-# LANGUAGE ConstraintKinds #-}"
         , "{-# LANGUAGE TypeFamilies #-}"
         , ""
         , "module Data.FingerTree.Gen where"
         , ""
         , "import Data.Monoid ((<>))"
         , "import Data.FingerTree (Digit(..), Node(..), FingerTree(..), Measured(..), Meas(..), (<|), (|>), node2', node3')"
         ]

generate = writeFile "src/Data/FingerTree/Gen.hs" $ unlines $
           header ++ concat templatesTree ++ concat templatesCombine
