module Lib
    ( someFunc
    ) where

import Control.Monad.State
import Control.Monad

data AExp = AVar String
          | AConst Int
          | AOp AOp AExp AExp
          deriving (Eq, Ord, Show)

data AOp = OpAdd | OpMul | OpSub | OpDiv
         deriving (Eq, Ord, Show)

data BExp = BTrue
          | BFalse
          | BNot BExp
          | BOp BOp BExp BExp
          | BAOp BAOp AExp AExp
          deriving (Eq, Ord, Show)

data BOp = And | Or
         deriving (Eq, Ord, Show)

data BAOp = OpEqual | OpLessThan
          deriving (Eq, Ord, Show)

data Stmt label = SAssign label String AExp
                | SSkip label
                | SSeq (Stmt label) (Stmt label)
                | SIf label BExp (Stmt label) (Stmt label)
                | SWhile label BExp (Stmt label)
                deriving (Eq, Ord, Show)

data BasicStmt = BasicTest BExp
               | BasicAssign String AExp
               | BasicSkip
               deriving (Eq, Ord, Show)

assignLabels :: Stmt () -> Stmt Int
assignLabels origStmt = evalState (go origStmt) 0
  where freshLabel :: State Int Int
        freshLabel = do
          i <- get
          put (i + 1)
          return i

        go :: Stmt () -> State Int (Stmt Int)
        go (SAssign () name expr) = SAssign <$> freshLabel <*> pure name <*> pure expr
        go (SSkip ()) = SSkip <$> freshLabel
        go (SSeq s1 s2) = SSeq <$> go s1 <*> go s2
        go (SIf () test s1 s2) = SIf <$> freshLabel <*> pure test <*> go s1 <*> go s2
        go (SWhile () test body) = SWhile <$> freshLabel <*> pure test <*> go body

data FlowGraph = FlowGraph { vertices :: [(Int, BasicStmt)], edges :: [(Int, Int)] }
               deriving (Eq, Ord, Show)

initialLabel :: Stmt Int -> Int
initialLabel (SAssign i _ _) = i
initialLabel (SSkip i) = i
initialLabel (SSeq s1 _) = initialLabel s1
initialLabel (SIf i _ _ _) = i
initialLabel (SWhile i _ _) = i

finalLabels :: Stmt Int -> [Int]
finalLabels (SAssign i _ _) = [i]
finalLabels (SSkip i) = [i]
finalLabels (SSeq _ s2) = finalLabels s2
finalLabels (SIf _ _ s1 s2) = finalLabels s1 ++ finalLabels s2
finalLabels (SWhile i _ _) = [i]

blocks :: Stmt Int -> [(Int, BasicStmt)]
blocks (SAssign i name expr) = [(i, BasicAssign name expr)]
blocks (SSkip i) = [(i, BasicSkip)]
blocks (SSeq s1 s2) = blocks s1 ++ blocks s2
blocks (SIf i test s1 s2) = (i, BasicTest test) : blocks s1 ++ blocks s2
blocks (SWhile i test body) = (i, BasicTest test) : blocks body

flowEdges :: Stmt Int -> [(Int, Int)]
flowEdges (SAssign _ _ _) = []
flowEdges (SSkip _) = []
flowEdges (SSeq s1 s2) = flowEdges s1 ++ flowEdges s2 ++ internalEdges
  where internalEdges = [ (f, next) | let next = initialLabel s2, f <- finalLabels s1 ]
flowEdges (SIf i _ s1 s2) = flowEdges s1 ++ flowEdges s2 ++ [(i, initialLabel s1), (i, initialLabel s2)]
flowEdges (SWhile i _ body) = flowEdges body ++ [(i, initialLabel body), (initialLabel body, i)]

determineFlowGraph :: Stmt Int -> FlowGraph
determineFlowGraph stmt = FlowGraph { vertices = blocks stmt, edges = flowEdges stmt }

someFunc :: IO ()
someFunc = do
  let prog = SIf () (BAOp OpEqual (AVar "x") (AVar "x")) (SAssign () "x" (AConst 3)) (SAssign () "x" (AConst 4))
  let labeled = assignLabels prog
  let graph = determineFlowGraph labeled
  putStrLn "Vertices: "
  forM_ (vertices graph) print
  putStrLn "Edges: "
  forM_ (edges graph) print
