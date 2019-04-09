{-# LANGUAGE ScopedTypeVariables #-}
module Lib
    ( someFunc
    ) where

import Control.Monad.State
import Control.Monad
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Maybe

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

class Ord lat => CompleteLattice lat where
  bottom :: lat
  combine :: lat -> lat -> lat

data MonotoneFramework lat = MonotoneFramework
  { flowGraph :: [(Int, Int)]
  , extremal :: [Int]
  , extremalValue :: lat
  , transfer :: Int -> (lat -> lat)
  }

-- uses worklist algorithm
solveFramework :: forall lat. CompleteLattice lat => MonotoneFramework lat -> Map Int (lat, lat)
solveFramework fw = present (go (flowGraph fw) initialAnalysis)
  where initialValue :: Int -> lat
        initialValue i
          | i `elem` extremal fw = extremalValue fw
          | otherwise = bottom

        initialAnalysis :: Map Int lat
        initialAnalysis = M.fromList (fromFlow ++ fromExtremal)
          where fromFlow = [ (i, initialValue i) | (a, b) <- flowGraph fw, i <- [a, b] ]
                fromExtremal = [ (i, initialValue i) | i <- extremal fw ]

        -- bit of a hack, but the mapping should always contain a
        -- value for the items we look up in it
        analysisValue :: Ord k => Map k v -> k -> v
        analysisValue mapping i = fromJust (M.lookup i mapping)

        successorFlows :: Int -> [(Int, Int)]
        successorFlows i = [ edge | edge@(source, _) <- flowGraph fw, source == i ]

        go :: [(Int, Int)] -> Map Int lat -> Map Int lat
        go [] analysis = analysis -- TODO: also put the block exit analysis value
        go ((source, target):remaining) analysisOld
          -- ignore the results of the transfer function if they do
          -- not give better information than we already had for the
          -- target of this flow
          | transferResults <= targetOld = go remaining analysisOld
          -- otherwise propagate the changes
          | otherwise = go (successorFlows target ++ remaining) analysisNew
          where transferResults = transfer fw source (analysisValue analysisOld source)
                targetOld = analysisValue analysisOld target
                targetUpdated = targetOld `combine` transferResults
                analysisNew = M.insert target targetUpdated analysisOld

        present :: Map Int lat -> Map Int (lat, lat)
        present analysis = M.fromList [ (i, (entryValue, exitValue)) | (i, entryValue) <- M.toList analysis, let exitValue = transfer fw i entryValue ]

someFunc :: IO ()
someFunc = do
  let prog = SIf () (BAOp OpEqual (AVar "x") (AVar "x")) (SAssign () "x" (AConst 3)) (SAssign () "x" (AConst 4))
  let labeled = assignLabels prog
  let graph = determineFlowGraph labeled
  putStrLn "Vertices: "
  forM_ (vertices graph) print
  putStrLn "Edges: "
  forM_ (edges graph) print
