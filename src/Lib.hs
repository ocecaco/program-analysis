{-# LANGUAGE ScopedTypeVariables #-}
module Lib
    ( someFunc
    ) where

import Control.Monad.State
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as S
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
assignLabels origStmt = evalState (go origStmt) 1
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

class Eq lat => CompleteLattice lat where
  bottom :: lat
  combine :: lat -> lat -> lat

data MonotoneFramework lat = MonotoneFramework
  { flows :: [(Int, Int)]
  , extremal :: [Int]
  , extremalValue :: lat
  , transfer :: Int -> (lat -> lat)
  }

-- uses worklist algorithm
solveFramework :: forall lat. CompleteLattice lat => MonotoneFramework lat -> Map Int (lat, lat)
solveFramework fw = present (go (flows fw) initialAnalysis)
  where initialValue :: Int -> lat
        initialValue i
          | i `elem` extremal fw = extremalValue fw
          | otherwise = bottom

        initialAnalysis :: Map Int lat
        initialAnalysis = M.fromList (fromFlow ++ fromExtremal)
          where fromFlow = [ (i, initialValue i) | (a, b) <- flows fw, i <- [a, b] ]
                fromExtremal = [ (i, initialValue i) | i <- extremal fw ]

        -- bit of a hack, but the mapping should always contain a
        -- value for the items we look up in it
        analysisValue :: Ord k => Map k v -> k -> v
        analysisValue mapping i = fromJust (M.lookup i mapping)

        successorFlows :: Int -> [(Int, Int)]
        successorFlows i = [ edge | edge@(source, _) <- flows fw, source == i ]

        go :: [(Int, Int)] -> Map Int lat -> Map Int lat
        go [] analysis = analysis -- TODO: also put the block exit analysis value
        go ((source, target):remaining) analysisOld
          -- if nothing changes in the analysis value of the target
          -- node, no need to propagate any changes
          | targetUpdated == targetOld = go remaining analysisOld
          -- otherwise propagate the changes
          | otherwise = go (successorFlows target ++ remaining) analysisNew
          where transferResults = transfer fw source (analysisValue analysisOld source)
                targetOld = analysisValue analysisOld target
                targetUpdated = targetOld `combine` transferResults
                analysisNew = M.insert target targetUpdated analysisOld

        present :: Map Int lat -> Map Int (lat, lat)
        present analysis = M.fromList
          [ (i, (entryValue, exitValue))
          | (i, entryValue) <- M.toList analysis
          , let exitValue = transfer fw i entryValue ]

-- analysis values for reaching definitions:
-- mapping from variable name to the places where it might have
-- received its value. The value None indicates that the variable
-- is potentially uninitialized
newtype RD = RD (Map String (Set (Maybe Int)))
        deriving (Eq, Show)

instance CompleteLattice RD where
  bottom = RD M.empty
  combine (RD a1) (RD a2) = RD (M.unionWith S.union a1 a2)

freeVariablesAExp :: AExp -> [String]
freeVariablesAExp (AVar name) = [name]
freeVariablesAExp (AConst _) = []
freeVariablesAExp (AOp _ a1 a2) = freeVariablesAExp a1 ++ freeVariablesAExp a2

freeVariablesBExp :: BExp -> [String]
freeVariablesBExp BTrue = []
freeVariablesBExp BFalse = []
freeVariablesBExp (BNot b) = freeVariablesBExp b
freeVariablesBExp (BOp _ b1 b2) = freeVariablesBExp b1 ++ freeVariablesBExp b2
freeVariablesBExp (BAOp _ a1 a2) = freeVariablesAExp a1 ++ freeVariablesAExp a2

freeVariablesStmt :: Stmt a -> [String]
freeVariablesStmt (SAssign _ name _) = [name]
freeVariablesStmt (SSkip _) = []
freeVariablesStmt (SSeq s1 s2) = freeVariablesStmt s1 ++ freeVariablesStmt s2
freeVariablesStmt (SIf _ test s1 s2) = freeVariablesBExp test ++ freeVariablesStmt s1 ++ freeVariablesStmt s2
freeVariablesStmt (SWhile _ test body) = freeVariablesBExp test ++ freeVariablesStmt body

reachingDefinitions :: Stmt Int -> Map Int (RD, RD)
reachingDefinitions stmt = solveFramework framework
  where flowGraph = determineFlowGraph stmt
        extval = RD (M.fromList [ (name, S.singleton Nothing) | name <- freeVariablesStmt stmt ])

        trans :: Int -> (RD -> RD)
        trans i r@(RD rdOld) = case block of
          -- skip and test don't do anything to the definitions
          BasicSkip -> r
          BasicTest _ -> r
          -- for an assignment, replace all definitions for our name
          -- with just our label
          BasicAssign name _ -> RD (M.insert name (S.singleton (Just i)) rdOld)
          where -- it's probably inefficient to do this lookup every
                -- time a transfer function gets called
                Just block = lookup i (vertices flowGraph)

        framework = MonotoneFramework
          { flows = edges flowGraph
          , extremal = [initialLabel stmt]
          , extremalValue = extval
          , transfer = trans
          }

someFunc :: IO ()
someFunc = do
  let stmt1 = SAssign () "x" (AConst 5)
  let stmt2 = SAssign () "y" (AConst 1)
  let stmt3 = BAOp OpLessThan (AConst 1) (AVar "x")
  let stmt4 = SAssign () "y" (AOp OpMul (AVar "x") (AVar "y"))
  let stmt5 = SAssign () "x" (AOp OpSub (AVar "x") (AConst 1))
  let prog = SSeq stmt1 (SSeq stmt2 (SWhile () stmt3 (SSeq stmt4 stmt5)))
  let labeled = assignLabels prog
  let graph = determineFlowGraph labeled
  putStrLn "Vertices: "
  forM_ (vertices graph) print
  putStrLn "Edges: "
  forM_ (edges graph) print

  putStrLn ""
  forM_ (M.toList (reachingDefinitions labeled)) $ \(node, (RD before, RD after)) -> do
    putStrLn ("node: " ++ show node)
    putStrLn "before: "
    forM_ (M.toList before) $ \(name, reaching) ->
      putStrLn (name ++ ": " ++ show reaching)
    putStrLn "after: "
    forM_ (M.toList after) $ \(name, reaching) ->
      putStrLn (name ++ ": " ++ show reaching)
    putStrLn ""
