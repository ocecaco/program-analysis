module Lib
    ( someFunc
    ) where

data AExp = AVar String
          | AConst Int
          | AOp AOp AExp AExp
          deriving (Eq, Ord, Show)

data AOp = Add | Mul | Sub | Div
         deriving (Eq, Ord, Show)

data BExp = BTrue
          | BFalse
          | BNot BExp
          | BOp BOp BExp BExp
          | BAOp BAOp BExp BExp
          deriving (Eq, Ord, Show)

data BOp = And | Or
         deriving (Eq, Ord, Show)

data BAOp = Equal | LessThan
          deriving (Eq, Ord, Show)

data Stmt = SAssign String AExp
          | SSkip
          | SSeq Stmt Stmt
          | SIf BExp Stmt Stmt
          | SWhile BExp Stmt
          deriving (Eq, Ord, Show)

someFunc :: IO ()
someFunc = putStrLn "someFunc"
