-- Bottom-Up Inductive Synthesizer with Elimination of Equivalents
-- Supports input/output examples of integer arithmetic
-- Generates programs using integers and +,-,*,/
-- Notable limitation: synthesized programs can only use integers 0-9

-- Broad strokes, I want to
--  - take input of a number of input/output examples
--  - parse these
--  - generate programs that satisfy them using the inductive synthesis method
--    with elimination of equivalents
--  - lazily print out valid programs that satisfy the examples until user stops it








-- Top-Down Explicit-Search Type-Directed Synthesis
-- TESTS
-- Supports input/output examples of integer arithmetic and lists
-- Only one example at a time, sorry. Lists are hard.

module Synth ( synthesize ) where

import qualified Data.Map as M
import Control.Monad.State.Lazy ( State(..)
                                , modify
                                , evalState
                                )

main = do
    (input :: Expr) <- read <$> getLine
    (output :: Expr) <- read <$> getLine
    putStrLn . showExpr $ synthesize (Example (input, output))

newtype Example = Example (Expr, Expr) deriving (Show, Read)

type Id = String

type Env = M.Map Id Type

data Type = IntT | BoolT | ListT Type | ArrT Type Type | AnyT
    deriving (Show, Read)

data IExpr = Add IExpr IExpr
           | Mul IExpr IExpr
           | Sub IExpr IExpr
           | Div IExpr IExpr
           | ILit Int
           | IVar Id
    deriving (Show, Read)

data BExpr = And BExpr BExpr
           | Or BExpr BExpr
           | Not BExpr
           | BLit Bool
           | GT IExpr IExpr
           | LT IExpr IExpr
           | EQ IExpr IExpr
           | BVar Id
    deriving (Show, Read)

data LExpr = Filter Expr Expr
           | Map Expr Expr
           | Foldl Expr Expr Expr
           | LLit [Expr]
           | LVar Id
    deriving (Show, Read)

data Expr = Lam Expr Expr
          | LExpr LExpr
          | IExpr IExpr
          | BExpr BExpr
    deriving (Show, Read)

type TExpr = (Type, Expr)

type Fresh = State Int  -- for generating unique binders

getFresh :: Fresh Id
getFresh = do
    i <- get
    modify (+1)
    return $ "x" ++ (show i)

showExpr :: Expr -> String
showExpr = undefined

synthesize :: Example -> Expr
synthesize (Example (input, output)) =
    let inputT = infer input
        outputT = infer output
        in evalState 0

-- don't worry about the holes
-- use haskell type constructors
-- do enumeration of the options using list comprehension

findExprOfType :: Type -> Fresh [Expr]
findExprOfType IntT =
    return $
        [ IExpr $ ILit i | i <- [0..9] ] ++
        concat [ map IExpr [Add x y, Mul x y, Sub x y, Div x y] |
                 x <- findExprOfType IntT, y <- findExprOfType IntT ]
findExprOfType BoolT =
    return $
        (BExpr $ BLit False) : (BExpr $ BLit True) :
        concat [ map BExpr [And x y, Or x y, Not x] |
                 x <- findExprOfType BoolT, y <- findExprOfType BoolT ] ++
        concat [ map BExpr [GT x y, LT x y, EQ x y] |
                 x <- findExprOfType IntT, y <- findExprOfType IntT ]
findExprOfType (ListT t) = do
    v <- getFresh
    return $
        (LExpr $ LLit []) :
        (LExpr $ Filter (LExpr $ Lam (LVar v) (findExprOfType BoolT))
        (LExpr $ Map (LExpr $ Lam (LVar v) (findExprOfType BoolT))
        (LExpr $ Foldl (LExpr $ Lam (LVar v) (findExprOfType BoolT))
findExprOfType AnyT = error "cannot generate infinite type..."

infer :: Expr -> Type
infer (Lam v e) = ArrT (infer v) (infer e)
infer (LExpr (Filter f xs)) = infer xs
infer (LExpr (Map f xs)) = let ArrT _ t = infer f in ListT t
infer (LExpr (Foldl f acc xs)) = let ArrT _ t = infer f in t
infer (LExpr (LLit [])) = ListT AnyT
infer (LExpr (LLit (x:xs))) = ListT (infer x)
infer (LExpr (LVar _)) = ListT AnyT
infer (IExpr _) = IntT
infer (BExpr _) = BoolT

-- (Lam (IExpr (IVar "x")) (IExpr (Add (ILit 1) (IVar "x"))))
