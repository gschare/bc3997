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
                                , get
                                )
import Control.Monad            ( unless
                                , guard
                                )

synthLoop :: [Example] -> IO ()
synthLoop exs = do
    s <- getLine
    unless (null s) $ do
        let (e :: Example) = Example . read $ s
        let exs' = e:exs
        putStrLn . show $ synthesize exs'
        synthLoop exs'

main = do
    synthLoop []

newtype Example = Example (Expr, Expr) deriving (Show, Read)

{-
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
           | Gt IExpr IExpr
           | Lt IExpr IExpr
           | Eq IExpr IExpr
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

-}

-- Simply-Typed Lambda Calculus
type TEnv = M.Map Id Type
type Env = M.Map Id Expr

data Type = IntT | BoolT | ArrT Type Type
    deriving (Show, Read, Eq)

newtype Id = Id String deriving (Show, Read, Eq)

data UnOp = Not
   deriving (Show, Read, Eq)

data BinOp = Plus
           | Minus
           | Mult
           | Div
           | Greater
           | Lesser
           | Equal
           | Or
           | And
   deriving (Show, Read, Eq)

data Expr = Var Id
          | Lam (Id, Type) Expr
          | App Expr Expr
          | BLit Bool
          | ILit Int
          | Bin BinOp Expr Expr
          | Un UnOp Expr
    deriving (Show, Read, Eq)

type Fresh = State Int  -- for generating unique binders

eval :: Env -> Expr -> Maybe a
eval m e =
    case e of
        Var v -> eval m <$> M.lookup v m
        Lam (v, t1) body ->
            (infer e >>= \t2 ->
                guard (t1 == t2)
                >> (\e -> eval (M.insert v e m) body))
        BLit b -> Just b
        ILit i -> Just i
        Bin op e1 e2 ->
            case op of
                Equal -> do
                    t1 <- infer e1
                    t2 <- infer e2
                    guard (t1==t2)
                    (==) <$> eval m e1 <*> eval m e2
                Or  -> do
                    t1 <- infer e1
                    t2 <- infer e2
                    guard (all (==BoolT) [t1,t2])
                    (||) <$> eval m e1 <*> eval m e2
                And -> do
                    t1 <- infer e1
                    t2 <- infer e2
                    guard (all (==BoolT) [t1,t2])
                    (&&) <$> eval m e1 <*> eval m e2
                otherwise -> do
                    t1 <- infer e1
                    t2 <- infer e2
                    guard (all (==IntT) [t1,t2])
                    let f = case op of
                                Plus -> (+)
                                Minus -> (-)
                                Mult -> (*)
                                Div -> (div)
                                Greater -> (>)
                                Lesser -> (<)
                    f <$> eval m e1 <*> eval m e2
        Un Not e -> infer e >>= \t -> guard (t==BoolT) >> Just . not <$> eval m e
        App f a -> do
            ArrT t1 t2 <- infer f
            t3 <- infer a
            guard (t1 == t3)
            eval m f <*> eval m a

getFresh :: Fresh Id
getFresh = do
    i <- get
    modify (+1)
    return . Id $ "x" ++ (show i)

infer :: TEnv -> Expr -> Maybe Type
infer m (Var v) = M.lookup v m
infer _ (BLit _) = return BoolT
infer _ (ILit _) = return IntT
infer m (Lam (v,t) e) = return <$> pure $ ArrT t <*> infer e
infer m (App f a) = do
    ArrT t1 t2 <- infer f
    t3 <- infer a
    guard (t1 == t3)
    return t2
infer _ (Un Not e) = return BoolT
infer _ (Bin Plus _ _) = return IntT
infer _ (Bin Minus _ _) = return IntT
infer _ (Bin Mult _ _) = return IntT
infer _ (Bin Div _ _) = return IntT
infer _ (Bin Greater _ _) = return BoolT
infer _ (Bin Lesser _ _) = return BoolT
infer _ (Bin Equal _ _) = return BoolT
infer _ (Bin Or _ _) = return BoolT
infer _ (Bin And _ _) = return BoolT

synthesize :: [Example] -> Expr
synthesize [] = error "no examples provided"
synthesize exs =
    let Example (i,o) = head exs
        exprs = exprOfType (ArrT (infer i) (infer o)) 0
        sat = all (\(Example (i,o)) -> eval M.empty i == o) exs
        goodExprs = filter sat exprs
    in head goodExprs

exprOfType :: Type -> Fresh [Expr]
exprOfType BoolT = return [False, True] -- TODO: primitives (And, Or, Not)
exprOfType IntT = return $ [0..] -- TODO: primitives (Plus, Minus, etc)
exprOfType (ArrT t1 t2) = undefined
    {-
    do v <- getFresh
        Lam (v, BoolT) 
        Lam (v, IntT)
        Lam (v, ArrT)
    -}
        -- TODO: bodies for various types using the previously-generated
        --       expressions
        -- TODO: something with typed holes to make it top-down?
        -- Maybe reorganize it instead of a function that returns expressions
        -- of types, have a function that returns primitives with holes, and
        -- then the synthesizer has a helper function that recursively fills in
        -- those holes by calling the primitive-hole generator.

{-
   Examples:
(BLit True, BLit False)
(BLit False, BLit True)
(BLit True, 
-}

{-
showExpr :: Expr -> String
showExpr = undefined

synthesize :: Example -> Expr
synthesize (Example (input, output)) =
    let inputT = infer input
        outputT = infer output
        in head $ evalState (findExprOfType $ ArrT inputT outputT) 0

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
        concat [ map BExpr [Gt x y, Lt x y, Eq x y] |
                 x <- findExprOfType IntT, y <- findExprOfType IntT ]
findExprOfType (ListT t) = do
    v <- getFresh
    return $
        [ (LExpr $ LLit [])
        --, (LExpr $ Filter (LExpr $ Lam (LVar v) (findExprOfType BoolT)))
        --, (LExpr $ Map (LExpr $ Lam (LVar v) (findExprOfType BoolT)))
        --, (LExpr $ Foldl (LExpr $ Lam (LVar v) (findExprOfType BoolT)))
        ]
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
-}

-- (Lam (IExpr (IVar "x")) (IExpr (Add (ILit 1) (IVar "x"))))
