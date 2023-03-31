-- Top-Down Explicit-Search Type-Directed Synthesis
-- TESTS
-- Supports sets of input/output examples of Booleans and integers

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
import Data.Maybe               ( fromJust )

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

-- Simply-Typed Lambda Calculus
type Env = M.Map Id Expr

-- ArrT n t1 t2: n is maximum depth
-- i.e. a -> b has depth 1
--      a -> b -> c has depth 2
--      a -> (b -> c) -> d also has depth 2
-- types t1 and t2 are the input and ouput types (the first and last)
-- basically depth is the arity of the function after uncurrying
data Type = IntT | BoolT | ArrT Int Type Type
    deriving (Show, Read, Eq)

newtype Id = Id String deriving (Show, Read, Eq, Ord)

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
          | Hole Type
    deriving (Show, Read, Eq)

type Fresh = State Int  -- for generating unique binders

eval :: (Eq a) => Env -> Expr -> Maybe a
eval m e =
    case e of
        Var v -> M.lookup v m >>= \e -> eval m e
        Lam (v, t1) body ->
            (infer m e >>= \t2 ->
                guard (t1 == t2)
                >> (Just (\e -> fromJust $ eval (M.insert v e m) body)))
        BLit b -> Just b
        ILit i -> Just i
        Bin op e1 e2 ->
            case op of
                Equal -> do
                    t1 <- infer m e1
                    t2 <- infer m e2
                    guard (t1==t2)
                    (==) <$> eval m e1 <*> eval m e2
                Or  -> do
                    t1 <- infer m e1
                    t2 <- infer m e2
                    guard (all (==BoolT) [t1,t2])
                    (||) <$> eval m e1 <*> eval m e2
                And -> do
                    t1 <- infer m e1
                    t2 <- infer m e2
                    guard (all (==BoolT) [t1,t2])
                    (&&) <$> eval m e1 <*> eval m e2
                otherwise -> do
                    t1 <- infer m e1
                    t2 <- infer m e2
                    guard (all (==IntT) [t1,t2])
                    let f = case op of
                                Plus -> (+)
                                Minus -> (-)
                                Mult -> (*)
                                Div -> (div)
                                Greater -> (>)
                                Lesser -> (<)
                    f <$> eval m e1 <*> eval m e2
        Un Not e -> infer m e >>= \t -> guard (t==BoolT) >> not <$> eval m e
        App f a -> do
            ArrT n t1 t2 <- infer m f
            t3 <- infer m a
            guard (t1 == t3)
            eval m f <*> eval m a
        Hole t -> error "cannot evaluate typed hole"

getFresh :: Fresh Id
getFresh = do
    i <- get
    modify (+1)
    return . Id $ "x" ++ (show i)

infer :: Env -> Expr -> Maybe Type
infer m (Var v) = M.lookup v m >>= \e -> infer m e
infer _ (BLit _) = return BoolT
infer _ (ILit _) = return IntT
infer m (Lam (v,t) e) = infer m e >>= \t2 -> Just $ ArrT 1 t t2
infer m (App f a) = do
    ArrT n t1 t2 <- infer m f
    t3 <- infer m a
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
infer _ (Hole t) = return t

synthesize :: [Example] -> Expr
synthesize [] = error "no examples provided"
synthesize exs =
    let Example (i,o) = head exs
        -- maximum depth 5
        exprs = evalState (exprOfType (ArrT 5 (fromJust $ infer M.empty i) (fromJust $ infer M.empty o))) 0
        sat e = all (\(Example (i,o)) -> fromJust (eval M.empty (App e i)) == fromJust (eval M.empty o)) exs
        -- Remove holes?!
        goodExprs = filter sat exprs
    in head goodExprs

exprOfType :: Type -> Fresh [Expr]
exprOfType BoolT = return [ BLit False
                          , BLit True
                          , Hole BoolT
                          , Un Not (Hole BoolT)
                          , Bin Or (Hole BoolT) (Hole BoolT)
                          , Bin And (Hole BoolT) (Hole BoolT)
                          , Bin Greater (Hole IntT) (Hole IntT)
                          , Bin Lesser (Hole IntT) (Hole IntT)
                          , Bin Equal (Hole BoolT) (Hole BoolT)
                          , Bin Equal (Hole IntT) (Hole IntT)
                          , App (Hole $ ArrT 3 BoolT BoolT) (Hole BoolT)
                          , App (Hole $ ArrT 3 IntT BoolT) (Hole IntT)
                          ]
exprOfType IntT = return $ (ILit <$> [0..10]) ++
    [ Hole IntT
    , Bin Plus (Hole IntT) (Hole IntT)
    , Bin Minus (Hole IntT) (Hole IntT)
    , Bin Mult (Hole IntT) (Hole IntT)
    , Bin Div (Hole IntT) (Hole IntT)
    ]
exprOfType (ArrT n t1 t2) = undefined
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

-- (Lam (IExpr (IVar "x")) (IExpr (Add (ILit 1) (IVar "x"))))
