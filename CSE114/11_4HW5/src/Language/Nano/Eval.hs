{-# LANGUAGE OverloadedStrings #-}

module Language.Nano.Eval
  ( execFile, execString, execExpr
  , eval, lookupId, prelude
  , parse
  , env0
  )
  where

import Control.Exception (throw, catch)
import Language.Nano.Types
import Language.Nano.Parser

--------------------------------------------------------------------------------
execFile :: FilePath -> IO Value
--------------------------------------------------------------------------------
execFile f = (parseFile f >>= execExpr) `catch` exitError

--------------------------------------------------------------------------------
execString :: String -> IO Value
--------------------------------------------------------------------------------
execString s = execExpr (parseString s) `catch` exitError

--------------------------------------------------------------------------------
execExpr :: Expr -> IO Value
--------------------------------------------------------------------------------
execExpr e = return (eval prelude e) `catch` exitError

--------------------------------------------------------------------------------
-- | `parse s` returns the Expr representation of the String s
--
-- >>> parse "True"
-- EBool True
--
-- >>> parse "False"
-- EBool False
--
-- >>> parse "123"
-- EInt 123
--
-- >>> parse "foo"
-- EVar "foo"
--
-- >>> parse "x + y"
-- EBin Plus (EVar "x") (EVar "y")
--
-- >>> parse "if x <= 4 then a || b else a && b"
-- EIf (EBin Le (EVar "x") (EInt 4)) (EBin Or (EVar "a") (EVar "b")) (EBin And (EVar "a") (EVar "b"))
--
-- >>> parse "if 4 <= z then 1 - z else 4 * z"
-- EIf (EBin Le (EInt 4) (EVar "z")) (EBin Minus (EInt 1) (EVar "z")) (EBin Mul (EInt 4) (EVar "z"))
--
-- >>> parse "let a = 6 * 2 in a /= 11"
-- ELet "a" (EBin Mul (EInt 6) (EInt 2)) (EBin Ne (EVar "a") (EInt 11))
--
-- >>> parseTokens "() (  )"
-- Right [LPAREN (AlexPn 0 1 1),RPAREN (AlexPn 1 1 2),LPAREN (AlexPn 3 1 4),RPAREN (AlexPn 6 1 7)]
--
-- >>> parse "f x"
-- EApp (EVar "f") (EVar "x")
--
-- >>> parse "(\\ x -> x + x) (3 * 3)"
-- EApp (ELam "x" (EBin Plus (EVar "x") (EVar "x"))) (EBin Mul (EInt 3) (EInt 3))
--
-- >>> parse "(((add3 (x)) y) z)"
-- EApp (EApp (EApp (EVar "add3") (EVar "x")) (EVar "y")) (EVar "z")
--
-- >>> parse <$> readFile "tests/input/t1.hs"
-- EBin Mul (EBin Plus (EInt 2) (EInt 3)) (EBin Plus (EInt 4) (EInt 5))
--
-- >>> parse <$> readFile "tests/input/t2.hs"
-- ELet "z" (EInt 3) (ELet "y" (EInt 2) (ELet "x" (EInt 1) (ELet "z1" (EInt 0) (EBin Minus (EBin Plus (EVar "x") (EVar "y")) (EBin Plus (EVar "z") (EVar "z1"))))))
--
-- >>> parse "1-2-3"
-- EBin Minus (EBin Minus (EInt 1) (EInt 2)) (EInt 3)
-- >>> parse "1+a&&b||c+d*e-f-g x"
-- EBin Or (EBin And (EBin Plus (EInt 1) (EVar "a")) (EVar "b")) (EBin Minus (EBin Minus (EBin Plus (EVar "c") (EBin Mul (EVar "d") (EVar "e"))) (EVar "f")) (EApp (EVar "g") (EVar "x")))
--
-- >>> parse "1:3:5:[]"
-- EBin Cons (EInt 1) (EBin Cons (EInt 3) (EBin Cons (EInt 5) ENil))
--
-- >>> parse "[1,3,5]"
-- EBin Cons (EInt 1) (EBin Cons (EInt 3) (EBin Cons (EInt 5) ENil))

--------------------------------------------------------------------------------
parse :: String -> Expr
--------------------------------------------------------------------------------
parse = parseString

exitError :: Error -> IO Value
exitError (Error msg) = return (VErr msg)

--------------------------------------------------------------------------------
-- | `eval env e` evaluates the Nano expression `e` in the environment `env`
--   (i.e. uses `env` for the values of the **free variables** in `e`),
--   and throws an `Error "unbound variable"` if the expression contains
--   a free variable that is **not bound** in `env`.
--
-- part (a)
--
-- >>> eval env0 (EBin Minus (EBin Plus "x" "y") (EBin Plus "z" "z1"))
-- 0
--
-- >>> eval env0 "p"
-- *** Exception: Error {errMsg = "unbound variable: p"}
--
-- part (b)
--
-- >>> eval []  (EBin Le (EInt 2) (EInt 3))
-- True
--
-- >>> eval []  (EBin Eq (EInt 2) (EInt 3))
-- False
--
-- >>> eval []  (EBin Eq (EInt 2) (EBool True))
-- False
--
-- >>> eval []  (EBin Lt (EInt 2) (EBool True))
-- *** Exception: Error {errMsg = "type error: binop"}
--
-- >>> let e1 = EIf (EBin Lt "z1" "x") (EBin Ne "y" "z") (EBool False)
-- >>> eval env0 e1
-- True
--
-- >>> let e2 = EIf (EBin Eq "z1" "x") (EBin Le "y" "z") (EBin Le "z" "y")
-- >>> eval env0 e2
-- False
--
-- part (c)
--
-- >>> let e1 = EBin Plus "x" "y"
-- >>> let e2 = ELet "x" (EInt 1) (ELet "y" (EInt 2) e1)
-- >>> eval [] e2
-- 3
--
-- part (d)
--
-- >>> eval [] (EApp (ELam "x" (EBin Plus "x" "x")) (EInt 3))
-- 6
--
-- >>> let e3 = ELet "h" (ELam "y" (EBin Plus "x" "y")) (EApp "f" "h")
-- >>> let e2 = ELet "x" (EInt 100) e3
-- >>> let e1 = ELet "f" (ELam "g" (ELet "x" (EInt 0) (EApp "g" (EInt 2)))) e2
-- >>> eval [] e1
-- 102
--
-- part (e)
-- |
-- >>> :{
-- eval [] (ELet "fac" (ELam "n" (EIf (EBin Eq "n" (EInt 0))
--                                  (EInt 1)
--                                  (EBin Mul "n" (EApp "fac" (EBin Minus "n" (EInt 1))))))
--             (EApp "fac" (EInt 10)))
-- :}
-- 3628800
--
-- part (f)
--
-- >>> let el = EBin Cons (EInt 1) (EBin Cons (EInt 2) ENil)
-- >>> execExpr el
-- (1 : (2 : []))
-- >>> execExpr (EApp "head" el)
-- 1
-- >>> execExpr (EApp "tail" el)
-- (2 : [])
--------------------------------------------------------------------------------
eval :: Env -> Expr -> Value -- need to pattern match all cases here
--------------------------------------------------------------------------------
eval env expr = case expr of
  EInt x-> VInt x -- needs to return a Int Value type
  EBool x->VBool x -- Needs to return a Bool Value type
  EVar x -> lookupId x env -- how we check to see if a variable is in an environment
  EBin binop e1 e2 -> evalOp binop (eval env e1) (eval env e2) -- all binops are evaluated and passed into evalOp
  EIf p t f -> case eval env p of -- probably could have done this cleaner but whatever
    VBool True -> (eval env t)
    VBool False -> (eval env f)
    _ -> throw (Error "type error")

  ELet id expr1 expr2 -> eval env' expr2 -- Evaluate e2 in extended environment where e1 has been evaluated
    where env' = (id, eval env expr1) : env
    
  ELam x e -> VClos env x e -- Means nothin on its own, need to capture environment in value

  EApp e1 e2 -> case (eval env e1) of
    VClos (closureEnv) (formal) (body) -> eval (((formal,(eval env e2)):closureEnv)++env) body --case where evaluation of e1 is a function 
    VPrim func -> func (eval env e2) --case where evaluation of e1 is VPrim (We just apply the prim)
    _->throw (Error "type error")
  ENil -> VNil -- Nil just returns Nil
--------------------------------------------------------------------------------
evalOp :: Binop -> Value -> Value -> Value 
--------------------------------------------------------------------------------
-- Implementing case where Bools are passed --------------------------------------
evalOp binop (VBool v1) (VBool v2) 
 | binop == Eq = VBool (v1 == v2)
 | binop == Ne = VBool (v1 /= v2)
 | binop == And = VBool (v1 && v2)
 | binop == Or = VBool (v1 || v2)
 | otherwise = throw (Error "type error:VBool")
 
--evalOp binop (VInt _) (VBool _) = throw (Error "Cannot match Bool and Int")
-- Implementing case where Ints are passed --------------------------------------
evalOp binop (VInt v1) (VInt v2) 
-- need to pattern match with VInts and VBools
 | binop == Plus = VInt (v1 + v2) 
 | binop == Minus = VInt (v1 - v2)
 | binop == Mul = VInt (v1 * v2)
 | binop == Div =VInt (v1 `div` v2)
 | binop == Lt = VBool (v1 < v2)
 | binop == Le = VBool (v1 <= v2)
 | binop == Eq = VBool (v1 == v2)
 | binop == Ne = VBool (v1 /= v2)
 | otherwise = throw (Error("type error:VInt"))
-- Implementing List functionality -------------------------------------
evalOp Eq VNil VNil = VBool True
evalOp Eq (VPair a b) (VPair c d) = if a==c && b==d then VBool True else VBool False 
evalOp Eq (VPair _ _) VNil = VBool False -- case where Vpair is compared to VNil
-- Implementing Cons Functionality ----------------------------------------
evalOp Cons (x) (VNil) = VPair (x) (VNil) -- case where only nil is passed
evalOp Cons (x) (VPair a b) =  VPair (x) (VPair (a) (b)) -- 
evalOp (_) (_) (_) = throw (Error "type error : NON-EXHAUSTIVE")
--------------------------------------------------------------------------------
-- | `lookupId x env` returns the most recent
--   binding for the variable `x` (i.e. the first
--   from the left) in the list representing the
--   environment, and throws an `Error` otherwise.
--
-- >>> lookupId "z1" env0
-- 0
-- >>> lookupId "x" env0
-- 1
-- >>> lookupId "y" env0
-- 2
-- >>> lookupId "mickey" env0
-- *** Exception: Error {errMsg = "unbound variable: mickey"}
--------------------------------------------------------------------------------
lookupId :: Id -> Env -> Value
--------------------------------------------------------------------------------
lookupId x [] = throw (Error ("unbound variable: " ++ x)) -- throw error if end of list is reached
lookupId x env = if (fst e) == x then (snd e) else lookupId x es
  where
    (e:es) = env -- search the env list for ID, return a number for every iteration

prelude :: Env
prelude =
  [ -- HINT: you may extend this "built-in" environment
    -- with some "operators" that you find useful...
    ("head", VPrim (\(VPair a _) -> a)), -- Head func
    ("tail", VPrim (\(VPair _ b) -> b)) -- Tail func
  ]

env0 :: Env
env0 =  [ ("z1", VInt 0)
        , ("x" , VInt 1)
        , ("y" , VInt 2)
        , ("z" , VInt 3)
        , ("z1", VInt 4)
        ]

--------------------------------------------------------------------------------
