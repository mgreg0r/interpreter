module Exec where

import System.IO
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Map as Map
import AbsGrammar

exec :: Stmt -> IO ()
exec s = do
  result <- runExceptT (execStateT(runReaderT (evalStmt s) (Map.empty, Map.empty, VoidValue)) Map.empty)
  case result of
    Left e -> hPutStrLn stderr ("ERROR: " ++ e)
    Right _ -> return ()


-- TYPES
type ResultT = ReaderT Env (StateT Store (ExceptT String IO))
data FuncDescriptor = Func Type Ident [Arg] Block Env
type VarEnv = Map.Map Ident Int
type FuncEnv = Map.Map Ident FuncDescriptor
type Env = (VarEnv, FuncEnv, Value)
type Store = Map.Map Int Value

data Value = StringValue String | IntValue Integer | BoolValue Bool | VoidValue deriving(Read, Show, Eq, Ord) 

-- Eval statements
evalStmt :: Stmt -> ResultT Env
evalStmt Empty = do
  env <- ask
  return env

evalStmt (ExpStmt e) = do
  env <- ask
  evalExpr e
  return env

evalStmt (Print e) = do
  val <- evalExpr e
  case val of
    StringValue s -> liftIO $ print s
    IntValue n -> liftIO $ print n
    BoolValue b -> liftIO $ print b
  env <- ask
  return env

evalStmt (BStmt b) = do
  (vEnv, fEnv, retVal) <- ask
  (_, _, newVal) <- evalBlock b
  return (vEnv, fEnv, retVal)

evalStmt (VarDecl t name) = do
  (eVar, eFunc, retVal) <- ask
  state <- get
  let location = Map.size state
  modify (Map.insert location (defaultValue t))
  return ((Map.insert name location eVar), eFunc, retVal)

evalStmt (VarAsgn ident e) = do
  (eVar, eFunc, retVal) <- ask
  state <- get
  let location = eVar Map.! ident
  value <- evalExpr e
  modify (Map.insert location value)
  return (eVar, eFunc, retVal)

evalStmt (Cond e s) = do
  (eVar, eFunc, retVal) <- ask
  value <- evalExpr e
  if value == (BoolValue True) then do
    (_, _, newVal) <- evalBlock s
    return (eVar, eFunc, newVal)
  else do
    return (eVar, eFunc, retVal)

evalStmt (CondElse e s1 s2) = do
  (eVar, eFunc, retVal) <- ask
  value <- evalExpr e
  if value == (BoolValue True) then do
    (_, _, newVal) <- evalBlock s1
    return (eVar, eFunc, newVal)
  else do
    (_, _, newVal) <- evalBlock s2
    return (eVar, eFunc, newVal)

evalStmt (While e s) = do
  (eVar, eFunc, retVal) <- ask
  value <- evalExpr e
  if value == (BoolValue True) then do
    (_, _, newVal) <- evalBlock s
    (_, _, finalVal) <- local (\_ -> (eVar, eFunc, newVal)) (evalStmt (While e s))
    return (eVar, eFunc, finalVal)
  else do
    return (eVar, eFunc, retVal)
    
evalStmt (FnDecl t name args block) = do
  (eVar, eFunc, retVal) <- ask
  return (eVar, Map.insert name (Func t name args block (eVar, eFunc, VoidValue)) eFunc, retVal)

evalStmt (Ret e) = do
  (eVar, eFunc, _) <- ask
  value <- evalExpr e
  return (eVar, eFunc, value)

evalStmt VRet = do
  env <- ask
  return env

-- Eval block
evalBlock :: Block -> ResultT Env
evalBlock (BBlock []) = do
  env <- ask
  return env

evalBlock (BBlock (s:t)) = do
  env <- evalStmt s
  nextEnv <- local(\_ -> env) (evalBlock (BBlock t))
  return nextEnv

-- Eval expressions
evalExpr :: Expr -> ResultT Value
evalExpr (EString s) = return (StringValue s)
evalExpr (ELitInt n) = return (IntValue n)
evalExpr (ELitTrue) = return (BoolValue True)
evalExpr (ELitFalse) = return (BoolValue False)

evalExpr (Neg e) = do
  (IntValue v) <- evalExpr e
  return (IntValue (-v))

evalExpr (Not e) = do
  (BoolValue v) <- evalExpr e
  return (BoolValue (not v))

evalExpr (EVar ident) = do
  (eVar, _, _) <- ask
  state <- get
  let location = eVar Map.! ident
  let value = state Map.! location
  return value

evalExpr (EAdd e1 o e2) = do
  (IntValue v1) <- evalExpr e1
  (IntValue v2) <- evalExpr e2
  case o of
    Plus -> return (IntValue (v1 + v2))
    Minus -> return (IntValue (v1 - v2))

evalExpr (EMul e1 o e2) = do
  (IntValue v1) <- evalExpr e1
  (IntValue v2) <- evalExpr e2
  case o of
    Times -> return (IntValue (v1 * v2))
    Div ->  if v2 == 0 then throwError $ "Division by zero" else return (IntValue (div v1 v2))
    Mod -> return (IntValue (mod v1 v2))

evalExpr (EAnd e1 e2) = do
  (BoolValue v1) <- evalExpr e1
  (BoolValue v2) <- evalExpr e2
  return (BoolValue (v1 && v2))

evalExpr (EOr e1 e2) = do
  (BoolValue v1) <- evalExpr e1
  (BoolValue v2) <- evalExpr e2
  return (BoolValue (v1 || v2))

evalExpr (ERel e1 o e2) = do
  v1 <- evalExpr e1
  v2 <- evalExpr e2
  case o of
    EQU -> return (BoolValue (v1 == v2))
    NE -> return (BoolValue (v1 /= v2))
    LTH -> return (BoolValue (v1 < v2))
    LE -> return (BoolValue (v1 <= v2))
    GTH -> return (BoolValue (v1 > v2))
    GE -> return (BoolValue (v1 >= v2))

evalExpr (EApp ident exprs) = do
  (eVar, eFunc, _) <- ask
  state <- get
  argValues <- mapM evalExpr exprs
  let (Func fType fName fArgs fBlock (fVarEnv, fFuncEnv, _)) = eFunc Map.! ident
  let args = packArgs fArgs exprs argValues
  let (valArgs, refArgs) = splitArgs args  
  let locations = assignLocations (Map.size state) (length valArgs)
  modify (\_ -> (Map.union state (Map.fromList (zip locations (map (\(_, _, val) -> val) valArgs)))))
  let envWithValueArgs = addValueArgs fVarEnv valArgs locations
  let envWithRefArgs = addRefArgs eVar envWithValueArgs refArgs
  (_, _, retValue) <- local(\_ -> (envWithRefArgs, (Map.insert fName (Func fType fName fArgs fBlock (fVarEnv, fFuncEnv, VoidValue)) fFuncEnv), VoidValue)) (evalBlock (fBlock))
  if retValue == VoidValue && fType /= Void then return (defaultValue fType)
  else return retValue


-- helpers

assignLocations :: Int -> Int -> [Int]
assignLocations from count = if count <= 0 then [] else from:(assignLocations (from+1) (count-1))

packArgs :: [Arg] -> [Expr] -> [Value] -> [(Arg, Expr, Value)]
packArgs [] [] [] = []
packArgs (ah:at) (eh:et) (vh:vt) = (ah, eh, vh):(packArgs at et vt)

splitArgs :: [(Arg, Expr, Value)] -> ([(Arg, Expr, Value)], [(Arg, Expr, Value)])
splitArgs [] = ([], [])
splitArgs ((a, e, v):r) = let (valArgs, refArgs) = splitArgs r in 
  case (a, e) of
    ((RefArg t i), (EVar _)) -> (valArgs, (((RefArg t i), e ,v):refArgs))  -- ref args that are more complicated expressions are treated as value args
    ((ValArg t i), _) -> ((((ValArg t i), e, v):valArgs), refArgs)
    ((RefArg t i), _) -> ((((ValArg t i), e, v):valArgs), refArgs)

addValueArgs :: Map.Map Ident Int -> [(Arg, Expr, Value)] -> [Int] -> Map.Map Ident Int
addValueArgs env args locations = Map.union (Map.fromList (zip (map mapArgToEnv args) locations)) env

addRefArgs :: Map.Map Ident Int -> Map.Map Ident Int -> [(Arg, Expr, Value)] -> Map.Map Ident Int
addRefArgs env fEnv args = Map.union (Map.fromList (map (mapRefArg env) args)) fEnv

mapArgToEnv :: (Arg, Expr, Value) -> Ident
mapArgToEnv ((ValArg _ n), _, _) = n

mapRefArg :: Map.Map Ident Int -> (Arg, Expr, Value) -> (Ident, Int)
mapRefArg env ((RefArg t newIdent), (EVar orgIdent), _) = (newIdent, env Map.! orgIdent)


-- Default values
defaultValue :: Type -> Value
defaultValue Int = IntValue 0
defaultValue Str = StringValue ""
defaultValue Bool = BoolValue False
defaultValue Void = VoidValue

