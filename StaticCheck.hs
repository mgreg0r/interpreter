module StaticCheck where

import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Identity
import qualified Data.Map as Map
import AbsGrammar

type VarMap = Map.Map Ident Type
type FuncMap = Map.Map Ident FuncDescriptor
data FuncDescriptor = Func Type [Arg]
type Env = (VarMap, FuncMap, Type)
type ResultT = ReaderT Env (ExceptT String Identity)
data CheckResult = OK | Fail String

staticCheck :: Stmt -> CheckResult
staticCheck s = case runExceptT (runReaderT (evalStmt s) (Map.empty, Map.empty, Void)) of
  Identity (Left e) -> Fail e
  Identity (Right _) -> OK

evalStmt :: Stmt -> ResultT Env
evalStmt Empty = do
  env <- ask
  return env

evalStmt (BStmt block) = evalBlock block

evalStmt (ExpStmt e) = do
  env <- ask
  evalExpr e
  return env

evalStmt (VarDecl t name) = do
  (varEnv, funEnv, retType) <- ask
  return (Map.insert name t varEnv, funEnv, retType)

evalStmt (VarAsgn ident expr) = do
  (varEnv, funEnv, retType) <- ask
  exprType <- evalExpr expr
  if Map.member ident varEnv then do
    let varType = varEnv Map.! ident
    if varType == exprType then return (varEnv, funEnv, retType) else throwError $ "type " ++ show varType ++ " is incopatible with type " ++ show exprType
  else throwError $ "Undefined variable: " ++ show ident

evalStmt (Print expr) = do
  env <- ask
  exprType <- evalExpr expr
  if exprType == Void then throwError $ "Cannot print void type" else return env

evalStmt (Cond expr block) = do
  env <- ask
  exprType <- evalExpr expr
  if exprType == Bool then do
    evalBlock block
    return env
  else throwError $ "Condition must be of type Bool"

evalStmt (CondElse expr b1 b2) = do
  env <- ask
  exprType <- evalExpr expr
  if exprType == Bool then do
    evalBlock b1
    evalBlock b2
    return env
  else throwError $ "Condition must be of type Bool"

evalStmt (While expr block) = do
  env <- ask
  exprType <- evalExpr expr
  if exprType == Bool then do
    evalBlock block
    return env
  else throwError $ "Condition must be of type Bool"

evalStmt (FnDecl t name args block) = do
  (varEnv, funEnv, retType) <- ask
  let newFunEnv = Map.insert name (Func t args) funEnv
  let newVarEnv = Map.union (Map.fromList (map extractArg args)) varEnv
  local(\_ -> (newVarEnv, newFunEnv, t)) (evalBlock block)
  return (varEnv, newFunEnv, retType)

evalStmt (Ret expr) = do
  (varEnv, funEnv, retType) <- ask
  exprValue <- evalExpr expr
  if exprValue == retType then return (varEnv, funEnv, retType)
  else throwError $ "Returning value of type " ++ show exprValue ++ " in function of type " ++ show retType

evalStmt (VRet) = do
  (varEnv, funEnv, retType) <- ask
  if retType == Void then return (varEnv, funEnv, retType)
  else throwError $ "Returning void value in function of type " ++ show retType

evalBlock :: Block -> ResultT Env
evalBlock (BBlock []) = do
  env <- ask
  return env

evalBlock (BBlock (h:t)) = do
  env <- evalStmt h
  nextEnv <- local(\_ -> env) (evalBlock (BBlock t))
  return nextEnv

evalExpr :: Expr -> ResultT Type
evalExpr (ELitInt _) = do return Int
evalExpr ELitTrue = do return Bool
evalExpr ELitFalse = do return Bool
evalExpr (EString _) = do return Str

evalExpr (Neg e) = do
  exprValue <- evalExpr e
  if exprValue == Int then return Int
  else throwError $ "Cannot apply negation to type " ++ show exprValue

evalExpr (Not e) = do
  exprValue <- evalExpr e
  if exprValue == Bool then return Bool
  else throwError $ "Cannot apply NOT operator to type " ++ show exprValue

evalExpr (EAdd e1 op e2) = do
  e1Value <- evalExpr e1
  e2Value <- evalExpr e2
  if e1Value == Int && e2Value == Int then return Int
  else throwError $ "Cannot apply " ++ show op ++ " operator to types " ++ show e1Value ++ " and " ++ show e2Value 

evalExpr (EMul e1 op e2) = do
  e1Value <- evalExpr e1
  e2Value <- evalExpr e2
  if e1Value == Int && e2Value == Int then return Int
  else throwError $ "Cannot apply " ++ show op ++ " operator to types " ++ show e1Value ++ " and " ++ show e2Value

evalExpr (ERel e1 op e2) = do
  e1Value <- evalExpr e1
  e2Value <- evalExpr e2
  if e1Value == e2Value then return Bool
  else throwError $ "Cannot apply " ++ show op ++ " operator to types " ++ show e1Value ++ " and " ++ show e2Value

evalExpr (EAnd e1 e2) = do
  e1Value <- evalExpr e1
  e2Value <- evalExpr e2
  if e1Value == Bool && e2Value == Bool then return Bool
  else throwError $ "Cannot apply AND operator to types " ++ show e1Value ++ " and " ++ show e2Value

evalExpr (EOr e1 e2) = do
  e1Value <- evalExpr e1
  e2Value <- evalExpr e2
  if e1Value == Bool && e2Value == Bool then return Bool
  else throwError $ "Cannot apply OR operator to types " ++ show e1Value ++ " and " ++ show e2Value

evalExpr (EVar ident) = do
  (varEnv, _, _) <- ask
  if Map.member ident varEnv then return (varEnv Map.! ident)
  else throwError $ "Undefined variable: " ++ show ident 

evalExpr (EApp ident exprs) = do
  (_, funEnv, _) <- ask
  if Map.member ident funEnv then do
    let (Func t args) = funEnv Map.! ident
    exprTypes <- mapM evalExpr exprs
    let argTypes = map getArgType args
    if verifyArgTypes exprTypes argTypes then return t
    else throwError $ "Arguments do not match function signature"
  else throwError $ "Undefined function: " ++ show ident


-- helpers

getArgType :: Arg -> Type
getArgType (ValArg t _) = t
getArgType (RefArg t _) = t

verifyArgTypes :: [Type] -> [Type] -> Bool
verifyArgTypes [] [] = True
verifyArgTypes [] (h:t) = False
verifyArgTypes (h:t) [] = False
verifyArgTypes (h1:t1) (h2:t2) = if h1 == h2 then verifyArgTypes t1 t2 else False

extractArg :: Arg -> (Ident, Type)
extractArg (ValArg t i) = (i, t)
extractArg (RefArg t i) = (i, t)

