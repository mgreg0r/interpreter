

module AbsGrammar where

-- Haskell module generated by the BNF converter




newtype Ident = Ident String deriving (Eq, Ord, Show, Read)
data Block = BBlock [Stmt]
  deriving (Eq, Ord, Show, Read)

data Stmt
    = BStmt Block
    | Empty
    | ExpStmt Expr
    | VarDecl Type Ident
    | VarAsgn Ident Expr
    | Print Expr
    | Cond Expr Block
    | CondElse Expr Block Block
    | While Expr Block
    | ArrayDecl Type Ident [Expr]
    | ArrayAsgn Ident [Expr] Expr
    | Break
    | Continue
    | FnDecl Type Ident [Arg] Block
    | Ret Expr
    | VRet
  deriving (Eq, Ord, Show, Read)

data Arg = ValArg Type Ident | RefArg Type Ident
  deriving (Eq, Ord, Show, Read)

data Type = Int | Str | Bool | Void
  deriving (Eq, Ord, Show, Read)

data Expr
    = EVar Ident
    | ELitInt Integer
    | ELitTrue
    | ELitFalse
    | EApp Ident [Expr]
    | EIndex Ident [Expr]
    | EString String
    | Neg Expr
    | Not Expr
    | EMul Expr MulOp Expr
    | EAdd Expr AddOp Expr
    | ERel Expr RelOp Expr
    | EAnd Expr Expr
    | EOr Expr Expr
  deriving (Eq, Ord, Show, Read)

data AddOp = Plus | Minus
  deriving (Eq, Ord, Show, Read)

data MulOp = Times | Div | Mod
  deriving (Eq, Ord, Show, Read)

data RelOp = LTH | LE | GTH | GE | EQU | NE
  deriving (Eq, Ord, Show, Read)
