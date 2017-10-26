module Head where

type Index = Int
type Id = String
data TI a = TI (Index -> (a, Index))
type Subst  = [(Id, SimpleType)]
data Type = Forall SimpleType deriving (Eq, Show)
data Assump = Id :>: Type deriving (Eq, Show)

data Literal = Int | Bool | TInt Int | TBool Bool deriving (Eq)

data SimpleType  = TVar Id
                 | TArr SimpleType SimpleType
                 | TLit Literal
                 | TCon Id
                 | TApp SimpleType SimpleType
                 | TGen Int
                 deriving Eq

data Pat = PVar Id
         | PLit Literal
         | PCon Id [Pat]
         deriving (Eq, Show)

data Expr =  Var Id
            | App Expr Expr
            | Lam Id Expr
            | Lit Literal
            | If Expr Expr Expr
            | Case Expr [(Pat,Expr)]
            | Let (Id,Expr) Expr
            deriving (Eq, Show)

instance Show SimpleType where
    show (TVar i) = i
    show (TArr (TVar i) t) = i++"->"++show t
    show (TArr (TLit tipo) t) = show tipo ++"->"++show t
    show (TArr t t') = "("++show t++")"++"->"++show t'
    show (TCon i) = i
    show (TApp c v) = show c ++ " " ++ show v

    show (TLit tipo) = show tipo
    show (TGen n) = "tg" ++ show n

instance Show Literal where
    show (TInt _) = "Int"
    show (TBool _) = "Bool"
    show Int = "Int"
    show Bool = "Bool"
