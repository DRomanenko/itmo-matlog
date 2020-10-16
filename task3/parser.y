{
module Parser where

import Tokenizer
}

%name      parse
%tokentype {Token}
%error     {error "Parsing error"}

%token
  LEFT          {LeftBracket}
  NOT           {NOT}
  OR            {OR}
  AND           {AND}
  MUL           {MULTIPLY}
  PLUS          {PLUS}          
  IMPLICATION   {Implication}
  TURNSTILE     {Turnstile}
  POINT         {Point}
  QUOTE         {QUOTE}
  RAVNO         {RAVNO}
  FORALL        {FORALL}
  EXIST         {EXIST}
  VARIABLE      {Variable $$}
  PREDICATE     {PREDICATE $$}
  ZERO          {ZERO}
  RIGHT         {RightBracket}
%%

Task: 
    TURNSTILE Expr                  {Head $2}
    | Expr                          {Tail $1}

Expr:
    MyOr                            {$1}
    | MyOr IMPLICATION Expr         {Apply Impl $1 $3}      

MyOr:
    MyAnd                           {$1}
    | MyOr OR MyAnd                 {Apply Or $1 $3}

MyAnd:
    Negative                        {$1}
    | MyAnd AND Negative            {Apply And $1 $3}

Negative:
    Predicate                       {Expr $1}
    | NOT Negative                  {Not $2}
    | LEFT Expr RIGHT               {$2}
    | FORALL VARIABLE POINT Expr    {Apply1 Forall (Term $2) $4}
    | EXIST VARIABLE POINT Expr     {Apply1 Exist (Term $2) $4}

Predicate: 
    PREDICATE                       {Predicate $1}    
    | Term RAVNO Term               {Ravno $1 $3}

Term:
    Slagayemoye                     {$1}
    | Term PLUS Slagayemoye         {Apply2 Plus $1 $3}

Slagayemoye:
    MyMul                           {$1}
    | Slagayemoye MUL MyMul         {Apply2 Mul $1 $3}

MyMul:
    VARIABLE                        {Term $1}
    | LEFT Term RIGHT               {$2}
    | ZERO                          {Zero}
    | MyMul QUOTE                   {Quote $1}   
    
{
data OrAndImpl = Or | And | Impl deriving (Eq, Ord)

instance Show OrAndImpl where
    show Or = "|"
    show And = "&"
    show Impl = "->"

data ForallExist = Forall | Exist deriving (Eq, Ord)

instance Show ForallExist where
    show Forall = "@"
    show Exist = "?"

data Expr = Not Expr | Expr Predicate | Apply OrAndImpl Expr Expr | Apply1 ForallExist Term Expr deriving (Ord)

instance Show Expr where
    show (Expr e) = show e
    show (Not e) = "(!" ++ show e ++ ")"
    show (Apply op a b) = "(" ++ show a ++ show op ++ show b ++ ")"
    show (Apply1 op a b) = "(" ++ show op ++ show a ++ "." ++ show b ++ ")"

instance Eq Expr where
    (Expr e) == (Expr e') = e == e'
    (Not e) == (Not e') = e == e'
    (Apply op a b) == (Apply op1 c d) = (op == op1) && (a == c) && (b == d) 
    (Apply1 op a b) == (Apply1 op1 c d) = (op == op1) && (a == c) && (b == d) 
    _ == _ = False  

data PlusMul = Plus | Mul deriving (Eq, Ord)

instance Show PlusMul where
    show Plus = "+" 
    show Mul = "*" 

data Term = Zero | Term String | Quote Term | Apply2 PlusMul Term Term deriving (Ord)

instance Show Term where
    show (Zero) = "0"
    show (Term e) = e
    show (Quote e) = show e ++ "'"  
    show (Apply2 op a b) = "(" ++ show a ++ show op ++ show b ++ ")"

instance Eq Term where 
    (Zero) == (Zero) = True
    (Term e) == (Term e') = e == e'
    (Quote e) == (Quote e') = e == e'
    (Apply2 op a b) == (Apply2 op1 c d) = (op == op1) && (a == c) && (b == d)
    _ == _ = False   

data Predicate = Predicate String | Ravno Term Term deriving (Ord)     

instance Show Predicate where
    show (Predicate v) = v    
    show (Ravno a b) = "(" ++ show a ++ "=" ++ show b ++ ")"

instance Eq Predicate where
    (Predicate v) == (Predicate v') = v == v'
    (Ravno a b) == (Ravno c d) = a == c && b == d
    _ == _ = False  

data Task = Tail {line :: Expr} | Head Expr 

instance Show Task where
    show (Head e) = "|-" ++ show e
    show (Tail e) = show e 

data SignedExpr = AxiomSch Expr String | MP Expr Int Int | Axiom Expr Int | Intro Expr Int deriving (Eq, Show)

getExpr (AxiomSch expr _) = expr
getExpr (MP expr _ _) = expr
getExpr (Axiom expr _) = expr
getExpr (Intro expr _) = expr

showSignedExpr (AxiomSch expr n) = ". Ax. sch. " ++ n ++ "] " ++ show expr
showSignedExpr (MP expr i q) = ". M.P. " ++ show (i + 1) ++ ", " ++ show (q + 1) ++ "] " ++ show expr
showSignedExpr (Axiom expr n) = ". Ax. A" ++ show n ++ "] " ++ show expr
showSignedExpr (Intro expr n) = ". ?@-intro " ++ show (n + 1) ++ "] " ++ show expr
}
