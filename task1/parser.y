{
module Parser where
import Tokenizer
}

%name         parse
%tokentype    { Token }
%error        { error "Parsing error" }

%token
  LEFT        {LeftBracket}
  NOT         {NOT}
  OR          {OR}
  AND         {AND}
  IMPLICATION {Implication}
  VARIABLE    {Variable $$}
  RIGHT       {RightBracket}
%%

Expr:
  MyOr {$1}
  | MyOr IMPLICATION Expr {Apply Impl $1 $3}

MyOr:
  MyAnd {$1}
  | MyOr OR MyAnd {Apply Or $1 $3}

MyAnd:
  Negative {$1}
  | MyAnd AND Negative {Apply And $1 $3}

Negative:
  NOT Negative {Not $2}
  | VARIABLE {Var $1}
  | LEFT Expr RIGHT {$2}

{
data OrAndImpl = Or | And | Impl

instance Show OrAndImpl where
  show Or = "|"
  show And = "&"
  show Impl = "->"

data Expr = Var String | Not Expr | Apply OrAndImpl Expr Expr

instance Show Expr where
  show (Var v) = v
  show (Not e) = "(!" ++ (show e) ++ ")"
  show (Apply op a b) = "(" ++ show op ++ "," ++ show a ++ "," ++ show b ++ ")"
}

