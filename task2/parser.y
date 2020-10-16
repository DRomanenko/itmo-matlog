{
module Parser where

import           Tokenizer

import qualified Data.Map   as M
}

%name         parse
%tokentype    {Token}
%error        {error "Parsing error"}

%token
  LEFT        {LeftBracket}
  NOT			    {NOT}
  OR          {OR}
  AND			    {AND}
  IMPLICATION {Implication}
  TURNSTILE   {Turnstile}
  COMMA       {Comma}
  VARIABLE    {Variable $$}
  RIGHT       {RightBracket}
%%

Task:
	Hypo TURNSTILE Expr	     {Head ($1, $3)}
	| TURNSTILE Expr		     {Head ([], $2)}
	| Expr                   {Tail $1}

Hypo:
	Expr COMMA Hypo          {$1 : $3}
	| Expr                   {[$1]}

Expr:
	MyOr                     {$1}
	| MyOr IMPLICATION Expr  {Apply Impl $1 $3}

MyOr:
	MyAnd 			             {$1}
	| MyOr OR MyAnd	         {Apply Or $1 $3}

MyAnd:
	Negative 				         {$1}
	| MyAnd AND Negative 	   {Apply And $1 $3}

Negative:
	NOT Negative		         {Not $2}
	| VARIABLE 		           {Var $1}
	| LEFT Expr RIGHT        {$2}

{
data OrAndImpl = And | Or | Impl deriving (Eq, Ord)

instance Show OrAndImpl where
	show Or = "|"
	show And = "&"
	show Impl = "->"

data Expr = Var String | Not Expr | Apply OrAndImpl Expr Expr deriving (Ord)

instance Show Expr where
	show (Var v) = v
	show (Not e) = "!" ++ (show e) ++ ""
	show (Apply op a b) = "(" ++ show a ++ " " ++ show op ++ " " ++ show b ++ ")"

instance Eq Expr where
	(Var v) == (Var v') = v == v'
	(Not e) == (Not e') = e == e'
	(Apply op a b) == (Apply op1 c d) = (op == op1) && (a == c) && (b == d)
	_ == _ = False

data Task = Tail {line :: Expr} | Head ([Expr], Expr)

data SignedExpr = Hypothesis Expr Int | Axiom Expr Int | MP Expr Int Int

getExpr (Axiom expr _)      = expr
getExpr (Hypothesis expr _) = expr
getExpr (MP expr _ _ )      = expr

showSignedExpr (Axiom expr n) _ = "Ax. sch. " ++ show n
showSignedExpr (Hypothesis expr n) _ = "Hypothesis " ++ show n
showSignedExpr (MP expr i q) map = "M.P. " ++ (show $ map M.! i + 1) ++ ", " ++ (show $ map M.! q + 1)
}
