{
module Tokenizer where
}

%wrapper "basic"

$zero = 0
$lower = [a-z]
$capital = [A-Z]

:-
  $white+                             ;
  \(                                  {\a -> LeftBracket}
  \!                                  {\a -> NOT}
  \|                                  {\a -> OR}
  \&                                  {\a -> AND}
  \*                                  {\a -> MULTIPLY}
  \+                                  {\a -> PLUS}
  "->"                                {\a -> Implication}
  "|-"                                {\a -> Turnstile}
  \.                                  {\a -> Point}
  \'                                  {\a -> QUOTE}
  \=                                  {\a -> RAVNO}
  \@                                  {\a -> FORALL}
  \?                                  {\a -> EXIST}
  $lower                              {\a -> Variable a}
  $capital                            {\a -> PREDICATE a}
  $zero                               {\a -> ZERO}     
  \)                                  {\a -> RightBracket}

{
data Token = LeftBracket|NOT|OR|AND|MULTIPLY|PLUS|Implication|Turnstile|Point|QUOTE|RAVNO|FORALL|EXIST|Variable String|PREDICATE String|ZERO|RightBracket
}