{
module Tokenizer where
}

%wrapper "basic"

$digit = 0-9
$alphabet = [A-Z]

:-
  $white+ 								            ;
  \(      								            {\a -> LeftBracket}
  \!      								            {\a -> NOT}
  \|      								            {\a -> OR}
  \&      								            {\a -> AND}
  "->"    								            {\a -> Implication}
  "|-"									              {\a -> Turnstile}
  \,									                {\a -> Comma}
  $alphabet [$alphabet $digit ’ \']*  {\a -> Variable a}
  \)      								            {\a -> RightBracket}

{
data Token = LeftBracket|NOT|OR|AND|Implication|Variable String|Turnstile|Comma|RightBracket
}
