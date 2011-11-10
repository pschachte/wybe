{
module Main where

import Scanner
}

%name calc
%tokentype { FrgToken }
%error { parseError }

%token 
      int             { TokInt $$ }
      float           { TokFloat $$ }
      '='             { TokSymbol "=" }
      '+'             { TokSymbol "+" }
      '-'             { TokSymbol "-" }
      '*'             { TokSymbol "*" }
      '/'             { TokSymbol "/" }
      var             { TokIdent $$}
      '('             { TokLBracket Paren }
      ')'             { TokRBracket Paren }

%right in
%nonassoc '>' '<'
%left '+' '-'
%left '*' '/'
%left NEG
%%

Exp   : Exp '+' Exp             { Plus $1 $3 }
      | Exp '-' Exp             { Minus $1 $3 }
      | Exp '*' Exp             { Times $1 $3 }
      | Exp '/' Exp             { Div $1 $3 }
      | '(' Exp ')'             { $2 }
      | '-' Exp %prec NEG       { Negate $2 }
      | int                     { IntValue $1 }
      | float                   { FloatValue $1 }
      | var                     { Var $1 }


{
parseError :: [FrgToken] -> a
parseError _ = error "Parse error"

data Exp
      = Plus Exp Exp
      | Minus Exp Exp
      | Negate Exp
      | Times Exp Exp
      | Div Exp Exp
      | IntValue Integer
      | FloatValue Double
      | Var String 
      deriving Show

main = do
  toks <- inputTokens
  print $ calc $ map frgtoken toks
}
