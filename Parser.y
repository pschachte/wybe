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
      '('             { TokLBracket Paren }
      ')'             { TokRBracket Paren }

%%

Exp1  : Exp1 '+' Term           { Plus $1 $3 }
      | Exp1 '-' Term           { Minus $1 $3 }
      | Term                    { Term $1 }

Term  : Term '*' Factor         { Times $1 $3 }
      | Term '/' Factor         { Div $1 $3 }
      | Factor                  { Factor $1 }

Factor			  
      : int                     { IntValue $1 }
      | float                   { FloatValue $1 }
      | '(' Exp1 ')'            { Brack $2 }


{
parseError :: [FrgToken] -> a
parseError _ = error "Parse error"

data Exp1 
      = Plus Exp1 Term 
      | Minus Exp1 Term 
      | Term Term
      deriving Show

data Term 
      = Times Term Factor 
      | Div Term Factor 
      | Factor Factor
      deriving Show

data Factor 
      = IntValue Integer
      | FloatValue Double
      | Var String 
      | Brack Exp1
      deriving Show

main = do
  toks <- inputTokens
  print $ calc $ map frgtoken toks
}
