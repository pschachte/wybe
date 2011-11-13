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
      ','             { TokComma }
      ';'             { TokSemicolon }
      ':'             { TokSemicolon }
      '.'             { TokSymbol "." }
      type            { TokIdent "type" }
      func            { TokIdent "func" }
      proc            { TokIdent "proc" }
      where           { TokIdent "where" }
      end             { TokIdent "end" }
      ident           { TokIdent $$}
      '('             { TokLBracket Paren }
      ')'             { TokRBracket Paren }

%right in
%nonassoc '>' '<'
%left '+' '-'
%left '*' '/'
%left NEG
%%

Item  : Visibility type Idents	  { Type $1 $3 }
--      | FuncDecl                { $1 }
--      | ProcDecl                { $1 }


Idents : RevIdents              { reverse $1 }

RevIdents : ident               { [$1] }
       | RevIdents ',' ident    { $3:$1 }


Exp   : Exp '+' Exp             { Plus $1 $3 }
      | Exp '-' Exp             { Minus $1 $3 }
      | Exp '*' Exp             { Times $1 $3 }
      | Exp '/' Exp             { Div $1 $3 }
      | '(' Exp ')'             { $2 }
      | '-' Exp %prec NEG       { Negate $2 }
      | int                     { IntValue $1 }
      | float                   { FloatValue $1 }
      | ident                   { Var $1 }


Visibility : {- empty -}        { Private }
      | public                  { Public }


{
parseError :: [FrgToken] -> a
parseError _ = error "Parse error"

data Item
      = Type Visibility Idents
      deriving Show

type Idents = [String]

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

data Visibility = Public | Private deriving Show
  


main = do
  toks <- inputTokens
  print $ calc $ map frgtoken toks
}
