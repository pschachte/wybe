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
      ':'             { TokColon }
      '.'             { TokSymbol "." }
      'public'        { TokIdent "public" }
      'type'          { TokIdent "type" }
      'func'          { TokIdent "func" }
      'proc'          { TokIdent "proc" }
      'where'         { TokIdent "where" }
      'end'           { TokIdent "end" }
      ident           { TokIdent $$}
      '('             { TokLBracket Paren }
      ')'             { TokRBracket Paren }

%right in
%nonassoc '>' '<'
%left '+' '-'
%left '*' '/'
%left NEG
%%

Item  : Visibility 'type' TypeProto '=' Ctors
                  { TypeDecl $1 $3 $5 }
      | Visibility 'func' FnProto '=' Exp
                  { FuncDecl $1 $3 $5 }
--      | ProcDecl                { $1 }


TypeProto : ident OptIdents     { TypeProto $1 $2 }

Ctors : RevCtors                { reverse $1 }

RevCtors : FnProto              { [$1] }
       | RevCtors FnProto       { $2:$1 }

FnProto : ident OptParamList    { FnProto $1 $2 }

OptParamList : {- empty -}	{ [] }
       | '(' Params ')'         { $2 }

Params : RevParams              { reverse $1 }

RevParams : Param               { [$1] }
       | RevParams ',' Param    { $3 : $1 }

Param : ident ':' Type          { Param $1 $3 }

Type : ident OptTypeList        { Type $1 $2 }

OptTypeList : {- empty -}	{ [] }
       | '(' Types ')'          { $2 }

Types : RevTypes                { reverse $1 }

RevTypes : Type                 { [$1] }
      | RevTypes ',' Type       { $3 : $1 }


OptIdents : {- empty -}         { [] }
       | '(' Idents ')'         { $2 }

Idents : RevIdents              { reverse $1 }

RevIdents : ident               { [$1] }
       | RevIdents ',' ident    { $3:$1 }

Visibility : {- empty -}          { Private }
       | 'public'                 { Public }

Exp   : Exp '+' Exp             { Plus $1 $3 }
      | Exp '-' Exp             { Minus $1 $3 }
      | Exp '*' Exp             { Times $1 $3 }
      | Exp '/' Exp             { Div $1 $3 }
      | '(' Exp ')'             { $2 }
      | '-' Exp %prec NEG       { Negate $2 }
      | int                     { IntValue $1 }
      | float                   { FloatValue $1 }
      | ident                   { Var $1 }



{
parseError :: [FrgToken] -> a
parseError _ = error "Parse error"

data Item
      = TypeDecl Visibility TypeProto [FnProto]
      | FuncDecl Visibility FnProto Exp
      deriving Show

type Idents = [String]

data TypeProto = TypeProto String [String]
      deriving Show

data Type = Type String [Type]
      deriving Show

data FnProto = FnProto String [Param]
      deriving Show

data Param = Param String Type
      deriving Show


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
