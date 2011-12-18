{
module Parser (parse) where

import Scanner
}

%name parse
%tokentype { FrgToken }
%error { parseError }

%token 
      int             { TokInt $$ }
      float           { TokFloat $$ }
      dstring         { TokString DoubleQuote $$ }
      sstring         { TokString SingleQuote $$ }
      '='             { TokSymbol "=" }
      '+'             { TokSymbol "+" }
      '-'             { TokSymbol "-" }
      '*'             { TokSymbol "*" }
      '/'             { TokSymbol "/" }
      '<'             { TokSymbol "<" }
      '>'             { TokSymbol ">" }
      '<='            { TokSymbol "<=" }
      '>='            { TokSymbol ">=" }
      '=='            { TokSymbol "==" }
      '/='            { TokSymbol "/=" }
      ','             { TokComma }
      ';'             { TokSemicolon }
      ':'             { TokColon }
      '.'             { TokSymbol "." }
      'public'        { TokIdent "public" }
      'type'          { TokIdent "type" }
      'func'          { TokIdent "func" }
      'proc'          { TokIdent "proc" }
      'let'           { TokIdent "let" }
      'where'         { TokIdent "where" }
      'end'           { TokIdent "end" }
      'in'            { TokIdent "in" }
      'if'            { TokIdent "if" }
      'then'          { TokIdent "then" }
      'elseif'        { TokIdent "elseif" }
      'else'          { TokIdent "else" }
      'do'            { TokIdent "do" }
      'for'           { TokIdent "for" }
      'while'         { TokIdent "while" }
      'until'         { TokIdent "until" }
      'when'          { TokIdent "when" }
      'unless'        { TokIdent "unless" }
      'from'          { TokIdent "from" }
      'to'            { TokIdent "to" }
      'by'            { TokIdent "by" }
      ident           { TokIdent $$}
      '('             { TokLBracket Paren }
      ')'             { TokRBracket Paren }

%nonassoc 'where' 'let'
%nonassoc 'in'
%left '>' '<' '<=' '>=' '==' '/='
%left '+' '-'
%left '*' '/'
%left NEG
%%

Items : RevItems                { reverse $1 }

RevItems : {- empty -}          { [] }
         | RevItems Item        { $2:$1 }

Item  : Visibility 'type' TypeProto '=' Ctors
                                { TypeDecl $1 $3 $5 }
      | Visibility 'func' FnProto OptType '=' Exp
                                { FuncDecl $1 $3 $4 $6 }
      | Visibility 'proc' ProcProto ProcBody
                                { ProcDecl $1 $3 $4 }
      | Stmt                    { StmtDecl $1 }



TypeProto : ident OptIdents     { TypeProto $1 $2 }

Ctors : RevCtors                { reverse $1 }

RevCtors : FnProto              { [$1] }
       | RevCtors FnProto       { $2:$1 }

FnProto : ident OptParamList    { FnProto $1 $2 }

ProcProto : ident OptParamList  { ProcProto $1 $2 }

OptParamList : {- empty -}	{ [] }
       | '(' Params ')'         { $2 }

Params : RevParams              { reverse $1 }

RevParams : Param               { [$1] }
       | RevParams ',' Param    { $3 : $1 }

Param : ident OptType           { Param $1 $2 }

OptType : {- empty -}		{ Unspecified }
        | ':' Type              { $2 }


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

Visibility : {- empty -}        { Private }
       | 'public'               { Public }

ProcBody : Stmts 'end'          { $1 }

Stmts : RevStmts                { reverse $1 }

RevStmts : {- empty -}          { [] }
         | RevStmts Stmt        { $2:$1 }

Stmt  : ident '=' Exp           { Assign $1 $3 }
      | ident OptProcArgs       { ProcCall $1 $2 }
      | 'if' Exp 'then' Stmts Condelse 'end'
                                { Cond $2 $4 $5 }
      | 'do' LoopBody 'end'
                                { Loop $2 }

LoopBody : RevLoopBody          { reverse $1 }

RevLoopBody : {- empty -}       { [] }
            | RevLoopBody LoopStmt
                                { $2:$1 }

LoopStmt : 'for' Generator      { For $2 }
         | 'until' Exp          { BreakIf $2 }
         | 'unless' Exp         { NextIf $2 }
         | Stmt                 { NormalStmt $1 }

OptProcArgs : {- empty -}       { [] }
           | '(' Exp ExpList ')'
                                { $2:$3 }

Condelse : 'else' Stmts         { $2 }
         | {- empty -}          { [] }

Generator : ident 'in' Exp      { In $1 $3 }
          | ident 'from' Exp 'to' Exp 'by' Exp
                                { InRange $1 $3 $7 (Just $5) }
          | ident 'from' Exp 'by' Exp 'to' Exp
                                { InRange $1 $3 $5 (Just $7) }
          | ident 'from' Exp 'to' Exp
                                { InRange $1 $3 (IntValue 1) (Just $5) }
          | ident 'from' Exp 'by' Exp
                                { InRange $1 $3 $5 Nothing }

Exp   : Exp '+' Exp             { Plus $1 $3 }
      | Exp '-' Exp             { Minus $1 $3 }
      | Exp '*' Exp             { Times $1 $3 }
      | Exp '/' Exp             { Div $1 $3 }
      | Exp '<' Exp             { Less $1 $3 }
      | Exp '<=' Exp            { Leq $1 $3 }
      | Exp '>' Exp             { Less $3 $1 }
      | Exp '>=' Exp            { Leq $3 $1 }
      | Exp '==' Exp            { Equal $1 $3 }
      | Exp '/=' Exp            { Neq $1 $3 }
      | 'if' Exp 'then' Exp 'else' Exp
                                { CondExp $2 $4 $6 }
      | 'let' Stmts 'in' Exp    { Where $2 $4 }
      | Exp 'where' ProcBody    { Where $3 $1 }
      | '(' Exp ')'             { $2 }
      | '-' Exp %prec NEG       { Negate $2 }
      | int                     { IntValue $1 }
      | float                   { FloatValue $1 }
      | dstring                 { StringValue $1 }
      | ident                   { Var $1 }
      | ident ArgList           { Fncall $1 $2 }

ArgList : '(' Exp ExpList ')'   { $2:$3 }

ExpList : RevExpList            { reverse $1 }

RevExpList : {- empty -}        { [] }
           | RevExpList ',' Exp { $3:$1 }

{
parseError :: [FrgToken] -> a
parseError _ = error "Parse error"

data Item
     = TypeDecl Visibility TypeProto [FnProto]
     | FuncDecl Visibility FnProto Type Exp
     | ProcDecl Visibility ProcProto Stmts
     | StmtDecl Stmt
    deriving Show

type Idents = [String]

data TypeProto = TypeProto String [String]
      deriving Show

data Type = Type String [Type]
          | Unspecified
      deriving Show

data FnProto = FnProto String [Param]
      deriving Show

data ProcProto = ProcProto String [Param]
      deriving Show

data Param = Param String Type
      deriving Show

type Stmts = [Stmt]

data Stmt
     = Assign String Exp
     | ProcCall String [Exp]
     | Cond Exp Stmts Stmts
     | Loop [LoopStmt]
     | Nop
    deriving Show

data LoopStmt
     = For Generator
     | BreakIf Exp
     | NextIf Exp
     | NormalStmt Stmt
    deriving Show


data Exp
      = Plus Exp Exp
      | Minus Exp Exp
      | Negate Exp
      | Times Exp Exp
      | Div Exp Exp
      | Less Exp Exp
      | Leq Exp Exp
      | Equal Exp Exp
      | Neq Exp Exp
      | Where Stmts Exp
      | CondExp Exp Exp Exp
      | IntValue Integer
      | FloatValue Double
      | StringValue String
      | Fncall String [Exp]
      | Var String
      deriving Show

data Visibility = Public | Private deriving Show

data Generator 
      = In String Exp
      | InRange String Exp Exp (Maybe Exp)
    deriving Show

}
