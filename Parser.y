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
      char            { TokChar $$ }
      dstring         { TokString DoubleQuote $$ }
      bstring         { TokString BackQuote $$ }
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
      '?'             { TokSymbol "?" }
      '!'             { TokSymbol "!" }
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
      'and'           { TokIdent "and" }
      'or'            { TokIdent "or" }
      'not'           { TokIdent "not" }
      ident           { TokIdent $$}
      '('             { TokLBracket Paren }
      ')'             { TokRBracket Paren }

%nonassoc 'where' 'let'
%left 'or'
%left 'and'
%left 'not'
%nonassoc 'in'
%left '>' '<' '<=' '>=' '==' '/='
%left '+' '-'
%left '*' '/'
%left NEG
%%

Items :: { [Item] }
    : RevItems                  { reverse $1 }

RevItems :: { [Item] }
    : {- empty -}               { [] }
    | RevItems Item             { $2:$1 }


Item  :: { Item }
    : Visibility 'type' TypeProto '=' Ctors
                                { TypeDecl $1 $3 $5 }
    | Visibility 'func' FnProto OptType '=' Exp
                                { FuncDecl $1 $3 $4 $6 }
    | Visibility 'proc' ProcProto ProcBody
                                { ProcDecl $1 $3 $4 }
    | Stmt                      { StmtDecl $1 }



TypeProto :: { TypeProto }
    : ident OptIdents           { TypeProto $1 $2 }

Ctors :: { [FnProto] }
    : RevCtors                  { reverse $1 }

RevCtors :: { [FnProto] }
    : FnProto                   { [$1] }
    | RevCtors FnProto          { $2:$1 }

FnProto :: { FnProto }
    : ident OptParamList        { FnProto $1 $2 }

ProcProto :: { ProcProto }
    : ident OptProcParamList    { ProcProto $1 $2 }

OptParamList :: { [Param] }
    : {- empty -}               { [] }
    | '(' Params ')'            { $2 }

Params :: { [Param] }
    : RevParams                 { reverse $1 }

RevParams :: { [Param] }
    : Param                     { [$1] }
    | RevParams ',' Param       { $3 : $1 }

Param :: { Param }
    : ident OptType             { Param $1 $2 }

OptProcParamList :: { [ProcParam] }
    : {- empty -}               { [] }
    | '(' ProcParams ')'        { $2 }

ProcParams :: { [ProcParam] }
    : RevProcParams             { reverse $1 }

RevProcParams :: { [ProcParam] }
    : ProcParam                 { [$1] }
    | RevProcParams ',' ProcParam
                                { $3 : $1 }

ProcParam :: { ProcParam }
    : ident OptType             { ProcParam $1 $2 ParamIn }
    | '?' ident OptType         { ProcParam $2 $3 ParamOut }
    | '!' ident OptType         { ProcParam $2 $3 ParamInOut }

OptType :: { Type }
    : {- empty -}               { Unspecified }
    | ':' Type                  { $2 }


Type :: { Type }
    : ident OptTypeList         { Type $1 $2 }

OptTypeList :: { [Type] }
    : {- empty -}               { [] }
    | '(' Types ')'             { $2 }

Types :: { [Type] }
    : RevTypes                  { reverse $1 }

RevTypes :: { [Type] }
    : Type                      { [$1] }
    | RevTypes ',' Type         { $3 : $1 }


OptIdents :: { [String] }
    : {- empty -}               { [] }
    | '(' Idents ')'            { $2 }

Idents :: { [String] }
    : RevIdents                 { reverse $1 }

RevIdents :: { [String] }
    : ident                     { [$1] }
    | RevIdents ',' ident       { $3:$1 }

Visibility :: { Visibility }
    : {- empty -}               { Private }
    | 'public'                  { Public }

ProcBody :: { [Stmt] }
    : Stmts 'end'               { $1 }

Stmts :: { [Stmt] }
    : RevStmts                  { reverse $1 }

RevStmts :: { [Stmt] }
    : {- empty -}               { [] }
    | RevStmts Stmt             { $2:$1 }

Stmt :: { Stmt }
    : ident '=' Exp             { Assign $1 $3 }
    | ident OptProcArgs         { ProcCall $1 $2 }
    | 'if' Exp 'then' Stmts Condelse 'end'
                                { Cond $2 $4 $5 }
    | 'do' LoopBody 'end'       { Loop $2 }

LoopBody :: { [LoopStmt] }
    : RevLoopBody               { reverse $1 }

RevLoopBody :: { [LoopStmt] }
    : {- empty -}               { [] }
    | RevLoopBody LoopStmt      { $2:$1 }

LoopStmt :: { LoopStmt }
    : 'for' Generator           { For $2 }
    | 'until' Exp               { BreakIf $2 }
    | 'while' Exp               { BreakIf (Fncall "not" [$2]) }
    | 'unless' Exp              { NextIf $2 }
    | 'when' Exp                { NextIf (Fncall "not" [$2]) }
    | Stmt                      { NormalStmt $1 }

OptProcArgs :: { [Exp] }
    : {- empty -}               { [] }
    | '(' Exp ExpList ')'       { $2:$3 }

Condelse :: { [Stmt] }
    : 'else' Stmts              { $2 }
    | {- empty -}               { [] }

Generator :: { Generator }
    : ident 'in' Exp            { In $1 $3 }
    | ident 'from' Exp 'to' Exp 'by' Exp
                                { InRange $1 $3 $7 (Just $5) }
    | ident 'from' Exp 'by' Exp 'to' Exp
                                { InRange $1 $3 $5 (Just $7) }
    | ident 'from' Exp 'to' Exp { InRange $1 $3 (IntValue 1) (Just $5) }
    | ident 'from' Exp 'by' Exp { InRange $1 $3 $5 Nothing }

Exp :: { Exp }
    : Exp '+' Exp               { Fncall "+" [$1, $3] }
    | Exp '-' Exp               { Fncall "-" [$1, $3] }
    | Exp '*' Exp               { Fncall "*" [$1, $3] }
    | Exp '/' Exp               { Fncall "/" [$1, $3] }
    | Exp '<' Exp               { Fncall "<" [$1, $3] }
    | Exp '<=' Exp              { Fncall "<=" [$1, $3] }
    | Exp '>' Exp               { Fncall "<" [$3, $1] }
    | Exp '>=' Exp              { Fncall "<=" [$3, $1] }
    | Exp '==' Exp              { Fncall "==" [$1, $3] }
    | Exp '/=' Exp              { Fncall "+" [$1, $3] }
    | 'not' Exp                 { Fncall "not" [$2] }
    | Exp 'and' Exp             { Fncall "and" [$1, $3] }
    | Exp 'or' Exp              { Fncall "or" [$1, $3] }
    | 'if' Exp 'then' Exp 'else' Exp
                                { CondExp $2 $4 $6 }
    | 'let' Stmts 'in' Exp      { Where $2 $4 }
    | Exp 'where' ProcBody      { Where $3 $1 }
    | '(' Exp ')'               { $2 }
    | '-' Exp %prec NEG         { Fncall "Negate" [$2] }
    | int                       { IntValue $1 }
    | float                     { FloatValue $1 }
    | char                      { CharValue $1 }
    | dstring                   { StringValue $1 }
    | bstring                   { StringValue $1 }
    | ident                     { Var $1 }
    | ident ArgList             { Fncall $1 $2 }

ArgList :: { [Exp] }
    : '(' Exp ExpList ')'       { $2:$3 }

ExpList :: { [Exp] }
    : RevExpList                { reverse $1 }

RevExpList :: { [Exp] }
    : {- empty -}               { [] }
    | RevExpList ',' Exp        { $3:$1 }

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

data ProcProto = ProcProto String [ProcParam]
      deriving Show

data Param = Param String Type
      deriving Show

data ProcParam = ProcParam String Type FlowDirection
      deriving Show

data FlowDirection = ParamIn | ParamOut | ParamInOut
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
      = Where Stmts Exp
      | CondExp Exp Exp Exp
      | IntValue Integer
      | FloatValue Double
      | StringValue String
      | CharValue Char
      | Fncall String [Exp]
      | Var String
      deriving Show

data Visibility = Public | Private deriving Show

data Generator 
      = In String Exp
      | InRange String Exp Exp (Maybe Exp)
    deriving Show

}
