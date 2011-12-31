{
module Parser (parse) where
import Scanner
import AST
-- import Text.ParserCombinators.Parsec.Pos

}

%name parse
%tokentype { Token }
%error { parseError }

%token 
      int             { TokInt $$ _ }
      float           { TokFloat $$ _ }
      char            { TokChar $$ _ }
      dstring         { TokString DoubleQuote $$ _ }
      bstring         { TokString BackQuote $$ _ }
      '='             { TokSymbol "=" _ }
      '+'             { TokSymbol "+" _ }
      '-'             { TokSymbol "-" _ }
      '*'             { TokSymbol "*" _ }
      '/'             { TokSymbol "/" _ }
      '<'             { TokSymbol "<" _ }
      '>'             { TokSymbol ">" _ }
      '<='            { TokSymbol "<=" _ }
      '>='            { TokSymbol ">=" _ }
      '=='            { TokSymbol "==" _ }
      '/='            { TokSymbol "/=" _ }
      ','             { TokComma _ }
      ';'             { TokSemicolon _ }
      ':'             { TokColon _ }
      '.'             { TokSymbol "." _ }
      '?'             { TokSymbol "?" _ }
      '!'             { TokSymbol "!" _ }
      'public'        { TokIdent "public" _ }
      'resource'      { TokIdent "resource" _ }
      'type'          { TokIdent "type" _ }
      'func'          { TokIdent "func" _ }
      'proc'          { TokIdent "proc" _ }
      'let'           { TokIdent "let" _ }
      'where'         { TokIdent "where" _ }
      'end'           { TokIdent "end" _ }
      'in'            { TokIdent "in" _ }
      'if'            { TokIdent "if" _ }
      'then'          { TokIdent "then" _ }
      'elseif'        { TokIdent "elseif" _ }
      'else'          { TokIdent "else" _ }
      'do'            { TokIdent "do" _ }
      'for'           { TokIdent "for" _ }
      'while'         { TokIdent "while" _ }
      'until'         { TokIdent "until" _ }
      'when'          { TokIdent "when" _ }
      'unless'        { TokIdent "unless" _ }
      'from'          { TokIdent "from" _ }
      'to'            { TokIdent "to" _ }
      'by'            { TokIdent "by" _ }
      'and'           { TokIdent "and" _ }
      'or'            { TokIdent "or" _ }
      'not'           { TokIdent "not" _ }
      ident           { TokIdent _ _ }
      '('             { TokLBracket Paren _ }
      ')'             { TokRBracket Paren _ }

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
                                { TypeDecl $1 $3 $5 $ Just $ tokenPosition $2 }
    | Visibility 'resource' ident OptType
                                { ResourceDecl $1 (identName $3) $4
				    $ Just $ tokenPosition $2 }
    | Visibility 'func' FnProto OptType '=' Exp
                                { FuncDecl $1 $3 $4 $6
				    $ Just $ tokenPosition $2 }
    | Visibility 'proc' ProcProto ProcBody
                                { ProcDecl $1 $3 $4 $ Just $ tokenPosition $2 }
    | Stmt                      { StmtDecl (content $1) (place $1) }



TypeProto :: { TypeProto }
    : ident OptIdents           { TypeProto (identName $1) $2 }

Ctors :: { [FnProto] }
    : RevCtors                  { reverse $1 }

RevCtors :: { [FnProto] }
    : FnProto                   { [$1] }
    | RevCtors FnProto          { $2:$1 }

FnProto :: { FnProto }
    : ident OptParamList        { FnProto (identName $1) $2 }

ProcProto :: { ProcProto }
    : ident OptProcParamList    { ProcProto (identName $1) $2 }

OptParamList :: { [Param] }
    : {- empty -}               { [] }
    | '(' Params ')'            { $2 }

Params :: { [Param] }
    : RevParams                 { reverse $1 }

RevParams :: { [Param] }
    : Param                     { [$1] }
    | RevParams ',' Param       { $3 : $1 }

Param :: { Param }
    : ident OptType             { Param (identName $1) $2 ParamIn }

OptProcParamList :: { [Param] }
    : {- empty -}               { [] }
    | '(' ProcParams ')'        { $2 }

ProcParams :: { [Param] }
    : RevProcParams             { reverse $1 }

RevProcParams :: { [Param] }
    : ProcParam                 { [$1] }
    | RevProcParams ',' ProcParam
                                { $3 : $1 }

ProcParam :: { Param }
    : ident OptType             { Param (identName $1) $2 ParamIn }
    | '?' ident OptType         { Param (identName $2) $3 ParamOut }
    | '!' ident OptType         { Param (identName $2) $3 ParamInOut }

OptType :: { TypeSpec }
    : {- empty -}               { Unspecified }
    | ':' Type                  { $2 }


Type :: { TypeSpec }
    : ident OptTypeList         { TypeSpec (identName $1) $2 }

OptTypeList :: { [TypeSpec] }
    : {- empty -}               { [] }
    | '(' Types ')'             { $2 }

Types :: { [TypeSpec] }
    : RevTypes                  { reverse $1 }

RevTypes :: { [TypeSpec] }
    : Type                      { [$1] }
    | RevTypes ',' Type         { $3 : $1 }


OptIdents :: { [String] }
    : {- empty -}               { [] }
    | '(' Idents ')'            { $2 }

Idents :: { [String] }
    : RevIdents                 { reverse $1 }

RevIdents :: { [String] }
    : ident                     { [identName $1] }
    | RevIdents ',' ident       { (identName $3):$1 }

Visibility :: { Visibility }
    : {- empty -}               { Private }
    | 'public'                  { Public }

ProcBody :: { [Placed Stmt] }
    : Stmts 'end'               { $1 }

Stmts :: { [Placed Stmt] }
    : RevStmts                  { reverse $1 }

RevStmts :: { [Placed Stmt] }
    : {- empty -}               { [] }
    | RevStmts Stmt             { $2:$1 }

Stmt :: { Placed Stmt }
    : ident '=' Exp             { Placed (Assign (identName $1) $3) (tokenPosition $1) }
    | ident OptProcArgs         { Placed (ProcCall (identName $1) $2) (tokenPosition $1) }
    | 'if' Exp 'then' Stmts Condelse 'end'
                                { Placed (Cond $2 $4 $5) (tokenPosition $1) }
    | 'do' LoopBody 'end'       { Placed (Loop $2) (tokenPosition $1) }

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
    | Stmt                      { NormalStmt (content $1) }

OptProcArgs :: { [Exp] }
    : {- empty -}               { [] }
    | '(' Exp ExpList ')'       { $2:$3 }

Condelse :: { [Placed Stmt] }
    : 'else' Stmts              { $2 }
    | {- empty -}               { [] }

Generator :: { Generator }
    : ident 'in' Exp            { In (identName $1) $3 }
    | ident 'from' Exp 'to' Exp 'by' Exp
                                { InRange (identName $1) $3 $7 (Just $5) }
    | ident 'from' Exp 'by' Exp 'to' Exp
                                { InRange (identName $1) $3 $5 (Just $7) }
    | ident 'from' Exp 'to' Exp { InRange (identName $1) $3 (IntValue 1) 
	                                  (Just $5) }
    | ident 'from' Exp 'by' Exp { InRange (identName $1) $3 $5 Nothing }

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
    | ident                     { Var (identName $1) }
    | ident ArgList             { Fncall (identName $1) $2 }

ArgList :: { [Exp] }
    : '(' Exp ExpList ')'       { $2:$3 }

ExpList :: { [Exp] }
    : RevExpList                { reverse $1 }

RevExpList :: { [Exp] }
    : {- empty -}               { [] }
    | RevExpList ',' Exp        { $3:$1 }

{
parseError :: [Token] -> a
parseError (tok:_) = error $ (showPosition (tokenPosition tok)) 
                             ++ ": Parse error"
}
