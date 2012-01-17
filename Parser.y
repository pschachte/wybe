{
--  File     : Parser.y
--  Author   : Peter Schachte
--  Origin   : Tue Nov 08 22:23:55 2011
--  Purpose  : Parser for the Frege language
--  Copyright: © 2011-2012 Peter Schachte.  All rights reserved.

module Parser (parse) where
import Scanner
import AST
-- import Text.ParserCombinators.Parsec.Pos

}

%name parse
%tokentype { Token }
%error { parseError }

%token 
      int             { TokInt _ _ }
      float           { TokFloat _ _ }
      char            { TokChar _ _ }
      dstring         { TokString DoubleQuote _ _ }
      bstring         { TokString BackQuote _ _ }
      '='             { TokSymbol "=" _ }
      '+'             { TokSymbol "+" _ }
      '-'             { TokSymbol "-" _ }
      '*'             { TokSymbol "*" _ }
      '/'             { TokSymbol "/" _ }
      '++'            { TokSymbol "++" _ }
      '<'             { TokSymbol "<" _ }
      '>'             { TokSymbol ">" _ }
      '<='            { TokSymbol "<=" _ }
      '>='            { TokSymbol ">=" _ }
      '=='            { TokSymbol "==" _ }
      '/='            { TokSymbol "/=" _ }
      '|'             { TokSymbol "|" _ }
-- If any other symbol tokens that can be used as funcs or procs are
-- defined here, they need to be added to the defintion of Symbol below
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
      'is'            { TokIdent "is" _ }
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
      'downto'        { TokIdent "downto" _ }
      'by'            { TokIdent "by" _ }
      'and'           { TokIdent "and" _ }
      'or'            { TokIdent "or" _ }
      'not'           { TokIdent "not" _ }
      'foreign'       { TokIdent "foreign" _ }
      ident           { TokIdent _ _ }
      '('             { TokLBracket Paren _ }
      ')'             { TokRBracket Paren _ }
      '['             { TokLBracket Bracket _ }
      ']'             { TokRBracket Bracket _ }
      '{'             { TokLBracket Brace _ }
      '}'             { TokRBracket Brace _ }
      symbol          { TokSymbol _ _ }


%nonassoc 'where' 'let'
%left 'or'
%left 'and'
%left 'not'
%nonassoc 'in'
%left '>' '<' '<=' '>=' '==' '/='
%right '++'
%left '+' '-'
%left '*' '/'
%left NEG
%left '.'
%%

Items :: { [Item] }
    : RevItems                  { reverse $1 }

RevItems :: { [Item] }
    : {- empty -}               { [] }
    | RevItems Item             { $2:$1 }


Item  :: { Item }
    : Visibility 'type' TypeProto '=' Ctors 'end'
                                { TypeDecl $1 $3 $5 $ Just $ tokenPosition $2 }
    | Visibility 'type' TypeProto 'is' Items 'end'
                                { NonAlgType $1 $3 $5 $ 
				    Just $ tokenPosition $2 }
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
    | Symbol OptParamList       { FnProto (symbolName $1) $2 }

Symbol :: { Token }
    : '='             { $1 }
    | '+'             { $1 }
    | '-'             { $1 }
    | '*'             { $1 }
    | '/'             { $1 }
    | '++'            { $1 }
    | '<'             { $1 }
    | '>'             { $1 }
    | '<='            { $1 }
    | '>='            { $1 }
    | '=='            { $1 }
    | '/='            { $1 }
    | '|'             { $1 }
    | '[' ']'         { TokSymbol "[]"  (symbolPos $1) }
    | '[' '|' ']'     { TokSymbol "[|]" (symbolPos $1) }
    | '{' '}'         { TokSymbol "{}"  (symbolPos $1) }
    | symbol          { $1 }


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
    : FlowDirection ident OptType
                                { Param (identName $2) $3 $1 }

FlowDirection :: { FlowDirection }
    : {- empty -}               { ParamIn }
    | '?'                       { ParamOut }
    | '!'                       { ParamInOut }

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
    : ProcArg '=' ProcArg       { maybePlace (ProcCall (symbolName $2) [$1, $3])
	                                     (case $1 of 
					      (ProcArg exp _) -> place exp) }
    | ident OptProcArgs         { Placed (ProcCall (identName $1) $2)
	                                 (tokenPosition $1) }
    | 'foreign' ident ident OptProcArgs
                                { Placed (ForeignCall (identName $2)
					  (identName $3) $4)
                                         (tokenPosition $1) }
    | 'if' Exp 'then' Stmts Condelse 'end'
                                { Placed (Cond $2 $4 $5) (tokenPosition $1) }
    | 'do' LoopBody 'end'       { Placed (Loop $2) (tokenPosition $1) }

LoopBody :: { [Placed LoopStmt] }
    : RevLoopBody               { reverse $1 }

RevLoopBody :: { [Placed LoopStmt] }
    : {- empty -}               { [] }
    | RevLoopBody LoopStmt      { $2:$1 }

LoopStmt :: { Placed LoopStmt }
    : 'for' Generator           { Placed (For $2) (tokenPosition $1) }
    | 'until' Exp               { Placed (BreakIf $2) (tokenPosition $1) }
    | 'while' Exp               { Placed (BreakIf 
					  (maybePlace (Fncall "not" [$2])
					   (place $2)))
	                                 (tokenPosition $1) }
    | 'unless' Exp              { Placed (NextIf $2) (tokenPosition $1) }
    | 'when' Exp                { Placed (NextIf
					  (maybePlace (Fncall "not" [$2])
					   (place $2)))
	                                 (tokenPosition $1) }
    | Stmt                      { maybePlace (NormalStmt $1)
	                                     (place $1) }

OptProcArgs :: { [ProcArg] }
    : {- empty -}               { [] }
    | '(' ProcArg ProcArgList ')'
                                { $2:$3 }

ProcArgList :: { [ProcArg] }
    : RevProcArgList            { reverse $1 }

RevProcArgList :: { [ProcArg] }
    : {- empty -}               { [] }
    | RevProcArgList ',' ProcArg
                                { $3:$1 }

ProcArg :: { ProcArg }
    : FlowDirection Exp         { (ProcArg $2 $1) }

Condelse :: { [Placed Stmt] }
    : 'else' Stmts              { $2 }
    | {- empty -}               { [] }

Generator :: { Generator }
    : ident 'in' Exp            { In (identName $1) $3 }
    | ident 'from' Exp toLimit byStep
                                { InRange (identName $1) $3 
				    (fst $4) $5 (snd $4) }

byStep :: { Placed Exp }
    : 'by' Exp                  { $2 }
    | {- empty -}               { Unplaced $ IntValue 1 }

toLimit :: { (ProcName, Maybe (String,Placed Exp)) }
    : 'to' Exp                  { ("+", Just (">", $2)) }
    | 'downto' Exp              { ("-", Just ("<", $2)) }
    | {- empty -}               { ("+", Nothing) }


Exp :: { Placed Exp }
    : Exp '+' Exp               { maybePlace (Fncall (symbolName $2) [$1, $3])
	                                     (place $1) }
    | Exp '-' Exp               { maybePlace (Fncall (symbolName $2) [$1, $3])
                                             (place $1) }
    | Exp '*' Exp               { maybePlace (Fncall (symbolName $2) [$1, $3])
                                             (place $1) }
    | Exp '/' Exp               { maybePlace (Fncall (symbolName $2) [$1, $3])
                                             (place $1) }
    | Exp '++' Exp              { maybePlace (Fncall (symbolName $2) [$1, $3])
                                             (place $1) }
    | Exp '<' Exp               { maybePlace (Fncall (symbolName $2) [$1, $3])
                                             (place $1) }
    | Exp '<=' Exp              { maybePlace (Fncall (symbolName $2) [$1, $3])
                                             (place $1) }
    | Exp '>' Exp               { maybePlace (Fncall (symbolName $2) [$1, $3])
                                             (place $1) }
    | Exp '>=' Exp              { maybePlace (Fncall (symbolName $2) [$1, $3])
                                             (place $1) }
    | Exp '==' Exp              { maybePlace (Fncall (symbolName $2) [$1, $3])
                                             (place $1) }
    | Exp '/=' Exp              { maybePlace (Fncall (symbolName $2) [$1, $3])
                                             (place $1) }
    | 'not' Exp                 { Placed (Fncall (identName $1) [$2])
	                                 (tokenPosition $1) }
    | Exp 'and' Exp             { maybePlace (Fncall (identName $2) [$1, $3])
	                                     (place $1) }
    | Exp 'or' Exp              { maybePlace (Fncall (identName $2) [$1, $3])
                                             (place $1) }
    | 'if' Exp 'then' Exp 'else' Exp
                                { Placed (CondExp $2 $4 $6)
				         (tokenPosition $1) }
    | 'let' Stmts 'in' Exp      { Placed (Where $2 $4) (tokenPosition $1) }
    | Exp 'where' ProcBody      { maybePlace (Where $3 $1) (place $1) }
    | '(' Exp ')'               { Placed (content $2) (tokenPosition $1) }
    | '-' Exp %prec NEG         { Placed (Fncall "Negate" [$2])
	                                 (tokenPosition $1) }
    | int                       { Placed (IntValue $ intValue $1)
	                                 (tokenPosition $1) }
    | float                     { Placed (FloatValue $ floatValue $1)
	                                 (tokenPosition $1) }
    | char                      { Placed (CharValue $ charValue $1)
	                                 (tokenPosition $1) }
    | dstring                   { Placed (StringValue $ stringValue $1)
	                                 (tokenPosition $1) }
    | bstring                   { Placed (StringValue $ stringValue $1)
	                                 (tokenPosition $1) }
    | ident                     { Placed (Var (identName $1))
	                                 (tokenPosition $1) }
    | ident ArgList             { Placed (Fncall (identName $1) $2)
	                                 (tokenPosition $1) }
    | 'foreign' ident ident ArgList
                                { Placed (ForeignFn (identName $2)
					  (identName $3) $4)
                                         (tokenPosition $1) }
    | '[' ']'                   { Placed (Fncall "[]" [])
	                                 (tokenPosition $1) }
    | '[' Exp ListTail          { Placed (Fncall "[|]" [$2, $3])
	                                 (tokenPosition $1) }
    | '{' '}'                   { Placed (Fncall "{}" [])
	                                 (tokenPosition $1) }

ListTail :: { Placed Exp }
    : ']'                       { Unplaced (Fncall "[]" []) }
    | ',' Exp ListTail          { Unplaced (Fncall "[|]" [$2,$3]) }
    | '|' Exp ']'               { $2 }


ArgList :: { [Placed Exp] }
    : '(' Exp ExpList ')'       { $2:$3 }

ExpList :: { [Placed Exp] }
    : RevExpList                { reverse $1 }

RevExpList :: { [Placed Exp] }
    : {- empty -}               { [] }
    | RevExpList ',' Exp        { $3:$1 }

{
parseError :: [Token] -> a
parseError (tok:_) = error $ (showPosition (tokenPosition tok)) 
                             ++ ": Parse error"
}
