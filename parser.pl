% Prolog version of wybe parser

items([]) --> ""
items([Item|Items]) -->
	item(Item),
	items(Items).

item(typedecl(Vis, Typ, Items)) -->
	visibility(Vis),
	"type",
	typeproto(Typ),
	"is",
	items(Items),
	"end".
item(moduledecl(Vis, Id, Items)) -->
	visibility(Vis),
	"module",
	ident(Id),
	"is",
	items(Items),
	"end".
item(importmods(Vis, Mods)) -->
	visibility(Vis),
	"use",
	modspecs(Mods).
item(importitems(Vis, Mod, Ids)) -->
	visibility(Vis),
	"from",
	modspec(Mod),
	"use",
	idents(Ids).
item(resourcedecl(Vis, Id, OptType, OptInit)) -->
	visibility(Vis),
	"resource",
	ident(Id),
	opt(type, OptType),
	opt(init, OptInit).
item(funcdecl(Vis, Proto, Ty, Body)) -->
	visibility(Vis),
	"func",
	fnproto(Proto),
	opt(Type, Ty),
	"=",
	exp(Body).
item(procdecl(Vis, Proto, Body)) -->
	visibility(Vis),
	"proc",
	procproto(Proto),
	procbody(Body).
item(ctordecl(Vis, Proto)) -->
	visibility(Vis),
	"ctor",
	fnproto(Proto).
item(stmtdecl(Stmt)) -->
	stmt(Stmt).


typeproto(type_proto(Id, Opt)) -->
	ident(Id),
	opt_plist(ident, Opt).

modspecs([Mod|Mods]) -->
	modspec(Mod),
	modspeclist(Mods).

modspeclist([]) --> "".
modspeclist((Mod|Mods]) -->
	modspec(Mod),
	",",
	modspeclist(Mods).

modspec([Id|Tail]) -->
	ident(Id),
	moduletail(Tail).

moduletail([]) --> "".
moduletail([Id|Tail]) -->
	ident(Id),
	".",
	moduletail(Tail).

fnproto(fnproto(Nm, Params, Ress)) -->
	funcprocname(Nm),
	opt_plist(param, Params),
	useresources(Ress).

funcprocname(Nm) -->
	ident(Nm).
funcprocname(Nm) -->
	symbol(Nm).


symbol('=') --> "=".
symbol('+') --> "+".
symbol('-') --> "-".
symbol('*') --> "*".
symbol('/') --> "/".
symbol('++') --> "++".
symbol('<') --> "<".
symbol('>') --> ">".
symbol('<=') --> "<=".
symbol('>=') --> ">=".
symbol('==') --> "==".
symbol('/=') --> "/=".
symbol('|') --> "|".
% XXX this does not work:
%    | "..",                      { $1 }
symbol('[]') --> "[]".
symbol('[|]') --> "[|]".
symbol('{}') --> "{}".

procproto(procproto(Name,Params,Resources)) -->
	funcprocname(Name),
	opt_plist(param,Params),
	useresources(Resources).

OptParamList --> ""               { [] }
    | "(", Params, ")",            { $2 }

Params -->
	RevParams                 { reverse $1 }

RevParams -->
	Param                     { [$1] }
    | RevParams, ",", Param       { $3 : $1 }

Param -->
	ident(Id), opt(Type, Opt),            { Param Id $2 ParamIn Ordinary }

OptProcParamList --> ""               { [] }
    | "(", ProcParams, ")",        { $2 }

ProcParams -->
	RevProcParams             { reverse $1 }

RevProcParams -->
	ProcParam                 { [$1] }
    | RevProcParams, ",", ProcParam
                                { $3 : $1 }

ProcParam -->
	FlowDirection, ident(Id), OptType
                                { Param Id $3 $1 Ordinary}

FlowDirection --> ""               { ParamIn }
    | "?",                       { ParamOut }
    | "!",                       { ParamInOut }

OptType --> ""               { Unspecified }
    | ":", Type,                  { $2 }


Type -->
	ident(Id), opt(TypeList, Opt),        { TypeSpec [] Id $2 }

OptTypeList --> ""               { [] }
    | "(", Types, ")",             { $2 }

Types -->
	RevTypes                  { reverse $1 }

RevTypes -->
	Type                      { [$1] }
    | RevTypes, ",", Type         { $3 : $1 }


OptIdents --> ""               { [] }
    | "(", Idents, ")",            { $2 }

Idents -->
	RevIdents                 { reverse $1 }

RevIdents -->
	ident                     { [identName $1] }
    | RevIdents, ",", ident       { Id:$1 }

Visibility(private) --> "".
Visibility(public) --> "public".

UseResources --> ""               { [] }
    | "use", ResourceFlowSpecs       { $2 }


ResourceFlowSpecs -->
	ResourceFlowSpec, RevResourceFlowSpecs
                                { $1 : reverse $2 }

RevResourceFlowSpecs --> ""               { [] }
    | RevResourceFlowSpecs, ",", ResourceFlowSpec
                                { $3:$1 }

ResourceFlowSpec -->
	FlowDirection, modIdent    { ResourceFlowSpec 
	                          (ResourceSpec (fst $2) (snd $2))
                                  $1 }


modIdent -->
	revDottedIdents, ident     { (reverse $1,identName $2) }


revDottedIdents --> ""               { [] }
    | revDottedIdents, ".", ident
                                { (identName $2:$1) }


ProcBody -->
	Stmts, "end",               { $1 }

Stmts -->
	RevStmts                  { reverse $1 }

RevStmts --> ""               { [] }
    | RevStmts, Stmt             { $2:$1 }

Stmt -->
	StmtExp                   { fmap expToStmt $1 }
    | "if", Exp, "then", Stmts, Condelse
                                { Placed (Cond [] $2 $4 $5)
                                 (tokenPosition $1) }
    | "do", Stmts, "end",          { Placed (Loop $2)
                                  (tokenPosition $1) }
    | "for", Exp, "in", Exp        { Placed (For $2 $4)
                                  (tokenPosition $1) }
    | "until", Exp               { Placed (Cond [] $2 [Unplaced $ Break]
                                                     [Unplaced $ Nop])
                                  (tokenPosition $1) }
    | "while", Exp               { Placed (Cond [] $2 [Unplaced $ Nop]
                                                     [Unplaced $ Break])
                                  (tokenPosition $1) }
    | "unless", Exp              { Placed (Cond [] $2 [Unplaced $ Nop]
                                                     [Unplaced $ Next])
                                         (tokenPosition $1) }
    | "when", Exp                { Placed (Cond [] $2 [Unplaced $ Next]
					             [Unplaced $ Nop])
                                         (tokenPosition $1) }

Condelse --> "else", Stmts, "end",        { $2 }
    |  "end",                    { [] }


OptInit --> ""               { Nothing }
    | "=", Exp                   { Just $2 }



SimpleExp -->
	Exp, "+", Exp               { maybePlace (Fncall [] (symbolName $2)
                                              [$1, $3])
	                                     (place $1) }
    | Exp, "-", Exp               { maybePlace (Fncall [] (symbolName $2)
                                              [$1, $3])
                                             (place $1) }
    | Exp, "*", Exp               { maybePlace (Fncall [] (symbolName $2)
                                              [$1, $3])
                                             (place $1) }
    | Exp, "/", Exp               { maybePlace (Fncall [] (symbolName $2)
                                              [$1, $3])
                                             (place $1) }
    | Exp, "mod", Exp             { maybePlace (Fncall [] (identName $2)
                                              [$1, $3])
                                             (place $1) }
    | Exp, "^", Exp               { maybePlace (Fncall [] (symbolName $2)
                                              [$1, $3])
                                             (place $1) }
    | Exp, "++", Exp              { maybePlace (Fncall [] (symbolName $2)
                                              [$1, $3])
                                             (place $1) }
    | Exp, "<", Exp               { maybePlace (Fncall [] (symbolName $2)
                                              [$1, $3])
                                             (place $1) }
    | Exp, "<=", Exp              { maybePlace (Fncall [] (symbolName $2)
                                              [$1, $3])
                                             (place $1) }
    | Exp, ">", Exp               { maybePlace (Fncall [] (symbolName $2)
                                              [$1, $3])
                                             (place $1) }
    | Exp, ">=", Exp              { maybePlace (Fncall [] (symbolName $2)
                                              [$1, $3])
                                             (place $1) }
    | Exp, "==", Exp              { maybePlace (Fncall [] (symbolName $2)
                                              [$1, $3])
                                             (place $1) }
    | Exp, "/=", Exp              { maybePlace (Fncall [] (symbolName $2)
                                              [$1, $3])
                                             (place $1) }
%    | "not", Exp                 { Placed (Fncall [] (identName $1) [$2])
%	                                 (tokenPosition $1) }
%    | Exp, "and", Exp             { maybePlace (Fncall [] (identName $2)
%                                              [$1, $3])
%	                                     (place $1) }
%    | Exp, "or", Exp              { maybePlace (Fncall [] (identName $2)
%                                              [$1, $3])
%                                             (place $1) }
%    | Exp, "..", Exp              { maybePlace (Fncall [] (symbolName $2) 
%					      [$1, $3, Unplaced $ IntValue 1])
%                                             (place $1) }
    | "(", Exp, ")",               { Placed (content $2) (tokenPosition $1) }
    | "-", Exp, %prec NEG         { Placed (Fncall [] "-" [$2])
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
    | "?", ident                 { Placed (Var (identName $2) ParamOut Ordinary)
	                                 (tokenPosition $1) }
    | "!", ident                 { Placed (Var (identName $2) 
					  ParamInOut Ordinary)
	                                 (tokenPosition $1) }
    | "[", "]",                   { Placed (Fncall [] "[]" [])
	                                 (tokenPosition $1) }
    | "[", Exp, ListTail          { Placed (Fncall [] "[|]" [$2, $3])
	                                 (tokenPosition $1) }
    | "{", "}",                   { Placed (Fncall [] "{}" [])
	                                 (tokenPosition $1) }
    | Exp, ":", Type              { maybePlace (Typed (content $1) $3)
	                                 (place $1) }
    | StmtExp                   { $1 }

Exp --> "if", Exp, "then", Exp, "else", Exp
                                { Placed (CondExp $2 $4 $6)
				         (tokenPosition $1) }
    | "let", Stmts, "in", Exp      { Placed (Where $2 $4) (tokenPosition $1) }
    | Exp, "where", ProcBody      { maybePlace (Where $3 $1) (place $1) }
    | SimpleExp                 { $1 }


StmtExp -->
	ident                     { Placed (Var (identName $1) ParamIn Ordinary)
	                                 (tokenPosition $1) }
    | Exp, "=", Exp               { maybePlace (Fncall [] (symbolName $2)
                                              [$1, $3])
                                             (place $1) }
    | ident(Id), ArgList             { Placed (Fncall [] (identName $1) $2)
	                                 (tokenPosition $1) }
    | Exp, ".", ident(Id), ArgList     { maybePlace (Fncall [] (identName $3) ($1:$4))
	                                     (place $1) }
    | Exp, ".", ident             { maybePlace (Fncall [] (identName $3) [$1])
	                                     (place $1) }
    | symbol, ArgList            { Placed (Fncall [] (symbolName $1) $2)
	                                 (tokenPosition $1) }
    | "foreign", ident(Id), FuncProcName, flags, ArgList
                                { Placed (ForeignFn (identName $2)
					  $3 $4 $5)
                                         (tokenPosition $1) }

flags -->
	revFlags                  { reverse $1 }

revFlags --> ""               { [] }
    | revFlags, ident            { identName $2:$1 }


--optMod --> ""               { [] }
%    | ModSpec, ".",               { $1 }


ListTail --> "]",                       { Unplaced (Fncall [] "[]" []) }
    | ",", Exp, ListTail          { Unplaced (Fncall [] "[|]" [$2,$3]) }
    | "|", Exp, "]",               { $2 }


OptArgList --> ""               { [] }
    | "(", Exp, ExpList, ")",       { $2:$3 }

ArgList --> "(", Exp, ExpList, ")",       { $2:$3 }

ExpList -->
	RevExpList                { reverse $1 }

RevExpList --> ""               { [] }
    | RevExpList, ",", Exp,        { $3:$1 }
