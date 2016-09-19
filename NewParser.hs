{-|
Module      : NewParser
Description : Re-write of the Wybe parser using Parsec.
Copyright   : (c) Ashutosh Rishi Ranjan, 2016
License     : GPL-3
Maintainer  : ashutoshrishi92@gmail.com
Stability   : experimental
Portability : POSIX

This module defines the new Wybe language parser written using the Haskell
parser combinator library, "Parsec". The grammar here follows the grammar of
the old happy based parser.
-}

module NewParser where

{-
NOTES:
Parser Type : ParsecT [Token] () Identity a
-}

import AST hiding (option)
import Control.Monad.Identity
import Scanner
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Pos


-- | Alias for our 'Parsec s u'.
type Parser a = Parsec [Token] () a

-- | Alias for Wybe operator token pareser
type WybeOperator a = Operator [Token] () Identity a

-- | Tabulates the precedence and associativeness of 'WybeOperator's.
type WybeOperatorTable a = [[ WybeOperator a ]]



main :: IO ()
main = do
    let file = "tokentest.wybe"
    stream <- fileTokens file
    -- print stream
    -- putStrLn "--------------------"
    case parse itemParser file stream of
        Left err -> print err
        Right items -> printItems items


printItems :: [Item] -> IO ()
printItems =  mapM_ (putStrLn . (++ "\n-------") . show)



foo :: String -> IO ()
foo s = do
    let stream = tokenise (initialPos "<stdin>") s
    case parse itemParser "<stdin>" stream of
        Left err -> print err
        Right expr -> print expr


-----------------------------------------------------------------------------
-- Grammar                                                                 --
-----------------------------------------------------------------------------

-- | Parser entry for a Wybe program.
itemParser :: Parser [Item]
itemParser =
    many procOrFuncParser <* eof



-----------------------------------------------------------------------------
-- Top Level Items                                                         --
-----------------------------------------------------------------------------

-- | Parse a procedure or function, since both items share the same prefix of
-- 'visibility' 'determinism'.
procOrFuncParser :: Parser Item
procOrFuncParser = do
    v <- visibility
    d <- determinism
    procItemParser (v,d) <|> funcItemParser (v,d) <?> "Procedure/Function"


-- | Procedure parser.
-- Proc -> Vis Det 'proc' ProcProto ProcBody
-- ProcProto -> FuncProcName OptProcParamlist UseResources
-- FuncProcName -> ident | Symbol
-- OptProcparamlist -> '(' ProcParams ')'
-- ProcParam -> FlowDirection ident OptType
procItemParser :: (Visibility, Determinism) -> Parser Item
procItemParser (vis, det) = do
    _ <- ident "proc"
    -- Proc proto
    name <- funcNamePlaced <?> "no keywords"
    params <- option [] $ between
              ( leftBracket Paren )
              ( rightBracket Paren )
              ( sepBy procParamParser comma)
    -- Resources
    rs <- option [] (ident "use" *> sepBy resourceFlowSpec comma)
    let proto = ProcProto (content name) params rs
    -- ProcBody
    body <- many stmtParser <* ident "end"
    -- Final
    let pos = place name
    return $
        ProcDecl vis det False proto body pos


-- | A procedure param parser.
-- ProcParam -> FlowDirection ident OptType
procParamParser :: Parser Param
procParamParser = do
    flow <- flowDirection
    name <- identString
    ty <- optType
    return $ Param name ty flow Ordinary


-- | Function parser.
-- Func -> Vis Det func Proto Opttype '=' Exp
-- Proto -> PlacedFuncName OptParamList UseResources
-- PlacedFuncName -> ident | Symbol
-- OptParamList ->   | '(' Params ')'
-- Params -> ident OptType
-- UseResources -> 'use' ResourceFlowSpecs
-- ResourceFlowSpecs -> FlowDirection modIdent
-- modIdent -> ident
-- FlowDirection -> '?' | '!' |
funcItemParser :: (Visibility, Determinism) -> Parser Item
funcItemParser (vis, det) = do
    _ <- ident "func"
    -- Function prototype : FnProto
    pName <- funcNamePlaced <?> "no keywords"
    params <- option [] $ between
              ( leftBracket Paren )
              ( rightBracket Paren )
              ( paramParser `sepBy` comma )
    -- Resource flow specs, optional
    rs <- option [] (ident "use" *> sepBy resourceFlowSpec comma)
    let proto = FnProto (content pName) params rs
    -- Optional return type
    ty <- optType
    -- Function body
    body <- symbol "=" *> expParser
    let pos = place pName
    return $
        FuncDecl vis det False proto ty body pos



-- | Parser for a function 'Param'. The flow is implicitly 'ParamIn' unlike for
-- procedures.
-- Param -> ident OptType
paramParser :: Parser Param
paramParser = do
    name <- identString
    ty <- optType
    return $ Param name ty ParamIn Ordinary



-- | ResourceFlowSpecs -> FlowDirection modIdent
resourceFlowSpec :: Parser ResourceFlowSpec
resourceFlowSpec = do
    flow <- flowDirection
    m <- moduleIdent
    return $ ResourceFlowSpec (ResourceSpec (init m) (last m)) flow


-- | Optional flow direction symbol prefix.
flowDirection :: Parser FlowDirection
flowDirection =
    option ParamIn $ (ParamIn <$ symbol "?") <|> (ParamOut <$ symbol "!")


-- | Module name, period separated
moduleIdent :: Parser ModSpec
moduleIdent = identString `sepBy` symbol "."


-- | Parser for an optional type.
optType :: Parser TypeSpec
optType = option AnyType (symbol ":" *> typeParser)


-- | Parser a type.
-- Type -> ident OptTypeList
typeParser :: Parser TypeSpec
typeParser = do
    name <- identString
    optTypeList <- option [] $ between
                   ( leftBracket Paren )
                   ( rightBracket Paren )
                   ( typeParser `sepBy` comma )
    case name of
        "any" -> return AnyType
        "invalid" -> return InvalidType
        _   -> return $ TypeSpec [] name optTypeList



-----------------------------------------------------------------------------
-- Statement Parsing                                                       --
-----------------------------------------------------------------------------

stmtParser :: Parser (Placed Stmt)
stmtParser =  try assignmentParser
          <|> doStmt
          <|> forStmt
          <|> whileStmt
          <|> untilStmt
          <|> unlessStmt
          <|> whenStmt
          <|> untilStmt
          <|> procCallParser



-- | A simple proc call stmt.
procCallParser :: Parser (Placed Stmt)
procCallParser = do
    p <- identButNot keywords
    args <- option [] argListParser
    return $ maybePlace (ProcCall [] (content p) Nothing args) (place p)


-- | Introduces ambiguity on the token '=', as it is also a binary infix
-- operator in a simple express
assignmentParser :: Parser (Placed Stmt)
assignmentParser = do
    x <- simpleExpParser <* symbol "="
    y <- expParser
    return $ maybePlace (ProcCall [] "=" Nothing [x,y]) (place x)


doStmt :: Parser (Placed Stmt)
doStmt = do
    pos <- tokenPosition <$> ident "do"
    body <- many1 stmtParser <* ident "end"
    return $ Placed (Loop body) pos


forStmt :: Parser (Placed Stmt)
forStmt = do
    pos <- tokenPosition <$> ident "for"
    cond <- expParser <* ident "in"
    body <- expParser
    return $ Placed (For cond body) pos


whileStmt :: Parser (Placed Stmt)
whileStmt = do
    pos <- tokenPosition <$> ident "while"
    e <- expParser
    return $ Placed (Cond [] e [Unplaced Nop] [Unplaced Break]) pos


untilStmt :: Parser (Placed Stmt)
untilStmt = do
    pos <- tokenPosition <$> ident "until"
    e <- expParser
    return $ Placed (Cond [] e [Unplaced Break] [Unplaced Nop]) pos


unlessStmt :: Parser (Placed Stmt)
unlessStmt = do
    pos <- tokenPosition <$> ident "unless"
    e <- expParser
    return $ Placed (Cond [] e [Unplaced Nop] [Unplaced Next]) pos

whenStmt :: Parser (Placed Stmt)
whenStmt = do
    pos <- tokenPosition <$> ident "when"
    e <- expParser
    return $ Placed (Cond [] e [Unplaced Next] [Unplaced Nop]) pos





-----------------------------------------------------------------------------
-- Expression Parsing                                                      --
-----------------------------------------------------------------------------

-- | Parse expressions.
expParser :: Parser (Placed Exp)
expParser =  buildExpressionParser operatorTable expTerms
         <?> "expresions"


-- | Parse simple expressions.
simpleExpParser :: Parser (Placed Exp)
simpleExpParser = buildExpressionParser operatorTable simpleExpTerms


-- | Exp -> 'if' Exp 'then' Exp 'else' Exp
ifExpParser :: Parser (Placed Exp)
ifExpParser = do
    pos <- tokenPosition <$> ident "if"
    cond <- expParser
    thenBody <- ident "then" *> expParser
    elseBody <- ident "else" *> expParser
    return $ Placed (CondExp cond thenBody elseBody) pos


letExpParser :: Parser (Placed Exp)
letExpParser = do
    pos <- tokenPosition <$> ident "let"
    body <- many stmtParser <* ident "in"
    e <- expParser
    return $ Placed (Where body e) pos



expTerms :: Parser (Placed Exp)
expTerms =  ifExpParser
        <|> letExpParser
        <|> simpleExpTerms


simpleExpTerms :: Parser (Placed Exp)
simpleExpTerms =  parenExp
              <|> intExp
              <|> floatExp
              <|> charExp
              <|> stringExp
              <|> outParam
              <|> inoutParam
              <|> try (emptyBrackets Bracket)
              <|> (listExpParser <?> "list")
              -- ident ArgList
              <|> try funcCallParser
              -- ident
              <|> identifier
              <|> try (emptyBrackets Brace)
              <|> foreignExp
              <?> "simple expression terms."



-- | Parenthesised expressions.
parenExp :: Parser (Placed Exp)
parenExp = do
    pos <- tokenPosition <$> leftBracket Paren
    e <- content <$> expParser <* rightBracket Paren
    return $ Placed e pos


typedExp :: Parser (Placed Exp)
typedExp = do
    pExp <- expParser <* symbol ":"
    ty <- typeParser
    return $ maybePlace (Typed (content pExp) ty False) (place pExp)




-- | Table defining operator precedence and associativeness, helps parsec to
-- deal with expression parsing without ambiguity.
operatorTable :: WybeOperatorTable (Placed Exp)
operatorTable =
    [ [ Postfix funcAppExp ]
    , [ prefix "-" ]
    , [ binary "^" AssocLeft ]
    , [ binary "*"   AssocLeft
      , binary "/"   AssocLeft
      , binary "mod" AssocLeft
      ]
    , [ binary "+" AssocLeft
      , binary "-" AssocLeft
      ]
    , [ binary "++" AssocRight ]
    , [ binary' ".." AssocNone [ Unplaced (IntValue 1) ] ]
    , [ binary ">"  AssocLeft
      , binary "<"  AssocLeft
      , binary "<=" AssocLeft
      , binary ">=" AssocLeft
      ]
    , [ binary "/=" AssocNone
      , binary "="  AssocNone
      ]
    , [ prefix "not" ]
    , [ binary "and" AssocLeft ]
    , [ binary "or"  AssocLeft ]
    ]


-- | Helper to make a placed function call expression out of n number of
-- arguments.
makeFnCall :: String -> [Placed Exp] -> Placed Exp
makeFnCall sym args@(x:_) = maybePlace (Fncall [] sym args) (place x)
makeFnCall sym [] = Unplaced (Fncall [] sym [])


-- | Helper to create a binary operator expression parser.
binary :: String -> Assoc -> WybeOperator (Placed Exp)
binary sym = Infix (symOrIdent sym *> return (binFn sym))
  where
    binFn s a b = makeFnCall s [a, b]


-- | Same as 'binary', but takes a list of extra expression arguments to be
-- given to the combined function call expression.
binary' :: String -> Assoc -> [Placed Exp] -> WybeOperator (Placed Exp)
binary' sym assoc exArgs =
    Infix (symOrIdent sym *> return (binFnEx sym)) assoc
  where
    binFnEx s a b = makeFnCall s ([a, b] ++ exArgs)


-- | Helper to create an unary prefix operator expression parser.
prefix :: String -> WybeOperator (Placed Exp)
prefix sym = Prefix (symOrIdent sym *> return (unFn sym))
  where
    unFn s a = makeFnCall s [a]


-- | Helper to parse a symbol or an identifier as the same semantic token.
symOrIdent :: String -> Parser Token
symOrIdent s = choice [ symbol s, ident s]


-- | Postfix '.' operator. There are two variants of the postfix
-- . operator. They are:
-- . ident
-- . ident ( ArgList )
funcAppExp :: Parser (Placed Exp -> Placed Exp)
funcAppExp = do
    nm <- content <$> (symbol "." *> identButNot keywords)
    optargs <- option [] argListParser
    return $ \a ->
        maybePlace (Fncall [] nm (a:optargs)) (place a)



-- | Parse a list.
-- List -> '[' Exp ListTail
listExpParser :: Parser (Placed Exp)
listExpParser = do
    pos <- tokenPosition <$> leftBracket Bracket
    hd <- expParser
    tl <- listTailParser
    return $ Placed (Fncall [] "[|]" [hd, tl]) pos


-- | Parse the tail of a list.
-- ListTail -> ']' | ',' Exp ListTail
listTailParser :: Parser (Placed Exp)
listTailParser =
        rightBracket Bracket *> return (Unplaced (Fncall [] "[]" []))
    <|> comma *>
        do hd <- expParser
           tl <- listTailParser
           return $ Unplaced (Fncall [] "[|]" [hd, tl])
    <|> symbol "|" *> expParser <* symbol "]"


-- | Parse a function call.
-- Exp -> ident ArgList
-- ArgList -> '(' ExpList ')'
funcCallParser :: Parser (Placed Exp)
funcCallParser = do
    pName <- identButNot keywords
    args <- argListParser
    let pos = place pName
    return $ maybePlace (Fncall [] (content pName) args) pos


argListParser :: Parser [Placed Exp]
argListParser =
    between (leftBracket Paren) (rightBracket Paren)
    ( expParser `sepBy` comma )



foreignExp :: Parser (Placed Exp)
foreignExp = do
    pos <- tokenPosition <$> ident "foreign"
    group <- identString
    fname <- content <$> funcNamePlaced
    flags <- option [] (identString `sepBy` comma)
    args <- argListParser
    return $ Placed (ForeignFn group fname flags args) pos



-----------------------------------------------------------------------------
-- Terminals                                                               --
-----------------------------------------------------------------------------

-- | Tests an individual token.
takeToken :: (Token -> Maybe a) -> Parser a
takeToken = token show tokenPosition


-- | Parse a float literal token.
floatExp :: Parser (Placed Exp)
floatExp = takeToken test
    where
      test (TokFloat f p) = Just $ Placed (FloatValue f) p
      test _ = Nothing


-- | Parse an integer literal token.
intExp :: Parser (Placed Exp)
intExp = takeToken test
  where
    test (TokInt i p) = Just $ Placed (IntValue i) p
    test _ = Nothing


charExp :: Parser (Placed Exp)
charExp = takeToken test
    where
      test (TokChar c p) = Just $ Placed (CharValue c) p
      test _ = Nothing


-- | Parse a string literal token.
stringExp :: Parser (Placed Exp)
stringExp = takeToken test
  where
    test (TokString _ s p) = Just $ Placed (StringValue s) p
    test _ = Nothing


outParam :: Parser (Placed Exp)
outParam = do
    pos <- tokenPosition <$> symbol "?"
    s <- content <$> identButNot keywords
    return $ Placed (Var s ParamOut Ordinary) pos

inoutParam :: Parser (Placed Exp)
inoutParam = do
    pos <- tokenPosition <$> symbol "!"
    s <- content <$> identButNot keywords
    return $ Placed (Var s ParamInOut Ordinary) pos


-- | Parse the keyword terminal 'key', in the form of identifier tokens.
ident :: String -> Parser Token
ident key = takeToken test
  where
    test tok@(TokIdent t _) = if t == key then Just tok else Nothing
    test _ = Nothing


-- | Parse an identifier token.
identifier :: Parser (Placed Exp)
identifier = takeToken test
  where
    test (TokIdent s p) =
        if s `elem` keywords
        then Nothing
        else Just $ Placed (Var s ParamIn Ordinary) p
    test _ = Nothing



identString :: Parser String
identString = takeToken test
  where
    test (TokIdent s _) = Just s
    test _ = Nothing


identPlaced :: Parser (Placed String)
identPlaced = takeToken test
  where
    test (TokIdent s p) = Just $ Placed s p
    test _ = Nothing


-- | Parse an ident token if its string value is not in the list 'avoid'.
identButNot :: [String] -> Parser (Placed String)
identButNot avoid = takeToken test
  where
    test (TokIdent s p) =
        if s `elem` avoid then Nothing else Just $ Placed s p
    test _ = Nothing


-- | Parse all symbol tokens.
symbolAny :: Parser Token
symbolAny = takeToken test
  where
    test tok@TokSymbol{} = Just tok
    test _ = Nothing


-- | Parse the symbol token of the string 'symbol'.
symbol :: String -> Parser Token
symbol sym = takeToken test
  where
    test tok@(TokSymbol s _) = if sym == s then Just tok else Nothing
    test _ = Nothing


symbolPlaced :: Parser (Placed String)
symbolPlaced = takeToken test
  where
    test (TokSymbol s p) = Just $ Placed s p
    test _ = Nothing


-- | Parses a function or procedure name.
funcNamePlaced :: Parser (Placed String)
funcNamePlaced = choice [ identButNot keywords
                        , funcSymbolPlaced
                        ]


-- | Symbol function names.
funcSymbolPlaced :: Parser (Placed String)
funcSymbolPlaced =
    let placeToken (TokIdent s p) = Placed s p
        placeToken (TokSymbol s p) = Placed s p
        placeToken _ = error "Only ident and symbol token expected."
    in choice [ placeToken <$> symbolAny
              , placeToken <$> ident "and"
              , placeToken <$> ident "or"
              , placeToken <$> ident "not"
              -- []
              , do t <- leftBracket Bracket <* rightBracket Bracket
                   return $ Placed "[]" (tokenPosition t)
              -- [|]
              , do t <- leftBracket Bracket <* symbol "|"
                        <* rightBracket Bracket
                   return $ Placed "[|]" (tokenPosition t)
              -- {}
              , do t <- leftBracket Brace <* rightBracket Brace
                   return $ Placed "{}" (tokenPosition t)
              ]



-- | Parse a comma token.
comma :: Parser Token
comma = takeToken test
  where
    test tok@TokComma{} = Just tok
    test _ = Nothing





-- | Parse a left bracket of style 'bs'.
leftBracket :: BracketStyle -> Parser Token
leftBracket bs = takeToken test
  where
    test tok@(TokLBracket sty _) = if bs == sty
                                   then Just tok
                                   else Nothing
    test _ = Nothing


-- | Parse a right bracket of style 'bs'.
rightBracket :: BracketStyle -> Parser Token
rightBracket bs = takeToken test
  where
    test tok@(TokRBracket sty _) = if bs == sty
                                  then Just tok
                                  else Nothing
    test _ = Nothing


-- | Parses each of "()", "[]", "{}".
emptyBrackets :: BracketStyle -> Parser (Placed Exp)
emptyBrackets bs = do
    pos <- tokenPosition <$> leftBracket bs <* rightBracket bs
    let fnname = case bs of
            Paren -> "()"
            Bracket -> "[]"
            Brace -> "{}"
    return $ Placed (Fncall [] fnname []) pos


-- | Terminal "public" / "private".
visibility :: Parser Visibility
visibility = option Private (ident "public" *> return Public)


-- | Terminal for determinism.
determinism :: Parser Determinism
determinism = option Det (ident "test" *> return SemiDet)


keywords :: [String]
keywords =
    [ "if", "then", "else", "proc", "end", "use"
    , "do",  "until", "unless", "or", "test", "import"
    , "while", "foreign", "in"
    ]
