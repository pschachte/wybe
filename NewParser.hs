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


import AST hiding (option)
import Data.Set as Set
import Data.List as List
import Control.Monad.Identity (Identity)
import Scanner
import Text.Parsec
-- import qualified Parser as OldParser
import Text.Parsec.Expr
import Data.Algorithm.Diff (getGroupedDiff)
import Data.Algorithm.DiffOutput (ppDiff)



-- | Alias for our 'Parsec s u'.
type Parser a = Parsec [Token] () a

-- | Alias for Wybe operator token pareser
type WybeOperator a = Operator [Token] () Identity a

-- | Tabulates the precedence and associativeness of 'WybeOperator's.
type WybeOperatorTable a = [[ WybeOperator a ]]



main :: IO ()
main = do
    let file = "test-cases/tests.wybe"
    stream <- fileTokens file
    -- print stream
    -- putStrLn "--------------------"
    case parseWybe stream file of
        Left err -> print err
        Right is -> printItems is

-- | Parse a Wybe module.
parseWybe :: [Token] -> FilePath -> Either ParseError [Item]
parseWybe toks file = parse (itemParser <* eof) file toks


------------- Some testing helpers --------------------

printItems :: [Item] -> IO ()
printItems =  mapM_ (putStrLn . (++ "\n-------") . show)

writeItems :: FilePath -> FilePath -> IO ()
writeItems file to = do
    stream <- fileTokens file
    case parseWybe stream file of
        Left err -> print err
        Right is -> writeFile to (show is)


-- compareOld :: FilePath -> IO ()
-- compareOld file = do
--     stream <- fileTokens file
--     case parseWybe stream file of
--         Left err -> print err
--         Right is -> do
--             let old = OldParser.parse stream
--             let diff = getGroupedDiff (map show old) (map show is)
--             putStrLn "Comparing..."
--             putStrLn $ ppDiff diff

-----------------------------------------------------------------------------
-- Grammar                                                                 --
-----------------------------------------------------------------------------

-- | Parser entry for a Wybe program.
itemParser :: Parser [Item]
itemParser =
    many (visibilityItem <|> topLevelStmtItem)


topLevelStmtItem :: Parser Item
topLevelStmtItem = do
    st <- stmtParser
    return $ StmtDecl (content st) (place st)


-- | Parse 'Item's with the common 'Visibility' prefix.
visibilityItem :: Parser Item
visibilityItem = do
    v <- visibility
    procOrFuncItemParser v
        <|> moduleItemParser v
        <|> typeItemParser v
        <|> resourceItemParser v
        <|> useItemParser v
        <|> fromUseItemParser v


-----------------------------------------------------------------------------
-- Top Level Items                                                         --
-----------------------------------------------------------------------------

-- | Module item parser.
moduleItemParser :: Visibility -> Parser Item
moduleItemParser v = do
    pos <- tokenPosition <$> ident "module"
    modName <- identString <* ident "is"
    body <- itemParser <* ident "end"
    return $ ModuleDecl v modName body (Just pos)


-- | Type declaration item parser.
typeItemParser :: Visibility -> Parser Item
typeItemParser v = do
    pos <- tokenPosition <$> ident "type"
    proto <- TypeProto <$> identString <*>
             option [] (betweenB Paren (identString `sepBy` comma))
    imp <- typeImpParser
    items <- itemParser <* ident "end"
    return $ TypeDecl v proto imp items (Just pos)


-- | Type implementation parser.
typeImpParser :: Parser TypeImpln
typeImpParser =
        TypeRepresentation <$> (ident "is" *> identString)
    <|> TypeCtors <$> (symbol "=" *> visibility) <*>
        funcProtoParser `sepBy` symbol "|"



-- | Resource declaration parser.
resourceItemParser :: Visibility -> Parser Item
resourceItemParser v = do
    pos <- tokenPosition <$> ident "resource"
    let optInit = optionMaybe (symbol "=" *> expParser)
    ResourceDecl v <$> identString
        <*> optType <*> optInit <*> return (Just pos)



useItemParser :: Visibility -> Parser Item
useItemParser v = do
    pos <- tokenPosition <$> ident "use"
    ImportMods v <$> (modSpecParser `sepBy` comma) <*> return (Just pos)


fromUseItemParser :: Visibility -> Parser Item
fromUseItemParser v = do
    pos <- tokenPosition <$> ident "from"
    m <- modSpecParser <* ident "use"
    ids <- identString `sepBy` comma
    return $ ImportItems v m ids (Just pos)




-- | Parse a procedure or function, since both items share the same prefix of
-- 'visibility' 'determinism'.
procOrFuncItemParser :: Visibility -> Parser Item
procOrFuncItemParser v = do
    d <- determinism
    procItemParser v d <|> funcItemParser v d <?> "Procedure/Function"


-- | Procedure parser.
-- Proc -> Vis Det 'proc' ProcProto ProcBody
-- ProcProto -> FuncProcName OptProcParamlist UseResources
-- FuncProcName -> ident | Symbol
-- OptProcparamlist -> '(' ProcParams ')'
-- ProcParam -> FlowDirection ident OptType
procItemParser :: Visibility -> Determinism -> Parser Item
procItemParser vis det = do
    pos <- tokenPosition <$> ident "proc"
    -- Proc proto
    name <- funcNamePlaced <?> "no keywords"
    params <- option [] $ betweenB Paren (procParamParser `sepBy` comma)
    -- Resources
    rs <- option [] (ident "use" *> sepBy resourceFlowSpec comma)
    let proto = ProcProto (content name) params $ fromList rs
    -- ProcBody
    body <- many stmtParser <* ident "end"
    -- Final
    return $
        ProcDecl vis det False proto body (Just pos)


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
funcItemParser :: Visibility -> Determinism -> Parser Item
funcItemParser vis det = do
    pos <- tokenPosition <$> ident "func"
    proto <- content <$> funcProtoParser
    -- Optional return type
    ty <- optType
    -- Function body
    body <- symbol "=" *> expParser
    return $
        FuncDecl vis det False proto ty body (Just pos)


-- | Function prototype parser : FnProto
funcProtoParser :: Parser (Placed FnProto)
funcProtoParser = do
    pName <- funcNamePlaced <?> "no keywords"
    params <- option [] $ betweenB Paren (paramParser `sepBy` comma)
    -- Resource flow specs, optional
    rs <- option [] (ident "use" *> sepBy resourceFlowSpec comma)
    return $ maybePlace (FnProto (content pName) params $fromList rs)
             (place pName)


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
    res <- resourceSpec
    return $ ResourceFlowSpec res flow


resourceSpec :: Parser ResourceSpec
resourceSpec = do
    m <- modSpecParser
    return $ ResourceSpec (init m) (last m)


-- | Optional flow direction symbol prefix.
flowDirection :: Parser FlowDirection
flowDirection =
    option ParamIn $ (ParamOut <$ symbol "?") <|> (ParamInOut <$ symbol "!")


-- | Module name, period separated
modSpecParser :: Parser ModSpec
modSpecParser = identString `sepBy` symbol "."


-- | Parser for an optional type.
optType :: Parser TypeSpec
optType = option AnyType (symbol ":" *> typeParser)


-- | Parser a type.
-- Type -> ident OptTypeList
typeParser :: Parser TypeSpec
typeParser = do
    name <- identString
    optTypeList <- option [] $ betweenB Paren (typeParser `sepBy` comma)
    case name of
        "any" -> return AnyType
        "invalid" -> return InvalidType
        _   -> return $ TypeSpec [] name optTypeList



-----------------------------------------------------------------------------
-- Statement Parsing                                                       --
-----------------------------------------------------------------------------

stmtParser :: Parser (Placed Stmt)
stmtParser =
          doStmt
          <|> forStmt
          <|> whileStmt
          <|> untilStmt
          <|> unlessStmt
          <|> whenStmt
          <|> untilStmt
          <|> ifStmtParser
          <|> useStmt
          <|> simpleStmt


simpleStmt :: Parser (Placed Stmt)
simpleStmt = try procCallParser
          <|> try expStmtParser
          <|> relStmtParser


testStmt :: Parser (Placed Stmt)
testStmt =
          fmap expToStmt <$> simpleExpParser
          -- XXX Need to handle and, or, and not
          -- (   do pos <- tokenPosition <$> ident "and"
          --        rest <- testStmt
          --        return maybePlace (And [stmt1,rest]) pos
          -- <|> do pos <- tokenPosition <$> ident "or"
          --        rest <- testStmt
          --        return maybePlace (And [stmt1,rest]) pos
          -- <|> return [stmt1]
          -- )


-- | A simple proc call stmt.
procCallParser :: Parser (Placed Stmt)
procCallParser = do
    resourceful <- option False (symbol "!" >> return True)
    p <- identButNot keywords
    args <- option [] argListParser
    return $ maybePlace (ProcCall [] (content p) Nothing Det resourceful args)
      (place p)



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
    cond <- testStmt
    return $ Placed (Cond cond [Unplaced Nop] [Unplaced Break]) pos


untilStmt :: Parser (Placed Stmt)
untilStmt = do
    pos <- tokenPosition <$> ident "until"
    e <- testStmt
    return $ Placed (Cond e [Unplaced Break] [Unplaced Nop]) pos


unlessStmt :: Parser (Placed Stmt)
unlessStmt = do
    pos <- tokenPosition <$> ident "unless"
    e <- testStmt
    return $ Placed (Cond e [Unplaced Next] [Unplaced Nop]) pos

whenStmt :: Parser (Placed Stmt)
whenStmt = do
    pos <- tokenPosition <$> ident "when"
    e <- testStmt
    return $ Placed (Cond e [Unplaced Nop] [Unplaced Next]) pos


-- | If statement parser.
ifStmtParser :: Parser (Placed Stmt)
ifStmtParser = do
    pos <- tokenPosition <$> ident "if"
    cases <- (ifCaseParser `sepBy` symbol "|") <* ident "end"
    let final = List.foldr (\(cond, body) rest ->
                           [Unplaced (Cond cond body rest)]) [] cases
    if List.null final
        then unexpected "if cases statement structure."
        else return $ Placed ((content . head) final) pos


ifCaseParser :: Parser (Placed Stmt, [Placed Stmt])
ifCaseParser = do
    cond <- testStmt <* symbol "::"
    body <- many stmtParser
    return (cond, body)


-- | Test statement parser.
-- testStmt :: Parser (Placed Stmt)
-- testStmt = do
--     pos <- tokenPosition <$> ident "test"
--     rel <- relExpParser
--     let e = case rel of
--                 Placed (Var s ParamIn Ordinary) p ->
--                     Placed (Fncall [] s []) p
--                 _ ->
--                     rel
--     return $ Placed (TestBool e) pos
    


useStmt :: Parser (Placed Stmt)
useStmt = do
    pos <- tokenPosition <$> ident "use"
    resources <- resourceSpec `sepBy` comma <* ident "in"
    body <- many1 stmtParser <* ident "end"
    return $ Placed (UseResources resources body) pos


-- | Parse expression statement.
expStmtParser :: Parser (Placed Stmt)
expStmtParser = try foreignCallStmt
             <|> try assignmentParser


foreignCallStmt :: Parser (Placed Stmt)
foreignCallStmt = do
    Placed (ForeignFn a b c d) pos <- foreignExp
    return $ Placed (ForeignCall a b c d) pos


-- | Introduces ambiguity on the token '=', as it is also a binary infix
-- operator in a simple express
assignmentParser :: Parser (Placed Stmt)
assignmentParser = do
    x <- simpleExpTerms <* symbol "="
    y <- expParser
    return $ maybePlace (ProcCall [] "=" Nothing Det False [x,y]) (place x)






-----------------------------------------------------------------------------
-- Expression Parsing                                                      --
-----------------------------------------------------------------------------

-- | Parse expressions.
expParser :: Parser (Placed Exp)
expParser =  buildExpressionParser completeOperatorTable expTerms
         <?> "expresions"


-- | Parse simple expressions.
simpleExpParser :: Parser (Placed Exp)
simpleExpParser =  buildExpressionParser completeOperatorTable simpleExpTerms
               <?> "simple expressions"

-- | Parser for test statements built over the relational operators table and
-- simple expression terms.
relStmtParser :: Parser (Placed Stmt)
relStmtParser = do
    exp <- buildExpressionParser relOperatorTable simpleExpTerms
           <?> "relational expressions"
    return (expToStmt <$> exp)


-- | Exp -> 'if' Exp 'then' Exp 'else' Exp
ifExpParser :: Parser (Placed Exp)
ifExpParser = do
    pos <- tokenPosition <$> ident "if"
    cond <- testStmt
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
              <|> listExpParser
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






-- | Table defining operator precedence and associativeness, helps parsec to
-- deal with expression parsing without ambiguity.
completeOperatorTable :: WybeOperatorTable (Placed Exp)
completeOperatorTable =
    [ [ Postfix funcAppExp ]
    , [ Postfix typedExp ]
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
    , [ binary ">"  AssocNone
      , binary "<"  AssocNone
      , binary "<=" AssocNone
      , binary ">=" AssocNone
      ]
    , [ binary "/=" AssocNone
      , binary "="  AssocNone
      ]
    , [ prefix "not" ]
    , [ binary "and" AssocLeft ]
    , [ binary "or"  AssocLeft ]
    , [ Postfix whereBodyParser]
    ]

-- | Wybe relational operators table, separated out for test statements.
relOperatorTable :: WybeOperatorTable (Placed Exp)
relOperatorTable =
    [ [ binary ">"  AssocNone
      , binary "<"  AssocNone
      , binary "<=" AssocNone
      , binary ">=" AssocNone
      ]
    , [ binary "/=" AssocNone
      , binary "="  AssocNone
      ]
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


typedExp :: Parser (Placed Exp -> Placed Exp)
typedExp = do
    _ <- symbol ":"
    ty <- typeParser
    return $ \e -> maybePlace (Typed (content e) ty False) (place e)


whereBodyParser :: Parser (Placed Exp -> Placed Exp)
whereBodyParser = do
    body <- ident "where" *> many1 stmtParser <* ident "end"
    return $ \e -> maybePlace (Where body e) (place e)


-- | Parse all expressions beginning with the terminal "[".
-- List -> '[' Exp ListTail
-- Empty List -> '[' ']'
-- List Cons -> '[' '|' ']'
listExpParser :: Parser (Placed Exp)
listExpParser = do
    pos <- (tokenPosition <$> leftBracket Bracket) <?> "list"
    rightBracket Bracket *> return (Placed (Fncall [] "[]" []) pos)
        <|> listHeadParser pos


listHeadParser :: SourcePos -> Parser (Placed Exp)
listHeadParser pos = do
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
    <|> symbol "|" *> expParser <* rightBracket Bracket


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
argListParser = betweenB Paren (expParser `sepBy` comma)



foreignExp :: Parser (Placed Exp)
foreignExp = do
    pos <- tokenPosition <$> ident "foreign"
    group <- identString
    fname <- content <$> funcNamePlaced
    flags <- option [] (identString `sepBy` comma)
    args <- argListParser
    return $ Placed (ForeignFn group fname flags args) pos



-----------------------------------------------------------------------------
-- Terminal helpers                                                        --
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

              -- [] or [|]
              , do p <- tokenPosition <$> leftBracket Bracket
                   rightBracket Bracket *> return (Placed "[]" p)
                       <|> symbol "|"
                       *>  rightBracket Bracket
                       *>  return (Placed "[|]" p)

              -- {}
              , tokenPosition <$> leftBracket Brace
                  >>= \p -> return (Placed "{}" p)
                  <*  rightBracket Brace
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


-- | Helper to run a parser between enclosing brackets of the given style.
betweenB :: BracketStyle -> Parser a -> Parser a
betweenB bs = between (leftBracket bs) (rightBracket bs)


-- | Terminal "public" / "private".
visibility :: Parser Visibility
visibility = option Private (ident "public" *> return Public)


-- | Terminal for determinism.
determinism :: Parser Determinism
determinism = option Det (ident "test" *> return SemiDet)


-- | Wybe keywords to exclude from identitfier tokens conditionally.
keywords :: [String]
keywords =
    [ "if", "then", "else", "proc", "end", "use"
    , "do",  "until", "unless", "and", "or", "not", "test", "import"
    , "while", "foreign", "in", "when"
    ]
