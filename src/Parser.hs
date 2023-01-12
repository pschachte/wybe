{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
--  File     : Parser.hs
--  Author   : Peter Schachte <schachte@unimelb.edu.au>
--  Purpose  : Parser for the Wybe language using Parsec.
--  Copyright: (c) 2021 Peter Schachte
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

module Parser where


import AST hiding (option)
import Data.Set as Set
import Data.List as List
import Data.Maybe as Maybe
import Data.Bits
import Data.Either.Extra (mapLeft)
import Control.Monad.Identity (Identity)
import Scanner
import Util
import Snippets
import Config
import Text.Parsec
import Text.Parsec.Pos
import Data.Functor
import Control.Monad
import Debug.Trace


-----------------------------------------------------------------------------
-- Top level of the parser:  parsing Items                                 --
-----------------------------------------------------------------------------

-- | The parser monad.
type Parser a = Parsec [Token] () a


-- | Report a syntax error
syntaxError :: SourcePos -> String -> Either (SourcePos,String) a
syntaxError pos msg = Left (pos,msg)


-- | Get the currnt SourcePos of the Parser
sourcePos :: Parser SourcePos
sourcePos = statePos <$> getParserState


-- | Parse a Wybe module.
parseWybe :: [Token] -> FilePath -> Either ParseError [Item]
parseWybe toks file = parse (maybeSetPosition toks items <* eof) file toks


-- | Set the Parser position to the position of the head Token, if it exists
maybeSetPosition :: [Token] -> Parser a -> Parser a
maybeSetPosition toks parser = do
    maybe (return ()) (setPosition . tokenPosition) $ listToMaybe toks
    parser


-- | Parser entry for a Wybe program, items separated by some separator.
items :: Parser [Item]
items = item `sepBy` separator


-- | Parse a single items
item :: Parser Item
item = visibilityItem <|> privateItem <|> topLevelStmtItem


-- | Parse a top-level statement itme
topLevelStmtItem :: Parser Item
topLevelStmtItem = do
    st <- stmt <?> "top-level statement"
    return $ StmtDecl (content st) (place st)


-- | Parse 'Item's with the common 'Visibility' prefix.
visibilityItem :: Parser Item
visibilityItem = do
    v <- visibility
    procOrFuncItem v
        <|> moduleItem v
        <|> typeItem v
        <|> dataCtorItemParser v
        <|> resourceItem v
        <|> useItemParser v
        <|> fromUseItemParser v
    <?> "top-level item"


-- | Parse module-local items (with no visibility prefix).
privateItem :: Parser Item
privateItem = typeRepItem <|> pragmaItem


-- | Parse a pragma item
pragmaItem :: Parser Item
pragmaItem = ident "pragma" *> (PragmaDecl <$> parsePragma)


-- TODO:  Should use the Term parser to parse the declaration body.
-- | Parse a Pragma, currently only "no_standard_library"
parsePragma :: Parser Pragma
parsePragma = ident "no_standard_library" $> NoStd


-- | Module item parser.
moduleItem :: Visibility -> Parser Item
moduleItem v = do
    pos <- tokenPosition <$> ident "module"
    modName <- moduleName
    body <- betweenB Brace items
    return $ ModuleDecl v modName body (Just pos)


-- | Type declaration item parser.
typeItem :: Visibility -> Parser Item
typeItem v = do
    pos <- tokenPosition <$> ident "type"
    modifiers <- List.foldl processTypeModifier defaultTypeModifiers
                 <$> modifierList
    proto <- TypeProto <$> moduleName <*> typeVarNames
    (imp, items) <- typeImpln <|> typeCtors
    return $ TypeDecl v proto modifiers imp items (Just pos)


-- | Module type representation declaration
typeRepItem :: Parser Item
typeRepItem = do
    keypos <- tokenPosition <$> ident "representation"
    params <- typeVarNames
    ident "is"
    modifiers <- List.foldl processTypeModifier defaultTypeModifiers
                 <$> modifierList
    rep <- typeRep
    return $ RepresentationDecl params modifiers rep $ Just keypos


-- | Module type representation declaration
dataCtorItemParser :: Visibility -> Parser Item
dataCtorItemParser v = do
    pos <- tokenPosition <$> (ident "constructor" <|> ident "constructors")
    params <- typeVarNames
    modifiers <- List.foldl processTypeModifier defaultTypeModifiers
                 <$> modifierList
    ctors <- ctorDecls
    return $ ConstructorDecl v params modifiers ctors $ Just pos


-- | Type declaration body where representation and items are given
typeImpln :: Parser (TypeImpln, [Item])
typeImpln = do
    impln <- TypeRepresentation <$> (ident "is" *> typeRep)
    items <- betweenB Brace items
    return (impln,items)


-- | Type declaration body where representation and items are given
typeRep :: Parser TypeRepresentation
typeRep = do
    ident "address" $> Address
    <|> do bits <- option wordSize
                   (fromIntegral . content <$> intLiteral <* ident "bit")
           ident "unsigned" $> Bits bits
            <|> ident "signed" $> Signed bits
            <|> ident "float" $> Floating bits


-- | Type declaration body where visibility, constructors, and items are given
typeCtors :: Parser (TypeImpln,[Item])
typeCtors = betweenB Brace $ do
    vis <- option Private 
        $ try (visibility <* (ident "constructor" <|> ident "constructors"))
    ctors <- TypeCtors vis <$> ctorDecls
    items <- option [] (separator *> items)
    return (ctors, items)


-- | Parse a collection of Constructor declarations, separated by `|`s
ctorDecls :: Parser [(Visibility, Placed ProcProto)]
ctorDecls = (visibility >>= \vis -> (vis,) <$> (term >>= parseWith termToCtorDecl)) `sepBy1` symbol "|"


-- | Resource declaration parser.
resourceItem :: Visibility -> Parser Item
resourceItem v = do
    pos <- tokenPosition <$> ident "resource"
    let optInit = optionMaybe (symbol "=" *> expr)
    ResourceDecl v <$> identString <* symbol ":"
        <*> typeSpec <*> optInit <*> return (Just pos)


-- | Parse a "use" item. Either an import statement or a use-block
useItemParser :: Visibility -> Parser Item
useItemParser v = do
    pos <- Just . tokenPosition <$> ident "use"
    ident "foreign" *> foreignFileOrLib v pos
      <|> (moduleSpec `sepBy` comma >>= useBody v pos)

-- | Parse a foreign library or object import
foreignFileOrLib :: Visibility -> OptPos -> Parser Item
foreignFileOrLib v pos =
    ImportForeignLib
        <$> (ident "library" *> identString `sepBy` comma) <*> return pos
    <|> ImportForeign
            <$> (ident "object" *> identString `sepBy` comma) <*> return pos

-- | Parse a use-block body or an import statement
useBody :: Visibility -> OptPos -> [ModSpec] -> Parser Item
useBody v pos mods =
    (ident "in" *> do
        if v == Private
        then topLevelUseStmt pos (modSpecToResourceSpec <$> mods)
        else fail "invalid use-block")
    <|> return (ImportMods v mods pos)

-- | Parse a top-level use statement with specified
topLevelUseStmt :: OptPos -> [ResourceSpec] -> Parser Item
topLevelUseStmt pos ress = do
    body <- stmtSeq
    return $ StmtDecl (UseResources ress Nothing body) pos


-- | Convert a ModSpce to a ResourceSpec
modSpecToResourceSpec :: ModSpec -> ResourceSpec
modSpecToResourceSpec modspec = ResourceSpec (init modspec) (last modspec)


-- | Parse a from-use item
fromUseItemParser :: Visibility -> Parser Item
fromUseItemParser v = do
    pos <- tokenPosition <$> ident "from"
    m <- moduleSpec <* ident "use"
    ids <- identString `sepBy` comma
    return $ ImportItems v m ids (Just pos)


-- | Parse a procedure or function, since both items share the same prefix of
-- 'visibility' 'determinism'.
procOrFuncItem :: Visibility -> Parser Item
procOrFuncItem vis = do
    pos <- tokenPosition <$> ident "def"
    mods <- modifierList >>= parseWith (processProcModifiers pos "procedure or function declaration")
    (proto, returnType) <- limitedTerm prototypePrecedence
                            >>= parseWith termToPrototype
    do
        body <- symbol "=" *> expr
        return $ FuncDecl vis mods proto returnType body $ Just pos
      <|> if returnType /= AnyType
          then fail "unexpected return type in proc declaration"
          else do
            rs <- option [] (ident "use" *> resourceFlowSpec `sepBy1` comma)
            let proto' = proto { procProtoResources = Set.fromList rs }
            body <- embracedTerm >>= parseWith termToBody
            return $ ProcDecl vis mods proto' body $ Just pos


-- | Parse a specification of a resource and its flow direction.
resourceFlowSpec :: Parser ResourceFlowSpec
resourceFlowSpec = do
    flow <- flowDirection
    res <- resourceSpec
    return $ ResourceFlowSpec res flow


-- | Parse a resource spec
resourceSpec :: Parser ResourceSpec
resourceSpec = moduleSpec <&> modSpecToResourceSpec


-- | Optional flow direction symbol prefix.
flowDirection :: Parser FlowDirection
flowDirection =
    option ParamIn $ symbol "?" $> ParamOut <|> symbol "!" $> ParamInOut


-----------------------------------------------------------------------------
-- Handling type modifiers                                                 --
-----------------------------------------------------------------------------
-- | Add a type modifier by name to a TypeModifiers.
processTypeModifier :: TypeModifiers -> Ident -> TypeModifiers
processTypeModifier tms "unique" = tms {tmUniqueness = True}
processTypeModifier tms unknown  = tms {tmUnknown = tmUnknown tms ++ [unknown]}


-----------------------------------------------------------------------------
-- Handling proc modifiers                                                 --
-----------------------------------------------------------------------------

-- | Extract a ProcModifiers from a list of identifiers.  If the Bool is False,
-- then don't report any errors in the modifiers.  The position is the source
-- location of the list of modifiers.
processProcModifiers :: SourcePos -> String -> [String] -> Either (SourcePos,String) ProcModifiers
processProcModifiers pos ctx
    = mapLeft (pos,) . foldM (flip $ processProcModifier ctx) defaultProcModifiers

-- | Update a collection of ProcModifiers
processProcModifier :: String -> String -> ProcModifiers -> Either String ProcModifiers
processProcModifier ctx "test"     = updateModsDetism   ctx "test" SemiDet
processProcModifier ctx "partial"  = updateModsDetism   ctx "partial" SemiDet
processProcModifier ctx "failing"  = updateModsDetism   ctx "failing" Failure
processProcModifier ctx "terminal" = updateModsDetism   ctx "terminal" Terminal
processProcModifier ctx "inline"   = updateModsInlining ctx "inline" Inline
processProcModifier ctx "noinline" = updateModsInlining ctx "noinline" NoInline
processProcModifier ctx "pure"     = updateModsImpurity ctx "pure" PromisedPure
processProcModifier ctx "semipure" = updateModsImpurity ctx "semipure" Semipure
processProcModifier ctx "impure"   = updateModsImpurity ctx "impure" Impure
processProcModifier ctx "resource" = updateModsResource ctx "resource" True
processProcModifier ctx modName    = 
    const $ Left $ "Unknown modifier '" ++ modName ++ "' in " ++ ctx



-- | Update the ProcModifiers to specify the given determinism, which was
-- specified with the given identifier.  Since Det is the default, and can't be
-- explicitly specified, it's alway OK to change from Det to something else.
updateModsDetism :: String -> String -> Determinism -> ProcModifiers 
                 -> Either String ProcModifiers
updateModsDetism _ _ detism mods@ProcModifiers{modifierDetism=Det} =
    return mods {modifierDetism=detism}
updateModsDetism ctx modName detism mods =
    Left $ modifierConflictMsg modName ctx


-- | Update the ProcModifiers to specify the given inlining, which was specified
-- with the given identifier.  Since MayInline is the default, and can't be
-- explicitly specified, it's alway OK to change from MayInline to something
-- else.
updateModsInlining :: String -> String -> Inlining -> ProcModifiers 
                   -> Either String ProcModifiers
updateModsInlining _ _ inlining mods@ProcModifiers{modifierInline=MayInline} =
    return $ mods {modifierInline=inlining}
updateModsInlining ctx modName _ mods =    
    Left $ modifierConflictMsg modName ctx
    

-- | Update the ProcModifiers to specify the given Impurity, which was specified
-- with the given identifier.  Since Pure is the default, and can't be
-- explicitly specified, it's alway OK to change from Pure to something
-- else.
updateModsImpurity :: String -> String -> Impurity -> ProcModifiers 
                   -> Either String ProcModifiers
updateModsImpurity _ _ impurity mods@ProcModifiers{modifierImpurity=Pure} =
    return $ mods {modifierImpurity=impurity}
updateModsImpurity ctx modName _ mods =    
    Left $ modifierConflictMsg modName ctx

-- | Update the ProcModifiers to specify the given Resourcefulness, which was 
-- specified with the given identifier.  Since resourceless is the default, 
-- and can't be explicitly specified, it's alway OK to change from resourceless
-- to resourceful.
updateModsResource :: String -> String -> Bool -> ProcModifiers 
                   -> Either String ProcModifiers
updateModsResource _ _ resful mods@ProcModifiers{modifierResourceful=False} =
    return $ mods {modifierResourceful=resful}
updateModsResource ctx modName _ mods =
    Left $ modifierConflictMsg modName ctx


modifierConflictMsg :: String -> String -> String
modifierConflictMsg mod ctx = 
    "Modifier '" ++ mod ++ "' conflicts with earlier modifier in " ++ ctx


modifierError :: SourcePos -> String -> String -> Either (SourcePos,String) a
modifierError pos modName ctx = 
    syntaxError pos $ "Modifier '" ++ modName ++ "' cannot be used in a " ++ ctx

-----------------------------------------------------------------------------
-- Combined statement and expression parsing                               --
--
-- While parsing statements, sometimes it is not clear whether the part just
-- read will turn out to be a statement or expression.  For example, if the
-- first thing you see when trying to parse a statement is
--
--    foo(a,b)
--
-- the parser does not know whether this is the end of the statment, meaning
-- foo(a,b) is a statement, or whether it will be followed by
--
--    = bar
--
-- meaning the foo(a,b) part is an expression.  Therefore, we define a type that
-- does not distinguish between expression and statement to be used until the
-- whole statement has been read.  After that, its parts will be converted to
-- expressions and statements as appropriate.
-----------------------------------------------------------------------------

-- |Parse a body.
stmtSeq :: Parser [Placed Stmt]
stmtSeq = term >>= parseWith termToBody


-- |Parse a single Placed Stmt.
stmt :: Parser (Placed Stmt)
stmt = limitedTerm lowestStmtPrecedence >>= parseWith termToStmt


-- |Parse a placed Exp
expr :: Parser (Placed Exp)
expr = term >>= parseWith termToExp
    <?> "expression"


-- | Parse a TypeSpec
typeSpec :: Parser TypeSpec
typeSpec = limitedTerm prototypePrecedence >>= parseWith termToTypeSpec


-- |Parse a term.
term :: Parser Term
term = limitedTerm lowestTermPrecedence


-- |A term with an operator precedence of limited looseness.
limitedTerm :: Int -> Parser Term
limitedTerm precedence = termFirst >>= termRest precedence


-- |The left argument to an infix operator.  This is a primaryTerm,
-- possibly preceded by a prefix operator or followed by an termSuffix.
-- Valid suffixes include parenthesised argument lists or square bracketed
-- indices.  If both prefix and suffix are present, the suffix binds tighter.
termFirst :: Parser Term
termFirst = 
    ((prefixOp >>= (primaryTerm >>=) . applyPrefixOp) <|> primaryTerm) 
        >>= termSuffix


-- |Apply zero or more parenthesised or square bracketed suffixes to the
-- specified term. If multiple suffixes are present, they associate to the
-- left.
termSuffix :: Term -> Parser Term
termSuffix left =
    (try (termSuffix' left) >>= termSuffix) <|> return left


-- |Apply one parenthesised or square bracketed suffixes to the specified
-- term.
termSuffix' :: Term -> Parser Term
termSuffix' left =
    (argumentList Paren >>= applyArguments left)
    <|> (embracedTerm >>= applyEmbraced left)
    <|> (Call (termPos left) [] "[]" ParamIn . (left:)
         <$> argumentList Bracket)


-- |Comma-separated, non-empty argument list, surrounded by the specified
-- bracket type.
argumentList :: BracketStyle -> Parser [Term]
argumentList Brace = shouldnt "brace-enclosed argument list"
argumentList bracket = betweenB bracket (term `sepBy` comma)


-- |Supply arguments to function call we thought was something else.
applyArguments :: Term -> [Term] -> Parser Term
applyArguments term args =
    case term of
        call@Call{} ->
            return $ call {callArguments = callArguments call ++ args}
        embraced@Embraced{embracedArg=Nothing, embracedPos=pos} ->
            return $ embraced{embracedArg=Just $ Embraced pos Paren args Nothing}
        other -> fail $ "unexpected argument list following expression "
                        ++ show other

applyEmbraced :: Term -> Term -> Parser Term
applyEmbraced expr@(Embraced _ Brace _ Nothing) arg =
    return expr{embracedArg=Just arg}
applyEmbraced expr _ = fail $ "unexpected embraced term following " ++ show expr


-- |Complete parsing an term of precedence no looser than specified, given
-- that we have already parsed the specified term on the left.
-- XXX this doesn't handle non-associative operators correctly; it treats them
-- as right associative.
termRest :: Int -> Term -> Parser Term
termRest minPrec left =
    do -- A functional Pratt operator precedence parser
         -- parse an infix operator of at least the specified precedence
        (op,rightPrec) <- infixOp minPrec
        -- parse expression of high enough precedence to be the right argument
        right <- limitedTerm rightPrec
        let pos = termPos left
        -- construct a call of the op with the left and right arguments, and
        -- treat that as the left argument of the rest of the expr
        termRest minPrec $ Call pos [] op ParamIn [left,right]
    <|> -- Otherwise try to parse a call with 1 un-parenthesised argument;
        -- failing that, the left context is the whole expression.
        case left of
            Call _ m n _ [] | minPrec <= lowestStmtPrecedence
                            || List.null m && prefixKeyword n ->
                (term
                    >>= applyArguments left . (:[])
                    >>= termRest minPrec)
                <|> return left
            _ -> return left


-- |Scan an infix operator of at least the specified left precedence, returning
-- the operator and its right precedence.
infixOp :: Int -> Parser (String,Int)
infixOp minPrec = takeToken test
  where
    test tok
      | lPrec > minPrec && isInfixOp tok = Just (name, prec)
      | otherwise                        = Nothing
        where name = tokenName tok
              (prec,assoc) = operatorAssociativity name
              lPrec = prec + if assoc == LeftAssociative  then 0 else 1
              rPrec = prec - if assoc /= RightAssociative then 0 else 1


-- |Parse a simple, Term, not involving any operators.
primaryTerm :: Parser Term
primaryTerm =
    parenthesisedTerm
    <|> embracedTerm
    <|> foreignCall
    <|> forLoop
    <|> varOrCall
    <|> anonParamVar
    <|> intConst
    <|> floatConst
    <|> charConst
    <|> stringConst
    <|> listTerm
    <?> "simple expression"


parenthesisedTerm :: Parser Term
parenthesisedTerm = do
    pos <- sourcePos
    exps <- betweenB Paren (limitedTerm lowestParenthesisedPrecedence
                            `sepBy` comma)
    return $ Embraced pos Paren exps Nothing


varOrCall :: Parser Term
varOrCall = do
    pos <- getPosition
    modVar <- moduleSpec
    return $ Call pos (init modVar) (last modVar) ParamIn []


anonParamVar :: Parser Term
anonParamVar = do
    pos <- tokenPosition <$> symbol "@"
    num <- optionMaybe intConst
    return $ Call pos [] "@" ParamIn $ maybeToList num


-- | Parse a sequence of Terms enclosed in braces.
embracedTerm :: Parser Term
embracedTerm = do
    pos <- tokenPosition <$> leftBracket Brace
    embraced <- Embraced pos Brace
        <$> limitedTerm lowestStmtSeqPrecedence `sepBy` comma
        <* rightBracket Brace
    return $ embraced Nothing


-- | Parse all expressions beginning with the terminal "[".
-- List -> '[' Term ListTail
-- Empty List -> '[' ']'
-- List Cons -> '[' '|' ']'
listTerm :: Parser Term
listTerm = do
    pos <- (tokenPosition <$> leftBracket Bracket) <?> "list"
    rightBracket Bracket $> Call pos [] "[]" ParamIn []
        <|> do
            head <- term
            tail <- listTail
            return $ Call pos [] "[|]" ParamIn [head,tail]


-- | Parse the tail of a list.
-- ListTail -> ']' | ',' Term ListTail
listTail :: Parser Term
listTail = do
        pos <- tokenPosition <$> rightBracket Bracket
        return $ Call pos [] "[]" ParamIn []
    <|> do
        pos <- tokenPosition <$> comma
        head <- term
        tail <- listTail
        return $ Call pos [] "[|]" ParamIn [head, tail]
    <|> symbol "|" *> term <* rightBracket Bracket


-- |A foreign function or procedure call.
foreignCall :: Parser Term
foreignCall = do
    pos <- tokenPosition <$> ident "foreign"
    language <- identString
    flags <- modifierList
    fname <- identString
    Foreign pos language fname flags <$> argumentList Paren


-- |A for loop.
forLoop :: Parser Term
forLoop = do
    pos <- tokenPosition <$> ident "for"
    gen <- limitedTerm lowestStmtSeqPrecedence
    body <- embracedTerm
    return $ Call pos [] "for" ParamIn [gen,body]


-----------------------------------------------------------------------------
-- Operators                                                               --
-----------------------------------------------------------------------------

-- |Allowable operator associativities.
data Associativity = LeftAssociative | NonAssociative | RightAssociative
    deriving (Eq,Show)


-- |The precedence and associativity of the specified operator.  Covers all
-- operator symbols.
-- TODO decide how to handle: @ $ \ :
operatorAssociativity :: String -> (Int,Associativity)
operatorAssociativity ":"  = (11, LeftAssociative)
operatorAssociativity ":!" = (11, LeftAssociative)
operatorAssociativity ","  = ( 0, RightAssociative)
operatorAssociativity ";"  = (-1, RightAssociative)
operatorAssociativity "\n" = (-1, RightAssociative)
operatorAssociativity "::" = (-2, NonAssociative)
operatorAssociativity "|"  = (-3, RightAssociative)
operatorAssociativity str
  | infixKeyword str = ( 5, NonAssociative)
  | otherwise =
    case last str of
        '^' -> (10, LeftAssociative)
        '*' -> ( 9, LeftAssociative)
        '/' -> ( 9, LeftAssociative)
        '%' -> ( 9, LeftAssociative)
        '+' -> ( 8, LeftAssociative)
        '-' -> ( 8, LeftAssociative)
        ',' -> ( 7, RightAssociative) -- other than a lone ","
        '.' -> ( 7, RightAssociative) -- other than a lone "."
        '<' -> ( 6, NonAssociative)
        '>' -> ( 6, NonAssociative)
        ';' -> ( 5, RightAssociative) -- other than a lone ";"
        ':' -> ( 5, NonAssociative)  -- other than a lone ":" or "::"
        '=' -> ( 5, NonAssociative)
        '~' -> ( 5, LeftAssociative) -- ~ as last char of an *infix* operator
        -- lower precedence than a single proc call
        '&' -> ( 4, RightAssociative)
        '|' -> ( 3, RightAssociative) -- other than a lone "|"
        _   -> ( 5, NonAssociative)


-- |Lowest (loosest) operator precedence number
lowestTermPrecedence :: Int
lowestTermPrecedence = 1


-- |Lowest (loosest) operator precedence of an individual statement
lowestStmtPrecedence :: Int
lowestStmtPrecedence = 0


-- |Lowest (loosest) operator precedence of a proc body
lowestParenthesisedPrecedence :: Int
lowestParenthesisedPrecedence = -3


-- |Lowest (loosest) operator precedence of a proc body
lowestStmtSeqPrecedence :: Int
lowestStmtSeqPrecedence = -4


-- |Lowest (loosest) operator precedence of a proc/function prototype
prototypePrecedence :: Int
prototypePrecedence = 10


-- |Prefix operator symbols; these all bind very tightly
prefixOp :: Parser Token
prefixOp = choice $ List.map symbol ["-", "~", "?", "!"]


-- |Apply the specified prefix op to the specified term.  Fail if it should
-- be a syntax error.
applyPrefixOp :: Token -> Term -> Parser Term
applyPrefixOp tok term = do
    let pos = tokenPosition tok
    case (tokenName tok, term) of
        ("-", IntConst _ num) -> return $ IntConst pos (-num)
        ("-", FloatConst _ num) -> return $ FloatConst pos (-num)
        ("-", Call{}) -> return $ call1 pos "-" term
        ("-", Foreign{}) -> return $ call1 pos "-" term
        ("-", Embraced{embracedStyle=Paren,embraced=[expr]})
            -> return $ call1 pos "-" expr
        ("-", _) -> fail $ "cannot negate " ++ show term
        ("~", IntConst _ num) -> return $ IntConst pos (complement num)
        ("~", Call{}) -> return $ call1 pos "~" term
        ("~", Foreign{}) -> return $ call1 pos "~" term
        ("~", Embraced{embracedStyle=Paren,embraced=[expr]})
            -> return $ call1 pos "~" expr
        ("~", _) -> fail $ "cannot negate " ++ show term
        ("?", Call{callVariableFlow=ParamIn}) -> return $ setCallFlow ParamOut term
        ("?", _) -> fail $ "unexpected " ++ show term ++ " following '?'"
        ("!", Call{callVariableFlow=ParamIn}) -> return $ setCallFlow ParamInOut term
        ("!", _) -> fail $ "unexpected " ++ show term ++ " following '!'"
        (_,_) -> shouldnt $ "Unknown prefix operator " ++ show tok
                            ++ " in applyPrefixOp"


-- |Unary call to the specified proc name with the specified argument.  The
-- default (empty) module and default (ParamIn) variable flow are used.
call1 :: SourcePos -> ProcName -> Term -> Term
call1 pos name arg = Call pos [] name ParamIn [arg]


-- |Is the specified token an infix operator?
isInfixOp :: Token -> Bool
isInfixOp (TokSymbol _ _)    = True
isInfixOp (TokIdent name _)  = infixKeyword name
isInfixOp (TokSeparator _ _) = True  --  but very low precedence
isInfixOp _                  = False


-- |Infix keyword (ie, alphabetic) operators.
infixKeyword :: String -> Bool
infixKeyword "in"    = True
infixKeyword "where" = True
infixKeyword _       = False


-- |Prefix keyword (ie, alphabetic) operators.
prefixKeyword :: String -> Bool
prefixKeyword "if"  = True
prefixKeyword "let"  = True
prefixKeyword "use"  = True
prefixKeyword "case" = True
prefixKeyword _     = False


-- | Test if operator name is for a separator operator.
separatorName :: [Char] -> Bool
separatorName ";"  = True
separatorName "\n" = True
separatorName _    = False


-- |Special default test for conditionals.
defaultGuard :: String -> Bool
defaultGuard = (=="else")


-----------------------------------------------------------------------------
-- Terminal helpers                                                        --
-----------------------------------------------------------------------------

-- | Tests an individual token.
takeToken :: (Token -> Maybe a) -> Parser a
takeToken = token show tokenPosition


-- | Parse a float literal token.
floatConst :: Parser Term
floatConst = takeToken test
    where
      test (TokFloat f p) = Just $ FloatConst p f
      test _              = Nothing


-- | Parse an integer literal token.
intConst :: Parser Term
intConst = takeToken test
  where
    test (TokInt i p) = Just $ IntConst p i
    test _            = Nothing


-- |Parse an integer constant
intLiteral :: Parser (Placed Integer)
intLiteral = takeToken test
  where
    test (TokInt i p) = Just $ Placed i p
    test _            = Nothing


-- | Parse a character literal token.
charConst :: Parser Term
charConst = takeToken test
    where
      test (TokChar c p) = Just $ CharConst p c
      test _             = Nothing


-- | Parse a string literal token.
stringConst :: Parser Term
stringConst = takeToken test
  where
    test (TokString d s p) = Just $ StringConst p s d
    test _                 = Nothing


-- | Parse the keyword terminal 'key', in the form of identifier tokens.
ident :: String -> Parser Token
ident key = takeToken test
  where
    test tok@(TokIdent t _) = if t == key then Just tok else Nothing
    test _                  = Nothing


-- | Parse an identifier token.
identifier :: Parser Term
identifier = takeToken test
  where
    test (TokIdent s p) = Just $ Call p [] s ParamIn []
    test _ = Nothing


-- | Parse an identifier as a String
identString :: Parser String
identString = takeToken test
  where
    test (TokIdent s _) = Just s
    test _              = Nothing


-- | Parse a type variable name
typeVarName :: Parser Ident
typeVarName = takeToken test
 where
    test (TokIdent s _) | isTypeVar s = Just s
    test _                            = Nothing


-- | Parse a list of comma-separated TypeVarNames, between parentheses
typeVarNames :: Parser [Ident]
typeVarNames = option [] (betweenB Paren $ typeVarName `sepBy` comma)


-- | Parse a module name, any ident that is not a TypeVarName
moduleName :: Parser Ident
moduleName = takeToken test
 where
    test (TokIdent s _) | not $ isTypeVar s = Just s
    test _                                  = Nothing


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
    test _               = Nothing


-- | Parse the symbol token of the string 'symbol'.
symbol :: String -> Parser Token
symbol sym = takeToken test
  where
    test tok@(TokSymbol s _) = if sym == s then Just tok else Nothing
    test _                   = Nothing


-- | Parse a comma token.
comma :: Parser Token
comma = takeToken test
  where
    test tok@TokComma{} = Just tok
    test _              = Nothing


-- | Parse a period token.
period :: Parser Token
period = takeToken test
  where
    test tok@TokPeriod{} = Just tok
    test _               = Nothing


-- | Parse a statement separator token.
separator :: Parser Token
separator = takeToken test
  where
    test tok@TokSeparator{} = Just tok
    test _                  = Nothing


-- | Module name, period separated.  This is greedy, so m1.m2.name will take the
-- whole thing to be a module spec.  If you want a moduleSpec followed by a
-- name, just use moduleSpec, and take init and last of it to get the module
-- spec and name.
moduleSpec :: Parser ModSpec
moduleSpec = identString `sepBy1` period


-- |Parse an optional list of identifiers enclosed in braces
modifierList :: Parser [Ident]
modifierList = option [] $ betweenB Brace (identString `sepBy` comma)


-- | Parse a left bracket of style 'bs'.
leftBracket :: BracketStyle -> Parser Token
leftBracket bs = takeToken test
  where
    test tok@(TokLBracket sty _) | bs == sty = Just tok
    test _ = Nothing


-- | Parse a right bracket of style 'bs'.
rightBracket :: BracketStyle -> Parser Token
rightBracket bs = takeToken test
  where
    test tok@(TokRBracket sty _) = if bs == sty
                                   then Just tok
                                   else Nothing
    test _ = Nothing


-- | Helper to run a parser between enclosing brackets of the given style.
betweenB :: BracketStyle -> Parser a -> Parser a
betweenB bs = between (leftBracket bs) (rightBracket bs)


-- | Terminal "public" / "private".
visibility :: Parser Visibility
visibility = option Private (ident "pub" $> Public)


-- | Terminal for determinism.
determinism :: Parser Determinism
determinism = option Det (ident "test" $> SemiDet
                          <|> ident "partial" $> SemiDet
                          <|> ident "failing" $> Failure
                          <|> ident "terminal" $> Terminal)

-- | Translate the output of a parser to something else
parseWith :: (a -> Either (SourcePos,String) b) -> a -> Parser b
parseWith translator = either reportFailure return . translator


-- |Fail the parser with the provided error message and associated SourcePos
reportFailure :: (SourcePos,String) -> Parser a
reportFailure (pos, message) = setPosition pos >> parserFail message


-----------------------------------------------------------------------------
-- Translating Term to the correct output types                        --
-----------------------------------------------------------------------------

-- |Type alias for a translation function
type TranslateTo t = Term -> Either (SourcePos,String) t


parensToTerm :: [Term] -> [Term]
parensToTerm [Embraced _ Paren parensed Nothing] = parensed
parensToTerm ses = ses

-- |Convert a Term to a proc/func prototype and a return type (AnyType for a
-- proc declaration or a function with no return type specified).
termToPrototype :: TranslateTo (ProcProto, TypeSpec)
termToPrototype (Call _ [] ":" ParamIn [rawProto,rawTy]) = do
    returnType <- termToTypeSpec rawTy
    (proto,_)  <- termToPrototype rawProto
    return (proto,returnType)
termToPrototype (Embraced _ Paren [proto] Nothing) = termToPrototype proto
termToPrototype (Call pos mod name ParamIn rawParams) =
    if List.null mod
    then do
        params <- mapM termToParam $ parensToTerm rawParams
        return (ProcProto name params Set.empty,AnyType)
    else Left (pos, "module not permitted in proc declaration " ++ show mod)
termToPrototype other =
    syntaxError (termPos other)
                $ "invalid proc/func prototype " ++ show other


-- |Convert a Term to a body, if possible, or give a syntax error if not.
termToBody :: TranslateTo [Placed Stmt]
termToBody (Call pos [] sep ParamIn [left,right])
  | separatorName sep = do
    left' <- termToBody left
    right' <- termToBody right
    return $ left' ++ right'
termToBody (Embraced pos Brace [body] Nothing) =
    termToBody body
termToBody other = (:[]) <$> termToStmt other


-- |Convert a Term to a Stmt, if possible, or give a syntax error if not.
termToStmt :: TranslateTo (Placed Stmt)
-- termToStmt (Call pos [] "if" ParamIn [conditional]) =
--     translateConditionalStmt conditional
termToStmt (Embraced _ Paren [body] Nothing) = termToStmt body
termToStmt (Embraced _ Brace [body] Nothing) = termToStmt body
termToStmt (Call pos [] "if" ParamIn [conditional]) =
    termToStmt conditional
termToStmt (Call pos [] "case" ParamIn
                [Call _ [] "in" ParamIn
                      [exp,Embraced _ Brace [body] Nothing]]) = do
    expr' <- termToExp exp
    (cases,deflt) <- termToCases termToBody body
    return $ Placed (Case expr' cases deflt) pos
termToStmt (Call pos [] "do" ParamIn [body]) =
    (`Placed` pos) . flip (`Loop` Nothing) Nothing <$> termToBody body
termToStmt (Call pos [] "for" ParamIn [gen,body]) = do
    genStmts <- termToGenerators gen
    (`Placed` pos) . For genStmts <$> termToBody body
termToStmt (Call pos [] "use" ParamIn
                    [Call _ [] "in" ParamIn [ress,body]]) = do
    ress' <- termToResourceList ress
    body' <- termToBody body
    return $ Placed (UseResources ress' Nothing body') pos
termToStmt (Call pos [] "while" ParamIn [test]) = do
    t <- termToStmt test
    return $ Placed (Cond t [Unplaced Nop] [Unplaced Break] Nothing Nothing Nothing) pos
termToStmt (Call pos [] "until" ParamIn [test]) = do
    t <- termToStmt test
    return $ Placed (Cond t [Unplaced Break] [Unplaced Nop] Nothing Nothing Nothing) pos
termToStmt (Call pos [] "when" ParamIn [test]) = do
    t <- termToStmt test
    return $ Placed (Cond t [Unplaced Nop] [Unplaced Next] Nothing Nothing Nothing) pos
termToStmt (Call pos [] "unless" ParamIn [test]) = do
    t <- termToStmt test
    return $ Placed (Cond t [Unplaced Next] [Unplaced Nop] Nothing Nothing Nothing) pos
termToStmt (Call pos [] "pass" ParamIn []) = do
    return $ Placed Nop pos
termToStmt (Call pos [] "|" ParamIn
             [Call _ [] "::" ParamIn [test1,thn],
              Call _ [] "::" ParamIn [Call _ [] test2 ParamIn [],els]])
  | defaultGuard test2 = do
    test1' <- termToStmt test1
    thn' <- termToBody thn
    els' <- termToBody els
    return $ Placed (Cond test1' thn' els' Nothing Nothing Nothing) pos
termToStmt
        (Call _ [] "|" ParamIn [Call pos [] "::" ParamIn [test,body],rest]) = do
    test' <- termToStmt test
    body' <- termToBody body
    rest' <- termToBody rest
    return $ Placed (Cond test' body' rest' Nothing Nothing Nothing) pos
termToStmt (Call pos [] "|" ParamIn disjs) = do
    (`Placed` pos) . flip (`Or` Nothing) Nothing <$> mapM termToStmt disjs
termToStmt (Call pos [] "::" ParamIn [Call _ [] guard ParamIn [],body])
  | defaultGuard guard = do
    syntaxError pos  "'else' outside an 'if'"
termToStmt (Call pos [] "::" ParamIn [test,body]) = do
    test' <- termToStmt test
    body' <- termToBody body
    return $ Placed (Cond test' body' [Unplaced Nop] Nothing Nothing Nothing) pos
termToStmt (Call pos [] "&" ParamIn conjs) = do
    (`Placed` pos) . And <$> mapM termToStmt conjs
termToStmt (Call _ [] fn ParamIn [first,rest])
  | separatorName fn = do
    first' <- termToStmt first
    rest'  <- termToStmt rest
    return $ Unplaced $ And [first',rest']
termToStmt (Call pos mod fn ParamIn args)
    = (`Placed` pos) . ProcCall (regularModProc mod fn) Det False
        <$> mapM termToExp args
termToStmt (Call pos mod fn ParamInOut args)
    = (`Placed` pos) . ProcCall (regularModProc mod fn) Det True
        <$> mapM termToExp args
termToStmt (Call pos mod fn flow args) =
    syntaxError pos $ "invalid statement prefix: " ++ flowPrefix flow
termToStmt (Foreign pos lang inst flags args) =
    (`Placed` pos) . ForeignCall lang inst flags <$> mapM termToExp args
termToStmt other =
    syntaxError (termPos other) $ "invalid statement " ++ show other


--  Convert a term to a list of generators, of the form `i in is; j in js; ...`
termToGenerators :: TranslateTo [Placed Generator]
termToGenerators (Call pos [] sep ParamIn [left,right])
  | separatorName sep = do
    left' <- termToGenerators left
    right' <- termToGenerators right
    return $ left' ++ right'
termToGenerators (Call pos [] "in" ParamIn [var,exp]) = do
    var' <- termToExp var
    exp' <- termToExp exp
    return [Placed (In var' exp') pos]
termToGenerators other =
    syntaxError (termPos other) $ "invalid generator " ++ show other


-- |Convert a Term to the body of a case statement or expression.  The
-- supplied translator is used to translate the bodies of the cases, which will
-- be expressions in a case expression, and statement sequences in a case
-- statement.
termToCases :: TranslateTo a -> TranslateTo ([(Placed Exp,a)], Maybe a)
termToCases caseTrans
      (Call pos [] "|" ParamIn [Call _ [] "::" ParamIn [val,thn], rest]) = do
    val' <- termToExp val
    thn' <- caseTrans thn
    (rest',deflt) <- termToCases caseTrans rest
    return ((val',thn') : rest', deflt)
termToCases caseTrans (Call _ [] "::" ParamIn [Call _ [] g ParamIn [],thn])
  | defaultGuard g = do
    thn' <- caseTrans thn
    return ([], Just thn')
termToCases caseTrans (Call _ [] "::" ParamIn [val,thn]) = do
    val' <- termToExp val
    thn' <- caseTrans thn
    return ([(val',thn')], Nothing)
termToCases _ other =
    syntaxError (termPos other) $ "invalid case body " ++ show other


-- |Convert a Term to an Exp, if possible, or give a syntax error if not.
termToExp :: TranslateTo (Placed Exp)
termToExp (Call pos [] ":" ParamIn [exp,ty]) = do
    exp' <- content <$> termToExp exp
    ty' <- termToTypeSpec ty
    case exp' of
        Typed exp'' ty'' (Just AnyType) -> -- already cast, but not typed
            return $ Placed (Typed exp'' ty'' $ Just ty') pos
        Typed exp'' _ _ -> -- already typed, whether casted or not
            syntaxError (termPos ty) $ "repeated type constraint" ++ show ty
        _ -> -- no cast, no type
            return $ Placed (Typed exp'  ty' Nothing) pos
termToExp (Call pos [] ":!" ParamIn [exp,ty]) = do
    exp' <- content <$> termToExp exp
    ty' <- termToTypeSpec ty
    case exp' of
        Typed exp'' inner Just{} ->
            syntaxError (termPos ty) $ "repeated cast " ++ show ty
        Typed exp'' inner Nothing ->
            return $ Placed (Typed exp'' ty' $ Just inner) pos
        _  ->
            return $ Placed (Typed exp'  ty' $ Just AnyType) pos
termToExp (Call pos [] "where" ParamIn [exp,body]) = do
    exp' <- termToExp exp
    body' <- termToBody body
    return $ Placed (Where body' exp') pos
termToExp (Call pos [] "let" ParamIn [Call _ [] "in" ParamIn [body,exp]]) =
  do
    exp' <- termToExp exp
    body' <- termToBody body
    return $ Placed (Where body' exp') pos
termToExp (Call pos [] "^" ParamIn [exp,op]) = do
    exp' <- termToExp exp
    op'  <- termToExp op
    case op' of
        Placed (Fncall mod fn False args) _
            -> return $ Placed (Fncall mod fn False (exp':args)) pos
        Placed (Var var ParamIn Ordinary) _
            -> return $ Placed (Fncall [] var False [exp']) pos
        _ -> syntaxError pos "invalid second argument to '^'"
termToExp (Call pos [] "@" flow exps) = do
    exps' <- mapM termToExp exps
    case content <$> exps' of
        [] -> return $ Placed (AnonParamVar Nothing flow) pos
        [IntValue i] | i > 0 -> return $ Placed (AnonParamVar (Just i) flow) pos
        _ -> syntaxError pos "invalid anonymous parameter expression"
termToExp (Call pos [] "|" ParamIn [exp1,exp2]) = do
    exp1' <- termToExp exp1
    exp2' <- termToExp exp2
    return $ Placed (DisjExp exp1' exp2') pos
termToExp (Call pos [] "if" ParamIn [conditional]) =
    termToConditionalExp conditional
termToExp (Embraced _ Paren [exp] Nothing) = termToExp exp
termToExp body@(Embraced pos Brace _ Nothing) = do
    body' <- termToBody body
    return $ Placed (AnonProc defaultProcModifiers [] body' Nothing Nothing) pos
termToExp mods@(Embraced pos Brace _
                    (Just body@(Embraced _ Brace _ _))) = do
    procMods <- termToProcModifiers "anonymous procedure" mods
    let inlining = modifierInline procMods
    unless (inlining == MayInline)
        $ modifierError pos (inliningName inlining) "anonymous procedure"
    anonProc <- content <$> termToExp body
    case anonProc of
        AnonProc oldMods ps body clsd _ | oldMods == defaultProcModifiers
            -> return $ Placed (AnonProc procMods ps body clsd Nothing) pos
        _ -> syntaxError pos $ "malformed anonymous procedure " ++ show anonProc
termToExp embraced@(Embraced pos _ _ _) =
    syntaxError pos $ "malformed anonymous procedure " ++ show embraced
termToExp (Call pos [] "case" ParamIn
            [Call _ [] "in" ParamIn [exp,Embraced _ Brace [body] Nothing]]) = do
    expr' <- termToExp exp
    (cases,deflt) <- termToCases termToExp body
    return $ Placed (CaseExp expr' cases deflt) pos
termToExp (Call pos [] sep ParamIn [])
  | separatorName sep =
    syntaxError pos "invalid separated expression"
termToExp (Call pos [] var flow []) = -- looks like a var; assume it is
    return $ Placed (Var var flow Ordinary) pos
termToExp (Call pos mod fn flow args)
  | flow == ParamOut = 
    syntaxError pos $ "invalid function call prefix " ++ flowPrefix flow
  | otherwise = 
    (`Placed` pos) . Fncall mod fn (flow == ParamInOut) <$> mapM termToExp args
termToExp (Foreign pos lang inst flags args) =
    (`Placed` pos) . ForeignFn lang inst flags <$> mapM termToExp args
termToExp (IntConst pos num) = Right $ Placed (IntValue num) pos
termToExp (FloatConst pos num) = Right $ Placed (FloatValue num) pos
termToExp (CharConst pos char) = Right $ Placed (CharValue char) pos
termToExp (StringConst pos str DoubleQuote)
    = return $ Placed (StringValue str WybeString) pos
termToExp (StringConst pos str (IdentQuote "c" DoubleQuote))
    = return $ Placed (StringValue str CString) pos
termToExp str@StringConst{stringPos=pos}
    = syntaxError pos $ "invalid string literal " ++ show str


termToIdent :: TranslateTo Ident
termToIdent (Call _ [] ident ParamIn []) = return ident
termToIdent other
    = syntaxError (termPos other) $ "invalid ident " ++ show other

termToProcModifiers :: String -> TranslateTo ProcModifiers
termToProcModifiers ctx (Embraced pos Brace mods _) = do
    idents <- mapM termToIdent mods
    processProcModifiers pos ctx idents
termToProcModifiers ctx other
    = syntaxError (termPos other) 
    $ "invalid modifiers " ++ show other ++ " in " ++ ctx



-- |Translate an `if` expression into a Placed conditional Exp
termToConditionalExp :: TranslateTo (Placed Exp)
termToConditionalExp (Embraced _ Brace [body] Nothing) =
    termToConditionalExp' body
termToConditionalExp term =
    syntaxError (termPos term) "expecting '{'"

termToConditionalExp' :: TranslateTo (Placed Exp)
termToConditionalExp'
        (Call _ [] "|" ParamIn [Call pos [] "::" ParamIn [test,body],rest]) = do
    test' <- termToStmt test
    body' <- termToExp body
    rest' <- termToConditionalExp' rest
    return $ Placed (CondExp test' body' rest') pos
termToConditionalExp'
        (Call pos [] "::" ParamIn [Call _ [] guard ParamIn [],body])
    | defaultGuard guard = termToExp body
termToConditionalExp' term =
    syntaxError (termPos term)
          $ "missing 'else ::' in if expression: " ++ show term


-- |Convert a Term to a TypeSpec, or produce an error
termToTypeSpec :: TranslateTo TypeSpec
termToTypeSpec mods@(Embraced pos Brace _ (Just ty@(Embraced _ Paren _ Nothing))) = do
    mods <- termToProcModifiers "type constraint" mods
    let inlining = modifierInline mods
    unless (inlining == MayInline)
        $ modifierError pos (inliningName inlining) "type constraint"
    ty' <- termToTypeSpec ty
    case ty' of
        HigherOrderType _ params -> return $ HigherOrderType mods params
        _ -> syntaxError pos $ "invalid higher-order type " ++ show ty'
termToTypeSpec (Embraced _ Paren args Nothing) =
    HigherOrderType defaultProcModifiers <$> mapM termToTypeFlow args
termToTypeSpec (Call _ [] name ParamIn [])
  | isTypeVar name =
    return $ TypeVariable $ RealTypeVar name
termToTypeSpec (Call _ mod name ParamIn params)
  | not $ isTypeVar name =
    TypeSpec mod name <$> mapM termToTypeSpec params
termToTypeSpec other =
    syntaxError (termPos other) $ "invalid type specification " ++ show other

termToTypeFlow :: TranslateTo TypeFlow
termToTypeFlow (Call _ [] ":" _ [Call _ [] _ flow [],ty]) =
    (`TypeFlow` flow) <$> termToTypeSpec ty
termToTypeFlow ty@(Call _ _ _ flow _) =
    (`TypeFlow` flow) <$> termToTypeSpec (setCallFlow ParamIn ty)
termToTypeFlow other =
    syntaxError (termPos other) $ "invalid higher order type argument " ++ show other


-- | Translate a Term to a proc or func prototype (with empty resource list)
termToProto :: TranslateTo (Placed ProcProto)
termToProto (Call pos [] name ParamIn params) = do
    params' <- mapM termToParam params
    return $ Placed (ProcProto name params' Set.empty) pos
termToProto other =
    syntaxError (termPos other) $ "invalid prototype " ++ show other


-- | Translate a Term to a proc or func parameter
termToParam :: TranslateTo (Placed Param)
termToParam (Call pos [] ":" ParamIn [Call _ [] name flow [],ty]) = do
    ty' <- termToTypeSpec ty
    return $ Param name ty' flow Ordinary `maybePlace` Just pos
termToParam (Call pos [] name flow []) =
    return $ Param name AnyType flow Ordinary `maybePlace` Just pos
termToParam other =
    syntaxError (termPos other) $ "invalid parameter " ++ show other


-- | Translate a Term to a ctor declaration
termToCtorDecl :: TranslateTo (Placed ProcProto)
termToCtorDecl (Call pos [] name ParamIn fields) = do
    fields' <- mapM termToCtorField fields
    return $ Placed (ProcProto name fields' Set.empty) pos
termToCtorDecl other =
    syntaxError (termPos other)
        $ "invalid constructor declaration " ++ show other


-- | Translate a Term to a ctor field
termToCtorField :: TranslateTo (Placed Param)
termToCtorField (Call pos [] ":" ParamIn [Call _ [] name ParamIn [],ty]) = do
    ty' <- termToTypeSpec ty
    return $ Param name ty' ParamIn Ordinary `maybePlace` Just pos
termToCtorField (Call pos [] name ParamIn [])
  | isTypeVar name = do
    return $ Param "" (TypeVariable $ RealTypeVar name) ParamIn Ordinary
                `maybePlace` Just pos
termToCtorField (Call pos mod name ParamIn params)
  | not $ isTypeVar name = do
    tyParams <- mapM termToTypeSpec params
    return $ Param "" (TypeSpec mod name tyParams) ParamIn Ordinary
                `maybePlace` Just pos
termToCtorField other =
    syntaxError (termPos other) $ "invalid constructor field " ++ show other


-- | Extract a list of resource names from a Term (from a "use" statement).
termToResourceList :: TranslateTo [ResourceSpec]
termToResourceList (Embraced _ Brace args Nothing) =
    concat <$> mapM termToResourceList args
termToResourceList (Call _ mod name ParamIn []) =
    return [ResourceSpec mod name]
termToResourceList other =
    syntaxError (termPos other) "expected resource spec"

-----------------------------------------------------------------------------
-- Data structures                                                         --
-----------------------------------------------------------------------------

-- |Representation of expressions and statements.
data Term
    -- |a proc or function call, or a variable reference.
    = Call {
        callPos::SourcePos,               -- ^Where the call appears
        callModule::ModSpec,              -- ^the specified module, or empty
        callName::ProcName,               -- ^the called proc or variable name
        callVariableFlow::FlowDirection,  -- ^variable flow direction or
                                          --  call resourcefulness
        callArguments::[Term]             -- ^the specified arguments
    }
    -- |a foreign call, either as an expression or statement.
    | Foreign {
        foreignPos::SourcePos,         -- ^Where the foreign call appears
        foreignLanguage::Ident,        -- ^the specified foreign language
        foreignInstruction::ProcName,  -- ^the specified instruction
        foreignFlags::[Ident],         -- ^the specified modifiers
        foreignArguments::[Term]       -- ^the specified arguments
    }
    | Embraced {
        embracedPos::SourcePos,
        embracedStyle::BracketStyle,
        embraced::[Term],
        embracedArg::Maybe Term
    }
    -- |an integer manifest constant
    | IntConst {intPos::SourcePos, intConstValue::Integer}
    -- |a floating point manifest constant
    | FloatConst{floatPos::SourcePos, floatConstValue::Double}
    -- |a character literal
    | CharConst{charPos::SourcePos, charConstValue::Char}
    -- |a string literal
    | StringConst{
        stringPos::SourcePos,
        stringConstValue::String,
        stringConstantDelim::StringDelim
    }


instance Show Term where
    show (Call _ mod name flow args) =
        flowPrefix flow ++ maybeModPrefix mod ++ name ++ showArguments args
    show (Foreign _ lang instr flags args) =
        "foreign " ++ lang ++ " " ++ showFlags' flags ++ instr
        ++ showArguments args
    show (Embraced _ style embraced arg) =
        bracketString True style ++ intercalate "," (show <$> embraced)
                                 ++ bracketString False style
                                 ++ maybe "" show arg
    show (IntConst _ int) = show int
    show (FloatConst _ float) = show float
    show (CharConst _ char) = show char
    show (StringConst _ string delim) = delimitString delim string


-- |The SourcePos of a Term.
termPos :: Term -> SourcePos
termPos Call{callPos=pos}            = pos
termPos Foreign{foreignPos=pos}      = pos
termPos Embraced{embracedPos=pos}    = pos
termPos IntConst{intPos=pos}         = pos
termPos FloatConst{floatPos=pos}     = pos
termPos CharConst{charPos=pos}       = pos
termPos StringConst{stringPos=pos}   = pos


-- |Return the specified Term with its position replaced.
setTermPos :: SourcePos -> Term -> Term
setTermPos pos term@Call{} = term {callPos = pos}
setTermPos pos term@Foreign{} = term {foreignPos = pos}
setTermPos pos term@Embraced{} = term {embracedPos = pos}
setTermPos pos term@IntConst{} = term {intPos = pos}
setTermPos pos term@FloatConst{} = term {floatPos = pos}
setTermPos pos term@CharConst{} = term {charPos = pos}
setTermPos pos term@StringConst{} = term {stringPos = pos}


-- |Set the flow of a call
setCallFlow :: FlowDirection -> Term -> Term
setCallFlow flow term =
    case term of
        Call{} -> term {callVariableFlow = flow}
        _ -> shouldnt $ "setCallFlow of non-Call " ++ show term


-----------------------------------------------------------------------------
-- Parser testing                                                          --
-----------------------------------------------------------------------------

testFile :: String -> IO ()
testFile file = do
    stream <- fileTokens file
    putStrLn "--------------------"
    case parseWybe stream file of
        Left err -> print err
        Right is -> mapM_ print is

test :: Int -> String -> Term
test prec input = do
    let toks = stringTokens input
    case parse (maybeSetPosition toks (limitedTerm prec) <* eof) "<string>" toks of
        Left err -> StringConst (errorPos err) (show err) DoubleQuote
        Right is -> is

testParser :: Parser a -> String -> Either ParseError a
testParser parser input = parse (maybeSetPosition toks parser <* eof) "<string>" toks
  where toks = stringTokens input