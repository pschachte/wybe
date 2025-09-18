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
import Data.Bits (complement)
import Data.Either.Extra (mapLeft)
import Control.Monad.State
-- import Control.Monad.Identity (Identity)
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
-- The parser monad
--
-- The parser is a Parsec parser, with the token type being Token.  In addition
-- to producing an AST, the parser also provides information about the source
-- file content that led to each AST node.  In particular, it provides the
-- source file name, line, and column of the start and end of the node, as well
-- as a list of the tokens that comprise the node.  This information is used to
-- give precise and accurate error messages. 
-----------------------------------------------------------------------------

type Parser a = ParsecT [Token] () (Control.Monad.State.State ParserState) a


-- | The parser state
data ParserState =
    ParserState {
        currStart :: SourcePos      -- ^ Start of the current AST node
        ,currTokens :: [Token]      -- ^ Reversed tokens most recently consumed
                                    --   to parse this AST node
        ,pastTokens :: [[Token]]    -- ^ Reversed list of reversed lists
    }
    | EmptyState                    -- ^ Not parsing anything


-- | Record the specified token as being processed, if we're parsing something.
recordToken :: SourcePos -> Token -> [Token] -> ParserState -> ParserState
recordToken _ tok _ st =
    case st of
        EmptyState -> EmptyState
        ParserState pos toks past -> ParserState pos (tok:toks) past


-- | Report a syntax error
syntaxError :: SourceInfo -> String -> Parser a
syntaxError pos msg = fail $ show pos ++ ": " ++ msg


-- | Get the current SourcePos of the Parser
sourcePos :: Parser SourcePos
sourcePos = statePos <$> getParserState


-- | Set the Parser position to the position of the head Token, if it exists
maybeSetPosition :: [Token] -> Parser a -> Parser a
maybeSetPosition toks parser = do
    maybe (return ()) (setPosition . tokenPosition) $ listToMaybe toks
    parser


-----------------------------------------------------------------------------
-- Top level of the parser:  parsing Items                                 --
-----------------------------------------------------------------------------

-- | Parse a Wybe module.
parseWybe :: [Token] -> FilePath -> Either ParseError [Item]
parseWybe toks file =
    evalState (runParserT (maybeSetPosition toks items <* eof) () file toks)
              EmptyState


-- | Run the specified parser to produce an AST node.  While parsing this,
-- calling astNodeInfo will return the source info of the node being parsed.
-- XXX this doesn't work
astNode ::  Parser a -> Parser a
astNode parser = do
    -- origState <- sourcePos >>= pushSourceInfo
    result <- try parser
    -- put origState
    return result


-- | Note the start of parsing a new AST node.
pushSourceInfo :: SourcePos -> Parser ParserState
pushSourceInfo pos = do
    st <- get
    put $ ParserState pos [] []
    return st


-- | Return the SourceInfo of the AST node currently being parsed.
astNodeInfo :: Parser SourceInfo
astNodeInfo =
    get >>= \case
        EmptyState -> shouldnt "astNodeInfo called outside of parsing an AST node"
        ParserState start toks past -> do
            end <- sourcePos
            return $ SourceInfo start end $ toks:past


-- | Attach the current SourceInfo to the AST node being generated.
withSourceInfo :: (Maybe SourceInfo -> a) -> Parser a
withSourceInfo f = f . Just <$> astNodeInfo


-- | Attach the current SourceInfo to the AST node being generated.
termWithSourceInfo :: (SourceInfo -> Term) -> Parser Term
termWithSourceInfo f = f <$> astNodeInfo


-- | Attach the current SourceInfo to the AST node being generated.
succeedWithSourceInfo :: a -> Parser (Placed a)
succeedWithSourceInfo f = Placed f <$> astNodeInfo


-- | Parser entry for a Wybe program, items separated by some separator.
items :: Parser [Item]
items = item `sepBy` separator


-- | Parse a single items
item :: Parser Item
item = try visibilityItem <|> try privateItem <|> topLevelStmtItem


-- | Parse a top-level statement itme
topLevelStmtItem :: Parser Item
topLevelStmtItem = astNode $ do
    st <- stmt <?> "top-level statement"
    return $ StmtDecl (content st) (place st)


-- | Parse 'Item's with the common 'Visibility' prefix.
visibilityItem :: Parser Item
visibilityItem =
     astNode (do
    v <- visibility
    procOrFuncItem v
        <|> moduleItem v
        <|> typeItem v
        <|> dataCtorItemParser v
        <|> resourceItem v
        <|> useItemParser v
        <|> fromUseItemParser v
    <?> "top-level item")


-- | Parse module-local items (with no visibility prefix).
privateItem :: Parser Item
privateItem = astNode $ typeRepItem <|> pragmaItem


-- | Parse a pragma item
pragmaItem :: Parser Item
pragmaItem = ident "pragma" *> (PragmaDecl <$> parsePragma)


-- TODO:  Should use the Term parser to parse the declaration body.
-- | Parse a Pragma, currently only "no_standard_library"
parsePragma :: Parser Pragma
parsePragma = ident "no_standard_library" $> NoStd


-- | Module item parser.  Always called inside an astNode wrapper.
moduleItem :: Visibility -> Parser Item
moduleItem v = do
    modName <- moduleName
    body <- betweenB Brace items
    withSourceInfo $ ModuleDecl v modName body


-- | Type declaration item parser.  Always called inside an astNode wrapper.
typeItem :: Visibility -> Parser Item
typeItem v = do
    modifiers <- List.foldl processTypeModifier defaultTypeModifiers
                 <$> modifierList
    proto <- TypeProto <$> moduleName <*> typeVarNames
    (imp, items) <- typeImpln <|> typeCtors
    withSourceInfo $ TypeDecl v proto modifiers imp items


-- | Module type representation declaration
typeRepItem :: Parser Item
typeRepItem = astNode $ do
    ident "representation"
    params <- typeVarNames
    ident "is"
    modifiers <- List.foldl processTypeModifier defaultTypeModifiers
                 <$> modifierList
    rep <- typeRep
    withSourceInfo $ RepresentationDecl params modifiers rep


-- | Module type representation declaration.  Always called inside an astNode
-- wrapper.
dataCtorItemParser :: Visibility -> Parser Item
dataCtorItemParser v = do
    ident "constructor" <|> ident "constructors"
    params <- typeVarNames
    modifiers <- List.foldl processTypeModifier defaultTypeModifiers
                 <$> modifierList
    ctors <- ctorDecls
    withSourceInfo $ ConstructorDecl v params modifiers ctors


-- | Type declaration body where representation and items are given
typeImpln :: Parser (TypeImpln, [Item])
typeImpln = do
    impln <- TypeRepresentation <$> (ident "is" *> typeRep)
    items <- betweenB Brace items
    return (impln,items)


-- | Type declaration body where representation and items are given
typeRep :: Parser TypeRepresentation
typeRep = do
    ident "address" $> Pointer
    <|> ident "opaque" $> CPointer
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
ctorDecls = astNode (visibility
                >>= \vis -> (vis,) <$> (term >>= parseWith termToCtorDecl))
            `sepBy1` symbol "|"


-- | Resource declaration parser.  Always called inside an astNode wrapper.
resourceItem :: Visibility -> Parser Item
resourceItem v = do
    ident "resource"
    let optInit = optionMaybe (symbol "=" *> expr)
    resName <- identString
    ty <- symbol ":" *> typeSpec
    init <- optInit
    withSourceInfo $ ResourceDecl v resName ty init


-- | Parse a "use" item. Either an import statement or a use-block.  Always
-- called inside an astNode wrapper.
useItemParser :: Visibility -> Parser Item
useItemParser v = do
    ident "use"
    (ident "foreign" *> foreignFileOrLib v)
      <|> (moduleSpec `sepBy` comma >>= useBody v)


-- | Parse a foreign library or object import
foreignFileOrLib :: Visibility -> Parser Item
foreignFileOrLib v =
    (do
        ident "library"
        names <- identString `sepBy` comma
        withSourceInfo $ ImportForeignLib names
    )
    <|> (do
        ident "object"
        names <- identString `sepBy` comma
        withSourceInfo $ ImportForeign names
    )

-- | Parse a use-block body or an import statement
useBody :: Visibility -> [ModSpec] -> Parser Item
useBody v mods =
    (ident "in" *> do
        if v == Private
        then topLevelUseStmt (modSpecToResourceSpec <$> mods)
        else fail "invalid use-block")
    <|> withSourceInfo (ImportMods v mods)

-- | Parse a top-level use statement with specified
topLevelUseStmt :: [ResourceSpec] -> Parser Item
topLevelUseStmt ress = do
    body <- stmtSeq
    withSourceInfo $ StmtDecl (UseResources ress Nothing body)


-- | Convert a ModSpce to a ResourceSpec
modSpecToResourceSpec :: ModSpec -> ResourceSpec
modSpecToResourceSpec modspec = ResourceSpec (init modspec) (last modspec)


-- | Parse a from-use item.  Always called inside an astNode wrapper.
fromUseItemParser :: Visibility -> Parser Item
fromUseItemParser v = do
    ident "from"
    m <- moduleSpec
    ident "use"
    ids <- identString `sepBy` comma
    withSourceInfo $ ImportItems v m ids


-- | Parse a procedure or function, since both items share the same prefix of
-- 'visibility' 'determinism'.  Always called inside an astNode wrapper.
procOrFuncItem :: Visibility -> Parser Item
procOrFuncItem vis = do
    ident "def"
    mbLanguage <- optionMaybe (ident "foreign" *> identString)
    mods <- modifierList >>= processProcModifiers "procedure or function declaration"
    (proto, returnType) <- limitedTerm prototypePrecedence >>= parseWith termToPrototype
    do
        body <- symbol "=" *> expr
        if isNothing mbLanguage
        then withSourceInfo $ FuncDecl vis mods proto returnType body
        else fail "unexpected foreign language in function declaration"
        <|> if returnType /= AnyType
        then fail "unexpected return type in proc declaration"
        else do
            rs <- useResourceFlowSpecs
            let proto' = proto { procProtoResources = rs }
            case mbLanguage of
                Just language -> withSourceInfo $ ForeignProcDecl vis language mods proto'
                Nothing -> do
                    body <- embracedTerm >>= parseWith termToBody
                    withSourceInfo $ ProcDecl vis mods proto' body



-- | Parse an optional series of resource flows
useResourceFlowSpecs :: Parser [ResourceFlowSpec]
useResourceFlowSpecs = option [] (ident "use" *> resourceFlowSpec `sepBy1` comma)


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
processProcModifiers :: String -> [String] -> Parser ProcModifiers
processProcModifiers ctx idents =
    foldM (flip $ processProcModifier ctx) defaultProcModifiers idents

-- | Update a collection of ProcModifiers
processProcModifier :: String -> String -> ProcModifiers -> Parser ProcModifiers
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
    \_ -> fail $ "Unknown modifier '" ++ modName ++ "' in " ++ ctx



-- | Update the ProcModifiers to specify the given determinism, which was
-- specified with the given identifier.  Since Det is the default, and can't be
-- explicitly specified, it's alway OK to change from Det to something else.
updateModsDetism :: String -> String -> Determinism -> ProcModifiers
                 -> Parser ProcModifiers
updateModsDetism _ _ detism mods@ProcModifiers{modifierDetism=Det} =
    return mods {modifierDetism=detism}
updateModsDetism ctx modName detism mods =
    fail $ modifierConflictMsg modName ctx


-- | Update the ProcModifiers to specify the given inlining, which was specified
-- with the given identifier.  Since MayInline is the default, and can't be
-- explicitly specified, it's alway OK to change from MayInline to something
-- else.
updateModsInlining :: String -> String -> Inlining -> ProcModifiers
                   -> Parser ProcModifiers
updateModsInlining _ _ inlining mods@ProcModifiers{modifierInline=MayInline} =
    return $ mods {modifierInline=inlining}
updateModsInlining ctx modName _ mods =
    fail $ modifierConflictMsg modName ctx


-- | Update the ProcModifiers to specify the given Impurity, which was specified
-- with the given identifier.  Since Pure is the default, and can't be
-- explicitly specified, it's alway OK to change from Pure to something
-- else.
updateModsImpurity :: String -> String -> Impurity -> ProcModifiers
                   -> Parser ProcModifiers
updateModsImpurity _ _ impurity mods@ProcModifiers{modifierImpurity=Pure} =
    return $ mods {modifierImpurity=impurity}
updateModsImpurity ctx modName _ mods =
    fail $ modifierConflictMsg modName ctx

-- | Update the ProcModifiers to specify the given Resourcefulness, which was 
-- specified with the given identifier.  Since resourceless is the default, 
-- and can't be explicitly specified, it's alway OK to change from resourceless
-- to resourceful.
updateModsResource :: String -> String -> Bool -> ProcModifiers
                   -> Parser ProcModifiers
updateModsResource _ _ resful mods@ProcModifiers{modifierResourceful=False} =
    return $ mods {modifierResourceful=resful}
updateModsResource ctx modName _ mods =
    fail $ modifierConflictMsg modName ctx


modifierConflictMsg :: String -> String -> String
modifierConflictMsg mod ctx =
    "Modifier '" ++ mod ++ "' conflicts with earlier modifier in " ++ ctx


modifierError :: SourceInfo -> String -> String -> Parser a
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


-- |Parse a term.  The term is parsed in an astNode context, so its source info
-- is available.
term :: Parser Term
term = limitedTerm lowestTermPrecedence


-- |A term with an operator precedence of limited looseness.  The term is parsed
-- in an astNode context, so its source info is available.
limitedTerm :: Int -> Parser Term
limitedTerm precedence = astNode $ termFirst >>= termRest precedence


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
    <|> do
        args <- (left:) <$> argumentList Bracket
        termWithSourceInfo $ Call [] "[]" ParamIn args


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
            return $ embraced{embracedArg=Just $ Embraced Paren args Nothing pos}
        other -> fail $ "unexpected argument list following expression "
                        ++ show other

applyEmbraced :: Term -> Term -> Parser Term
applyEmbraced expr@(Embraced Brace _ Nothing _) arg =
    return expr{embracedArg=Just arg}
applyEmbraced expr _ = fail $ "unexpected embraced term following " ++ show expr


-- |Complete parsing a term of precedence no looser than specified, given
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
        termRest minPrec $ Call [] op ParamIn [left,right] pos
    <|> -- Otherwise try to parse a call with 1 un-parenthesised argument;
        -- failing that, the left context is the whole expression.
        case left of
            Call m n _ [] _ | minPrec <= lowestStmtPrecedence
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
    <|> anonymousTerm
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
    termWithSourceInfo $ Embraced Paren exps Nothing


varOrCall :: Parser Term
varOrCall = do
    pos <- getPosition
    modVar <- moduleSpec
    termWithSourceInfo $ Call (init modVar) (last modVar) ParamIn []


anonymousTerm :: Parser Term
anonymousTerm = do
    pos <- tokenPosition <$> symbol "@"
    term <- optionMaybe (choice [intConst, parenthesisedTerm])
    termWithSourceInfo $ Call [] "@" ParamIn $ maybeToList term


-- | Parse a sequence of Terms enclosed in braces.
embracedTerm :: Parser Term
embracedTerm = do
    leftBracket Brace
    embraced <- limitedTerm lowestStmtSeqPrecedence `sepBy` comma
                    <* rightBracket Brace
    termWithSourceInfo $ Embraced Brace embraced Nothing


-- | Parse all expressions beginning with the terminal "[".
-- List -> '[' Term ListTail
-- Empty List -> '[' ']'
-- List Cons -> '[' '|' ']'
listTerm :: Parser Term
listTerm = do
    leftBracket Bracket <?> "list"
    (rightBracket Bracket >> termWithSourceInfo (Call [] "[]" ParamIn []))
        <|> do
            head <- term
            tail <- listTail
            termWithSourceInfo $ Call [] "[|]" ParamIn [head,tail]


-- | Parse the tail of a list.
-- ListTail -> ']' | ',' Term ListTail
listTail :: Parser Term
listTail = do
        pos <- tokenPosition <$> rightBracket Bracket
        termWithSourceInfo $ Call [] "[]" ParamIn []
    <|> do
        pos <- tokenPosition <$> comma
        head <- term
        tail <- listTail
        termWithSourceInfo $ Call [] "[|]" ParamIn [head, tail]
    <|> symbol "|" *> term <* rightBracket Bracket


-- |A foreign function or procedure call.
foreignCall :: Parser Term
foreignCall = do
    ident "foreign"
    language <- identString
    flags <- modifierList
    fname <- identString
    args <- argumentList Paren
    termWithSourceInfo $ Foreign language fname flags args


-- |A for loop.
forLoop :: Parser Term
forLoop = do
    pos <- tokenPosition <$> ident "for"
    gen <- limitedTerm lowestStmtSeqPrecedence
    body <- embracedTerm
    termWithSourceInfo $ Call [] "for" ParamIn [gen,body]


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
    let inf = leftExtendSourceInfo tok $ termPos term
    case (tokenName tok, term) of
        ("-", IntConst num _) -> return $ IntConst (-num) inf
        ("-", FloatConst num _) -> return $ FloatConst (-num) inf
        ("-", Call{}) -> return $ call1 "-" term inf
        ("-", Foreign{}) -> return $ call1 "-" term inf
        ("-", Embraced{embracedStyle=Paren,embraced=[expr]})
            -> return $ call1 "-" expr inf
        ("-", _) -> fail $ "cannot negate " ++ show term
        ("~", IntConst num _) -> return $ IntConst (complement num) inf
        ("~", Call{}) -> return $ call1 "~" term inf
        ("~", Foreign{}) -> return $ call1 "~" term inf
        ("~", Embraced{embracedStyle=Paren,embraced=[expr]})
            -> return $ call1 "~" expr inf
        ("~", _) -> fail $ "cannot negate " ++ show term
        ("?", Call{callVariableFlow=ParamIn}) -> return $ setCallFlow ParamOut term
        ("?", _) -> fail $ "unexpected " ++ show term ++ " following '?'"
        ("!", Call{callVariableFlow=ParamIn}) -> return $ setCallFlow ParamInOut term
        ("!", _) -> fail $ "unexpected " ++ show term ++ " following '!'"
        (_,_) -> shouldnt $ "Unknown prefix operator " ++ show tok
                            ++ " in applyPrefixOp"


-- |Unary call to the specified proc name with the specified argument.  The
-- default (empty) module and default (ParamIn) variable flow are used.
call1 :: ProcName -> Term -> SourceInfo -> Term
call1 name arg = Call [] name ParamIn [arg]


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
takeToken =
    -- tokenPrimEx show tokPos $ Just recordToken
    tokenPrim show tokPos
    where tokPos _ tok _ = tokenPosition tok


unitTokenMatch :: Token -> (SourceInfo -> a) -> Maybe a
unitTokenMatch tok f = Just $ f $ unitSourceInfo tok


-- | Parse a float literal token.
floatConst :: Parser Term
floatConst = takeToken test
    where
      test t@(TokFloat f p) = unitTokenMatch t $ FloatConst f
      test _                = Nothing


-- | Parse an integer literal token.
intConst :: Parser Term
intConst = takeToken test
  where
    test t@(TokInt i p) = unitTokenMatch t $ IntConst i
    test _              = Nothing


-- |Parse an integer constant
intLiteral :: Parser (Placed Integer)
intLiteral = takeToken test
  where
    test t@(TokInt i p) = unitTokenMatch t $ Placed i
    test _              = Nothing


-- | Parse a character literal token.
charConst :: Parser Term
charConst = takeToken test
    where
      test t@(TokChar c p) = unitTokenMatch t $ CharConst c
      test _               = Nothing


-- | Parse a string literal token.
stringConst :: Parser Term
stringConst = takeToken test
  where
    test t@(TokString d s p) = unitTokenMatch t $ StringConst s d
    test _                   = Nothing


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
    test t@(TokIdent s p) = unitTokenMatch t $ Call [] s ParamIn []
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
    test t@(TokIdent s p) =
        if s `elem` avoid then Nothing else unitTokenMatch t $ Placed s
    test _                = Nothing


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
parseWith :: (Term -> Parser a) -> Term -> Parser a
parseWith translator t =
    translator t <|> reportFailure (sourceStart (termPos t)) "unexpected term"


-- |Fail the parser with the provided error message and associated SourcePos
reportFailure :: SourcePos -> String -> Parser a
reportFailure pos message = setPosition pos >> parserFail message


-----------------------------------------------------------------------------
-- Translating Term to the correct output types                        --
-----------------------------------------------------------------------------

-- |Type alias for a translation function
type TranslateTo t = Term -> Parser t


parensToTerm :: [Term] -> [Term]
parensToTerm [Embraced Paren parensed Nothing _] = parensed
parensToTerm ses = ses

-- |Convert a Term to a proc/func prototype and a return type (AnyType for a
-- proc declaration or a function with no return type specified).
termToPrototype :: TranslateTo (ProcProto, TypeSpec)
termToPrototype (Call [] ":" ParamIn [rawProto,rawTy] _) = do
    returnType <- termToTypeSpec rawTy
    (proto,_)  <- termToPrototype rawProto
    return (proto,returnType)
termToPrototype (Embraced Paren [proto] Nothing _) = termToPrototype proto
termToPrototype (Call mod name ParamIn rawParams pos) =
    if List.null mod
    then do
        params <- mapM termToParam $ parensToTerm rawParams
        return (ProcProto name params [],AnyType)
    else reportFailure (sourceStart pos)
            $ "module not permitted in proc declaration " ++ show mod
termToPrototype other =
    reportFailure (sourceStart (termPos other))
                $ "invalid proc/func prototype " ++ show other


-- |Convert a Term to a body, if possible, or give a syntax error if not.
termToBody :: TranslateTo [Placed Stmt]
termToBody (Call [] sep ParamIn [left,right] pos)
  | separatorName sep = do
    left' <- termToBody left
    right' <- termToBody right
    return $ left' ++ right'
termToBody (Embraced Brace [body] Nothing pos) =
    termToBody body
termToBody other = (:[]) <$> termToStmt other


-- |Convert a Term to a Stmt, if possible, or give a syntax error if not.
termToStmt :: TranslateTo (Placed Stmt)
termToStmt (Embraced Paren [body] Nothing _) = termToStmt body
termToStmt (Embraced Brace [body] Nothing _) = termToStmt body
termToStmt (Call [] "if" ParamIn [conditional] _) =
    termToStmt conditional
termToStmt (Call [] "case" ParamIn
                [Call [] "in" ParamIn
                      [exp,Embraced Brace [body] Nothing _] _] pos) = do
    expr' <- termToExp exp
    (cases,deflt) <- termToCases termToBody body
    return $ Placed (Case expr' cases deflt) pos
termToStmt (Call [] "do" ParamIn [body] pos) =
    (`Placed` pos) . flip (`Loop` Nothing) Nothing <$> termToBody body
termToStmt (Call [] "for" ParamIn [gen,body] pos) = do
    genStmts <- termToGenerators gen
    (`Placed` pos) . For genStmts <$> termToBody body
termToStmt (Call [] "use" ParamIn
                    [Call [] "in" ParamIn [ress,body] _] pos) = do
    ress' <- termToResourceList ress
    body' <- termToBody body
    return $ Placed (UseResources ress' Nothing body') pos
termToStmt (Call [] "while" ParamIn [test] pos) = do
    t <- termToStmt test
    return $ Placed (Cond t [Unplaced Nop] [Unplaced Break] Nothing Nothing Nothing) pos
termToStmt (Call [] "until" ParamIn [test] pos) = do
    t <- termToStmt test
    return $ Placed (Cond t [Unplaced Break] [Unplaced Nop] Nothing Nothing Nothing) pos
termToStmt (Call [] "when" ParamIn [test] pos) = do
    t <- termToStmt test
    return $ Placed (Cond t [Unplaced Nop] [Unplaced Next] Nothing Nothing Nothing) pos
termToStmt (Call [] "unless" ParamIn [test] pos) = do
    t <- termToStmt test
    return $ Placed (Cond t [Unplaced Next] [Unplaced Nop] Nothing Nothing Nothing) pos
termToStmt (Call [] "pass" ParamIn [] pos) = do
    return $ Placed Nop pos
termToStmt (Call [] "|" ParamIn
             [Call [] "::" ParamIn [test1,thn] _,
              Call [] "::" ParamIn [Call [] test2 ParamIn [] _,els] _] pos)
  | defaultGuard test2 = do
    test1' <- termToStmt test1
    thn' <- termToBody thn
    els' <- termToBody els
    return $ Placed (Cond test1' thn' els' Nothing Nothing Nothing) pos
termToStmt
        (Call [] "|" ParamIn [Call [] "::" ParamIn [test,body] pos,rest] _) = do
    test' <- termToStmt test
    body' <- termToBody body
    rest' <- termToBody rest
    return $ Placed (Cond test' body' rest' Nothing Nothing Nothing) pos
termToStmt (Call [] "|" ParamIn disjs pos) = do
    (`Placed` pos) . flip (`Or` Nothing) Nothing <$> mapM termToStmt disjs
termToStmt (Call [] "::" ParamIn [Call [] guard ParamIn [] _,body] pos)
  | defaultGuard guard = do
    syntaxError pos  "'else' outside an 'if'"
termToStmt (Call [] "::" ParamIn [test,body] pos) = do
    test' <- termToStmt test
    body' <- termToBody body
    return $ Placed (Cond test' body' [Unplaced Nop] Nothing Nothing Nothing) pos
termToStmt (Call [] "&" ParamIn conjs pos) = do
    (`Placed` pos) . And <$> mapM termToStmt conjs
termToStmt (Call [] fn ParamIn [first,rest] _)
  | separatorName fn = do
    first' <- termToStmt first
    rest'  <- termToStmt rest
    return $ Unplaced $ And [first',rest']
termToStmt (Call mod fn ParamIn args pos)
    = (`Placed` pos) . ProcCall (regularModProc mod fn) Det False
        <$> mapM termToExp args
termToStmt (Call mod fn ParamInOut args pos)
    = (`Placed` pos) . ProcCall (regularModProc mod fn) Det True
        <$> mapM termToExp args
termToStmt (Call mod fn flow args pos) =
    syntaxError pos $ "invalid statement prefix: " ++ flowPrefix flow
termToStmt (Foreign lang inst flags args pos) =
    (`Placed` pos) . ForeignCall lang inst flags <$> mapM termToExp args
termToStmt other =
    syntaxError (termPos other) $ "invalid statement " ++ show other


--  Convert a term to a list of generators, of the form `i in is; j in js; ...`
termToGenerators :: TranslateTo [Placed Generator]
termToGenerators (Call [] sep ParamIn [left,right] pos)
  | separatorName sep = do
    left' <- termToGenerators left
    right' <- termToGenerators right
    return $ left' ++ right'
termToGenerators (Call [] "in" ParamIn [var,exp] pos) = do
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
      (Call [] "|" ParamIn [Call [] "::" ParamIn [val,thn] _, rest] pos) = do
    val' <- termToExp val
    thn' <- caseTrans thn
    (rest',deflt) <- termToCases caseTrans rest
    return ((val',thn') : rest', deflt)
termToCases caseTrans (Call [] "::" ParamIn [Call [] g ParamIn [] _,thn] _)
  | defaultGuard g = do
    thn' <- caseTrans thn
    return ([], Just thn')
termToCases caseTrans (Call [] "::" ParamIn [val,thn] _) = do
    val' <- termToExp val
    thn' <- caseTrans thn
    return ([(val',thn')], Nothing)
termToCases _ other = do
    syntaxError (termPos other) $ "invalid case body " ++ show other


-- |Convert a Term to an Exp, if possible, or give a syntax error if not.
termToExp :: TranslateTo (Placed Exp)
termToExp (Call [] ":" ParamIn [exp,ty] pos) = do
    exp' <- content <$> termToExp exp
    ty' <- termToTypeSpec ty
    case exp' of
        Typed exp'' ty'' (Just AnyType) -> -- already cast, but not typed
            return $ Placed (Typed exp'' ty'' $ Just ty') pos
        Typed exp'' _ _ -> -- already typed, whether casted or not
            syntaxError (termPos ty) $ "repeated type constraint " ++ show ty
        _ -> -- no cast, no type
            return $ Placed (Typed exp'  ty' Nothing) pos
termToExp (Call [] ":!" ParamIn [exp,ty] pos) = do
    exp' <- content <$> termToExp exp
    ty' <- termToTypeSpec ty
    case exp' of
        Typed exp'' inner Just{} ->
            syntaxError (termPos ty) $ "repeated cast " ++ show ty
        Typed exp'' inner Nothing ->
            return $ Placed (Typed exp'' ty' $ Just inner) pos
        _  ->
            return $ Placed (Typed exp'  ty' $ Just AnyType) pos
termToExp (Call [] "fail" ParamIn [] pos) = return $ Placed FailExpr pos
termToExp (Call [] "where" ParamIn [exp,body] pos) = do
    exp' <- termToExp exp
    body' <- termToBody body
    return $ Placed (Where body' exp') pos
termToExp (Call [] "let" ParamIn [Call [] "in" ParamIn [body,exp] _] pos) =
  do
    exp' <- termToExp exp
    body' <- termToBody body
    return $ Placed (Where body' exp') pos
termToExp (Call [] "^" ParamIn [exp,op] pos) = do
    exp' <- termToExp exp
    op'  <- termToExp op
    case op' of
        Placed (Fncall mod fn False args) _
            -> return $ Placed (Fncall mod fn False (exp':args)) pos
        Placed (Var var ParamIn Ordinary) _
            -> return $ Placed (Fncall [] var False [exp']) pos
        _ -> syntaxError pos "invalid second argument to '^'"
termToExp (Call [] "@" flow exps pos) = do
    exps' <- mapM termToExp exps
    case content <$> exps' of
        [] -> return $ Placed (AnonParamVar Nothing flow) pos
        [IntValue i] | i > 0
            -> return $ Placed (AnonParamVar (Just i) flow) pos
        [exp]
            -> return $ Placed (AnonFunc $ head exps') pos
        _ -> syntaxError pos "invalid anonymous parameter/function expression"
termToExp (Call [] "|" ParamIn [exp1,exp2] pos) = do
    exp1' <- termToExp exp1
    exp2' <- termToExp exp2
    return $ Placed (DisjExp exp1' exp2') pos
termToExp (Call [] "if" ParamIn [conditional] pos) =
    termToConditionalExp conditional
termToExp (Embraced Paren [exp] Nothing _) = termToExp exp
termToExp body@(Embraced Brace _ Nothing pos) = do
    body' <- termToBody body
    return $ Placed (AnonProc defaultProcModifiers [] body' Nothing Nothing) pos
termToExp mods@(Embraced Brace _
                    (Just body@(Embraced Brace _ _ _)) pos) = do
    procMods <- termToProcModifiers "anonymous procedure" mods
    let inlining = modifierInline procMods
    unless (inlining == MayInline)
        $ modifierError pos (inliningName inlining) "anonymous procedure"
    anonProc <- content <$> termToExp body
    case anonProc of
        AnonProc oldMods ps body clsd _ | oldMods == defaultProcModifiers
            -> return $ Placed (AnonProc procMods ps body clsd Nothing) pos
        _ -> syntaxError pos $ "malformed anonymous procedure " ++ show anonProc
termToExp embraced@(Embraced _ _ _ pos) =
    syntaxError pos $ "malformed anonymous procedure " ++ show embraced
termToExp (Call [] "case" ParamIn
            [Call [] "in" ParamIn
                [exp,Embraced Brace [body] Nothing _] _] pos) = do
    expr' <- termToExp exp
    (cases,deflt) <- termToCases termToExp body
    return $ Placed (CaseExp expr' cases deflt) pos
termToExp (Call [] sep ParamIn [] pos)
  | separatorName sep =
    syntaxError pos "invalid separated expression"
termToExp (Call [] var flow [] pos) = -- looks like a var; assume it is
    return $ Placed (Var var flow Ordinary) pos
termToExp (Call mod fn flow args pos)
  | flow == ParamOut =
    syntaxError pos $ "invalid function call prefix " ++ flowPrefix flow
  | otherwise =
    (`Placed` pos) . Fncall mod fn (flow == ParamInOut) <$> mapM termToExp args
termToExp (Foreign lang inst flags args pos) =
    (`Placed` pos) . ForeignFn lang inst flags <$> mapM termToExp args
termToExp (IntConst num pos) = return $ Placed (IntValue num) pos
termToExp (FloatConst num pos) = return $ Placed (FloatValue num) pos
termToExp (CharConst char pos) = return $ Placed (CharValue char) pos
termToExp (StringConst str DoubleQuote pos)
    = return $ Placed (StringValue str WybeString) pos
termToExp (StringConst str (IdentQuote "c" DoubleQuote) pos)
    = return $ Placed (StringValue str CString) pos
termToExp str@StringConst{stringPos=pos}
    = syntaxError pos $ "invalid string literal " ++ show str


termToIdent :: TranslateTo Ident
termToIdent (Call [] ident ParamIn [] _) = return ident
termToIdent other
    = syntaxError (termPos other) $ "invalid ident " ++ show other

termToProcModifiers :: String -> TranslateTo ProcModifiers
termToProcModifiers ctx (Embraced Brace mods _ pos) = do
    idents <- mapM termToIdent mods
    processProcModifiers ctx idents
termToProcModifiers ctx other
    = syntaxError (termPos other)
    $ "invalid modifiers " ++ show other ++ " in " ++ ctx



-- |Translate an `if` expression into a Placed conditional Exp
termToConditionalExp :: TranslateTo (Placed Exp)
termToConditionalExp (Embraced Brace [body] Nothing _) =
    termToConditionalExp' body
termToConditionalExp term =
    syntaxError (termPos term) "expecting '{'"

termToConditionalExp' :: TranslateTo (Placed Exp)
termToConditionalExp'
        (Call [] "|" ParamIn [Call [] "::" ParamIn [test,body] pos,rest] _) = do
    test' <- termToStmt test
    body' <- termToExp body
    rest' <- termToConditionalExp' rest
    return $ Placed (CondExp test' body' rest') pos
termToConditionalExp'
        (Call [] "::" ParamIn [Call [] guard ParamIn [] _,body] pos)
    | defaultGuard guard = termToExp body
termToConditionalExp' (Call [] "::" ParamIn [test,body] pos) = do
    -- implicit "else :: fail"
    test' <- termToStmt test
    body' <- termToExp body
    return $ Placed (CondExp test' body' (Unplaced FailExpr)) pos
termToConditionalExp' term =
    syntaxError (termPos term) "expecting conditional case"


-- |Convert a Term to a TypeSpec, or produce an error
termToTypeSpec :: TranslateTo TypeSpec
termToTypeSpec mods@(Embraced Brace _ (Just ty@(Embraced Paren _ Nothing _)) pos) = do
    mods <- termToProcModifiers "type constraint" mods
    let inlining = modifierInline mods
    unless (inlining == MayInline)
        $ modifierError pos (inliningName inlining) "type constraint"
    ty' <- termToTypeSpec ty
    case ty' of
        HigherOrderType _ params -> return $ HigherOrderType mods params
        _ -> syntaxError pos $ "invalid higher-order type " ++ show ty'
termToTypeSpec (Embraced Paren args Nothing _) =
    HigherOrderType defaultProcModifiers <$> mapM termToTypeFlow args
termToTypeSpec (Call [] name ParamIn [] _)
  | isTypeVar name =
    return $ TypeVariable $ RealTypeVar name
termToTypeSpec (Call mod name ParamIn params _)
  | not $ isTypeVar name =
    TypeSpec mod name <$> mapM termToTypeSpec params
termToTypeSpec other =
    syntaxError (termPos other) $ "invalid type specification " ++ show other

termToTypeFlow :: TranslateTo TypeFlow
termToTypeFlow (Call [] ":" _ [Call [] _ flow [] _,ty] _) =
    (`TypeFlow` flow) <$> termToTypeSpec ty
termToTypeFlow ty@(Call _ _ flow _ _) =
    (`TypeFlow` flow) <$> termToTypeSpec (setCallFlow ParamIn ty)
termToTypeFlow other =
    syntaxError (termPos other) $ "invalid higher order type argument " ++ show other


-- | Translate a Term to a proc or func prototype (with empty resource list)
termToProto :: TranslateTo (Placed ProcProto)
termToProto (Call [] name ParamIn params pos) = do
    params' <- mapM termToParam params
    return $ Placed (ProcProto name params' []) pos
termToProto other =
    syntaxError (termPos other) $ "invalid prototype " ++ show other


-- | Translate a Term to a proc or func parameter
termToParam :: TranslateTo (Placed Param)
termToParam (Call [] ":" ParamIn [Call [] name flow [] _,ty] pos) = do
    ty' <- termToTypeSpec ty
    return $ Param name ty' flow Ordinary `maybePlace` Just pos
termToParam (Call [] name flow [] pos) =
    return $ Param name AnyType flow Ordinary `maybePlace` Just pos
termToParam other =
    syntaxError (termPos other) $ "invalid parameter " ++ show other


-- | Translate a Term to a ctor declaration
termToCtorDecl :: TranslateTo (Placed ProcProto)
termToCtorDecl (Call [] name ParamIn fields pos) = do
    fields' <- mapM termToCtorField fields
    succeedWithSourceInfo (ProcProto name fields' [])
termToCtorDecl other =
    syntaxError (termPos other)
        $ "invalid constructor declaration " ++ show other


-- | Translate a Term to a ctor field
termToCtorField :: TranslateTo (Placed Param)
termToCtorField (Call [] ":" ParamIn [Call [] name ParamIn [] _,ty] pos) = do
    ty' <- termToTypeSpec ty
    return $ Param name ty' ParamIn Ordinary `maybePlace` Just pos
termToCtorField (Call [] name ParamIn [] pos)
  | isTypeVar name = do
    return $ Param "" (TypeVariable $ RealTypeVar name) ParamIn Ordinary
                `maybePlace` Just pos
termToCtorField (Call mod name ParamIn params pos)
  | not $ isTypeVar name = do
    tyParams <- mapM termToTypeSpec params
    return $ Param "" (TypeSpec mod name tyParams) ParamIn Ordinary
                `maybePlace` Just pos
termToCtorField other =
    syntaxError (termPos other) $ "invalid constructor field " ++ show other


-- | Extract a list of resource names from a Term (from a "use" statement).
termToResourceList :: TranslateTo [ResourceSpec]
termToResourceList (Embraced Brace args Nothing _) =
    concat <$> mapM termToResourceList args
termToResourceList (Call mod name ParamIn [] _) =
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
        callModule::ModSpec,              -- ^the specified module, or empty
        callName::ProcName,               -- ^the called proc or variable name
        callVariableFlow::FlowDirection,  -- ^variable flow direction or
                                          --  call resourcefulness
        callArguments::[Term],            -- ^the specified arguments
        callPos::SourceInfo               -- ^Where the call appears
    }
    -- |a foreign call, either as an expression or statement.
    | Foreign {
        foreignLanguage::Ident,        -- ^the specified foreign language
        foreignInstruction::ProcName,  -- ^the specified instruction
        foreignFlags::[Ident],         -- ^the specified modifiers
        foreignArguments::[Term],      -- ^the specified arguments
        foreignPos::SourceInfo         -- ^Where the foreign call appears
    }
    | Embraced {
        embracedStyle::BracketStyle,
        embraced::[Term],
        embracedArg::Maybe Term,
        embracedPos::SourceInfo
    }
    -- |an integer manifest constant
    | IntConst {intConstValue::Integer, intPos::SourceInfo}
    -- |a floating point manifest constant
    | FloatConst{floatConstValue::Double, floatPos::SourceInfo}
    -- |a character literal
    | CharConst{charConstValue::Char, charPos::SourceInfo}
    -- |a string literal
    | StringConst{
        stringConstValue::String,
        stringConstantDelim::StringDelim,
        stringPos::SourceInfo
    }


instance Show Term where
    show (Call mod name flow args _) =
        flowPrefix flow ++ maybeModPrefix mod ++ name ++ showArguments args
    show (Foreign lang instr flags args _) =
        "foreign " ++ lang ++ " " ++ showFlags' flags ++ instr
        ++ showArguments args
    show (Embraced style embraced arg _) =
        bracketString True style ++ intercalate "," (show <$> embraced)
                                 ++ bracketString False style
                                 ++ maybe "" show arg
    show (IntConst int _) = show int
    show (FloatConst float _) = show float
    show (CharConst char _) = show char
    show (StringConst string delim _) = delimitString delim string


-- |The SourceInfo of a Term.
termPos :: Term -> SourceInfo
termPos Call{callPos=pos}            = pos
termPos Foreign{foreignPos=pos}      = pos
termPos Embraced{embracedPos=pos}    = pos
termPos IntConst{intPos=pos}         = pos
termPos FloatConst{floatPos=pos}     = pos
termPos CharConst{charPos=pos}       = pos
termPos StringConst{stringPos=pos}   = pos


-- |Return the specified Term with its position replaced.
setTermPos :: SourceInfo -> Term -> Term
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

-- test :: Int -> String -> Term
-- test prec input = do
--     let toks = stringTokens input
--     case parseWybe (maybeSetPosition toks (limitedTerm prec) <* eof) "<string>" toks of
--         Left err -> StringConst (show err) DoubleQuote (unitSourceInfo (errorPos err))
--         Right is -> is

testParser :: Parser a -> String -> Either ParseError a
testParser parser input =
    evalState (runParserT (maybeSetPosition toks parser <* eof) () "<string>" toks)
              EmptyState
  where toks = stringTokens input