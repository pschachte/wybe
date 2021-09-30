{-# LANGUAGE LambdaCase #-}
--  File     : Parser.hs
--  Author   : Peter Schachte <schachte@unimelb.edu.au>
--  Purpose  : Parser for the Wybe language using Parsec.
--  Copyright: (c) 2021 Peter Schachte
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.

module Parser where


import AST hiding (option)
import Debug.Trace
import Data.Set as Set
import Data.List as List
import Data.Bits
import Control.Monad.Identity (Identity)
import Scanner
import Util
import Config
import Text.Parsec
import Text.Parsec.Pos
import Data.Functor
-- import qualified Parser as OldParser
-- import           Data.Algorithm.Diff       (getGroupedDiff)
-- import           Data.Algorithm.DiffOutput (ppDiff)
-- import           Text.Parsec.Expr
import Control.Monad


-----------------------------------------------------------------------------
-- Top level of the parser:  parsing Items                                 --
-----------------------------------------------------------------------------

-- | The parser monad.
type Parser a = Parsec [Token] () a


-- | Report a syntax error
syntaxError :: SourcePos -> String -> Either (SourcePos,String) a
syntaxError pos msg = Left (pos,msg)


-- | Parse a Wybe module.
parseWybe :: [Token] -> FilePath -> Either ParseError [Item]
parseWybe toks file = parse (items <* eof) file toks


-- | Parser entry for a Wybe program.
items :: Parser [Item]
items = singleItem `sepBy` separator


singleItem :: Parser Item
singleItem = visibilityItem <|> privateItem <|> topLevelStmtItem


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


-- | Parse module-local items (with no visibility prefix).
privateItem :: Parser Item
privateItem = typeRepItem <|> pragmaItem


pragmaItem :: Parser Item
pragmaItem = ident "pragma" *> (PragmaDecl <$> parsePragma)


-- TODO:  Should use the StmtExpr parser to parse the declaration body.
parsePragma :: Parser Pragma
parsePragma = ident "no_standard_library" $> NoStd


-- | Module item parser.
moduleItem :: Visibility -> Parser Item
moduleItem v = do
    pos <- tokenPosition <$> ident "module"
    modName <- identString
    body <- betweenB Brace items
    return $ ModuleDecl v modName body (Just pos)


-- | Type declaration item parser.
typeItem :: Visibility -> Parser Item
typeItem v = do
    pos <- tokenPosition <$> ident "type"
    proto <- TypeProto <$> identString <*>
             option [] (betweenB Paren (typeVarName `sepBy` comma))
    (imp,items) <- typeImpln <|> typeCtors
    return $ TypeDecl v proto imp items (Just pos)


-- | Module type representation declaration
typeRepItem :: Parser Item
typeRepItem = do
    keypos <- tokenPosition <$> ident "representation"
    params <- option [] $ betweenB Paren (typeVarName `sepBy` comma)
    ident "is"
    rep <- typeRep
    return $ RepresentationDecl params rep $ Just keypos


-- | Module type representation declaration
dataCtorItemParser :: Visibility -> Parser Item
dataCtorItemParser v = do
    pos <- tokenPosition <$> (ident "constructor" <|> ident "constructors")
    params <- option [] $ betweenB Paren (typeVarName `sepBy` comma)
    ctors <- ctorDecl `sepBy1` symbol "|"
    return $ ConstructorDecl v params ctors $ Just pos


-- | Type declaration body where representation and items are given
typeImpln = do
    impln <- TypeRepresentation <$> (ident "is" *> typeRep)
    items <- betweenB Brace items
    return (impln,items)


-- | Type declaration body where representation and items are given
typeRep :: ParsecT [Token] () Identity TypeRepresentation
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
    vis <- visibility
    ctors <- procFuncProto `sepBy1` symbol "|"
    items <- option [] (separator *> items)
    return (TypeCtors vis ctors,items)


procFuncProto :: Parser (Placed ProcProto)
procFuncProto = stmtExpr >>= parseWith stmtExprToProto


ctorDecl :: Parser (Placed ProcProto)
ctorDecl = stmtExpr >>= parseWith stmtExprToCtorDecl


-- | Resource declaration parser.
resourceItem :: Visibility -> Parser Item
resourceItem v = do
    pos <- tokenPosition <$> ident "resource"
    let optInit = optionMaybe (symbol "=" *> expr)
    ResourceDecl v <$> identString <* symbol ":"
        <*> typeSpec <*> optInit <*> return (Just pos)


useItemParser :: Visibility -> Parser Item
useItemParser v = do
    pos <- Just . tokenPosition <$> ident "use"
    ident "foreign" *> foreignFileOrLib v pos
      <|> ImportMods v <$> (moduleSpec `sepBy` comma) <*> return pos


foreignFileOrLib :: Visibility -> OptPos -> Parser Item
foreignFileOrLib v pos =
    ImportForeignLib
        <$> (ident "library" *> identString `sepBy` comma) <*> return pos
    <|> ImportForeign
            <$> (ident "object" *> identString `sepBy` comma) <*> return pos


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
    pos <- Just . tokenPosition <$> ident "def"
    mods <- processProcModifiers <$> modifierList
    (proto, returnType) <- limitedStmtExpr prototypePrecedence
                            >>= parseWith stmtExprToPrototype
    do
        body <- symbol "=" *> expr
        return $ FuncDecl vis mods proto returnType body pos
      <|> if returnType /= AnyType
          then fail "unexpected return type in proc declaration"
          else do
            rs <- option [] (ident "use" *> resourceFlowSpec `sepBy1` comma)
            let proto' = proto { procProtoResources = Set.fromList rs }
            body <- embracedStmtExp >>= parseWith stmtExprToBody
            return $ ProcDecl vis mods proto' body pos


-- | Parse a proc or function prototype

-- | Parse a specification of a resource and its flow direction.
resourceFlowSpec :: Parser ResourceFlowSpec
resourceFlowSpec = do
    flow <- flowDirection
    res <- resourceSpec
    return $ ResourceFlowSpec res flow


resourceSpec :: Parser ResourceSpec
resourceSpec = do
    m <- moduleSpec
    return $ ResourceSpec (init m) (last m)


-- | Optional flow direction symbol prefix.
flowDirection :: Parser FlowDirection
flowDirection =
    option ParamIn $ symbol "?" $> ParamOut <|> symbol "!" $> ParamInOut


-----------------------------------------------------------------------------
-- Handling proc modifiers                                                 --
-----------------------------------------------------------------------------

-- | Extract a ProcModifiers from a list of identifiers.  If the Bool is False,
-- then don't report any errors in the modifiers.  The position is the source
-- location of the list of modifiers.
processProcModifiers :: [String] -> ProcModifiers
processProcModifiers = List.foldl (flip processProcModifier)
                        $ ProcModifiers Det MayInline Pure [] []

-- |Update 
processProcModifier :: String -> ProcModifiers -> ProcModifiers
processProcModifier "test"     = updateModsDetism   "test" SemiDet
processProcModifier "partial"  = updateModsDetism   "partial" SemiDet
processProcModifier "failing"  = updateModsDetism   "failing" Failure
processProcModifier "terminal" = updateModsDetism   "terminal" Terminal
processProcModifier "inline"   = updateModsInlining "inline" Inline
processProcModifier "noinline" = updateModsInlining "noinline" NoInline
processProcModifier "pure"     = updateModsImpurity "pure" PromisedPure
processProcModifier "semipure" = updateModsImpurity "semipure" Semipure
processProcModifier "impure"   = updateModsImpurity "impure" Impure
processProcModifier modName    =
    \ms -> ms {modifierUnknown=modName:modifierUnknown ms}



-- | Update the ProcModifiers to specify the given determinism, which was
-- specified with the given identifier.  Since Det is the default, and can't be
-- explicitly specified, it's alway OK to change from Det to something else.
updateModsDetism :: String -> Determinism -> ProcModifiers -> ProcModifiers
updateModsDetism _ detism mods@ProcModifiers{modifierDetism=Det} =
    mods {modifierDetism=detism}
updateModsDetism modName detism mods =
    mods {modifierConflict=modName:modifierConflict mods}


-- | Update the ProcModifiers to specify the given inlining, which was specified
-- with the given identifier.  Since MayInline is the default, and can't be
-- explicitly specified, it's alway OK to change from MayInline to something
-- else.
updateModsInlining :: String -> Inlining -> ProcModifiers -> ProcModifiers
updateModsInlining _ inlining mods@ProcModifiers{modifierInline=MayInline} =
    mods {modifierInline=inlining}
updateModsInlining modName inlining mods =
    mods {modifierConflict=modName:modifierConflict mods}


-- | Update the ProcModifiers to specify the given Impurity, which was specified
-- with the given identifier.  Since Pure is the default, and can't be
-- explicitly specified, it's alway OK to change from Pure to something
-- else.
updateModsImpurity :: String -> Impurity -> ProcModifiers -> ProcModifiers
updateModsImpurity _ impurity mods@ProcModifiers{modifierImpurity=Pure} =
    mods {modifierImpurity=impurity}
updateModsImpurity modName _ mods =
    mods {modifierConflict=modName:modifierConflict mods}


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
stmtSeq = stmtExpr >>= parseWith stmtExprToBody


-- |Parse a single Placed Stmt.
stmt :: Parser (Placed Stmt)
stmt = limitedStmtExpr lowestStmtPrecedence >>= parseWith stmtExprToStmt


-- |Parse a placed Exp
expr :: Parser (Placed Exp)
expr = stmtExpr >>= parseWith stmtExprToExp


typeSpec :: Parser TypeSpec
typeSpec = limitedStmtExpr prototypePrecedence >>= parseWith stmtExprToTypeSpec


-- |Parse a stmtExpr.
stmtExpr :: Parser StmtExpr
stmtExpr = limitedStmtExpr lowestExprPrecedence


-- |A stmtExpr with an operator precedence of limited looseness.
limitedStmtExpr :: Int -> Parser StmtExpr
limitedStmtExpr precedence = stmtExprFirst >>= stmtExprRest precedence


-- |The left argument to an infix operator.  This is a primaryStmtExpr,
-- possibly preceded by a prefix operator or followed by an stmtExprSuffix.
-- Valid suffixes include parenthesised argument lists or square bracketed
-- indices.  If both prefix and suffix are present, the suffix binds tighter.
stmtExprFirst :: Parser StmtExpr
stmtExprFirst = (do
             op <- prefixOp
             stmtExprFirst >>= applyPrefixOp op)
         <|> (primaryStmtExpr >>= stmtExprSuffix)


-- |Apply zero or more parenthesised or square bracketed suffixes to the
-- specified stmtExpr. If multiple suffixes are present, they associate to the
-- left.
stmtExprSuffix :: StmtExpr -> Parser StmtExpr
stmtExprSuffix left =
    (try (stmtExprSuffix' left) >>= stmtExprSuffix) <|> return left


-- |Apply one parenthesised or square bracketed suffixes to the specified
-- stmtExpr.
stmtExprSuffix' :: StmtExpr -> Parser StmtExpr
stmtExprSuffix' left =
    (argumentList Paren >>= applyArguments left)
    <|> (Call (stmtExprPos left) [] "[]" ParamIn . (left:)
         <$> argumentList Bracket)


-- |Comma-separated, non-empty argument list, surrounded by the specified
-- bracket type.
argumentList :: BracketStyle -> Parser [StmtExpr]
argumentList Brace = shouldnt "brace-enclosed argument list"
argumentList bracket = betweenB bracket (stmtExpr `sepBy` comma)


-- |Supply arguments to function call we thought was something else.
applyArguments :: StmtExpr -> [StmtExpr] -> Parser StmtExpr
applyArguments stmtOrExpr args =
    case stmtOrExpr of
        call@Call{} ->
            return $ call {callArguments = callArguments call ++ args}
        other -> fail $ "unexpected argument list following expression "
                        ++ show other


-- |Complete parsing an stmtExpr of precedence no looser than specified, given
-- that we have already parsed the specified stmtExpr on the left.
-- XXX this doesn't handle non-associative operators correctly; it treats them
-- as right associative.
stmtExprRest :: Int -> StmtExpr -> Parser StmtExpr
stmtExprRest minPrec left =
    do -- A functional Pratt operator precedence parser
         -- parse an infix operator of at least the specified precedence
        (op,rightPrec) <- infixOp minPrec
        -- parse expression of high enough precedence to be the right argument
        right <- limitedStmtExpr rightPrec
        let pos = stmtExprPos left
        -- construct a call of the op with the left and right arguments, and
        -- treat that as the left argument of the rest of the expr
        stmtExprRest minPrec $ Call pos [] op ParamIn [left,right]
    <|> -- Otherwise try to parse a call with 1 un-parenthesised argument;
        -- failing that, the left context is the whole expression.
        case left of
            Call _ m n _ [] | minPrec <= lowestStmtPrecedence
                            || List.null m && prefixKeyword n ->
                (limitedStmtExpr lowestExprPrecedence
                    >>= applyArguments left . (:[])
                    >>= stmtExprRest minPrec)
                <|> return left
            _ -> return left


-- |Scan an infix operator of at least the specified left precedence, returning
-- the operator and its right precedence.
infixOp :: Int -> Parser (String,Int)
infixOp minPrec = takeToken test
  where
    test tok
      | lPrec > minPrec && isInfixOp tok = Just (name, prec)
      | otherwise                           = Nothing
        where name = tokenName tok
              (prec,assoc) = operatorAssociativity name
              lPrec = prec + if assoc == LeftAssociative  then 0 else 1
              rPrec = prec - if assoc /= RightAssociative then 0 else 1


-- |Parse a simple, StmtExpr, not involving any operators.
primaryStmtExpr :: Parser StmtExpr
primaryStmtExpr =
    parenthesisedExp
    <|> embracedStmtExp
    <|> foreignCall
    <|> forLoop
    <|> varOrCall
    <|> intConst
    <|> floatConst
    <|> charConst
    <|> stringConst
    <|> listExp
    <?> "simple expression"


parenthesisedExp :: Parser StmtExpr
parenthesisedExp = do
    pos <- tokenPosition <$> leftBracket Paren
    setStmtExprPos pos <$> stmtExpr <* rightBracket Paren


varOrCall :: Parser StmtExpr
varOrCall = do
    pos <- getPosition
    modVar <- moduleSpec
    return $ Call pos (init modVar) (last modVar) ParamIn []


-- | Parse a sequence of StmtExprs enclosed in braces.
embracedStmtExp :: Parser StmtExpr
embracedStmtExp = do
    pos <- tokenPosition <$> leftBracket Brace
    Call pos [] "{}" ParamIn
        <$> limitedStmtExpr lowestStmtSeqPrecedence `sepBy` comma
        <* rightBracket Brace


-- | Parse all expressions beginning with the terminal "[".
-- List -> '[' StmtExpr ListTail
-- Empty List -> '[' ']'
-- List Cons -> '[' '|' ']'
listExp :: Parser StmtExpr
listExp = do
    pos <- (tokenPosition <$> leftBracket Bracket) <?> "list"
    rightBracket Bracket $> Call pos [] "[]" ParamIn []
        <|> do
            head <- stmtExpr
            tail <- listTail
            return $ Call pos [] "[|]" ParamIn [head,tail]


-- | Parse the tail of a list.
-- ListTail -> ']' | ',' StmtExpr ListTail
listTail :: Parser StmtExpr
listTail = do
        pos <- tokenPosition <$> rightBracket Bracket
        return $ Call pos [] "[]" ParamIn []
    <|> do
        pos <- tokenPosition <$> comma
        head <- stmtExpr
        tail <- listTail
        return $ Call pos [] "[|]" ParamIn [head, tail]
    <|> symbol "|" *> stmtExpr <* rightBracket Bracket


-- |A foreign function or procedure call.
foreignCall :: Parser StmtExpr
foreignCall = do
    pos <- tokenPosition <$> ident "foreign"
    language <- identString
    flags <- modifierList
    fname <- identString
    Foreign pos language fname flags <$> argumentList Paren


-- |A for loop.
forLoop :: Parser StmtExpr
forLoop = do
    pos <- tokenPosition <$> ident "for"
    gen <- limitedStmtExpr lowestStmtSeqPrecedence
    body <- embracedStmtExp
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
lowestExprPrecedence :: Int
lowestExprPrecedence = 1


-- |Lowest (loosest) operator precedence of an individual statement
lowestStmtPrecedence :: Int
lowestStmtPrecedence = 0


-- |Lowest (loosest) operator precedence of a proc body
lowestStmtSeqPrecedence :: Int
lowestStmtSeqPrecedence = -4


-- |Lowest (loosest) operator precedence of a proc/function prototype
prototypePrecedence :: Int
prototypePrecedence = 10


-- |Prefix operator symbols; these all bind very tightly
prefixOp :: Parser Token
prefixOp = choice $ List.map symbol ["-", "~", "?", "!", "@", ":"]


-- |Apply the specified prefix op to the specified stmtExpr.  Fail if it should
-- be a syntax error.
applyPrefixOp :: Token -> StmtExpr -> Parser StmtExpr
applyPrefixOp tok stmtExpr = do
    let pos = tokenPosition tok
    case (tokenName tok, stmtExpr) of
        ("-", IntConst _ num) -> return $ IntConst pos (-num)
        ("-", FloatConst _ num) -> return $ FloatConst pos (-num)
        ("-", Call{}) -> return $ call1 pos "-" stmtExpr
        ("-", Foreign{}) -> return $ call1 pos "-" stmtExpr
        ("-", _) -> fail $ "cannot negate " ++ show stmtExpr
        ("~", IntConst _ num) -> return $ IntConst pos (complement num)
        ("~", Call{}) -> return $ call1 pos "~" stmtExpr
        ("~", Foreign{}) -> return $ call1 pos "~" stmtExpr
        ("~", _) -> fail $ "cannot negate " ++ show stmtExpr
        ("?", Call{callVariableFlow=ParamIn, callName="@", callModule=[], 
                   callArguments=[IntConst{}]})
          -> return $ setCallFlow ParamOut stmtExpr
        ("?", Call{callVariableFlow=ParamIn}) -> return $ setCallFlow ParamOut stmtExpr
        ("?", _) -> fail $ "unexpected " ++ show stmtExpr ++ " following '?'"
        ("!", Call{callVariableFlow=ParamIn}) -> return $ setCallFlow ParamInOut stmtExpr
        ("!", _) -> fail $ "unexpected " ++ show stmtExpr ++ " following '!'"
        ("@", arg@IntConst{}) -> return $ Call pos [] "@" ParamIn [arg]
        ("@", _) -> fail $ "unexpected " ++ show stmtExpr ++ " following '@'"
        (":", _) -> return $ Call pos [] ":" ParamIn [stmtExpr]
        -- ("@", _) -> fail $ "unexpected " ++ show stmtExpr ++ " following '@'"
        (_,_) -> shouldnt $ "Unknown prefix operator " ++ show tok
                            ++ " in applyPrefixOp"


-- |Unary call to the specified proc name with the specified argument.  The
-- default (empty) module and default (ParamIn) variable flow are used.
call1 :: SourcePos -> ProcName -> StmtExpr -> StmtExpr
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
prefixKeyword _     = False


-- | Test if operator name is for a separator operator.
separatorName ";"  = True
separatorName "\n" = True
separatorName _    = False


-- |Special default test for conditionals.
defaultGuard :: String -> Bool
defaultGuard "else"      = True
defaultGuard "otherwise" = True
defaultGuard _           = False


-----------------------------------------------------------------------------
-- Terminal helpers                                                        --
-----------------------------------------------------------------------------

-- | Tests an individual token.
takeToken :: (Token -> Maybe a) -> Parser a
takeToken = token show tokenPosition


-- | Parse a float literal token.
floatConst :: Parser StmtExpr
floatConst = takeToken test
    where
      test (TokFloat f p) = Just $ FloatConst p f
      test _              = Nothing


-- | Parse an integer literal token.
intConst :: Parser StmtExpr
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
charConst :: Parser StmtExpr
charConst = takeToken test
    where
      test (TokChar c p) = Just $ CharConst p c
      test _             = Nothing


-- | Parse a string literal token.
stringConst :: Parser StmtExpr
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
identifier :: Parser StmtExpr
identifier = takeToken test
  where
    test (TokIdent s p) = Just $ Call p [] s ParamIn []
    test _ = Nothing


identString :: Parser String
identString = takeToken test
  where
    test (TokIdent s _) = Just s
    test _              = Nothing


-- | Parse a type variable name
typeVarName :: Parser Ident
typeVarName = symbol "?" *> identString


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
                          <|> ident "terminal" $> Terminal)


parseWith :: (a -> Either (SourcePos,String) b) -> a -> Parser b
parseWith translator = either reportFailure return . translator


-- |Fail the parser with the provided error message and associated SourcePos
reportFailure :: (SourcePos,String) -> Parser a
reportFailure (pos, message) = setPosition pos >> parserFail message


-----------------------------------------------------------------------------
-- Translating StmtExpr to the correct output types                        --
-----------------------------------------------------------------------------

-- |Type alias for a translation function
type TranslateTo ty = StmtExpr -> Either (SourcePos,String) ty


-- |Convert a StmtExpr to a proc/func prototype and a return type (AnyType for a
-- proc declaration or a function with no return type specified).
stmtExprToPrototype :: TranslateTo (ProcProto, TypeSpec)
stmtExprToPrototype (Call _ [] ":" ParamIn [rawProto,rawTy]) = do
    returnType <- stmtExprToTypeSpec rawTy
    (proto,_)  <- stmtExprToPrototype rawProto
    return (proto,returnType)
stmtExprToPrototype (Call pos mod name ParamIn rawParams) =
    if List.null mod
    then do
        params <- mapM stmtExprToParam rawParams
        return (ProcProto name params Set.empty,AnyType)
    else Left (pos, "module not permitted in proc declaration " ++ show mod)
stmtExprToPrototype other =
    syntaxError (stmtExprPos other)
                $ "invalid proc/func prototype " ++ show other


-- |Convert a StmtExpr to a body, if possible, or give a syntax error if not.
stmtExprToBody :: TranslateTo [Placed Stmt]
stmtExprToBody (Call pos [] sep ParamIn [left,right])
  | separatorName sep = do
    left' <- stmtExprToBody left
    right' <- stmtExprToBody right
    return $ left' ++ right'
stmtExprToBody (Call pos [] "{}" ParamIn [body]) =
    stmtExprToBody body
stmtExprToBody other = (:[]) <$> stmtExprToStmt other


-- |Convert a StmtExpr to a Stmt, if possible, or give a syntax error if not.
stmtExprToStmt :: TranslateTo (Placed Stmt)
-- stmtExprToStmt (Call pos [] "if" ParamIn [conditional]) =
--     translateConditionalStmt conditional
stmtExprToStmt (Call pos [] "{}" ParamIn [body]) =
    stmtExprToStmt body
stmtExprToStmt (Call pos [] "if" ParamIn [conditional]) =
    stmtExprToStmt conditional
stmtExprToStmt (Call pos [] "do" ParamIn [body]) =
    (`Placed` pos) . flip Loop Nothing <$> stmtExprToBody body
stmtExprToStmt (Call pos [] "for" ParamIn [gen,body]) = do
    genStmts <- stmtExprToGenerators gen
    (`Placed` pos) . For genStmts <$> stmtExprToBody body
stmtExprToStmt (Call pos [] "use" ParamIn
                    [Call _ [] "in" ParamIn [ress,body]]) = do
    ress' <- translateResourceList ress
    body' <- stmtExprToBody body
    return $ Placed (UseResources ress' Nothing body') pos
stmtExprToStmt (Call pos [] "while" ParamIn [test]) = do
    t <- stmtExprToStmt test
    return $ Placed (Cond t [Unplaced Nop] [Unplaced Break] Nothing Nothing) pos
stmtExprToStmt (Call pos [] "until" ParamIn [test]) = do
    t <- stmtExprToStmt test
    return $ Placed (Cond t [Unplaced Break] [Unplaced Nop] Nothing Nothing) pos
stmtExprToStmt (Call pos [] "when" ParamIn [test]) = do
    t <- stmtExprToStmt test
    return $ Placed (Cond t [Unplaced Nop] [Unplaced Next] Nothing Nothing) pos
stmtExprToStmt (Call pos [] "unless" ParamIn [test]) = do
    t <- stmtExprToStmt test
    return $ Placed (Cond t [Unplaced Next] [Unplaced Nop] Nothing Nothing) pos
stmtExprToStmt (Call pos [] "pass" ParamIn []) = do
    return $ Placed Nop pos
stmtExprToStmt
        (Call pos [] "|" ParamIn
         [Call _ [] "::" ParamIn [test1,thn],
          Call _ [] "::" ParamIn [Call _ [] test2 ParamIn [],els]])
  | defaultGuard test2 = do
    test1' <- stmtExprToStmt test1
    thn' <- stmtExprToBody thn
    els' <- stmtExprToBody els
    return $ Placed (Cond test1' thn' els' Nothing Nothing) pos
stmtExprToStmt
        (Call _ [] "|" ParamIn [Call pos [] "::" ParamIn [test,body],rest]) = do
    test' <- stmtExprToStmt test
    body' <- stmtExprToBody body
    rest' <- stmtExprToBody rest
    return $ Placed (Cond test' body' rest' Nothing Nothing) pos
stmtExprToStmt (Call pos [] "|" ParamIn disjs) = do
    flip Placed pos . flip Or Nothing <$> mapM stmtExprToStmt disjs
stmtExprToStmt (Call pos [] "::" ParamIn [Call _ [] guard ParamIn [],body])
  | defaultGuard guard = do
    syntaxError pos  "'else' or 'otherwise' outside an 'if'"
stmtExprToStmt (Call pos [] "::" ParamIn [test,body]) = do
    test' <- stmtExprToStmt test
    body' <- stmtExprToBody body
    return $ Placed (Cond test' body' [Unplaced Nop] Nothing Nothing) pos
stmtExprToStmt (Call _ [] fn ParamIn [first,rest])
  | separatorName fn = do
    first' <- stmtExprToStmt first
    rest'  <- stmtExprToStmt rest
    return $ Unplaced $ And [first',rest']
stmtExprToStmt (Call pos mod fn ParamIn args)
    = (`Placed` pos) . ProcCall mod fn Nothing Det False
        <$> mapM stmtExprToExp args
stmtExprToStmt (Call pos mod fn ParamInOut args)
    = (`Placed` pos) . ProcCall mod fn Nothing Det True
        <$> mapM stmtExprToExp args
stmtExprToStmt (Call pos mod fn flow args) =
    syntaxError pos $ "invalid statement prefix: " ++ flowPrefix flow
stmtExprToStmt (Foreign pos lang inst flags args) =
    (`Placed` pos) . ForeignCall lang inst flags <$> mapM stmtExprToExp args
stmtExprToStmt other =
    syntaxError (stmtExprPos other) $ "invalid statement " ++ show other


stmtExprToGenerators :: TranslateTo [Generator]
stmtExprToGenerators (Call pos [] sep ParamIn [left,right])
  | separatorName sep = do
    left' <- stmtExprToGenerators left
    right' <- stmtExprToGenerators right
    return $ left' ++ right'
stmtExprToGenerators (Call pos [] "in" ParamIn [var,exp]) = do
    var' <- stmtExprToExp var
    exp' <- stmtExprToExp exp
    return [In var' exp']
stmtExprToGenerators other =
    syntaxError (stmtExprPos other) $ "invalid generator " ++ show other


-- |Convert a StmtExpr to an Exp, if possible, or give a syntax error if not.
stmtExprToExp :: TranslateTo (Placed Exp)
stmtExprToExp (Call pos [] ":" ParamIn [exp,ty]) = do
    exp' <- content <$> stmtExprToExp exp
    ty' <- stmtExprToTypeSpec ty
    case exp' of
        Typed exp'' ty'' (Just AnyType) -> -- already cast, but not typed
            return $ Placed (Typed exp'' ty'' $ Just ty') pos
        Typed exp'' _ _ -> -- already typed, whether casted or not
            syntaxError (stmtExprPos ty) $ "repeated type constraint" ++ show ty
        _ -> -- no cast, no type
            return $ Placed (Typed exp'  ty' Nothing) pos
stmtExprToExp (Call pos [] ":!" ParamIn [exp,ty]) = do
    exp' <- content <$> stmtExprToExp exp
    ty' <- stmtExprToTypeSpec ty
    case exp' of
        Typed exp'' inner Just{} ->
            syntaxError (stmtExprPos ty) $ "repeated cast " ++ show ty
        Typed exp'' inner Nothing ->
            return $ Placed (Typed exp'' ty' $ Just inner) pos
        _  ->
            return $ Placed (Typed exp'  ty' $ Just AnyType) pos
stmtExprToExp (Call pos [] "where" ParamIn [exp,body]) = do
    exp' <- stmtExprToExp exp
    body' <- stmtExprToBody body
    return $ Placed (Where body' exp') pos
stmtExprToExp (Call pos [] "let" ParamIn [Call _ [] "in" ParamIn [body,exp]]) =
  do
    exp' <- stmtExprToExp exp
    body' <- stmtExprToBody body
    return $ Placed (Where body' exp') pos
stmtExprToExp (Call pos [] "^" ParamIn [exp,op]) = do
    exp' <- stmtExprToExp exp
    op'  <- stmtExprToExp op
    case op' of
        Placed (Fncall mod fn args) _
            -> return $ Placed (Fncall mod fn (exp':args)) pos
        Placed (Var var ParamIn Ordinary) _
            -> return $ Placed (Fncall [] var [exp']) pos
        _ -> syntaxError pos "invalid second argument to '^'"
stmtExprToExp (Call pos [] "@" flow [exp]) = do
    exp' <- stmtExprToExp exp
    case content exp' of
        IntValue i | i > 0 -> return $ Placed (Var (show i) flow Hole) pos
        _ -> syntaxError pos "invalid expression following @"
stmtExprToExp (Call pos [] "if" ParamIn [conditional]) =
    translateConditionalExp conditional
stmtExprToExp call@(Call pos [] "{}" ParamIn statements) = do
    statements' <- stmtExprToBody call
    return $ Placed (Lambda statements') pos    
stmtExprToExp (Call pos [] sep ParamIn [])
  | separatorName sep =
    syntaxError pos "invalid separated expression"
stmtExprToExp (Call pos [] var flow []) = -- looks like a var; assume it is
    return $ Placed (Var var flow Ordinary) pos
stmtExprToExp (Call pos mod fn flow args) =
    (`Placed` pos) . Fncall mod fn <$> mapM stmtExprToExp args
stmtExprToExp (Foreign pos lang inst flags args) =
    (`Placed` pos) . ForeignFn lang inst flags <$> mapM stmtExprToExp args
stmtExprToExp (IntConst pos num) = Right $ Placed (IntValue num) pos
stmtExprToExp (FloatConst pos num) = Right $ Placed (FloatValue num) pos
stmtExprToExp (CharConst pos char) = Right $ Placed (CharValue char) pos
stmtExprToExp (StringConst pos str DoubleQuote)
    = return $ Placed (StringValue str WybeString) pos
stmtExprToExp (StringConst pos str (IdentQuote "c" DoubleQuote))
    = return $ Placed (StringValue str CString) pos
stmtExprToExp str@StringConst{stringPos=pos}
    = Left (pos, "invalid string literal " ++ show str)


-- |Translate an `if` expression into a Placed conditional Exp
translateConditionalExp :: TranslateTo (Placed Exp)
translateConditionalExp (Call _ [] "{}" ParamIn [body]) =
    translateConditionalExp' body
translateConditionalExp stmtExpr =
    syntaxError (stmtExprPos stmtExpr) "expecting '{'"

translateConditionalExp'
        (Call _ [] "|" ParamIn [Call pos [] "::" ParamIn [test,body],rest]) = do
    test' <- stmtExprToStmt test
    body' <- stmtExprToExp body
    rest' <- translateConditionalExp' rest
    return $ Placed (CondExp test' body' rest') pos
translateConditionalExp'
        (Call pos [] "::" ParamIn [Call _ [] guard ParamIn [],body])
    | defaultGuard guard = stmtExprToExp body
translateConditionalExp' stmtExpr =
    syntaxError (stmtExprPos stmtExpr)
          $ "missing 'else::' in if expression: " ++ show stmtExpr


-- |Convert a StmtExpr to a TypeSpec, or produce an error
stmtExprToTypeSpec :: TranslateTo TypeSpec
stmtExprToTypeSpec (Call _ [] ":" flow [Call _ [] nm ParamOut []]) = 
    return $ HigherOrderType [TypeFlow (TypeVariable nm) flow]
stmtExprToTypeSpec (Call _ [] ":" flow [Call _ m nm ParamIn args]) = 
    HigherOrderType . ((:[]) . flip TypeFlow flow) . TypeSpec m nm <$> mapM stmtExprToTypeSpec args
stmtExprToTypeSpec (Call _ [] ":" _ [Call _ [] "_" flow [],arg]) = 
    HigherOrderType . ((:[]) . flip TypeFlow flow) <$> stmtExprToTypeSpec arg
stmtExprToTypeSpec (Call _ [] name ParamOut []) = Right $ TypeVariable name
stmtExprToTypeSpec call@(Call pos mod name ParamIn params) = do
    specs <- mapM stmtExprToTypeSpec params
    if not (List.null params) && all isHigherOrder specs && name == "_"
    then return $ HigherOrderType $ concatMap higherTypeParams specs
    else if any isHigherOrder specs
    then syntaxError pos "invaid type specification"
    else return $ TypeSpec mod name specs
stmtExprToTypeSpec other =
    syntaxError (stmtExprPos other) $ "invalid type specification " ++ show other


-- | Translate a StmtExpr to a proc or func prototype (with empty resource list)
stmtExprToProto :: TranslateTo (Placed ProcProto)
stmtExprToProto (Call pos [] name ParamIn params) = do
    params' <- mapM stmtExprToParam params
    return $ Placed (ProcProto name params' Set.empty) pos
stmtExprToProto other =
    syntaxError (stmtExprPos other) $ "invalid prototype " ++ show other


-- | Translate a StmtExpr to a proc or func parameter
stmtExprToParam :: TranslateTo Param
stmtExprToParam (Call _ [] ":" ParamIn [Call _ [] name flow [],ty]) = do
    ty' <- stmtExprToTypeSpec ty
    return $ Param name ty' flow Ordinary
stmtExprToParam (Call pos [] name flow []) =
    return $ Param name AnyType flow Ordinary
stmtExprToParam other =
    syntaxError (stmtExprPos other) $ "invalid parameter " ++ show other


-- | Translate a StmtExpr to a ctor declaration
stmtExprToCtorDecl :: TranslateTo (Placed ProcProto)
stmtExprToCtorDecl (Call pos [] name ParamIn fields) = do
    fields' <- mapM stmtExprToCtorField fields
    return $ Placed (ProcProto name fields' Set.empty) pos
stmtExprToCtorDecl other =
    syntaxError (stmtExprPos other)
        $ "invalid constructor declaration " ++ show other


-- | Translate a StmtExpr to a ctor field
stmtExprToCtorField :: TranslateTo Param
stmtExprToCtorField (Call _ [] ":" ParamIn [Call _ [] name flow [],ty]) = do
    ty' <- stmtExprToTypeSpec ty
    return $ Param name ty' flow Ordinary
stmtExprToCtorField (Call pos mod name flow params) = do
    tyParams <- mapM stmtExprToTypeSpec params
    return $ Param "" (TypeSpec mod name tyParams) flow Ordinary
stmtExprToCtorField other =
    syntaxError (stmtExprPos other) $ "invalid constructor field " ++ show other


-- | Extract a list of resource names from a StmtExpr (from a "use" statement).
translateResourceList :: TranslateTo [ResourceSpec]
translateResourceList (Call _ [] "{}" ParamIn args) =
    concat <$> mapM translateResourceList args
translateResourceList (Call _ mod name ParamIn []) =
    return [ResourceSpec mod name]
translateResourceList other =
    syntaxError (stmtExprPos other) "expected resource spec"

-----------------------------------------------------------------------------
-- Data structures                                                         --
-----------------------------------------------------------------------------

-- |Representation of expressions and statements.
data StmtExpr
    -- |a proc or function call, or a variable reference.
    = Call {
        callPos::SourcePos,               -- ^Where the call appears
        callModule::ModSpec,              -- ^the specified module, or empty
        callName::ProcName,               -- ^the called proc or variable name
        callVariableFlow::FlowDirection,  -- ^variable flow direction or
                                          --  call resourcefulness
        callArguments::[StmtExpr]         -- ^the specified arguments
    }
    -- |a foreign call, either as an expression or statement.
    | Foreign {
        foreignPos::SourcePos,         -- ^Where the foreign call appears
        foreignLanguage::Ident,        -- ^the specified foreign language
        foreignInstruction::ProcName,  -- ^the specified instruction
        foreignFlags::[Ident],         -- ^the specified modifiers
        foreignArguments::[StmtExpr]   -- ^the specified arguments
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


instance Show StmtExpr where
    show (Call _ mod name flow args) =
        flowPrefix flow ++ maybeModPrefix mod ++ name ++ showArguments args
    show (Foreign _ lang instr flags args) =
        "foreign " ++ lang ++ " " ++ showFlags flags ++ instr
        ++ showArguments args
    show (IntConst _ int) = show int
    show (FloatConst _ float) = show float
    show (CharConst _ char) = show char
    show (StringConst _ string delim) = delimitString delim string


-- |The SourcePos of a StmtExpr.
stmtExprPos :: StmtExpr -> SourcePos
stmtExprPos Call{callPos=pos}            = pos
stmtExprPos Foreign{foreignPos=pos}      = pos
stmtExprPos IntConst{intPos=pos}         = pos
stmtExprPos FloatConst{floatPos=pos}     = pos
stmtExprPos CharConst{charPos=pos}       = pos
stmtExprPos StringConst{stringPos=pos}   = pos


-- |Return the specified StmtExpr with its position replaced.
setStmtExprPos :: SourcePos -> StmtExpr -> StmtExpr
setStmtExprPos pos term@Call{} = term {callPos = pos}
setStmtExprPos pos term@Foreign{} = term {foreignPos = pos}
setStmtExprPos pos term@IntConst{} = term {intPos = pos}
setStmtExprPos pos term@FloatConst{} = term {floatPos = pos}
setStmtExprPos pos term@CharConst{} = term {charPos = pos}
setStmtExprPos pos term@StringConst{} = term {stringPos = pos}


setCallFlow :: FlowDirection -> StmtExpr -> StmtExpr
setCallFlow flow stmtExpr =
    case stmtExpr of
        Call{} -> stmtExpr {callVariableFlow = flow}
        _ -> shouldnt $ "setCallFlow of non-Call " ++ show stmtExpr


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

test :: Int -> String -> StmtExpr
test prec input = do
    case parse (limitedStmtExpr prec <* eof) "<string>" (stringTokens input) of
        Left err -> StringConst (errorPos err) (show err) DoubleQuote
        Right is -> is

testParser :: Parser a -> String -> Either ParseError a
testParser parser input = parse (parser <* eof) "<string>" (stringTokens input)
