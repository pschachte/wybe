--  File     : Scanner.hs
--  Author   : Peter Schachte
--  Purpose  : Lexical scanner for the Wybe language
--  Copyright: (c) 2010-2012 Peter Schachte.  All rights reserved.
--  License  : Licensed under terms of the MIT license.  See the file
--           : LICENSE in the root directory of this project.


module Scanner (Token(..), tokenPosition, floatValue, intValue, stringValue,
                charValue, identName, symbolName, tokenName, showPosition,
                StringDelim(..), BracketStyle(..), bracketString, fileTokens, tokenise,
                inputTokens, stringTokens, delimitString) where

import AST
import Util
import Data.Char
import Data.List
import Data.Tuple.Extra
import Data.Tuple.HT
import Text.ParserCombinators.Parsec.Pos

-- |The tokens of the wybe language, each carrying its source position.
data Token = TokFloat Double SourcePos          -- ^A floating point number
              | TokInt Integer SourcePos        -- ^An integer
              | TokString StringDelim String SourcePos
                                                -- ^A string with its delimiter
              | TokChar Char SourcePos          -- ^A character constant
              | TokIdent String SourcePos       -- ^An identifier
              | TokLBracket BracketStyle SourcePos
                                                -- ^Some kind of left bracket
              | TokRBracket BracketStyle SourcePos
                                                -- ^Some kind of right bracket
              | TokComma SourcePos              -- ^A comma
              | TokPeriod SourcePos             -- ^A period (full stop)
              | TokSymbol String SourcePos      -- ^A symbol made up of
                                                --  non-identifier chars
              | TokSeparator Bool SourcePos     -- ^A statement separator
                                                -- indicating whether explicit
              | TokError String SourcePos       -- ^A lexical error

-- |The different string delimiters.
data StringDelim = DoubleQuote
                 | BackQuote
                 | LongQuote String
                 | IdentQuote String StringDelim
               deriving (Eq, Ord)


instance Show Token where
    show (TokFloat n _)         = "floating point number " ++ show n
    show (TokInt n _)           = "integer " ++ show n
    show (TokString d s _)      = "literal string " ++ delimitString d s
    show (TokChar ch _)         = "literal character " ++ show ch
    show (TokIdent s _)         = "identifier " ++ s
    show (TokLBracket br _)     = "'" ++ bracketString True br  ++ "'"
    show (TokRBracket br _)     = "'" ++ bracketString False br ++ "'"
    show (TokComma _)           = "comma"
    show (TokPeriod _)          = "period"
    show (TokSymbol s _)        = "operator symbol " ++ s
    show (TokSeparator True _)  = "semicolon"
    show (TokSeparator False _) = "newline"
    show (TokError str _)       = str


-- |Returns the source position of a token.
tokenPosition :: Token -> SourcePos
tokenPosition (TokFloat _     pos) = pos
tokenPosition (TokInt   _     pos) = pos
tokenPosition (TokString _ _  pos) = pos
tokenPosition (TokChar _      pos) = pos
tokenPosition (TokIdent _     pos) = pos
tokenPosition (TokLBracket _  pos) = pos
tokenPosition (TokRBracket _  pos) = pos
tokenPosition (TokComma       pos) = pos
tokenPosition (TokPeriod      pos) = pos
tokenPosition (TokSymbol _    pos) = pos
tokenPosition (TokSeparator _ pos) = pos
tokenPosition (TokError _     pos) = pos

-- |Returns the value of a float token.
floatValue :: Token -> Double
floatValue (TokFloat float _) = float
floatValue _ = shouldnt "not a float"

-- |Returns the value of an int token.
intValue :: Token -> Integer
intValue (TokInt int _) = int
intValue _ = shouldnt "not an int"

-- |Returns the value of a string token.
stringValue :: Token -> String
stringValue (TokString _ string _) = string
stringValue _ = shouldnt "not a string"

-- |Returns the value of a character constant token.
charValue :: Token -> Char
charValue (TokChar char _) = char
charValue _ = shouldnt "not a char"

-- |Returns the name of an identifier token.
identName :: Token -> String
identName (TokIdent str _) = str
identName _ = shouldnt "not an ident"

-- |Returns the name of a symbol token.
symbolName :: Token -> String
symbolName (TokSymbol str _) = str
symbolName _ = shouldnt "not a symbol"


-- |Returns the text of the token.
tokenName :: Token -> String
tokenName (TokFloat n _)         = show n
tokenName (TokInt n _)           = show n
tokenName (TokString d s _)      = delimitString d s
tokenName (TokChar ch _)         = [ch]
tokenName (TokIdent s _)         = s
tokenName (TokLBracket br _)     = bracketString True br
tokenName (TokRBracket br _)     = bracketString False br
tokenName (TokComma _)           = ","
tokenName (TokPeriod _)          = "."
tokenName (TokSymbol s _)        = s
tokenName (TokSeparator True _)  = ";"
tokenName (TokSeparator False _) = "\n"
tokenName (TokError str _)       = "error: " ++ str


-- |How to display a source position.
showPosition :: SourcePos -> String
showPosition pos
  = sourceName pos ++ ":"
    ++ show (sourceLine pos) ++ ":"
    ++ show (sourceColumn pos)

-- |Wraps a string in delimiters
delimitString :: StringDelim -> String -> String
delimitString d s = delimStringStart d ++ tail (init $ show s)
                                       ++ delimStringEnd d


-- |Return the specified starting quote as a string.
delimStringStart :: StringDelim -> String
delimStringStart DoubleQuote      = "\""
delimStringStart BackQuote        = "`"
delimStringStart (LongQuote s)    = s
delimStringStart (IdentQuote i s) = i ++ delimStringStart s


-- |Return the specified ending quote as a string.
delimStringEnd :: StringDelim -> String
delimStringEnd DoubleQuote      = "\""
delimStringEnd BackQuote        = "`"
delimStringEnd (LongQuote s)    = s
delimStringEnd (IdentQuote _ s) = delimStringEnd s


-- |The different kinds of brackets.
data BracketStyle = Paren | Bracket | Brace
                  deriving (Eq)

-- |Return the specified bracket as a string, where the Bool specifies whether
-- it should be a left bracket.
bracketString :: Bool -> BracketStyle -> String
bracketString True  Paren   = "("
bracketString True  Bracket = "["
bracketString True  Brace   = "{"
bracketString False Paren   = ")"
bracketString False Bracket = "]"
bracketString False Brace   = "}"


-- |The contents of a file as a list of tokens.
fileTokens :: FilePath -> IO [Token]
fileTokens filename =
    pruneSeparators . tokenise (initialPos filename) <$> readFile filename


-- |The contents of stdin as a list of tokens.
inputTokens :: IO [Token]
inputTokens =
    pruneSeparators . tokenise (initialPos "<stdin>") <$> getContents


-- |The contents of one line of stdin as a list of tokens.
stringTokens :: String -> [Token]
stringTokens = pruneSeparators . tokenise (initialPos "<string>")


-- |Prune out unneeded implicit TokSeparators, which indicate newlines.  The
-- unneeded ones are those that couldn't separate two statements or items.  We
-- eliminate them when the previous token was a symbol, comma, left parenthesis,
-- bracket, or brace, or another separator, or when the following
-- token is a symbol, comma, right parenthesis, bracket, or brace, left brace,
-- or explict separator.  We also eliminate implicit separators that begin or
-- end a file.  All explicit TokSeparators (semicolons) are kept.
pruneSeparators :: [Token] -> [Token]
pruneSeparators [] = []
pruneSeparators (TokSeparator False _:rest) = pruneSeparators rest
pruneSeparators (tok:rest) = tok:pruneSeparators' rest tok

pruneSeparators' :: [Token] -> Token -> [Token]
pruneSeparators' [] _ = []
pruneSeparators' (sep@(TokSeparator False _):rest) prev
    | omitAfter prev || omitBefore rest = pruneSeparators' rest prev
    | otherwise                         = sep : pruneSeparators' rest sep
pruneSeparators' (tok:rest) _           = tok : pruneSeparators' rest tok


-- |Test whether an implicit separator following the specified token should be
-- pruned.
omitAfter :: Token -> Bool
omitAfter (TokSymbol s _) = s /= "@"
omitAfter TokComma{}      = True
omitAfter TokLBracket{}   = True
omitAfter TokSeparator{}  = True
omitAfter (TokIdent s _)  = nonendingKeyword s
omitAfter _               = False


-- |Test whether an implicit separator preceding the specified list of tokens
-- should be pruned.
omitBefore :: [Token] -> Bool
omitBefore []                       = True
omitBefore (TokSymbol s _:_)        = not $ statementStartSymbol s
omitBefore (TokComma{}:_)           = True
omitBefore (TokRBracket{}:_)        = True
omitBefore (TokIdent s _:_)         = nonstartingKeyword s
omitBefore (TokSeparator{}:_)       = True
omitBefore _                        = False


-- |Convert a sequence of characters to a sequence of tokens.
tokenise :: SourcePos -> String -> [Token]
tokenise _ [] = []
tokenise pos (c:str) =
    let (toks,pos',str') = tokenisePart pos c str
    in  toks ++ tokenise pos' str'


-- |The Scanner works by producing a list of tokens, the characters not yet
-- parsed, and the source position of the unparsed text.
type PartialTokenisation = ([Token],SourcePos,String)


-- |Wrap up a partial tokenisation with a token error. Currently the parser
-- gives up after an erroneous token, so there's not much point trying to carry
-- on.
terminalTokError :: String -> SourcePos -> PartialTokenisation
terminalTokError msg pos = ([TokError msg pos], pos, [])


-- |Partially convert a sequence of characters to a sequence of tokens,
-- giving some tokens, the remaining input characters, and the source position
-- of the start of the remaining characters.
tokenisePart :: SourcePos -> Char -> String -> PartialTokenisation
tokenisePart pos c cs
  | c == '\n' = singleCharTok c cs pos $ TokSeparator False pos
  | isSpace c || isControl c = ([], updatePosChar pos c, cs)
  | isDigit c = scanNumberToken pos (c:cs)
  | isIdentChar c =
    case span isIdentChar (c:cs) of
      (v@"c", '\"':cs') -> tokeniseString (IdentQuote "c" DoubleQuote) pos cs'
      (name, rest) -> multiCharTok name rest (TokIdent name pos) pos
  | otherwise = case c of
                    ',' -> specialToken ',' cs pos $ TokComma pos
                    '.' -> specialToken '.' cs pos $ TokPeriod pos
                    ';' -> specialToken ';' cs pos $ TokSeparator True pos
                    ':' -> specialToken ':' cs pos $ TokSymbol ":" pos
                    '(' -> singleCharTok c cs pos $ TokLBracket Paren pos
                    '[' -> singleCharTok c cs pos $ TokLBracket Bracket pos
                    '{' -> singleCharTok c cs pos $ TokLBracket Brace pos
                    ')' -> singleCharTok c cs pos $ TokRBracket Paren pos
                    ']' -> singleCharTok c cs pos $ TokRBracket Bracket pos
                    '}' -> singleCharTok c cs pos $ TokRBracket Brace pos
                    '?' -> singleCharTok c cs pos $ TokSymbol "?" pos
                    '!' -> singleCharTok c cs pos $ TokSymbol "!" pos
                    '@' -> singleCharTok c cs pos $ TokSymbol "@" pos
                    '\'' -> tokeniseChar pos cs
                    '\"' -> tokeniseString DoubleQuote pos cs
                    -- backquote makes anything an identifier
                    '`' -> tokeniseBackquote cs pos
                    '#' -> let  (target,trim,terminate) = case cs of
                                    ('|':_) -> ("|#","|#",True)
                                    _       -> ("\n","",False)
                                (comment,rest) =
                                    breakList (target `isPrefixOf`) cs
                                pos' = updatePosString pos (c:comment++trim)
                            in if terminate && null rest
                               then terminalTokError "unterminated comment" pos'
                               else ([], pos', drop (length trim) rest)
                    _   -> tokeniseSymbol pos (c:cs)


-- | Splits a list into the initial part whose prefix does not satisfy the
-- predicate and the first suffix that does.  Like the List.break function,
-- except that the predicate is applied to whole tails of the input list rather
-- than individual elements.
breakList :: ([a] -> Bool) -> [a] -> ([a],[a])
breakList pred [] = ([],[])
breakList pred lst@(h:t)
  | pred lst  = ([],lst)
  | otherwise = mapFst (h:) $ breakList pred t


-- |Handle a single character token and tokenize the rest of the input.
singleCharTok :: Char -> String -> SourcePos -> Token -> PartialTokenisation
singleCharTok c cs pos tok = ([tok], updatePosChar pos c, cs)

-- |Handle a symbol token and tokenize the rest of the input.
tokeniseSymbol :: SourcePos -> String -> PartialTokenisation
tokeniseSymbol pos (c:cs) =
  let (sym,rest) = span (isSymbolContinuation c) cs
      pos' = updatePosString pos sym
  in  multiCharTok (c:sym) rest (TokSymbol (c:sym) pos) pos'
tokeniseSymbol _ [] = shouldnt "empty symbol does not exist"


-- |Handle a token that is treated specially if not followed by symbol
-- characters, and tokenize the rest of the input.  Special characters are
-- comma, period, and semicolon.
specialToken :: Char -> String -> SourcePos -> Token -> PartialTokenisation
specialToken ch rest pos singleTok =
    case span (isSymbolContinuation ch) rest of
        ([],_) -> ([singleTok], updatePosChar pos ch, rest)
        (tokRest,rest') ->
            let sym = ch:tokRest
            in ([TokSymbol sym pos], updatePosString pos sym, rest')


-- |Recognise a character that cannot begin an expression, and therefore can
-- follow a comma in a symbol.
isSymbolContinuation :: Char -> Char -> Bool
isSymbolContinuation startChar ',' = True
isSymbolContinuation startChar ';' = True
isSymbolContinuation startChar '.' = True
isSymbolContinuation startChar ':' = True
isSymbolContinuation startChar '!' = startChar == ':'
isSymbolContinuation startChar '$' = True
isSymbolContinuation startChar '%' = True
isSymbolContinuation startChar '^' = True
isSymbolContinuation startChar '~' = True
isSymbolContinuation startChar '&' = True
isSymbolContinuation startChar '|' = True
isSymbolContinuation startChar '+' = True
isSymbolContinuation startChar '-' = True
isSymbolContinuation startChar '*' = True
isSymbolContinuation startChar '/' = True
isSymbolContinuation startChar '=' = True
isSymbolContinuation startChar '<' = True
isSymbolContinuation startChar '>' = True
isSymbolContinuation startChar '\\' = True
isSymbolContinuation startChar _   = False


-- |Handle a mult-character token and tokenize the rest of the input.
multiCharTok :: String -> String -> Token -> SourcePos -> PartialTokenisation
multiCharTok str cs tok pos = ([tok], updatePosString pos str, cs)

-- |Handle a character constant token and tokenize the rest of the input.
tokeniseChar :: SourcePos -> String -> PartialTokenisation
tokeniseChar pos ('\\':rest) =
    case scanCharEscape (updatePosChar pos '\\') rest of
        Just (ch,pos'','\'':cs') ->
             ([TokChar ch pos], pos'', cs')
        _ -> ([TokError "invalid character escape" pos]
                , updatePosChar pos '\'', rest)
tokeniseChar pos (c:'\'':cs) =
  ([TokChar c pos]
   ,updatePosChar (updatePosChar (updatePosChar pos '\'') c) '\'', cs)
tokeniseChar pos chars =
    ([TokError ("character constant beginning '" ++ front ++ "'...") pos]
    , updatePosString pos ('\'':front), back)
    where (front,back) = splitAt 2 chars

-- |Tokenise a delimited string and tokenize the rest of the input..
tokeniseString :: StringDelim -> SourcePos -> String -> PartialTokenisation
tokeniseString delim pos cs =
    case break (`elem` [termchar,'\\','$']) cs of
        (_,[]) -> tokErr
        (front,'\\':cs) ->
            let pos' = updatePosChar (updatePosString pos front) '\\'
            in case scanCharEscape pos' cs of
                Just (ch,pos'',cs') ->
                    case tokeniseString delim pos'' cs' of
                        (TokString d s p:rest, pos''', cs'') ->
                            (TokString d (front++(ch:s)) p:rest, pos''', cs'')
                        _ -> shouldnt "tokeniseString didn't return a string"
                Nothing -> tokErr
        ("",'$':cs) ->
            scanInterpolation cs delim $ updatePosChar pos '$'
        (front,'$':cs) ->
            let pos' = updatePosString pos front
            in mapFst3 ([TokString delim front pos, TokSymbol ",," pos']++)
               $ scanInterpolation cs delim (updatePosChar pos' '$')
        (front,t:cs) | t == termchar ->
            let pos' = updatePosChar (updatePosString pos front) t
            in ([TokString delim front pos], pos', cs)
        (front,rest) -> shouldnt "break broke in tokeniseString"
  where termchar = delimChar delim
        tokErr = terminalTokError "unterminated string" pos


-- |Scan a string interpolation followed by the rest of the string.  cs begins
-- with the first character after the '$'.
scanInterpolation :: String -> StringDelim -> SourcePos -> PartialTokenisation
scanInterpolation cs delim pos =
    case span isIdentChar cs of
        ("",'(':c:cs') ->
            mapFst3 ([TokIdent "fmt" pos, TokLBracket Paren pos]++)
            $ scanExprInterpolation 1 c cs' delim $ updatePosChar pos '('
        ("",cs) ->
            mapFst3
            (TokError "invalid string interpolation" pos:)
            $ tokeniseString delim pos cs
        (name,t:cs) | t == termchar ->
            let pos' = updatePosChar (updatePosString pos name) t
            in ([TokIdent "fmt" pos
                 , TokLBracket Paren pos
                 , TokIdent name pos
                 , TokRBracket Paren pos]
                , pos', cs)
        (name, rest) ->
            let pos' = updatePosString pos name
            in mapFst3
               ([TokIdent "fmt" pos
                , TokLBracket Paren pos
                , TokIdent name pos
                , TokRBracket Paren pos
                , TokSymbol ",," pos']++)
               $ tokeniseString delim pos' rest
  where termchar = delimChar delim


-- |Scan a string interpolation of the form $(...), followed by the rest of the
-- string.  cs begins with the first character after the "$("".  The provided
-- depth indicates the current parenthesis nesting depth.  We scan until the
-- nesting depth reaches 0, meaning we've reached the end of the opening "$(".
-- After that, we scan the rest of the string.
scanExprInterpolation :: Int -> Char -> String -> StringDelim -> SourcePos
                      -> PartialTokenisation
scanExprInterpolation 0 c cs delim pos
  | c == delimChar delim = ([], updatePosChar pos c, cs)
scanExprInterpolation 0 c cs delim pos =
    mapFst3 ([TokSymbol ",," pos]++) $ tokeniseString delim pos (c:cs)
scanExprInterpolation depth c cs delim pos =
    let (toks, pos', cs') = tokenisePart pos c cs
        depth' = foldr ((+) . tokenNesting) depth toks
    in  case cs' of
        [] -> terminalTokError "unterminated string" pos'
        (c'':cs'') ->
            mapFst3 (toks++)
            $ scanExprInterpolation depth' c'' cs'' delim pos'


-- |Return the change the token makes to the expression nesting depth.  This
-- only considers parentheses to change the nesting depth.
tokenNesting :: Token -> Int
tokenNesting (TokLBracket Paren _) = 1
tokenNesting (TokRBracket Paren _) = (-1)
tokenNesting _ = 0

-- |Scan a character escape sequence following a backslash character, returning
-- Maybe a triple of the single escaped character, the position of the following
-- character, and the remaining characters.  Returns Nothing for a syntax error.
-- XXX doesn't currently support unicode escapes
scanCharEscape :: SourcePos -> String -> Maybe (Char,SourcePos,String)
scanCharEscape pos "" = Nothing
scanCharEscape pos (ch:rest) =
    case ch of
        '0' -> Just ('\x00',nextPos,rest) -- null character
        'a' -> Just ('\a',nextPos,rest)
        'b' -> Just ('\b',nextPos,rest)
        'e' -> Just ('\x1b',nextPos,rest) -- escape character
        'f' -> Just ('\f',nextPos,rest)
        'n' -> Just ('\n',nextPos,rest)
        'r' -> Just ('\r',nextPos,rest)
        't' -> Just ('\t',nextPos,rest)
        'v' -> Just ('\v',nextPos,rest)
        x | x == 'x' || x == 'X' -> case rest of
            (c1:c2:rest') | isHexDigit c1 && isHexDigit  c2 ->
                Just (toEnum (16*digitToInt c1 + digitToInt c2),
                      updatePosChar (updatePosChar nextPos c1) c2,
                      rest')
            _ -> Nothing
        _ -> Just (ch,nextPos,rest)
    where nextPos = updatePosChar pos ch


-- |Is the specified char the expected final delimiter?
delimChar :: StringDelim -> Char
delimChar DoubleQuote = '\"'
delimChar (IdentQuote _ DoubleQuote) = '\"'
delimChar _ = shouldnt "not a delimiter character"

-- |Recognise an escaped character constant.
-- XXX doesn't currently support unicode escapes
escapedChar :: Char -> Char
escapedChar '0' = '\0'
escapedChar 'a' = '\a'
escapedChar 'b' = '\b'
escapedChar 'f' = '\f'
escapedChar 'n' = '\n'
escapedChar 'r' = '\r'
escapedChar 't' = '\t'
escapedChar 'v' = '\v'
escapedChar c = c

-- |Scan a number token and the rest of the input.  Handles decimal and hex
--  ints, floats with decimal point and/or e notation, and ignores embedded
--  underscores in integers. Doesn't handle negative numbers (these are handled by the parser).
scanNumberToken :: SourcePos -> [Char] -> PartialTokenisation
scanNumberToken pos cs =
    let (num0,rest0) = grabNumberChars False cs
        num = map toLower $ filter (/='_') num0
        (num',rest) = case (last num,rest0) of
          -- Handle negative exponents in scientific notation
          ('e','-':remains) -> let (negexp,remains') = span isDigit remains
                               in (num++'-':negexp, remains')
          _ -> (num, rest0)
        pos' = foldl updatePosChar pos num
    in ([case num' of
          '0':'x':hexDigits
            -> parseInteger 16 hexDigits pos
          '0':'b':binaryDigits
            -> parseInteger 2 binaryDigits pos
          '0':d:octal | isOctDigit d
            -> parseInteger 8 num' pos
          _ -> let (numPart,expPart) = span (/='e') num'
                   (wholePart,fracPart) = span (/='.') numPart
                   intTok = parseInteger 10 wholePart pos
                   errFloat = TokError ("invalid float '" ++ num' ++ "'") pos
               in case (intTok,expPart,fracPart) of
                    (TokInt int _, [], [])
                      -> intTok
                    (TokError _ _, _, _)
                      -> intTok
                    (_, "e", _)  -> errFloat
                    (_, "e-", _) -> errFloat
                    (_, 'e':'-':expDigits, _)
                      | not (all isDigit expDigits) -> errFloat
                    (_, 'e':digit1:expDigits, _)
                      | not (digit1 == '-' || isDigit digit1)
                        || not (all isDigit expDigits) -> errFloat
                    (_, _, ".")  -> errFloat
                    (_, _, '.':fracDigits)
                      | not (all isDigit fracDigits) -> errFloat
                    (TokInt intPart _, _, _) ->
                      let fracDigits =
                            if null fracPart then [] else tail fracPart
                          frac =
                            foldr
                            (\c f -> (f + fromIntegral (digitToInt c)) / 10.0)
                            0
                            fracDigits
                          (expDigits,expMult) =
                            case expPart of
                              []             -> ([],1)
                              ('e':'-':rest) -> (rest,-1)
                              ('e':rest)     -> (rest,1)
                              _ -> shouldnt "exponent must begin with e"
                          exponent =
                            foldl (\e c -> e * 10 + digitToInt c) 0 expDigits
                          multiplier = 10.0 ** fromIntegral (expMult * exponent)
                          value = (fromIntegral intPart + frac) * multiplier
                      in TokFloat value pos
                    (tok, _, _) -> shouldnt $ "unexpected token "
                                            ++ show tok
                                            ++ " when parsing a number "],
        pos', rest)


grabNumberChars :: Bool -> [Char] -> ([Char],[Char])
grabNumberChars seenPoint (c:cs)
 |  isIdentChar c = mapFst (c:) $ grabNumberChars seenPoint cs
grabNumberChars False ('.':c:cs)
 |  isDigit c = mapFst (('.':) . (c:)) $ grabNumberChars True cs
grabNumberChars _ cs = ([], cs)


-- |Convert the string to a non-negative integer in the specified radix.  The
-- string has already been vetted to contain only alphanumeric characters.  This
-- handles radices up to 36.
parseInteger :: Integer -> [Char] -> SourcePos -> Token
parseInteger radix str pos =
    if all (<radix) charValues
    then TokInt (foldl (\num val -> num * radix + val) 0 charValues) pos
    else TokError ("invalid integer '" ++ str ++ "'") pos
  where charValues = map alNumToInteger str


-- | Tokenise a symbol beginning with a backquote, which we've already scanned,
-- followed by the rest of the input.  In case of an invalid backquoted symbol,
-- we give up on tokenising the rest of the file.  Currently the parser gives up
-- after an erroneous token, so there's not much point trying to carry on.
tokeniseBackquote :: String -> SourcePos -> PartialTokenisation
tokeniseBackquote cs pos =
    let pos'  = updatePosChar pos '`'  -- count the opening `
        pos'' = updatePosChar pos' '`' -- pre-count the closing `
    in case break ((=='`') ||| (<' ') ||| (=='#')) cs of
        ([],_)           -> terminalTokError "empty backquoted symbol" pos
        (_,[])           -> terminalTokError "unclosed backquote" pos
        (name,'`':rest)  -> multiCharTok name rest (TokIdent name pos) pos''
        (name,'\n':rest) -> terminalTokError "multiline backquoted symbol" pos
        (name,'#':rest)  ->
            terminalTokError "hash character (#) in backquoted symbol" pos
        (name,_:rest)    ->
            terminalTokError "control character in a backquoted symbol" pos


-- |Returns the integer value of the specified char which is either a digit or
-- a lower case letter.
alNumToInteger :: Char -> Integer
alNumToInteger ch
  | isDigit ch = fromIntegral $ digitToInt ch
  | otherwise  = 10 + fromIntegral (fromEnum ch - fromEnum 'a')


-- |Is this a character that can appear in an identifier?
isIdentChar :: Char -> Bool
isIdentChar ch = isAlphaNum ch || ch == '_'

-- |Is this character part of a single (not necessarily valid) number token,
-- following a digit character?  This means any alphanumeric character or a
-- decimal point.
isNumberChar :: Char -> Bool
isNumberChar ch = isIdentChar ch || ch == '.'


-- |Keywords that can appear in the middle of a statement or declaration.
-- Newlines immediately before or after these words should not be taken as
-- separators.
nonstartingKeyword :: Ident -> Bool
nonstartingKeyword "in"    = True
-- nonstartingKeyword "is"    = True
nonstartingKeyword "where" = True
nonstartingKeyword _       = False


-- |Keywords that can appear in the middle of a statement or declaration.
-- Newlines immediately before or after these words should not be taken as
-- separators.
nonendingKeyword :: Ident -> Bool
nonendingKeyword "in"           = True
nonendingKeyword "is"           = True
nonendingKeyword "where"        = True
nonendingKeyword "pub"          = True
nonendingKeyword "def"          = True
nonendingKeyword "type"         = True
nonendingKeyword "constructor"  = True
nonendingKeyword "constructors" = True
nonendingKeyword _              = False


-- |Prefix operator symbols that could begin a statement.
statementStartSymbol :: String -> Bool
statementStartSymbol "!" = True
statementStartSymbol "?" = True
statementStartSymbol "~" = True
statementStartSymbol _   = False
