-- | Parser for Keel surface syntax (@.kl@ files), producing the surface program that
-- "Keel.Infer" completes. Grammar summary (spec/surface.md has the full description):
--
-- > [linear] data List a = Nil | Cons(a, Box (List a))
-- > codata Ord a { lt : a -> a -> Bool }
-- > effect MMIO { read : i64 => i64 ; write : W => Unit }
-- > bitdata LineStatus : u8 { ready @ 0 ; thr_empty @ 5 ; parity @ 1..2 }
-- > def map : forall a b 'e. (a ->{'e} b) -> List a ->{'e, Diverge} List b =
-- >   \f xs. case xs of { Nil -> Nil | Cons(x, rest) -> Cons(f x, box (map f (unbox rest))) }
-- > main = ...
module Keel.Parser (parseProgram, parseModule, parseLibrary) where

import Data.Char (isUpper)
import Data.Functor (($>))
import Data.Set qualified as S
import Keel.Syntax
import Text.Parsec hiding (lower, upper)
import Text.Parsec.String (Parser)
import Text.Parsec.Token qualified as Tok

-- | A single-file program: no imports, a @main@.
parseProgram :: FilePath -> String -> Either String Program
parseProgram path src = do
  Module imports decls main <- parseModule path src
  case (imports, main) of
    ((m, _) : _, _) -> Left (path ++ ": imports " ++ m ++ ": load it with keelc (the module loader)")
    (_, Nothing) -> Left (path ++ ": no main")
    ([], Just m) -> Right (Program (map snd decls) m)

-- | One source file of a multi-file program (see "Keel.Modules").
parseModule :: FilePath -> String -> Either String Module
parseModule path src = either (Left . show) Right (parse (whiteSpace *> moduleP <* eof) path src)

-- | Declarations without a @main@ (the prelude).
parseLibrary :: FilePath -> String -> Either String [Decl]
parseLibrary path src = either (Left . show) Right (parse (whiteSpace *> many decl <* eof) path src)

-- Lexer -------------------------------------------------------------------------------------

lexer :: Tok.TokenParser ()
lexer =
  Tok.makeTokenParser
    Tok.LanguageDef
      { Tok.commentStart = "{-"
      , Tok.commentEnd = "-}"
      , Tok.commentLine = "--"
      , Tok.nestedComments = True
      , Tok.identStart = letter <|> char '_'
      , Tok.identLetter = alphaNum <|> char '_'
      , Tok.opStart = oneOf "-+*=<&|:;.,\\%?>"
      , Tok.opLetter = oneOf "-+*=<>&|:%?"
      , Tok.reservedNames =
          [ "data", "linear", "codata", "effect", "def", "main", "forall", "let", "in", "var"
          , "if", "then", "else", "case", "of", "cocase", "handle", "with", "box", "unbox"
          , "true", "false", "mut", "Box", "Unit", "Bool", "Free", "Lin"
          , "bitdata", "land", "lor", "lxor", "lsl", "lsr", "as", "import", "private"
          ]
      , Tok.reservedOpNames = []
      , Tok.caseSensitive = True
      }

whiteSpace :: Parser ()
whiteSpace = Tok.whiteSpace lexer

reserved, op :: String -> Parser ()
reserved = Tok.reserved lexer
op name = Tok.lexeme lexer (try (string name >> notFollowedBy (oneOf "-+*=<>&|:%?")))

ident :: Parser String
ident = Tok.identifier lexer

-- | Names starting with a capital: types, constructors, effect labels.
upper :: Parser String
upper = try (do n <- ident; if capitalized n then pure n else unexpected ("lowercase name " ++ n))

lower :: Parser String
lower = try (do n <- ident; if capitalized n then unexpected ("capitalized name " ++ n) else pure n)

capitalized :: String -> Bool
capitalized (c : _) = isUpper c
capitalized [] = False

effVar :: Parser String
effVar = Tok.lexeme lexer (try (char '\'' >> ('\'' :) <$> many1 (alphaNum <|> char '_')))

parens, braces, brackets :: Parser a -> Parser a
parens = Tok.parens lexer
braces = Tok.braces lexer
brackets = Tok.brackets lexer

comma, semi :: Parser ()
comma = () <$ Tok.comma lexer
semi = () <$ Tok.semi lexer

-- | A hole for inference.
hole :: Ty
hole = TMeta (-1)

intTypes :: [(String, IntTy)]
intTypes = [("i8", i8), ("i16", i16), ("i32", i32), ("i64", i64), ("u8", u8), ("u16", u16), ("u32", u32), ("u64", u64)]

-- | @42@ (width inferred), @250u8@, @0x1000_0000@. Underscores separate digits. A negative
-- literal is @-@ before a number at the start of an operand (see 'appE'), so @n -1@ still
-- means @n - 1@.
number :: Parser Term
number = Tok.lexeme lexer $ try $ do
  n <- hex <|> decimal
  suffix <- optionMaybe (choice [try (string s <* notFollowedBy alphaNum) $> t | (s, t) <- intTypes])
  notFollowedBy alphaNum
  pure (maybe (NumLit Nothing n) (`IntLit` n) suffix)
  where
    hex = try (string "0x") >> digitsIn 16 hexDigit
    decimal = digitsIn 10 digit
    digitsIn base d = do
      ds <- (:) <$> d <*> many (d <|> (char '_' >> d))
      pure (foldl (\acc c -> acc * base + toInteger (digitValue c)) 0 ds)
    digitValue c
      | c >= 'a' = fromEnum c - fromEnum 'a' + 10
      | c >= 'A' = fromEnum c - fromEnum 'A' + 10
      | otherwise = fromEnum c - fromEnum '0'

negative :: Term -> Term
negative (NumLit t n) = NumLit t (negate n)
negative (IntLit t n) = IntLit t (negate n)
negative e = e

-- Declarations ------------------------------------------------------------------------------

-- | @import a.b@ lines, then declarations (optionally @private@), then an optional @main@.
moduleP :: Parser Module
moduleP = do
  imports <- many $ do
    pos <- getPosition
    reserved "import"
    name <- sepBy1 lower (op ".")
    pure (foldr1 (\a b -> a ++ "." ++ b) name, (sourceName pos, sourceLine pos, sourceColumn pos))
  decls <- many ((,) <$> option False (reserved "private" $> True) <*> decl)
  main <- optionMaybe (reserved "main" >> op "=" >> expr)
  pure (Module imports decls main)

decl :: Parser Decl
decl = dataDecl <|> codataDecl <|> effectDecl <|> bitdataDecl <|> defDecl
  where
    -- bitdata Name : u8 { field @ bit ; field @ lo..hi }
    bitdataDecl = do
      reserved "bitdata"
      name <- upper
      op ":"
      it <- choice [reserved' s $> i | (s, i) <- intTypes]
      Bitdata name it <$> braces (sepEndBy bitField semi)
    reserved' s = try (do n <- lower; if n == s then pure () else unexpected n)
    bitField = do
      f <- lower
      op "@"
      lo <- fromInteger <$> Tok.natural lexer
      hi <- option lo (op ".." >> fromInteger <$> Tok.natural lexer)
      pure (f, lo, hi - lo + 1)
    dataDecl = do
      lin <- option False (reserved "linear" $> True)
      reserved "data"
      name <- upper
      ps <- many lower
      op "="
      Data lin name ps <$> sepBy1 ctor (op "|")
    ctor = (,) <$> upper <*> option [] (parens (sepBy ty comma))
    codataDecl = do
      reserved "codata"
      name <- upper
      ps <- many lower
      Codata name ps <$> braces (sepEndBy ((,) <$> lower <* op ":" <*> ty) semi)
    effectDecl = do
      reserved "effect"
      name <- upper
      Effect name <$> braces (sepEndBy ((,,) <$> lower <* op ":" <*> ty <* op "=>" <*> ty) semi)
    defDecl = do
      reserved "def"
      name <- lower
      op ":"
      t <- ty
      op "="
      Def name t <$> expr

-- Types -----------------------------------------------------------------------------------

ty :: Parser Ty
ty = forallTy <|> arrowTy
  where
    forallTy = do
      reserved "forall"
      bs <- many1 binder
      op "."
      TForall [v | Left v <- bs] [e | Right e <- bs] <$> ty
    binder =
      (Right <$> effVar)
        <|> (Left . (,Lin) <$> lower)
        <|> parens (do v <- lower; op ":"; k <- (reserved "Free" $> Free) <|> (reserved "Lin" $> Lin); pure (Left (v, k)))

arrowTy :: Parser Ty
arrowTy = do
  p <- paramTy
  option p $ do
    arrow <- (op "->" $> TFun) <|> (op "-o" $> TLFun)
    e <- option S.empty (S.fromList <$> braces (sepBy (upper <|> effVar) comma))
    arrow p e <$> arrowTy

paramTy :: Parser Ty
paramTy = (op "&" >> ((reserved "mut" >> TMut <$> appTy) <|> (TRef <$> appTy))) <|> appTy

appTy :: Parser Ty
appTy =
  (reserved "Box" >> TBox <$> atomTy)
    <|> (TData <$> upper <*> many atomTy)
    <|> atomTy

atomTy :: Parser Ty
atomTy =
  (reserved "Bool" $> TBool)
    <|> (reserved "Unit" $> TUnit)
    <|> ((`TData` []) <$> upper)
    <|> (named <$> lower)
    <|> parens (do a <- ty; option a (comma >> TPair a <$> ty))
  where
    named n = maybe (TVar n) TInt (lookup n intTypes)

-- Expressions -----------------------------------------------------------------------------

-- | Sequencing binds loosest: @a; b; c@.
expr :: Parser Term
expr = foldr1 Seq <$> sepBy1 opExpr (op ";")

-- | Record where a term starts, for error messages. Whole expressions and applications are
-- marked, never a call's head or an argument atom, so the shapes later passes look for
-- (@App (Var f) a@, @Con c [] [x]@) stay intact.
located :: Parser Term -> Parser Term
located p = do
  pos <- getPosition
  At (sourceName pos, sourceLine pos, sourceColumn pos) <$> p

opExpr :: Parser Term
opExpr = located (lambda <|> letE <|> varE <|> ifE <|> handleE <|> assign <|> cmpE)
  where
    lambda = do
      _ <- Tok.symbol lexer "\\"
      ps <- many1 param
      op "."
      body <- expr
      pure (foldr (\(x, t) b -> Lam x t b) body ps)
    param =
      ((,hole) <$> lower)
        <|> (op "&" >> refParam)
        <|> parens (do (x, mk) <- (op "&" >> refName) <|> ((,id) <$> lower); op ":"; t <- ty; pure (x, mk t))
    refParam = do
      (x, mk) <- refName
      pure (x, mk hole)
    refName = (reserved "mut" >> (,TMut) <$> lower) <|> ((,TRef) <$> lower)
    letE = do
      reserved "let"
      bind <- (Left <$> parens ((,) <$> lower <* comma <*> lower)) <|> (Right <$> lower)
      op "="
      e <- expr
      reserved "in"
      body <- expr
      pure $ case bind of
        Left (x, y) -> LetPair x y e body
        Right x -> Let x e body
    varE = do
      reserved "var"
      x <- lower
      op "="
      e <- expr
      reserved "in"
      LetVar x e <$> expr
    ifE = do
      reserved "if"
      c <- expr
      reserved "then"
      a <- expr
      reserved "else"
      If c a <$> opExpr
    handleE = do
      reserved "handle"
      e <- expr
      reserved "with"
      l <- upper
      Handle l e <$> braces (sepBy1 ((,,) <$> lower <*> lower <* op "->" <*> expr) (op "|"))
    assign = try (do x <- lower; op ":="; Assign x <$> opExpr)

cmpE :: Parser Term
cmpE = do
  a <- addE
  option a $ do
    p <- (op "==" $> Eq) <|> (op "<" $> Lt)
    Prim p a <$> addE

addE, mulE :: Parser Term
addE = chainl1 mulE (arithOp [("+", Add), ("-", Sub)])
mulE = chainl1 convE (arithOp [("*", Mul)] <|> divOp <|> bitOp)

-- | @/@ and @%@: checked division and remainder (no wrapping or saturating forms).
divOp :: Parser (Term -> Term -> Term)
divOp = (op "/" $> Prim (Arith Checked Div)) <|> (op "%" $> Prim (Arith Checked Rem))

-- | @e as u8@: wrapping integer conversion, binding tighter than the operators.
convE :: Parser Term
convE = do
  e <- appE
  ts <- many (reserved "as" >> choice [try (do n <- lower; maybe (unexpected n) pure (lookup n intTypes))])
  pure (foldl (flip Convert) e ts)

-- | Bitwise operators, written as words (as in OCaml) since @&@ is a borrow.
bitOp :: Parser (Term -> Term -> Term)
bitOp = choice [reserved w $> Prim (Bits b) | (w, b) <- [("land", And), ("lor", Or), ("lxor", Xor), ("lsl", Shl), ("lsr", Shr)]]

-- | @+@ checked, @+%@ wrapping, @+|@ saturating, @+?@ returning Option (same for - and *).
arithOp :: [(String, ArithOp)] -> Parser (Term -> Term -> Term)
arithOp ops =
  choice
    [ op (sym ++ suffix) $> Prim (Arith ov a)
    | (sym, a) <- ops
    , (suffix, ov) <- [("%", Wrap), ("|", Saturate), ("?", Optional), ("", Checked)]
    ]

appE :: Parser Term
appE = located $ do
  h <-
    (reserved "box" >> Box <$> postfix)
      <|> (reserved "unbox" >> Unbox <$> postfix)
      <|> try (op "-" >> negative <$> number)
      <|> postfix
  args <- many arg
  pure (foldl App h args)
  where
    arg = borrow <|> try (parens borrow) <|> postfix
    borrow = op "&" >> ((reserved "mut" >> BorrowMut <$> lower) <|> (Borrow <$> lower))

-- | An atom with projections (@e.obs@) and explicit type arguments (@f[i64]@).
postfix :: Parser Term
postfix = do
  a <- atom
  ops <- many (projection <|> typeArgs)
  pure (foldl (flip ($)) a ops)
  where
    projection = try (op "." >> lower) >>= \o -> pure (`Proj` o)
    typeArgs = do
      ts <- brackets (sepBy ty comma)
      pure $ \t -> case t of
        Var f -> TyApp f ts []
        Con c [] as -> Con c ts as
        _ -> t

-- | @"text"@: a @List u8@ of the string's UTF-8 bytes (Haskell-style escapes).
stringLit :: Parser Term
stringLit = do
  s <- Tok.stringLiteral lexer
  pure (foldr (\b rest -> Con "Cons" [] [IntLit u8 b, Box rest]) (Con "Nil" [] []) (concatMap utf8 s))
  where
    utf8 c
      | n < 0x80 = [n]
      | n < 0x800 = [0xC0 + n `div` 64, 0x80 + n `mod` 64]
      | n < 0x10000 = [0xE0 + n `div` 4096, 0x80 + (n `div` 64) `mod` 64, 0x80 + n `mod` 64]
      | otherwise = [0xF0 + n `div` 262144, 0x80 + (n `div` 4096) `mod` 64, 0x80 + (n `div` 64) `mod` 64, 0x80 + n `mod` 64]
      where
        n = toInteger (fromEnum c)

atom :: Parser Term
atom =
  stringLit
    <|> number
    <|> (reserved "true" $> BoolLit True)
    <|> (reserved "false" $> BoolLit False)
    <|> try (parens (pure ()) $> UnitLit)
    <|> parens (do e <- expr; option e (comma >> Pair e <$> expr))
    <|> caseE
    <|> cocaseE
    <|> constructor
    <|> (Var <$> lower)
  where
    constructor = do
      c <- upper
      bitsLit c <|> do
        ts <- option [] (brackets (sepBy ty comma))
        Con c ts <$> option [] (parens (sepBy expr comma))
    -- Status { field = e, … }
    bitsLit c = BitsLit c <$> braces (sepBy ((,) <$> lower <* op "=" <*> expr) comma)
    caseE = do
      reserved "case"
      e <- expr
      reserved "of"
      Case e <$> braces (sepBy1 alt (op "|"))
    alt = do
      c <- upper
      xs <- option [] (parens (sepBy lower comma))
      op "->"
      b <- expr
      pure (c, xs, b)
    cocaseE = do
      reserved "cocase"
      d <- upper
      ts <- option [] (brackets (sepBy ty comma))
      Cocase d ts <$> braces (sepBy1 ((,) <$> lower <* op "->" <*> expr) (op "|"))
