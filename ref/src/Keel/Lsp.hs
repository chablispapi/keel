-- | The language server (M5): @keelc lsp@ speaks LSP over stdin/stdout. It reports parse,
-- module and type errors as diagnostics while you type (unsaved buffers are read instead of the
-- files on disk), hover shows the declared type of a top-level name, and go-to-definition
-- jumps to its declaration.
--
-- A file inside a project (a @keel.project@ in it or a parent directory) is checked as part of
-- the project, from its entry file; any other file is checked on its own.
--
-- ponytail: hover covers top-level names only (no types of locals): that needs inferred types
-- per node.
module Keel.Lsp (serve, diagnose, hover, definition, Diag (..), Json (..), parseJson, renderJson) where

import Control.Exception (SomeException, evaluate)
import Control.Exception qualified as E
import Control.Monad (forM_, unless)
import Data.ByteString qualified as B
import Data.ByteString.Char8 qualified as BC
import Data.Char (chr, isAlphaNum, isDigit, isSpace, ord)
import Data.IORef
import Data.List (isPrefixOf)
import Data.Maybe (listToMaybe)
import Data.Set qualified as S
import Data.Map.Strict qualified as M
import Data.Text qualified as T
import Data.Text.Encoding qualified as TE
import Keel.Check (TypeError (..))
import Keel.Infer (inferProgram)
import Keel.Modules (importPath, loadModulesWith)
import Keel.Parser (parseModule)
import Keel.Mono (compile)
import Keel.Syntax
import Numeric (readHex, showHex)
import System.Directory (doesFileExist)
import System.FilePath (normalise, takeDirectory, (</>))
import System.IO
import Text.Parsec hiding (State)
import Text.Parsec.String (Parser)

-- JSON ---------------------------------------------------------------------------------------

data Json = JNull | JBool Bool | JNum Double | JStr String | JArr [Json] | JObj [(String, Json)]
  deriving (Eq, Show)

parseJson :: String -> Maybe Json
parseJson = either (const Nothing) Just . parse (ws *> value <* eof) ""
  where
    value :: Parser Json
    value = (obj <|> arr <|> JStr <$> str <|> num <|> lit "null" JNull <|> lit "true" (JBool True) <|> lit "false" (JBool False)) <* ws
    lit s v = v <$ try (string s)
    obj = JObj <$> (char '{' *> ws *> sepBy ((,) <$> (str <* ws <* char ':' <* ws) <*> value) (char ',' *> ws) <* char '}')
    arr = JArr <$> (char '[' *> ws *> sepBy value (char ',' *> ws) <* char ']')
    num = do
      s <- many1 (satisfy (\c -> isDigit c || c `elem` "+-.eE"))
      pure (JNum (read s))
    str = char '"' *> manyTill ch (char '"') <* ws
    ch = (char '\\' *> esc) <|> anyChar
    esc =
      choice
        [ '"' <$ char '"', '\\' <$ char '\\', '/' <$ char '/', '\b' <$ char 'b', '\f' <$ char 'f'
        , '\n' <$ char 'n', '\r' <$ char 'r', '\t' <$ char 't'
        , char 'u' *> (hex4 >>= surrogate)
        ]
    hex4 = maybe 0 fst . listToMaybe . readHex <$> count 4 hexDigit
    surrogate h
      | h >= 0xD800 && h < 0xDC00 = do
          l <- string "\\u" *> hex4
          pure (chr (0x10000 + (h - 0xD800) * 0x400 + (l - 0xDC00)))
      | otherwise = pure (chr h)
    ws = skipMany (satisfy isSpace)

renderJson :: Json -> String
renderJson j = case j of
  JNull -> "null"
  JBool b -> if b then "true" else "false"
  JNum n -> if n == fromInteger (round n) then show (round n :: Integer) else show n
  JStr s -> show' s
  JArr xs -> "[" ++ commas (map renderJson xs) ++ "]"
  JObj kvs -> "{" ++ commas [show' k ++ ":" ++ renderJson v | (k, v) <- kvs] ++ "}"
  where
    commas = foldr1' (\a b -> a ++ "," ++ b)
    foldr1' f xs = if null xs then "" else foldr1 f xs
    show' s = "\"" ++ concatMap esc s ++ "\""
    esc c
      | c == '"' = "\\\""
      | c == '\\' = "\\\\"
      | c == '\n' = "\\n"
      | ord c < 0x20 = "\\u" ++ replicate (4 - length (showHex (ord c) "")) '0' ++ showHex (ord c) ""
      | otherwise = [c]

field :: String -> Json -> Maybe Json
field k (JObj kvs) = lookup k kvs
field _ _ = Nothing

path' :: [String] -> Json -> Maybe Json
path' ks j = foldl (\m k -> m >>= field k) (Just j) ks

-- Transport ----------------------------------------------------------------------------------

-- | Read one @Content-Length@-framed message.
readMessage :: Handle -> IO (Maybe Json)
readMessage h = do
  headers <- readHeaders []
  case [read (dropWhile isSpace v) :: Int | (k, v) <- headers, k == "content-length"] of
    n : _ -> parseJson . T.unpack . TE.decodeUtf8Lenient <$> B.hGet h n
    [] -> pure Nothing
  where
    readHeaders acc = do
      atEnd <- hIsEOF h
      if atEnd
        then pure acc
        else do
          l <- filter (/= '\r') . BC.unpack <$> BC.hGetLine h
          if null l
            then pure acc
            else let (k, v) = break (== ':') l in readHeaders ((map toLower' k, drop 1 v) : acc)
    toLower' c = if c >= 'A' && c <= 'Z' then chr (ord c + 32) else c

writeMessage :: Handle -> Json -> IO ()
writeMessage h j = do
  let body = TE.encodeUtf8 (T.pack (renderJson j))
  B.hPut h (BC.pack ("Content-Length: " ++ show (B.length body) ++ "\r\n\r\n") <> body)
  hFlush h

-- Checking -----------------------------------------------------------------------------------

-- | An error at (file, 1-based line, 1-based column), or at the entry file when it has no
-- position.
data Diag = Diag FilePath Int Int String
  deriving (Eq, Show)

-- | The entry file a source belongs to: its project's main, or the file itself.
entryFor :: FilePath -> IO FilePath
entryFor file = go (takeDirectory file)
  where
    go dir = do
      let manifest = dir </> "keel.project"
      found <- doesFileExist manifest
      if found
        then do
          src <- readFile manifest
          let mainKey = [dropWhile isSpace (drop 1 v) | l <- lines src, let (k, v) = break (== '=') (takeWhile (/= '#') l), trim k == "main"]
          pure (normalise (dir </> maybe "src/main.kl" trim (safeHead mainKey)))
        else if takeDirectory dir == dir then pure file else go (takeDirectory dir)
    trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace
    safeHead xs = case xs of x : _ -> Just x; [] -> Nothing

-- | Check the program a file belongs to, reading open buffers from the overlay.
diagnose :: M.Map FilePath String -> FilePath -> IO [Diag]
diagnose overlay file = do
  entry <- entryFor file
  r <- E.try $ do
    loaded <- loadModulesWith readSource entry
    let ds = case loaded of
          Left e -> [fromString entry e]
          Right (prog, _) -> case inferProgram prog >>= compile of
            Left (TypeError k msg pos) -> case pos of
              Just (f, l, c) -> [Diag f l c (msg ++ " [" ++ show k ++ "]")]
              Nothing -> [Diag entry 1 1 (msg ++ " [" ++ show k ++ "]")]
            Right _ -> []
    _ <- evaluate (length (show ds))
    pure ds
  pure $ case r of
    Right ds -> ds
    Left (e :: SomeException) -> [Diag entry 1 1 ("internal compiler error: " ++ show e)]
  where
    readSource p = case M.lookup (normalise p) overlay of
      Just s -> pure (Just s)
      Nothing -> do
        exists <- doesFileExist p
        if exists then Just <$> readFile p else pure Nothing

-- | Loader errors are strings; most start with @file:line:col: @.
fromString :: FilePath -> String -> Diag
fromString entry s = case parse located "" s of
  Right d -> d
  Left _ -> Diag entry 1 1 s
  where
    located = do
      f <- many1 (noneOf ":\n")
      l <- char ':' *> (read <$> many1 digit)
      c <- char ':' *> (read <$> many1 digit)
      msg <- char ':' *> spaces *> many anyChar
      pure (Diag f l c msg)

-- | A file's text: its open buffer, else the file on disk.
readWith :: M.Map FilePath String -> FilePath -> IO (Maybe String)
readWith overlay p = case M.lookup (normalise p) overlay of
  Just s -> pure (Just s)
  Nothing -> doesFileExist p >>= \e -> if e then Just <$> readFile p else pure Nothing

-- | The identifier under the cursor (1-based line and column), with the qualifier written
-- before it (@uart@ in @uart.putc@), if any.
wordAt :: String -> Int -> Int -> Maybe (Maybe String, String)
wordAt src line col = case drop (line - 1) (lines src) of
  l : _ ->
    let (before, after) = splitAt (col - 1) l
        start = reverse (takeWhile isW (reverse before))
        w = start ++ takeWhile isW after
        rest = drop (length start) (reverse before)
        q = case rest of
          '.' : more | p@(_ : _) <- takeWhile isW more -> Just (reverse p)
          _ -> Nothing
     in if null w then Nothing else Just (q, w)
  [] -> Nothing
  where
    isW c = isAlphaNum c || c `elem` "_'"

-- | The declared type of the top-level name under the cursor (1-based line and column).
hover :: M.Map FilePath String -> FilePath -> Int -> Int -> IO (Maybe String)
hover overlay file line col = do
  src <- maybe "" id <$> readWith overlay file
  case wordAt src line col of
    Nothing -> pure Nothing
    Just (_, w) -> do
      entry <- entryFor file
      loaded <- E.try @SomeException (loadModulesWith (readWith overlay) entry)
      pure $ case loaded of
        Right (Right (Program decls _, _)) -> describe w (decls ++ map (uncurry Effect) builtinEffects)
        _ -> Nothing
  where
    -- Private names are renamed name@module by the loader.
    named w n = n == w || (w ++ "@") `isPrefixOf` n
    describe w decls =
      listToMaybe $
        [w ++ " : " ++ prettyTy t | Def f t _ <- decls, named w f]
          ++ [ w ++ " : " ++ (if null fs then "" else unwords (map prettyTy fs) ++ " → ") ++ prettyTy (TData d (map TVar ps))
             | Data _ d ps cs <- decls
             , (c, fs) <- cs
             , named w c
             ]
          ++ [w ++ " : " ++ prettyTy a ++ " ⇒ " ++ prettyTy b ++ "  (effect " ++ l ++ ")" | Effect l ops <- decls, (o, a, b) <- ops, named w o]

-- | Where the name under the cursor is declared: in this file, else in an imported module
-- (the one its qualifier names, if it has one). On an @import@ line, the imported file.
--
-- ponytail: matches by name, so a local variable that shadows a top-level name jumps to the
-- top-level one, and prelude names have no file to jump to.
definition :: M.Map FilePath String -> FilePath -> Int -> Int -> IO (Maybe Pos)
definition overlay file line col = do
  src <- maybe "" id <$> readWith overlay file
  root <- takeDirectory <$> entryFor file
  let parsed p = maybe Nothing (either (const Nothing) Just . parseModule p) <$> readWith overlay p
      sitesIn p = maybe [] modSites <$> parsed p
  self <- parsed file
  case (self, wordAt src line col) of
    (Just m, Just (q, w))
      | (imp, _, _) : _ <- [i | i@(_, _, (_, l, _)) <- modImports m, l == line] -> do
          p <- importPath root imp
          exists <- doesFileExist p
          pure (if exists || M.member p overlay then Just (p, 1, 1) else Nothing)
      | otherwise -> do
          imported <- sequence [importPath root imp | (imp, alias, _) <- modImports m, maybe True (== alias) q]
          own <- if q == Nothing then pure (modSites m) else pure []
          others <- concat <$> mapM sitesIn imported
          pure (lookup w (own ++ others))
    _ -> pure Nothing

-- The server ---------------------------------------------------------------------------------

uriToPath :: String -> FilePath
uriToPath u = normalise (decode (if "file://" `isPrefixOf` u then drop 7 u else u))
  where
    decode s = case s of
      '%' : a : b : rest | [(n, "")] <- readHex [a, b] -> chr n : decode rest
      c : rest -> c : decode rest
      [] -> []

pathToUri :: FilePath -> String
pathToUri p = "file://" ++ concatMap enc p
  where
    enc c
      | isAlphaNum c || c `elem` "/-_.~" = [c]
      | otherwise = concat ["%" ++ (if b < 16 then "0" else "") ++ showHex b "" | b <- B.unpack (TE.encodeUtf8 (T.singleton c))]

-- | Serve until @exit@ or end of input.
serve :: Handle -> Handle -> IO ()
serve input output = do
  hSetBinaryMode input True
  hSetBinaryMode output True
  docs <- newIORef (M.empty :: M.Map FilePath String)
  published <- newIORef S.empty
  let send = writeMessage output
      reply i result = send (JObj [("jsonrpc", JStr "2.0"), ("id", i), ("result", result)])
      notify method params = send (JObj [("jsonrpc", JStr "2.0"), ("method", JStr method), ("params", params)])
      check file = do
        overlay <- readIORef docs
        ds <- diagnose overlay file
        before <- readIORef published
        let files = S.fromList (map normalise (M.keys overlay ++ S.toList before ++ [f | Diag f _ _ _ <- ds]))
        forM_ (S.toList files) $ \f ->
          notify "textDocument/publishDiagnostics" $
            JObj [("uri", JStr (pathToUri f)), ("diagnostics", JArr [diagJson d | d@(Diag f' _ _ _) <- ds, normalise f' == f])]
        writeIORef published (S.fromList [normalise f | Diag f _ _ _ <- ds])
      diagJson (Diag _ l c msg) =
        let line0 = fromIntegral (max 0 (l - 1))
            col0 = fromIntegral (max 0 (c - 1))
         in JObj
              [ ("range", JObj [("start", pos line0 col0), ("end", pos line0 (col0 + 1))])
              , ("severity", JNum 1)
              , ("source", JStr "keel")
              , ("message", JStr msg)
              ]
      pos l c = JObj [("line", JNum l), ("character", JNum c)]
      loop = do
        msg <- readMessage input
        case msg of
          Nothing -> pure ()
          Just m -> do
            let method = case field "method" m of Just (JStr s) -> s; _ -> ""
                params = maybe JNull id (field "params" m)
                uri = case path' ["textDocument", "uri"] params of Just (JStr u) -> Just (uriToPath u); _ -> Nothing
                ident = maybe JNull id (field "id" m)
            case method of
              "initialize" ->
                reply ident $
                  JObj
                    [ ("capabilities", JObj [("textDocumentSync", JObj [("openClose", JBool True), ("change", JNum 1), ("save", JBool True)]), ("hoverProvider", JBool True), ("definitionProvider", JBool True)])
                    , ("serverInfo", JObj [("name", JStr "keelc")])
                    ]
              "shutdown" -> reply ident JNull
              "textDocument/didOpen" | Just f <- uri, Just (JStr text) <- path' ["textDocument", "text"] params -> do
                modifyIORef docs (M.insert f text)
                check f
              "textDocument/didChange" | Just f <- uri, Just (JArr changes) <- field "contentChanges" params -> do
                forM_ [t | c <- changes, Just (JStr t) <- [field "text" c]] $ \t -> modifyIORef docs (M.insert f t)
                check f
              "textDocument/didSave" | Just f <- uri -> check f
              "textDocument/didClose" | Just f <- uri -> modifyIORef docs (M.delete f)
              "textDocument/hover" | Just f <- uri, Just (JNum l) <- path' ["position", "line"] params, Just (JNum c) <- path' ["position", "character"] params -> do
                overlay <- readIORef docs
                h <- hover overlay f (round l + 1) (round c + 1)
                reply ident $ case h of
                  Nothing -> JNull
                  Just s -> JObj [("contents", JObj [("kind", JStr "markdown"), ("value", JStr ("```keel\n" ++ s ++ "\n```"))])]
              "textDocument/definition" | Just f <- uri, Just (JNum l) <- path' ["position", "line"] params, Just (JNum c) <- path' ["position", "character"] params -> do
                overlay <- readIORef docs
                d <- definition overlay f (round l + 1) (round c + 1)
                reply ident $ case d of
                  Nothing -> JNull
                  Just (p, dl, dc) -> JObj [("uri", JStr (pathToUri p)), ("range", JObj [("start", pos (fromIntegral (dl - 1)) (fromIntegral (dc - 1))), ("end", pos (fromIntegral (dl - 1)) (fromIntegral (dc - 1)))])]
              _ | ident /= JNull -> unless (method == "exit") (reply ident JNull)
              _ -> pure ()
            unless (method == "exit") loop
  loop
