-- | Multi-file programs (M5). One file is one module; @import drivers.uart@ loads
-- @drivers/uart.kl@ relative to the entry file's directory. @import std.map@ loads the
-- standard library's @map.kl@, which ships with keelc (@ref/std/@).
--
-- Namespaces: a module sees its own declarations and the public declarations of the modules it
-- imports, by plain name (@putc@) or qualified by the import (@uart.putc@, or @u.putc@ after
-- @import drivers.uart as u@). The prelude is visible everywhere. Two imported modules may
-- declare the same name; using it unqualified is then an error. Names are resolved here, so
-- later phases see one flat program: a name declared by one module only keeps its name, and
-- private names and names declared by several modules become @name\@module@.
--
-- Types, constructors and effects are qualified the same way: @uart.Status@, @uart.Ready@.
--
-- ponytail: handler clauses name operations unqualified (@handle e with uart.Uart { read x ->
-- … }@); an operation two imported effects share can't be handled there.
module Keel.Modules (loadModules, loadModulesWith, importPath) where

import Control.Monad (foldM, forM, forM_, when)
import Data.List (intercalate, nub)
import Data.Map.Strict qualified as M
import Data.Maybe (listToMaybe)
import Data.Set qualified as S
import Keel.Parser (parseModule)
import Keel.Prelude (declared, preludeDecls, withPrelude)
import Keel.Syntax
import Paths_keel_ref (getDataFileName)
import System.Directory (doesFileExist)
import System.FilePath (takeBaseName, takeDirectory, (<.>), (</>))

-- | Load a program from its entry file. Returns the program (with the prelude) and every
-- source file read, for error messages.
loadModules :: FilePath -> IO (Either String (Program, M.Map FilePath String))
loadModules = loadModulesWith $ \path -> do
  exists <- doesFileExist path
  if exists then Just <$> readFile path else pure Nothing

-- | 'loadModules' with a file reader: the language server reads unsaved editor buffers.
loadModulesWith :: (FilePath -> IO (Maybe String)) -> FilePath -> IO (Either String (Program, M.Map FilePath String))
loadModulesWith readSource entry = do
  r <- visit M.empty [] (takeBaseName entry) entry Nothing
  pure $ do
    (loaded, order) <- r
    let mods = [(name, loaded M.! name) | name <- order]
    forM_ [path | (name, (path, _, m)) <- mods, name /= takeBaseName entry, Just _ <- [modMain m]] $ \path ->
      Left (path ++ ": only the entry file may define main")
    lib <- preludeDecls
    let names private = M.fromList [(name, S.unions [declared d | (p, d) <- modDecls m, p == private]) | (name, (_, _, m)) <- mods]
        scope = Scope (names False) (names True) (S.unions (map declared lib))
    resolved <- forM mods $ \(name, (path, _, m)) -> resolveModule scope name path m
    main <- case [m | (name, (_, Just m)) <- zip order resolved, name == takeBaseName entry] of
      m : _ -> Right m
      [] -> Left (entry ++ ": no main")
    let program = withPrelude lib (Program (concatMap fst resolved) main)
    pure (program, M.fromList [(path, src) | (_, (path, src, _)) <- mods])
  where
    root = takeDirectory entry

    -- Depth-first over imports: dependencies come before the modules that import them.
    visit ::
      M.Map String (FilePath, String, Module) ->
      [String] ->
      String ->
      FilePath ->
      Maybe Pos ->
      IO (Either String (M.Map String (FilePath, String, Module), [String]))
    visit loaded stack name path from
      | name `elem` stack = pure (Left ("import cycle: " ++ intercalate " → " (reverse (name : stack))))
      | M.member name loaded = pure (Right (loaded, []))
      | otherwise = do
          source <- readSource path
          case source of
            Nothing -> pure (Left (at from ++ "module " ++ name ++ " not found (looked for " ++ path ++ ")"))
            Just src ->
              case parseModule path src of
                Left e -> pure (Left e)
                Right m -> do
                  let loaded0 = M.insert name (path, src, m) loaded
                  foldM
                    ( \acc (imp, _, pos) -> case acc of
                        Left e -> pure (Left e)
                        Right (l, order) -> do
                          path' <- importPath root imp
                          r <- visit l (name : stack) imp path' (Just pos)
                          pure (fmap (\(l', o) -> (l', order ++ o)) r)
                    )
                    (Right (loaded0, []))
                    (modImports m)
                    >>= pure . fmap (\(l, order) -> (l, order ++ [name]))

-- | The file of an import: @drivers.uart@ is @ROOT/drivers/uart.kl@, and @std.map@ is the
-- standard library's @map.kl@.
importPath :: FilePath -> String -> IO FilePath
importPath root imp = case imp of
  's' : 't' : 'd' : '.' : m -> (</> file m) <$> getDataFileName "std"
  _ -> pure (root </> file imp)
  where
    file m = map (\c -> if c == '.' then '/' else c) m <.> "kl"

-- | Every module's public and private names, and the prelude's.
data Scope = Scope {publics, privates :: M.Map String (S.Set String), preludeNames :: S.Set String}

at :: Maybe Pos -> String
at (Just (f, l, c)) = f ++ ":" ++ show l ++ ":" ++ show c ++ ": "
at Nothing = ""

-- | The program-wide name of a module's declaration: its own name, unless it is private or
-- another module declares the same public name.
internal :: Scope -> String -> Bool -> String -> String
internal scope m private n
  | private || length [() | ns <- M.elems (publics scope), n `S.member` ns] > 1 = n ++ "@" ++ m
  | otherwise = n

-- | Resolve a module's names to program-wide names: its declarations and its main.
resolveModule :: Scope -> String -> FilePath -> Module -> Either String ([Decl], Maybe Term)
resolveModule scope self path (Module imports decls main _) = do
  decls' <- forM decls $ \(_, d) -> renameDecl d
  main' <- traverse (term (Just (path, 1, 1)) S.empty) main
  pure (decls', main')
  where
    own = M.fromList [(n, internal scope self p n) | (p, d) <- decls, n <- S.toList (declared d)]
    quals = M.fromList [(q, imp) | (imp, q, _) <- imports]
    imported = nub [imp | (imp, _, _) <- imports]
    pubs m = M.findWithDefault S.empty m (publics scope)

    -- An unqualified name: this module's, else an import's, else the prelude's (or unbound,
    -- which inference reports).
    plain pos n
      | Just i <- M.lookup n own = Right i
      | otherwise = case [m | m <- imported, n `S.member` pubs m] of
          [m] -> Right (internal scope m False n)
          ms@(_ : _ : _) ->
            Left (at pos ++ n ++ " is ambiguous: it is declared in " ++ intercalate " and " ms ++ "; write " ++ intercalate " or " [qualifier m ++ "." ++ n | m <- ms])
          []
            | n `S.notMember` preludeNames scope
            , m : _ <- [m | (m, ns) <- M.toList (publics scope), m /= self, n `S.member` ns] ->
                Left (at pos ++ n ++ " is declared in module " ++ m ++ "; import " ++ m ++ " to use it")
            | otherwise -> Right n
    qualifier m = case [q | (imp, q, _) <- imports, imp == m] of
      q : _ -> q
      [] -> m

    qualified pos q n = do
      let m = quals M.! q
      when (n `S.member` M.findWithDefault S.empty m (privates scope)) $
        Left (at pos ++ n ++ " is private to module " ++ m)
      when (n `S.notMember` pubs m) $
        Left (at pos ++ "module " ++ m ++ " has no " ++ n)
      Right (internal scope m False n)

    -- A name the parser read with its qualifier: q.f[t], q.Type, q.Con.
    name pos n = case break (== '.') n of
      (q, '.' : f) | M.member q quals -> qualified pos q f
      _ -> plain pos n

    -- Types carry no positions: their errors point at the declaration's first expression.
    renameDecl d = case d of
      Data lin n ps cs -> Data lin (r n) ps <$> mapM (\(c, fs) -> (r c,) <$> mapM (ty top) fs) cs
      Codata n ps os -> Codata (r n) ps <$> mapM (\(o, t) -> (o,) <$> ty top t) os
      Effect l ops -> Effect (r l) <$> mapM (\(o, a, b) -> (r o,,) <$> ty top a <*> ty top b) ops
      Def f t e -> let p = listToMaybe [q | At q _ <- universe e] in Def (r f) <$> ty p t <*> term p S.empty e
      Bitdata n it fs -> Right (Bitdata (r n) it fs)
      where
        r n = own M.! n
        top = Just (path, 1, 1)

    ty pos t = case t of
      TData n as -> TData <$> name pos n <*> mapM (ty pos) as
      TFun a e b -> TFun <$> ty pos a <*> effs pos e <*> ty pos b
      TLFun a e b -> TLFun <$> ty pos a <*> effs pos e <*> ty pos b
      TBox a -> TBox <$> ty pos a
      TPair a b -> TPair <$> ty pos a <*> ty pos b
      TRef a -> TRef <$> ty pos a
      TMut a -> TMut <$> ty pos a
      TForall vs es b -> TForall vs es <$> ty pos b
      _ -> Right t
    effs pos e = S.fromList <$> mapM (\l -> if take 1 l == "'" then Right l else name pos l) (S.toList e)

    -- Global names in a term, leaving local variables (which may shadow) alone. pos is the
    -- innermost enclosing source position, for errors.
    term pos bound tm = case tm of
      At p e -> At p <$> term (Just p) bound e
      Var x | x `S.notMember` bound -> Var <$> plain pos x
      Proj (Var q) n | q `S.notMember` bound, M.member q quals -> Var <$> qualified pos q n
      Lam x t b -> Lam x <$> ty pos t <*> go (S.insert x bound) b
      LLam x t b -> LLam x <$> ty pos t <*> go (S.insert x bound) b
      Let x e b -> Let x <$> go bound e <*> go (S.insert x bound) b
      LetVar x e b -> LetVar x <$> go bound e <*> go (S.insert x bound) b
      LetPair x y e b -> LetPair x y <$> go bound e <*> go (S.insert x (S.insert y bound)) b
      Case e alts -> Case <$> go bound e <*> mapM (\(c, xs, b) -> (,xs,) <$> name pos c <*> go (bound <> S.fromList xs) b) alts
      Handle l e cs -> Handle <$> name pos l <*> go bound e <*> mapM (\(op, x, b) -> (,x,) <$> plain pos op <*> go (S.insert x bound) b) cs
      Con c ts as -> Con <$> name pos c <*> mapM (ty pos) ts <*> mapM (go bound) as
      TyApp f ts es -> TyApp <$> name pos f <*> mapM (ty pos) ts <*> mapM (effs pos) es
      Cocase dn ts bs -> Cocase <$> name pos dn <*> mapM (ty pos) ts <*> mapM (\(o, b) -> (o,) <$> go bound b) bs
      BitsLit b fs -> BitsLit <$> name pos b <*> mapM (\(f, e) -> (f,) <$> go bound e) fs
      Perform op e -> Perform <$> plain pos op <*> go bound e
      _ -> descendM (go bound) tm
      where
        go = term pos
