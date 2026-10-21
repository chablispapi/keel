-- | Multi-file programs (M5). One file is one module; @import drivers.uart@ loads
-- @drivers/uart.kl@ relative to the entry file's directory. Imported declarations are visible
-- by their plain names, except those marked @private@, which are renamed per module so two
-- modules can each have a @private def helper@.
--
-- ponytail: no namespaces yet. Two modules declaring the same public name is an error that
-- names both files. Qualified names (@uart.putc@) need syntax that doesn't collide with
-- projection (@e.obs@).
module Keel.Modules (loadModules, loadModulesWith) where

import Control.Monad (foldM, forM_)
import Data.List (intercalate)
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Keel.Parser (parseModule)
import Keel.Prelude (declared, preludeDecls, withPrelude)
import Keel.Syntax
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
        renamed = [(name, path, renameModule name m) | (name, (path, _, m)) <- mods]
    checkDuplicates [(path, decls) | (_, path, (decls, _)) <- renamed]
    forM_ [(path, m) | (name, path, (_, m)) <- renamed, name /= takeBaseName entry, Just _ <- [m]] $ \(path, _) ->
      Left (path ++ ": only the entry file may define main")
    main <- case [m | (name, _, (_, Just m)) <- renamed, name == takeBaseName entry] of
      m : _ -> Right m
      [] -> Left (entry ++ ": no main")
    lib <- preludeDecls
    let program = withPrelude lib (Program (concat [decls | (_, _, (decls, _)) <- renamed]) main)
    pure (program, M.fromList [(path, src) | (_, (path, src, _)) <- mods])
  where
    root = takeDirectory entry

    -- Depth-first over imports: dependencies come before the modules that import them.
    visit ::
      M.Map String (FilePath, String, Module) ->
      [String] ->
      String ->
      FilePath ->
      Maybe (String, Pos) ->
      IO (Either String (M.Map String (FilePath, String, Module), [String]))
    visit loaded stack name path from
      | name `elem` stack = pure (Left ("import cycle: " ++ intercalate " → " (reverse (name : stack))))
      | M.member name loaded = pure (Right (loaded, []))
      | otherwise = do
          source <- readSource path
          case source of
            Nothing -> pure (Left (where' from ++ "module " ++ name ++ " not found (looked for " ++ path ++ ")"))
            Just src ->
              case parseModule path src of
                Left e -> pure (Left e)
                Right m -> do
                  let loaded0 = M.insert name (path, src, m) loaded
                  foldM
                    ( \acc (imp, pos) -> case acc of
                        Left e -> pure (Left e)
                        Right (l, order) -> do
                          r <- visit l (name : stack) imp (root </> map dotToSlash imp <.> "kl") (Just (imp, pos))
                          pure (fmap (\(l', o) -> (l', order ++ o)) r)
                    )
                    (Right (loaded0, []))
                    (modImports m)
                    >>= pure . fmap (\(l, order) -> (l, order ++ [name]))
    dotToSlash c = if c == '.' then '/' else c
    where' (Just (_, (f, l, c))) = f ++ ":" ++ show l ++ ":" ++ show c ++ ": "
    where' Nothing = ""

-- | Rename the module's private names apart (@name\@module@); returns its declarations and main.
renameModule :: String -> Module -> ([Decl], Maybe Term)
renameModule name (Module _ decls main) =
  (map (renameDecl s . snd) decls, renameTerm s S.empty <$> main)
  where
    s = M.fromList [(n, n ++ "@" ++ name) | (True, d) <- decls, n <- S.toList (declared d)]

-- | Public names declared by two modules.
checkDuplicates :: [(FilePath, [Decl])] -> Either String ()
checkDuplicates mods = do
  _ <-
    foldM
      ( \seen (path, decls) -> do
          let names = S.toList (S.unions (map declared decls))
          forM_ names $ \n -> case M.lookup n seen of
            Just other | other /= path -> Left (n ++ " is declared in both " ++ other ++ " and " ++ path)
            _ -> Right ()
          pure (M.union seen (M.fromList [(n, path) | n <- names]))
      )
      M.empty
      mods
  pure ()

renameDecl :: M.Map String String -> Decl -> Decl
renameDecl s d = case d of
  Data lin n ps cs -> Data lin (r n) ps [(r c, map (renameTy s) fs) | (c, fs) <- cs]
  Codata n ps os -> Codata (r n) ps [(o, renameTy s t) | (o, t) <- os]
  Effect l ops -> Effect (r l) [(r o, renameTy s a, renameTy s b) | (o, a, b) <- ops]
  Def f t e -> Def (r f) (renameTy s t) (renameTerm s S.empty e)
  Bitdata n it fs -> Bitdata (r n) it fs
  where
    r x = M.findWithDefault x x s

renameTy :: M.Map String String -> Ty -> Ty
renameTy s t = case t of
  TData n as -> TData (r n) (map go as)
  TFun a e b -> TFun (go a) (S.map r e) (go b)
  TLFun a e b -> TLFun (go a) (S.map r e) (go b)
  TBox a -> TBox (go a)
  TPair a b -> TPair (go a) (go b)
  TRef a -> TRef (go a)
  TMut a -> TMut (go a)
  TForall vs es b -> TForall vs es (go b)
  _ -> t
  where
    r x = M.findWithDefault x x s
    go = renameTy s

-- | Rename global references, leaving local variables (which may shadow) alone.
renameTerm :: M.Map String String -> S.Set String -> Term -> Term
renameTerm s bound tm = case tm of
  Var x | x `S.notMember` bound -> Var (r x)
  Lam x t b -> Lam x (ty t) (go (S.insert x bound) b)
  LLam x t b -> LLam x (ty t) (go (S.insert x bound) b)
  Let x e b -> Let x (go bound e) (go (S.insert x bound) b)
  LetVar x e b -> LetVar x (go bound e) (go (S.insert x bound) b)
  LetPair x y e b -> LetPair x y (go bound e) (go (S.insert x (S.insert y bound)) b)
  Case e alts -> Case (go bound e) [(r c, xs, go (bound <> S.fromList xs) b) | (c, xs, b) <- alts]
  Handle l e cs -> Handle (r l) (go bound e) [(r op, x, go (S.insert x bound) b) | (op, x, b) <- cs]
  Con c ts as -> Con (r c) (map ty ts) (map (go bound) as)
  TyApp f ts es -> TyApp (r f) (map ty ts) (map (S.map r) es)
  Cocase dn ts bs -> Cocase (r dn) (map ty ts) [(o, go bound b) | (o, b) <- bs]
  BitsLit b fs -> BitsLit (r b) [(f, go bound e) | (f, e) <- fs]
  Perform op e -> Perform (r op) (go bound e)
  _ -> descend (go bound) tm
  where
    r x = M.findWithDefault x x s
    ty = renameTy s
    go = renameTerm s
