-- | The Keel prelude (M5): declarations every @.kl@ program gets, written in Keel. A program
-- may declare any of these names itself; the prelude's version is then left out, together
-- with prelude definitions that refer to a left-out or redeclared name. Unused definitions
-- cost nothing: the optimizer removes them.
module Keel.Prelude (preludeSource, preludeDecls, loadProgram, withPrelude, declared) where

import Data.Set qualified as S
import Keel.Parser (parseLibrary, parseProgram)
import Keel.Syntax

preludeSource :: String
preludeSource =
  unlines
    [ "-- Lists, and strings as lists of bytes."
    , "data List a = Nil | Cons(a, Box (List a))"
    , ""
    , "def map : forall a b 'e. (a ->{'e} b) -> List a ->{'e, Diverge} List b ="
    , "  \\f xs. case xs of { Nil -> Nil | Cons(x, rest) -> Cons(f x, box (map f (unbox rest))) }"
    , ""
    , "def foldl : forall a (b : Free) 'e. (b -> a ->{'e} b) -> b -> List a ->{'e, Diverge} b ="
    , "  \\f acc xs. case xs of { Nil -> acc | Cons(x, rest) -> foldl f (f acc x) (unbox rest) }"
    , ""
    , "def length : forall (a : Free). List a ->{Diverge, Panic} i64 ="
    , "  \\xs. case xs of { Nil -> 0 | Cons(x, rest) -> 1 + length (unbox rest) }"
    , ""
    , "-- The inner λ captures the first list, which may be linear: a one-shot (-o) closure."
    , "def append : forall a. List a -> List a -o{Diverge} List a ="
    , "  \\xs ys. case xs of { Nil -> ys | Cons(x, rest) -> Cons(x, box (append (unbox rest) ys)) }"
    , ""
    , "def reverseOnto : forall a. List a -> List a -o{Diverge} List a ="
    , "  \\xs acc. case xs of { Nil -> acc | Cons(x, rest) -> reverseOnto (unbox rest) (Cons(x, box acc)) }"
    , ""
    , "def reverse : forall a. List a ->{Diverge} List a = \\xs. reverseOnto xs Nil"
    , ""
    , "-- Output."
    , "def print : List u8 ->{IO, Diverge} Unit ="
    , "  \\s. case s of { Nil -> () | Cons(c, rest) -> putc(c); print (unbox rest) }"
    , ""
    , "def println : List u8 ->{IO, Diverge} Unit = \\s. print s; putc(10)"
    , ""
    , "def printU64 : u64 ->{IO, Diverge, Panic} Unit ="
    , "  \\n. if n < 10 then putc((n + 48) as u8)"
    , "      else (printU64 (n / 10); putc((n % 10 + 48) as u8))"
    , ""
    , "-- Negative numbers go through -(n + 1), which can't overflow."
    , "def printInt : i64 ->{IO, Diverge, Panic} Unit ="
    , "  \\n. if n < 0 then (putc(45); printU64 (((0 - (n + 1)) as u64) + 1))"
    , "      else printU64 (n as u64)"
    , ""
    , "-- Input: every byte up to the end of input."
    , "def readOnto : List u8 ->{Input, Diverge} List u8 ="
    , "  \\acc. let c = getc () in if c < 0 then reverse acc else readOnto (Cons(c as u8, box acc))"
    , ""
    , "def readAll : Unit ->{Input, Diverge} List u8 = \\u. readOnto Nil"
    , ""
    , "-- The result of a comparison (std.map takes a comparison function)."
    , "data Ordering = Less | Equal | Greater"
    , ""
    , "def not : Bool -> Bool = \\b. if b then false else true"
    , ""
    , "def compareInt : i64 -> i64 -> Ordering = \\a b. if a < b then Less else if a == b then Equal else Greater"
    ]

-- | Parse a single-file program and add the prelude.
loadProgram :: FilePath -> String -> Either String Program
loadProgram path src = do
  user <- parseProgram path src
  lib <- preludeDecls
  pure (withPrelude lib user)

-- | The prelude's declarations, without positions (errors in it are compiler bugs, and its
-- positions would be read as the program's).
preludeDecls :: Either String [Decl]
preludeDecls = map unlocate <$> parseLibrary "<prelude>" preludeSource
  where
    unlocate (Def f t e) = Def f t (stripAt e)
    unlocate d = d

-- | Add the prelude declarations the program doesn't override.
withPrelude :: [Decl] -> Program -> Program
withPrelude lib (Program decls main) = Program ([d | (i, d) <- zip [0 :: Int ..] lib, i `S.notMember` dropped] ++ decls) main
  where
    userNames = S.unions (map declared decls)
    dropped = go S.empty
    -- Leave out declarations that redeclare a user name or mention a left-out or user name.
    go out =
      let out' =
            S.fromList
              [ i
              | (i, d) <- zip [0 :: Int ..] lib
              , not (S.null (declared d `S.intersection` userNames))
                  || not (S.null (mentions d `S.intersection` (userNames <> S.unions [declared (lib !! j) | j <- S.toList out])))
              ]
       in if out' == out then out else go out'

-- | Names a declaration introduces.
declared :: Decl -> S.Set String
declared d = case d of
  Data _ n _ cs -> S.fromList (n : map fst cs)
  Codata n _ os -> S.fromList (n : map fst os)
  Effect l ops -> S.fromList (l : [o | (o, _, _) <- ops])
  Def f _ _ -> S.singleton f
  Bitdata n _ _ -> S.singleton n

-- | Names a declaration refers to: variables, constructors and types.
mentions :: Decl -> S.Set String
mentions d = case d of
  Def _ t e -> tyNames t <> S.fromList (concatMap termNames (universe e))
  Data _ _ _ cs -> S.unions [tyNames f | (_, fs) <- cs, f <- fs]
  Codata _ _ os -> S.unions (map (tyNames . snd) os)
  Effect _ ops -> S.unions [tyNames a <> tyNames r | (_, a, r) <- ops]
  Bitdata {} -> S.empty
  where
    termNames tm = case tm of
      Var x -> [x]
      Con c _ _ -> [c]
      Case _ alts -> [c | (c, _, _) <- alts]
      _ -> []
    tyNames t = case t of
      TData n as -> S.insert n (S.unions (map tyNames as))
      TFun a _ b -> tyNames a <> tyNames b
      TLFun a _ b -> tyNames a <> tyNames b
      TBox a -> tyNames a
      TPair a b -> tyNames a <> tyNames b
      TForall _ _ b -> tyNames b
      _ -> S.empty
