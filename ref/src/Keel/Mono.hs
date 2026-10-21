-- | Monomorphization (spec/core.md §4.4): specialize every polymorphic definition at the
-- types and effects it is used with, starting from @main@ (the worklist of notes.md §4).
--
-- The output has no ∀, no type application, and no type variables outside data and codata
-- declarations, which stay as layout templates instantiated at closed types.
module Keel.Mono (monomorphize, isClosed, compile) where

import Control.Monad (forM_, unless)
import Data.List (intercalate)
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Keel.Check (ErrKind (..), TypeError (..), checkProgram, recursiveGroups)
import Keel.Elab (checkRefs, elaborate)
import Keel.Opt (optimize)
import Keel.Syntax

-- | The whole pipeline: place rules, elaboration, type checking, monomorphization,
-- optimization, and a final check of the result.
compile :: Program -> Either TypeError Program
compile p = do
  checkRefs p
  let core = elaborate p
  _ <- checkProgram core
  mono <- monomorphize core
  _ <- checkProgram mono
  -- Optimize (spec/perf.md) and check again: an optimizer bug shows up as a type error.
  let opt = optimize mono
  _ <- checkProgram opt
  pure opt

monomorphize :: Program -> Either TypeError Program
monomorphize (Program decls main) = do
  noPolyRecursion decls
  let poly = M.fromList [(f, (vs, es, b, e)) | Def f (TForall vs es b) e <- decls]
      monoDefs = [(f, t, e) | Def f t e <- decls, not (M.member f poly)]
      others = [d | d <- decls, not (isDef d)]
      seeds = concatMap (\(_, _, e) -> instancesIn e) monoDefs ++ instancesIn main
      instances = specialize poly M.empty seeds
  pure $
    Program
      ( others
          ++ [Def f t (rewrite e) | (f, t, e) <- monoDefs]
          ++ [Def name t (rewrite e) | (name, (t, e)) <- M.toList instances]
      )
      (rewrite main)
  where
    isDef Def {} = True
    isDef _ = False

-- | Worklist: each instance is specialized once; its body may request more instances.
specialize ::
  M.Map String ([(String, Kind)], [String], Ty, Term) ->
  M.Map String (Ty, Term) ->
  [(String, [Ty], [Eff])] ->
  M.Map String (Ty, Term)
specialize _ done [] = done
specialize poly done ((f, tys, effs) : rest)
  | M.member name done = specialize poly done rest
  | otherwise = case M.lookup f poly of
      Nothing -> specialize poly done rest
      Just (vs, es, body, e) ->
        let tv = M.fromList (zip (map fst vs) tys)
            ev = M.fromList (zip es effs)
            e' = substTerm tv ev e
         in specialize poly (M.insert name (substTy tv ev body, e') done) (instancesIn e' ++ rest)
  where
    name = mangle f tys effs

-- | Instantiations requested by a term.
instancesIn :: Term -> [(String, [Ty], [Eff])]
instancesIn e = [(f, tys, effs) | TyApp f tys effs <- universe e]

rewrite :: Term -> Term
rewrite (TyApp f tys effs) = Var (mangle f tys effs)
rewrite tm = descend rewrite tm

-- | Instance names contain @[@, which source names never do.
mangle :: String -> [Ty] -> [Eff] -> String
mangle f tys effs = f ++ "[" ++ intercalate "; " (map prettyTy tys ++ map showEff effs) ++ "]"
  where
    showEff e = "{" ++ intercalate ", " (S.toList e) ++ "}"

-- | §4.4: inside a recursive group, members may only be instantiated at the caller's own type
-- variables. Then every instance reachable from a closed one uses only types that already
-- occur in it, so the worklist terminates. Effect arguments are unrestricted: effect sets over
-- finitely many labels can't grow forever.
noPolyRecursion :: [Decl] -> Either TypeError ()
noPolyRecursion decls = forM_ [(f, vs, e) | Def f (TForall vs _ _) e <- decls] $ \(f, vs, e) -> do
  let group = M.findWithDefault S.empty f groups
      own = map fst vs
  forM_ [(g, tys) | TyApp g tys _ <- universe e, g `S.member` group] $ \(g, tys) ->
    unless (all (`elem` map TVar own) tys) $
      Left
        ( TypeError
            PolyRecursion
            (f ++ " calls " ++ g ++ " at [" ++ intercalate ", " (map prettyTy tys) ++ "]: recursion must keep the same type variables")
            Nothing
        )
  where
    groups = recursiveGroups decls

-- | No ∀, type application or type variable in any definition or in @main@.
isClosed :: Program -> Bool
isClosed (Program decls main) = all closedDecl decls && closedTerm main
  where
    closedDecl (Def _ t e) = closedTy t && closedTerm e
    closedDecl _ = True
    closedTerm e = all here (universe e)
    here tm = case tm of
      TyApp {} -> False
      Lam _ t _ -> closedTy t
      LLam _ t _ -> closedTy t
      Con _ tys _ -> all closedTy tys
      Cocase _ tys _ -> all closedTy tys
      _ -> True
    closedTy t = case t of
      TVar _ -> False
      TForall {} -> False
      TFun a e b -> closedTy a && closedTy b && not (any isEffVar e)
      TLFun a e b -> closedTy a && closedTy b && not (any isEffVar e)
      TData _ as -> all closedTy as
      TBox a -> closedTy a
      TPair a b -> closedTy a && closedTy b
      _ -> True
