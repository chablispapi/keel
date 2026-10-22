-- | Lowering (notes.md §5, §17): monomorphic Keel Core → A-normal form → closure conversion →
-- a first-order IR that maps one-to-one onto assembly, then reference counting (M2, spec/memory.md).
--
-- Covered: all integer widths, Bool, Unit, arithmetic in every overflow mode, if, let,
-- λ / λ°, application, recursive top-level definitions, data and case, Box, pairs, codata,
-- effect handlers and operations (M3).
--
-- Representation: every value is one 64-bit word. Integers are sign- or zero-extended to
-- 64 bits by their type; Bool and Unit are 0/1 and 0. Data values, pairs, closures and codata
-- values are pointers to heap blocks: @[tag, fields…]@, @[code, captured…]@ and
-- @[code₁, …, codeₙ, captured…]@, each preceded by a header word (reference count, size,
-- pointer map). @Box@ is the identity, since data is already behind a pointer.
module Keel.Lower (Atom (..), Rhs (..), Expr (..), Fun (..), LProg (..), lower, isPtr) where

import Control.Applicative ((<|>))
import Control.Monad (foldM, forM, forM_)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (State, StateT, evalState, get, gets, modify, put, runStateT)
import Data.Bits (setBit)
import Data.List (elemIndex, nub, sortOn)
import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe)
import Data.Set qualified as S
import Keel.Syntax

data Atom
  = AInt Integer -- ^ integers (canonical 64-bit form), and Bool / Unit as 0 or 1
  | AVar String  -- ^ a local variable (stack slot)
  | AGlobal Int  -- ^ the static block of top-level definition i (immortal)
  deriving (Show)

-- | Bitmaps mark which payload words hold pointers (bit i = word i); the runtime uses them to
-- drop children when a block is freed.
data Rhs
  = RAtom Atom
  | RPrim Prim IntTy Atom Atom          -- ^ arithmetic or comparison at an integer type
  | RCall Atom Atom                     -- ^ call an unknown closure (consumes both)
  | RCallKnown Int [Atom]               -- ^ direct call to function i with all its arguments
  | RClosure Int [String] Integer       -- ^ allocate a closure for function i
  | RCodata [Int] [String] Integer      -- ^ allocate a codata value: one function per observation
  | RProj Atom Int                      -- ^ observe: call the i-th function of a codata value
  | RAlloc Integer Integer [Atom]       -- ^ allocate a data block: tag, bitmap, fields
  | RAllocAt String Integer Integer [Atom] -- ^ the same, reusing a token's block if it has one
  | RField Atom Int                     -- ^ read field i of a data block (borrowed)
  | RPushHandler [(Int, Atom)] Integer  -- ^ push a handler frame: (operation number, clause closure)
  | RPopHandler Atom                    -- ^ pop (and drop) the frame
  | RPerform Int Atom                   -- ^ perform operation n: innermost handler, else the machine
  | RConv IntTy Atom                    -- ^ wrap a canonical integer into another integer type
  | RArray ArrayOp Bool [Atom]          -- ^ an array operation; whether the elements are pointers
  deriving (Show)

data Expr
  = Ret Atom                                  -- ^ the value of this expression
  | Bind String Rhs Expr                      -- ^ let x = rhs in e
  | BindIf String Atom Expr Expr Expr         -- ^ let x = (if a then e₁ else e₂) in e
  | BindCase String Atom [(Integer, Int, Expr)] Expr -- ^ case on a tag; each branch knows its block size
  | Dup String Expr                           -- ^ increment a reference count
  | Drop String Expr                          -- ^ decrement it, freeing the block at zero
  | DropReuse String String Expr              -- ^ drop, keeping the block as a reuse token if unique
  deriving (Show)

-- | A closure-converted function, called with its block in x0 and its arguments (owned) in
-- x1, x2, …: one for closures, several for the uncurried entry points of top-level
-- definitions. A function with @funDropsSelf@ owns its block and drops it after taking the
-- captured values, which start at word @funEnvBase@; @funEnvPtrs@ are the captured pointers,
-- duplicated on entry.
data Fun = Fun
  { funName :: String
  , funParams :: [String]
  , funEnvBase :: Int
  , funEnv :: [String]
  , funEnvPtrs :: [String]
  , funDropsSelf :: Bool
  , funBody :: Expr
  }
  deriving (Show)

-- | Functions are numbered: top-level λ definitions keep their definition's index, lifted
-- functions follow. Every top-level definition i also has a static block @_kc_i@, listed in
-- @lStatics@ with the functions it points to. @main@ is a separate function.
--
-- @lLocs@ is the source position of each bound variable's computation, where the program
-- still had one (only debug builds keep positions through optimization).
data LProg = LProg {lFuns :: M.Map Int Fun, lStatics :: [(Int, String, [Int])], lMain :: Fun, lLocs :: M.Map String Pos}
  deriving (Show)

-- | What lowering needs to know about declarations.
data Info = Info
  { iGlobals :: M.Map String (Int, Ty)
  , iKnown :: S.Set String                        -- ^ top-level λs: callable directly
  , iUncurried :: M.Map String (Int, Int)         -- ^ multi-parameter definitions: (function, arity)
  , iCons :: M.Map String (Integer, String, [Ty]) -- ^ constructor ↦ (tag, data name, field types)
  , iParams :: M.Map String [String]              -- ^ data / codata name ↦ parameters
  , iObs :: M.Map String [(String, Ty)]           -- ^ codata name ↦ observations in order
  , iOps :: M.Map String (Int, Ty, Ty)            -- ^ operation ↦ (number, argument, result)
  }

-- | Values that live on the heap and are reference counted.
isPtr :: Ty -> Bool
isPtr t = case t of
  TData _ _ -> True
  TFun {} -> True
  TLFun {} -> True
  TPair _ _ -> True
  TBox a -> isPtr a
  _ -> False

-- | lsPos is the innermost source position around the term being lowered.
data LS = LS {lsNext :: Int, lsFuns :: M.Map Int Fun, lsPtrs :: S.Set String, lsPos :: Maybe Pos, lsLocs :: M.Map String Pos}

type M = StateT LS (Either String)

unsupported :: String -> M a
unsupported what = lift (Left ("not supported yet: " ++ what))

-- | A fresh name, recorded as a pointer if its type is one. Every IR variable is unique, so
-- a name has one type across the program.
newVar :: String -> Ty -> M String
newVar base t = do
  s <- get
  let x = base ++ "%" ++ show (lsNext s)
  put s {lsNext = lsNext s + 1, lsPtrs = if isPtr t then S.insert x (lsPtrs s) else lsPtrs s}
  pure x

-- | Register a lifted function and return its index (after all definition indices).
liftFun :: Info -> Fun -> M Int
liftFun info f = do
  s <- get
  let ng = M.size (iGlobals info)
      i = case M.lookupMax (lsFuns s) of
        Just (k, _) | k >= ng -> k + 1
        _ -> ng
  put s {lsFuns = M.insert i f (lsFuns s)}
  pure i

-- | Pointer map: bit (offset + i) for each pointer among the given types.
bitmap :: Int -> [Bool] -> M Integer
bitmap offset ptrs = do
  let bits = [offset + i | (i, True) <- zip [0 ..] ptrs]
  if any (>= 16) bits
    then unsupported "a heap block with a pointer beyond word 16"
    else pure (foldl setBit 0 bits)

-- | Lower a monomorphic core program (the output of "Keel.Mono".compile).
lower :: Program -> Either String LProg
lower (Program userDecls main) = do
  let decls = optionDecl : arrayDecl : userDecls
      defs = [(f, t, e) | Def f t e <- decls]
      info =
        Info
          { iGlobals = M.fromList [(f, (i, t)) | (i, (f, t, _)) <- zip [0 ..] defs]
          , iKnown = S.fromList [f | (f, _, e) <- defs, isLam e]
          , iUncurried = M.fromList [(f, (i, length ps)) | (i, (f, ps, _)) <- uncurried]
          , iCons = M.fromList [(c, (tag, d, fs)) | Data _ d _ cs <- decls, (tag, (c, fs)) <- zip [0 ..] cs]
          , iParams = M.fromList ([(d, ps) | Data _ d ps _ <- decls] ++ [(d, ps) | Codata d ps _ <- decls])
          , iObs = M.fromList [(d, os) | Codata d _ os <- decls]
          , iOps = M.fromList [(op, (n, a, r)) | (n, (op, a, r)) <- zip [0 ..] allOps]
          }
      allOps = concat (map snd builtinEffects) ++ [o | Effect _ os <- decls, o <- os]
      -- Definitions taking several parameters (λx y. …) also get an uncurried entry point,
      -- numbered right after the definitions, so full applications need no closures.
      uncurried =
        zip [length defs ..] [(f, ps, b) | (f, _, e) <- defs, let (ps, b) = lams e, length ps >= 2]
  ((statics, mainF), s) <-
    runStateT
      ( do
          -- Reserve the uncurried functions' numbers before anything is lifted.
          modify (\st -> st {lsFuns = M.fromList [(i, Fun f [] 1 [] [] False (Ret (AInt 0))) | (i, (f, _, _)) <- uncurried]})
          forM_ uncurried $ \(i, (f, ps, b)) -> do
            ps' <- mapM (uncurry newVar) ps
            body <- expr info (M.fromList (zip (map fst ps) (zip ps' (map snd ps)))) b (pure . Ret)
            modify (\st -> st {lsFuns = M.insert i (Fun (f ++ "/" ++ show (length ps)) ps' 1 [] [] False body) (lsFuns st)})
          statics <- forM (zip [0 ..] defs) $ \(i, (f, _, e)) -> case e of
            Lam x t b -> topLam info i f x t b
            LLam x t b -> topLam info i f x t b
            -- A closed cocase is a static block of observation functions.
            Cocase d _ bs -> do
              let obs = M.findWithDefault [] d (iObs info)
              is <- forM obs $ \(o, _) -> do
                body <- expr info M.empty (fromMaybe UnitLit (lookup o bs)) (pure . Ret)
                liftFun info (Fun (f ++ "." ++ o) ["%self"] (length obs) [] [] True body)
              pure (i, f, is)
            _ -> unsupported ("top-level definition " ++ f ++ " that is neither a λ nor a cocase")
          m <- expr info M.empty main (pure . Ret)
          pure (statics, Fun "main" [] 1 [] [] False m)
      )
      (LS 0 M.empty S.empty Nothing M.empty)
  let ptrs = lsPtrs s
  pure (LProg (M.map (refcount ptrs) (lsFuns s)) statics (refcount ptrs mainF) (lsLocs s))
  where
    isLam e = case e of
      Lam {} -> True
      LLam {} -> True
      _ -> False

-- | The leading parameters of a definition (at most 7: they are passed in registers).
lams :: Term -> ([(String, Ty)], Term)
lams = go []
  where
    go ps tm | length ps == 7 = (reverse ps, tm)
    go ps (Lam x t b) = go ((x, t) : ps) b
    go ps (LLam x t b) = go ((x, t) : ps) b
    go ps tm = (reverse ps, tm)

-- | The head of an application and its arguments in order.
spine :: Term -> (Term, [Term])
spine (App f a) = let (h, as) = spine f in (h, as ++ [a])
spine t = (t, [])

-- | A top-level λ keeps its definition's index; its static block is its closure.
topLam :: Info -> Int -> String -> String -> Ty -> Term -> M (Int, String, [Int])
topLam info i f x t b = do
  x' <- newVar x t
  body <- expr info (M.singleton x (x', t)) b (pure . Ret)
  -- Its block is static, so it never drops it.
  modify (\s -> s {lsFuns = M.insert i (Fun f [x'] 1 [] [] False body) (lsFuns s)})
  pure (i, f, [i])

-- | Locals in scope: source name ↦ (IR name, type).
type Env = M.Map String (String, Ty)

-- | CPS-style ANF conversion: @k@ receives an atom for the value of the term.
expr :: Info -> Env -> Term -> (Atom -> M Expr) -> M Expr
expr info env tm k = case tm of
  -- The position holds while the term is lowered; the continuation gets the outer one back.
  At p e -> do
    outer <- gets lsPos
    modify (\s -> s {lsPos = Just p})
    expr info env e $ \v -> modify (\s -> s {lsPos = outer}) >> k v
  Var x
    | Just (x', _) <- M.lookup x env -> k (AVar x')
    | otherwise -> k (maybe (AVar x) (AGlobal . fst) (M.lookup x (iGlobals info)))
  UnitLit -> k (AInt 0)
  BoolLit b -> k (AInt (if b then 1 else 0))
  IntLit _ n -> k (AInt n)
  Prim op a b -> case typeOf info env a of
    TInt it -> sub a $ \va -> sub b $ \vb -> bindRhs (RPrim op it va vb)
    t -> lift (Left ("arithmetic on " ++ prettyTy t))
  Convert to e -> sub e $ \v -> bindRhs (RConv to v)
  ArrayPrim op t args -> subs args $ \vs -> bindRhs (RArray op (isPtr t) vs)
  -- let x = y: x is another name for y, not a second reference (which would cost a dup and a
  -- drop around every use, e.g. an inlined array.length xs).
  Let x e b | Var y <- stripAt e, Just y' <- M.lookup y env -> expr info (M.insert x y' env) b k
  Let x e b -> sub e $ \v -> do
    let t = typeOf info env e
    x' <- newVar x t
    Bind x' (RAtom v) <$> expr info (M.insert x (x', t) env) b k
  If c a b -> sub c $ \vc -> do
    x <- newVar "if" ty
    ea <- branch env a
    eb <- branch env b
    BindIf x vc ea eb <$> k (AVar x)
  Lam x t b -> closure x t b k
  LLam x t b -> closure x t b k
  -- f a₁ … aₙ with all of a multi-parameter definition's arguments: one direct call.
  App _ _
    | (Var g, args) <- spine tm
    , not (M.member g env)
    , Just (i, n) <- M.lookup g (iUncurried info)
    , length args == n ->
        subs args $ \vs -> bindRhs (RCallKnown i vs)
  App (Var g) a
    | Just (i, _) <- M.lookup g (iGlobals info)
    , g `S.member` iKnown info
    , not (M.member g env) ->
        sub a $ \va -> bindRhs (RCallKnown i [va])
  App f a -> sub f $ \vf -> sub a $ \va -> bindRhs (RCall vf va)
  Con c _ args -> do
    (tag, _, _) <- con c
    bm <- bitmap 1 (map (isPtr . typeOf info env) args)
    subs args $ \vs -> bindRhs (RAlloc tag bm vs)
  Case e alts -> sub e $ \ve -> do
    x <- newVar "case" ty
    let tys = case typeOf info env e of
          TData _ as -> as
          _ -> []
    bs <- forM alts $ \(c, xs, b) -> do
      (tag, d, fields) <- con c
      let inst = substTy (M.fromList (zip (M.findWithDefault [] d (iParams info)) tys)) M.empty
          fts = map inst fields
      xs' <- mapM (uncurry newVar) (zip xs fts)
      let env' = M.union (M.fromList (zip xs (zip xs' fts))) env
      body <- expr info env' b (pure . Ret)
      pure (tag, 1 + length fields, foldr (\(i, y) rest -> Bind y (RField ve i) rest) body (zip [0 ..] xs'))
    BindCase x ve (sortOn (\(t, _, _) -> t) bs) <$> k (AVar x)
  Box e -> expr info env e k
  Unbox e -> expr info env e k
  Pair a b -> do
    bm <- bitmap 1 (map (isPtr . typeOf info env) [a, b])
    subs [a, b] $ \vs -> bindRhs (RAlloc 0 bm vs)
  LetPair x y e b -> sub e $ \ve -> do
    let (tx, tyy) = case typeOf info env e of
          TPair p q -> (p, q)
          _ -> (TUnit, TUnit)
    x' <- newVar x tx
    y' <- newVar y tyy
    rest <- expr info (M.insert x (x', tx) (M.insert y (y', tyy) env)) b k
    pure (Bind x' (RField ve 0) (Bind y' (RField ve 1) rest))
  Cocase d _ bs -> do
    let obs = M.findWithDefault [] d (iObs info)
        ordered = [fromMaybe UnitLit (lookup o bs) | (o, _) <- obs]
        captured = [(v, ir, t) | v <- S.toList (S.unions (map freeVars ordered)), Just (ir, t) <- [M.lookup v env]]
        fvs = [ir | (_, ir, _) <- captured]
        base = length obs
        envB = M.fromList [(v, (ir, t)) | (v, ir, t) <- captured]
    is <- forM (zip obs ordered) $ \((o, _), e) -> do
      body <- expr info envB e (pure . Ret)
      liftFun info (Fun (d ++ "." ++ o) ["%self"] base fvs (ptrsOf captured) True body)
    bm <- bitmap base [isPtr t | (_, _, t) <- captured]
    bindRhs (RCodata is fvs bm)
  Proj e o -> sub e $ \ve -> case typeOf info env e of
    TData d _ | Just i <- elemIndex o (map fst (M.findWithDefault [] d (iObs info))) -> bindRhs (RProj ve i)
    t -> lift (Left ("observation " ++ o ++ " on " ++ prettyTy t))
  Perform op a -> case M.lookup op (iOps info) of
    Just (n, _, _) -> sub a $ \va -> bindRhs (RPerform n va)
    Nothing -> lift (Left ("unknown operation " ++ op))
  -- Clauses become closures in a frame pushed for the body and popped after it.
  Handle _ body cs -> clauses cs []
    where
      clauses [] acc = do
        bm <- bitmap 0 (False : False : concat [[False, True] | _ <- acc])
        fr <- newVar "frame" (TData "%frame" [])
        rest <- expr info env body $ \v -> do
          u <- newVar "pop" TUnit
          Bind u (RPopHandler (AVar fr)) <$> k v
        pure (Bind fr (RPushHandler (reverse acc) bm) rest)
      clauses ((op, x, e) : more) acc = case M.lookup op (iOps info) of
        Just (n, ta, _) -> closure x ta e $ \cv -> clauses more ((n, cv) : acc)
        Nothing -> lift (Left ("unknown operation " ++ op))
  _ -> unsupported (takeWhile (/= ' ') (show tm))
  where
    ty = typeOf info env tm
    sub e = expr info env e
    subs es kk = go es []
      where
        go [] acc = kk (reverse acc)
        go (e : rest) acc = sub e $ \v -> go rest (v : acc)

    branch env' e = expr info env' e (pure . Ret)

    bindRhs rhs = do
      x <- newVar "t" ty
      modify (\s -> s {lsLocs = maybe id (M.insert x) (lsPos s) (lsLocs s)})
      Bind x rhs <$> k (AVar x)

    con c = maybe (lift (Left ("unknown constructor " ++ c))) pure (M.lookup c (iCons info))

    ptrsOf captured = [ir | (_, ir, t) <- captured, isPtr t]

    -- Lift the λ to a numbered function capturing its free locals; @kk@ gets the closure.
    closure x t b kk = do
      let captured = [(v, ir, vt) | v <- S.toList (S.delete x (freeVars b)), Just (ir, vt) <- [M.lookup v env]]
          fvs = [ir | (_, ir, _) <- captured]
      x' <- newVar x t
      let env' = M.insert x (x', t) (M.fromList [(v, (ir, vt)) | (v, ir, vt) <- captured])
      body <- expr info env' b (pure . Ret)
      i <- liftFun info (Fun ("λ" ++ x) [x'] 1 fvs (ptrsOf captured) True body)
      bm <- bitmap 1 [isPtr vt | (_, _, vt) <- captured]
      c <- newVar "clo" (TFun t S.empty TUnit)
      Bind c (RClosure i fvs bm) <$> kk (AVar c)

-- | The type of a well-typed term (effects omitted: lowering doesn't need them).
typeOf :: Info -> Env -> Term -> Ty
typeOf info env tm = case tm of
  At _ e -> go e
  Var x -> fromMaybe TUnit ((snd <$> M.lookup x env) <|> (snd <$> M.lookup x (iGlobals info)))
  UnitLit -> TUnit
  BoolLit _ -> TBool
  IntLit t _ -> TInt t
  Prim Eq _ _ -> TBool
  Prim Lt _ _ -> TBool
  Prim (Arith Optional _) a _ -> TData "Option" [go a]
  Prim _ a _ -> go a
  ArrayPrim op t _ -> let (_, r, _) = arrayOpType op t in r
  Convert to _ -> TInt to
  If _ a _ -> go a
  Lam x t b -> TFun t S.empty (typeOf info (M.insert x (x, t) env) b)
  LLam x t b -> TLFun t S.empty (typeOf info (M.insert x (x, t) env) b)
  App f _ -> case go f of
    TFun _ _ r -> r
    TLFun _ _ r -> r
    _ -> TUnit
  Let x e b -> typeOf info (M.insert x (x, go e) env) b
  Con c tys _ -> case M.lookup c (iCons info) of
    Just (_, d, _) -> TData d tys
    Nothing -> TUnit
  Case e ((c, xs, b) : _) -> case (go e, M.lookup c (iCons info)) of
    (TData _ tys, Just (_, d, fields)) ->
      let inst = substTy (M.fromList (zip (M.findWithDefault [] d (iParams info)) tys)) M.empty
       in typeOf info (M.union (M.fromList [(x, (x, inst f)) | (x, f) <- zip xs fields]) env) b
    _ -> TUnit
  Box e -> TBox (go e)
  Unbox e -> case go e of
    TBox t -> t
    t -> t
  Pair a b -> TPair (go a) (go b)
  LetPair x y e b -> case go e of
    TPair p q -> typeOf info (M.insert x (x, p) (M.insert y (y, q) env)) b
    _ -> TUnit
  Cocase d tys _ -> TData d tys
  Proj e o -> case go e of
    TData d tys
      | Just t <- lookup o (M.findWithDefault [] d (iObs info)) ->
          substTy (M.fromList (zip (M.findWithDefault [] d (iParams info)) tys)) M.empty t
    _ -> TUnit
  Perform op _ -> maybe TUnit (\(_, _, r) -> r) (M.lookup op (iOps info))
  Handle _ e _ -> go e
  _ -> TUnit
  where
    go = typeOf info env

-- | Free variables of a term (locals and globals alike; callers keep the locals).
freeVars :: Term -> S.Set String
freeVars tm = case tm of
  Var x -> S.singleton x
  Lam x _ b -> S.delete x (freeVars b)
  LLam x _ b -> S.delete x (freeVars b)
  Let x e b -> freeVars e <> S.delete x (freeVars b)
  LetPair x y e b -> freeVars e <> (freeVars b S.\\ S.fromList [x, y])
  Case e alts -> freeVars e <> S.unions [freeVars b S.\\ S.fromList xs | (_, xs, b) <- alts]
  Handle _ e cs -> freeVars e <> S.unions [S.delete x (freeVars b) | (_, x, b) <- cs]
  _ -> S.unions (map freeVars (children tm))

-- Reference counting (spec/memory.md) ------------------------------------------------------

-- | Insert dup/drop so every pointer is owned exactly once: a variable is duplicated before
-- each use that consumes it except the last, and dropped right after its last use. A case
-- scrutinee that dies in a branch which then allocates a block of the same size becomes a
-- reuse token: if it was unique, that allocation happens in place.
refcount :: S.Set String -> Fun -> Fun
refcount ptrs f = f {funBody = evalState (go owned0 S.empty M.empty (funBody f)) 0}
  where
    isP v = v `S.member` ptrs
    owned0 = S.fromList (filter isP (funParams f ++ funEnvPtrs f))

    go :: S.Set String -> S.Set String -> M.Map String Int -> Expr -> State Int Expr
    go scope keep reuse e = case e of
      Ret a -> do
        let used = filter isP (atomVars a)
            drops = [v | v <- S.toList scope, v `S.notMember` keep, v `notElem` used]
            dups = [v | v <- used, v `S.member` keep]
        pure (foldr Drop (foldr Dup (Ret a) dups) drops)
      Bind x rhs rest -> do
        let cons = filter isP (consumed rhs)
            bor = filter isP (borrowed rhs)
            live = S.filter isP (fv rest) <> keep
            count v = length (filter (== v) cons)
            dups = concat [replicate (count v - 1 + fromEnum (v `S.member` live)) v | v <- nub cons]
            dyingUnused = [v | v <- S.toList scope, count v == 0, v `notElem` bor, v `S.notMember` live]
            dyingBorrowed = [v | v <- nub bor, v `S.member` scope, v `S.notMember` live]
            consumedDead = [v | v <- nub cons, v `S.notMember` live]
            gone = S.fromList (dyingUnused ++ dyingBorrowed ++ consumedDead)
            scope' = (scope S.\\ gone) <> pointer x
        rest' <- go scope' keep reuse rest
        afterDrops <- foldM (flip (dropOrReuse reuse)) rest' (reverse dyingBorrowed)
        let after = case rhs of
              RField _ _ | isP x -> Dup x afterDrops -- a field read is borrowed: own it
              RArray AGet _ _ | isP x -> Dup x afterDrops
              _ -> afterDrops
        stmt <- foldM (flip (dropOrReuse reuse)) (Bind x rhs after) (reverse dyingUnused)
        pure (foldr Dup stmt dups)
      BindIf x c a b rest -> do
        let keepBr = S.filter isP (fv rest) <> keep
        a' <- go scope keepBr reuse a
        b' <- go scope keepBr reuse b
        rest' <- go (S.intersection scope keepBr <> pointer x) keep reuse rest
        pure (BindIf x c a' b' rest')
      BindCase x s brs rest -> do
        let keepBr = S.filter isP (fv rest) <> keep
            reusable w = case s of
              AVar v | isP v, v `S.notMember` keepBr -> M.insert v w reuse
              _ -> reuse
        brs' <- forM brs $ \(tag, w, body) -> (tag,w,) <$> go scope keepBr (reusable w) body
        rest' <- go (S.intersection scope keepBr <> pointer x) keep reuse rest
        pure (BindCase x s brs' rest')
      _ -> pure e -- Dup/Drop only appear after this pass

    pointer x = if isP x then S.singleton x else S.empty

    -- Drop v before @e@, or turn it into a reuse token for the first same-size allocation in
    -- @e@'s straight-line code.
    dropOrReuse reuse v e = case M.lookup v reuse of
      Just w -> do
        n <- get
        put (n + 1)
        let tok = "%tok" ++ show n
        pure $ case useToken tok w e of
          Just e' -> DropReuse v tok e'
          Nothing -> Drop v e
      Nothing -> pure (Drop v e)

-- | Rewrite the first allocation of @w@ words in the straight-line part of an expression to
-- use the token.
useToken :: String -> Int -> Expr -> Maybe Expr
useToken tok w e = case e of
  Bind x (RAlloc tag bm as) rest | 1 + length as == w -> Just (Bind x (RAllocAt tok tag bm as) rest)
  Bind x rhs rest -> Bind x rhs <$> useToken tok w rest
  Dup v rest -> Dup v <$> useToken tok w rest
  Drop v rest -> Drop v <$> useToken tok w rest
  DropReuse v t rest -> DropReuse v t <$> useToken tok w rest
  _ -> Nothing

atomVars :: Atom -> [String]
atomVars (AVar v) = [v]
atomVars _ = []

-- | Variables whose reference a right-hand side takes over.
consumed :: Rhs -> [String]
consumed rhs = case rhs of
  RAtom a -> atomVars a
  RCall f a -> atomVars f ++ atomVars a
  RCallKnown _ as -> concatMap atomVars as
  RClosure _ fvs _ -> fvs
  RCodata _ fvs _ -> fvs
  RProj a _ -> atomVars a
  RAlloc _ _ as -> concatMap atomVars as
  RAllocAt _ _ _ as -> concatMap atomVars as
  RPushHandler cs _ -> concatMap (atomVars . snd) cs
  RPopHandler a -> atomVars a
  RPerform _ a -> atomVars a
  RArray op _ as -> concatMap atomVars (if op `elem` [ALength, AGet] then drop 1 as else as)
  _ -> []

-- | Variables a right-hand side only reads.
borrowed :: Rhs -> [String]
borrowed (RField a _) = atomVars a
borrowed (RArray op _ (a : _)) | op `elem` [ALength, AGet] = atomVars a
borrowed _ = []

-- | Variables used anywhere in an expression (names are unique, so no shadowing to track).
fv :: Expr -> S.Set String
fv e = case e of
  Ret a -> S.fromList (atomVars a)
  Bind _ rhs rest -> S.fromList (consumed rhs ++ borrowed rhs) <> fv rest
  BindIf _ c a b rest -> S.fromList (atomVars c) <> fv a <> fv b <> fv rest
  BindCase _ s brs rest -> S.fromList (atomVars s) <> S.unions [fv b | (_, _, b) <- brs] <> fv rest
  Dup v rest -> S.insert v (fv rest)
  Drop v rest -> S.insert v (fv rest)
  DropReuse v _ rest -> S.insert v (fv rest)
