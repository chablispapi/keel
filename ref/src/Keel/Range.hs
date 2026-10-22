-- | Range analysis on the lowered IR (M4, spec/perf.md): removes the overflow checks of
-- @+ - *@ that can't overflow, and the bounds checks of @array.get@ whose index is in bounds.
--
-- Facts are intervals of integers and relations @a ≤ b@, @a < b@, @a ≠ b@ between variables,
-- constants and array lengths, learned from arithmetic, from the branches of comparisons, and
-- from the parameters' invariants. An invariant is a candidate (@0 ≤ p@, @p ≤ k@ or @k ≤ p@
-- for a constant p is compared with, @p ≤ length q@) that holds at every call: the functions
-- only called directly start with all their candidates, and those some call can't prove are
-- dropped until the rest hold (Houdini). So @i@ in a loop @if i == length xs then … else
-- … get xs i … f (i + 1)@ is known to satisfy @0 ≤ i ≤ length xs@.
--
-- Every IR variable is bound once, and an array's length is fixed for the variable holding it,
-- so a fact stays true wherever its variables are in scope.
module Keel.Range (ranges) where

import Control.Monad.Trans.State.Strict (State, modify, runState)
import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe)
import Data.Set qualified as S
import Keel.Lower
import Keel.Syntax

-- | An integer: a constant, a variable or the length of the array a variable holds.
data Tm = K Integer | V String | Len String
  deriving (Eq, Ord, Show)

type Iv = (Maybe Integer, Maybe Integer) -- Nothing: unbounded

data Facts = Facts
  { fAlias :: M.Map String Tm
  , fIv :: M.Map String Iv
  , fRel :: [(Tm, Tm, Bool)] -- a ≤ b, or a < b when True
  , fNeq :: [(Tm, Tm)]
  , fCond :: M.Map String (Prim, Tm, Tm) -- booleans holding a comparison
  }

-- | An array's elements are words in a 64-bit address space.
maxLen :: Integer
maxLen = 2 ^ (61 :: Int)

ranges :: LProg -> LProg
ranges lp = lp {lFuns = M.mapWithKey (\i f -> f {funBody = fst (walk (entry i f) (funBody f))}) (lFuns lp), lMain = (lMain lp) {funBody = fst (walk none (funBody (lMain lp)))}}
  where
    funs = lFuns lp
    referenced = S.fromList (concatMap (closureRefs . funBody) (lMain lp : M.elems funs))
    reachable = reachableFuns funs (lStatics lp) (lMain lp)
    callers = (-1, lMain lp) : [(i, f) | (i, f) <- M.toList funs, i `S.member` reachable]
    invs = houdini (M.fromList [(i, candidates f) | (i, f) <- M.toList funs, i `S.notMember` referenced, null (funEnv f)])
    entry = entryWith invs
    entryWith cs i _ = none {fRel = [(a, b, False) | (a, b) <- M.findWithDefault [] i cs]}
    houdini cs =
      let obls = concat [snd (snd (walk (entryWith cs i f) (funBody f))) | (i, f) <- callers]
          cs' = M.mapWithKey (\j ps -> [c | c <- ps, all (holds j c) [o | o@(j', _, _) <- obls, j' == j]]) cs
          holds j (a, b) (_, fs, args) =
            let sub t = case t of
                  V p -> atomTm fs <$> lookup p (zip (params j) args)
                  Len p -> case lookup p (zip (params j) args) of
                    Just (AVar v) | V w <- norm fs v -> Just (Len w)
                    _ -> Nothing
                  _ -> Just t
             in maybe False (\(a', b') -> le fs a' b' False) ((,) <$> sub a <*> sub b)
       in if M.map length cs' == M.map length cs then cs else houdini cs'
    params j = maybe [] funParams (M.lookup j funs)
    -- Candidates from the comparisons in a function's body, over its parameters.
    candidates f =
      let ps = S.fromList (funParams f)
          isP t = case t of V p -> p `S.member` ps; Len p -> p `S.member` ps; _ -> False
          cmps = fst (snd (walk none (funBody f)))
          fromCmp (a, b) = [(a, b) | isP a || isP b, ok a, ok b] ++ [(b, a) | isP a || isP b, ok a, ok b]
          ok t = isP t || case t of K _ -> True; _ -> False
       in S.toList (S.fromList ([(K 0, V p) | p <- funParams f] ++ concatMap fromCmp cmps))

none :: Facts
none = Facts M.empty M.empty [] [] M.empty

norm :: Facts -> String -> Tm
norm fs v = M.findWithDefault (V v) v (fAlias fs)

atomTm :: Facts -> Atom -> Tm
atomTm fs a = case a of
  AInt k -> K k
  AVar v -> norm fs v
  _ -> V "%other"

-- | The interval of a term: its own, narrowed by the relations to constants and lengths.
iv :: Facts -> Tm -> Iv
iv fs t = shrink (foldl narrow (base t) (fRel fs))
  where
    base u = case u of
      K k -> (Just k, Just k)
      Len _ -> (Just 0, Just maxLen)
      V x -> M.findWithDefault (Nothing, Nothing) x (fIv fs)
    narrow (lo, hi) (a, b, s)
      | a == t, Just h <- snd (base b) = (lo, Just (maybe (h - st) (min (h - st)) hi))
      | b == t, Just l <- fst (base a) = (Just (maybe (l + st) (max (l + st)) lo), hi)
      | otherwise = (lo, hi)
      where
        st = if s then 1 else 0
    shrink (lo, hi)
      | Just l <- lo, neqK l = shrink (Just (l + 1), hi)
      | Just h <- hi, neqK h = shrink (lo, Just (h - 1))
      | otherwise = (lo, hi)
    neqK k = (t, K k) `elem` fNeq fs || (K k, t) `elem` fNeq fs

-- | Whether a ≤ b (a < b when strict) follows from the facts.
le :: Facts -> Tm -> Tm -> Bool -> Bool
le fs a b strict =
  (a == b && not strict)
    || maybe False id ((\h l -> h + s <= l) <$> snd (iv fs a) <*> fst (iv fs b))
    || or [s' || not strict | (a', b', s') <- fRel fs, a' == a, b' == b]
    || (strict && (a, b, False) `elem` fRel fs && ((a, b) `elem` fNeq fs || (b, a) `elem` fNeq fs))
  where
    s = if strict then 1 else 0

typeRange :: IntTy -> Iv
typeRange (IntTy sgn w)
  | sgn = (Just (-(2 ^ (w - 1))), Just (2 ^ (w - 1) - 1))
  | otherwise = (Just 0, Just (2 ^ w - 1))

within :: Iv -> Iv -> Bool
within (lo, hi) (tlo, thi) = maybe False id ((<=) <$> tlo <*> lo) && maybe False id ((<=) <$> hi <*> thi)

-- | Rewrites an expression with the facts it starts from. Also returns the comparisons it
-- makes (for candidates) and the direct calls with the facts at each (for invariants).
walk :: Facts -> Expr -> (Expr, ([(Tm, Tm)], [(Int, Facts, [Atom])]))
walk fs0 e0 = runState (go fs0 e0) ([], [])
  where
    go :: Facts -> Expr -> State ([(Tm, Tm)], [(Int, Facts, [Atom])]) Expr
    go fs e = case e of
      Ret _ -> pure e
      Bind x rhs rest -> do
        case rhs of
          RCallKnown j as -> modify (\(c, o) -> (c, (j, fs, as) : o))
          RPrim op _ a b | op `elem` [Eq, Lt] -> modify (\(c, o) -> ((atomTm fs a, atomTm fs b) : c, o))
          _ -> pure ()
        let (rhs', fs') = bind fs x rhs
        Bind x rhs' <$> go fs' rest
      BindIf x c a b rest -> do
        let (ft, ff) = case c of
              AVar v | Just cond <- M.lookup v (fCond fs) -> branches fs cond
              _ -> (fs, fs)
        BindIf x c <$> go ft a <*> go ff b <*> go fs rest
      BindCase x s bs rest -> BindCase x s <$> mapM (\(t, n, b) -> (,,) t n <$> go fs b) bs <*> go fs rest
      Dup v rest -> Dup v <$> go fs rest
      Drop v rest -> Drop v <$> go fs rest
      DropReuse v t rest -> DropReuse v t <$> go fs rest

-- | The facts in the then and else branches of a comparison.
branches :: Facts -> (Prim, Tm, Tm) -> (Facts, Facts)
branches fs (op, a, b) = case op of
  Eq -> (rel [(a, b, False), (b, a, False)], fs {fNeq = (a, b) : fNeq fs})
  _ -> (rel [(a, b, True)], rel [(b, a, False)])
  where
    rel rs = fs {fRel = rs ++ fRel fs}

-- | What binding x to rhs teaches, and rhs without the checks the facts make unnecessary.
bind :: Facts -> String -> Rhs -> (Rhs, Facts)
bind fs x rhs = case rhs of
  RAtom a | t@(K _) <- atomTm fs a -> (rhs, alias t)
  RAtom (AVar v) -> (rhs, alias (norm fs v))
  RArray ALength _ [AVar a] | V w <- norm fs a -> (rhs, alias (Len w))
  RArray AGet e [arr@(AVar a), i]
    | V w <- norm fs a, let ti = atomTm fs i, le fs (K 0) ti False, le fs ti (Len w) True -> (RIndex arr i e, fs)
  RPrim op _ a b | op `elem` [Eq, Lt] -> (rhs, fs {fCond = M.insert x (op, atomTm fs a, atomTm fs b) (fCond fs)})
  RPrim (Arith ov aop) it a b | aop `elem` [Add, Sub, Mul], ov `elem` [Checked, Wrap] ->
    let ta = atomTm fs a
        tb = atomTm fs b
        r = arith aop (clamp (iv fs ta)) (clamp (iv fs tb))
        -- the operands are values of the type
        clamp (lo, hi) = case typeRange it of
          (Just tlo, Just thi) -> (Just (maybe tlo (max tlo) lo), Just (maybe thi (min thi) hi))
          r' -> r'
        exact = within r (typeRange it)
        rhs' = if exact then RPrim (Arith Wrap aop) it a b else rhs
        fs' = fs {fIv = M.insert x (if exact then r else typeRange it) (fIv fs)}
        -- x = t + k for a constant k: x keeps t's relations, shifted.
        offset = case (aop, ta, tb) of
          (Add, t, K k) -> Just (t, k)
          (Add, K k, t) -> Just (t, k)
          (Sub, t, K k) -> Just (t, -k)
          _ -> Nothing
        shifted = case offset of
          Just (t, k) | exact || ov == Checked ->
            [(V x, u, k < 0 || (k == 0 && s)) | (t', u, _) <- fRel fs, t' == t, let s = le fs t u True, k <= 0 || (k == 1 && s)]
              ++ [(u, V x, k > 0 || (k == 0 && s)) | (u, t', _) <- fRel fs, t' == t, let s = le fs u t True, k >= 0 || (k == -1 && s)]
          _ -> []
     in (rhs', fs' {fRel = shifted ++ fRel fs'})
  RPrim (Bits And) _ a b | Just m <- mask (atomTm fs a) (atomTm fs b) -> (rhs, interval (Just 0, Just m))
  RConv to a -> (rhs, interval (let r = iv fs (atomTm fs a) in if within r (typeRange to) then r else typeRange to))
  _ -> (rhs, fs)
  where
    alias t = fs {fAlias = M.insert x t (fAlias fs)}
    interval r = fs {fIv = M.insert x r (fIv fs)}
    mask p q = case [m | K m <- [p, q], m >= 0] of
      [] -> Nothing
      ms -> Just (minimum ms)

-- | The interval of an exact result.
arith :: ArithOp -> Iv -> Iv -> Iv
arith op (alo, ahi) (blo, bhi) = case op of
  Add -> ((+) <$> alo <*> blo, (+) <$> ahi <*> bhi)
  Sub -> ((-) <$> alo <*> bhi, (-) <$> ahi <*> blo)
  _ -> fromMaybe (Nothing, Nothing) $ do
    ps <- sequence [(*) <$> p <*> q | p <- [alo, ahi], q <- [blo, bhi]]
    pure (Just (minimum ps), Just (maximum ps))
