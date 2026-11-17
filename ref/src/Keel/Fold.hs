-- | Identical code folding on the lowered IR ("Keel.Lower"): merges functions whose
-- alpha-normalized bodies, signatures and referenced equivalence classes agree.
module Keel.Fold (fold) where

import Control.Monad.Trans.State.Strict (State, get, modify', put, runState)
import Data.IntMap.Strict qualified as IM
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Keel.Lower
import Keel.Syntax (ArrayOp (..), ArithOp (..), BitOp (..), FloatOp (..), IntTy, Overflow (..), Prim (..), interruptDef)

type VarKey = (Int, Bool)

data KAtom
  = KAInt Integer
  | KAVar VarKey
  | KAGlobal Int
  | KANullary Integer
  | KAStatic Int
  deriving (Eq, Ord)

data KRhs
  = KRAtom KAtom
  | KRPrim (Int, Int, Int) IntTy KAtom KAtom
  | KRCall KAtom KAtom
  | KRCallKnown [KAtom]
  | KRClosure [VarKey] Integer
  | KRCodata Int [VarKey] Integer
  | KRProj KAtom Int
  | KRAlloc Integer (Maybe KAtom) [KAtom]
  | KRAllocAt VarKey Integer (Maybe KAtom) [KAtom]
  | KRField KAtom Int
  | KRRel KAtom Int
  | KRHeader KAtom Bool
  | KRPushHandler [(Int, KAtom)] Integer
  | KRPopHandler KAtom
  | KRPerform Int KAtom
  | KRPerform2 Int Integer KAtom KAtom
  | KRCell KAtom (Maybe KAtom)
  | KRConv IntTy KAtom
  | KRFPrim (Int, Int, Int) KAtom KAtom
  | KRFOfInt IntTy KAtom
  | KRFloat (Int, Maybe IntTy, String) [KAtom]
  | KRArray Int (Int, Bool) [KAtom]
  | KRArena Bool
  | KRIndex KAtom KAtom (Int, Bool)
  | KRJoin KAtom KAtom
  deriving (Eq, Ord)

data KExpr
  = KRet KAtom
  | KBind VarKey KRhs KExpr
  | KBindIf VarKey KAtom KExpr KExpr KExpr
  | KBindCase VarKey KAtom [(Integer, Int, KExpr)] KExpr
  | KDup VarKey KExpr
  | KDrop VarKey KExpr
  | KDropReuse VarKey Integer VarKey KExpr
  deriving (Eq, Ord)

data KFun = KFun [VarKey] Int [VarKey] [VarKey] Bool KExpr
  deriving (Eq, Ord)

kOverflow :: Overflow -> Int
kOverflow ov = case ov of
  Checked -> 0
  Wrap -> 1
  Saturate -> 2
  Optional -> 3

kArithOp :: ArithOp -> Int
kArithOp op = case op of
  Add -> 0
  Sub -> 1
  Mul -> 2
  Div -> 3
  Rem -> 4

kBitOp :: BitOp -> Int
kBitOp op = case op of
  And -> 0
  Or -> 1
  Xor -> 2
  Shl -> 3
  Shr -> 4

kPrim :: Prim -> (Int, Int, Int)
kPrim p = case p of
  Arith ov op -> (0, kOverflow ov, kArithOp op)
  Bits op -> (1, kBitOp op, 0)
  Eq -> (2, 0, 0)
  Lt -> (3, 0, 0)

kFloatOp :: FloatOp -> (Int, Maybe IntTy, String)
kFloatOp op = case op of
  FOfInt -> (0, Nothing, "")
  FToInt it -> (1, Just it, "")
  FSqrt -> (2, Nothing, "")
  FToBits -> (3, Nothing, "")
  FFromBits -> (4, Nothing, "")
  FLibm s -> (5, Nothing, s)
  FGe -> (6, Nothing, "")

kArrayOp :: ArrayOp -> Int
kArrayOp op = case op of
  AEmpty -> 0
  ANew -> 1
  ALength -> 2
  AGet -> 3
  ASet -> 4
  APush -> 5
  APop -> 6
  AArena -> 7

kElem :: Elem -> (Int, Bool)
kElem e = case e of
  ENarrow sgn -> (0, sgn)
  EWord -> (1, False)
  EPtr -> (2, False)

data NormState = NormState
  { nsNext :: !Int
  , nsVars :: !(M.Map String Int)
  , nsRefs :: [Int]
  }

type Norm = State NormState

normFun :: S.Set String -> Fun -> (KFun, [Int])
normFun wide f =
  let (kf, st) = runState go (NormState 0 M.empty [])
   in (kf, reverse (nsRefs st))
  where
    go = do
      ps <- mapM normVar (funParams f)
      env <- mapM normVar (funEnv f)
      ptrs <- mapM normVar (funEnvPtrs f)
      body <- normExpr (funBody f)
      pure (KFun ps (funEnvBase f) env ptrs (funDropsSelf f) body)

    normVar :: String -> Norm VarKey
    normVar v = do
      st <- get
      n <- case M.lookup v (nsVars st) of
        Just n -> pure n
        Nothing -> do
          let n = nsNext st
          put st {nsNext = n + 1, nsVars = M.insert v n (nsVars st)}
          pure n
      pure (n, S.member v wide)

    addRef :: Int -> Norm ()
    addRef i = modify' (\st -> st {nsRefs = i : nsRefs st})

    normAtom :: Atom -> Norm KAtom
    normAtom a = case a of
      AInt k -> pure (KAInt k)
      AVar v -> KAVar <$> normVar v
      AGlobal i -> pure (KAGlobal i)
      ANullary n -> pure (KANullary n)
      AStatic i -> pure (KAStatic i)

    normRhs :: Rhs -> Norm KRhs
    normRhs r = case r of
      RAtom a -> KRAtom <$> normAtom a
      RPrim p it a b -> KRPrim (kPrim p) it <$> normAtom a <*> normAtom b
      RCall f' a -> KRCall <$> normAtom f' <*> normAtom a
      RCallKnown i as -> addRef i >> KRCallKnown <$> mapM normAtom as
      RClosure i fvs lid -> addRef i >> KRClosure <$> mapM normVar fvs <*> pure lid
      RCodata is fvs lid -> mapM_ addRef is >> KRCodata (length is) <$> mapM normVar fvs <*> pure lid
      RProj a i -> KRProj <$> normAtom a <*> pure i
      RAlloc lid mh as -> KRAlloc lid <$> mapM normAtom mh <*> mapM normAtom as
      RAllocAt tok lid mh as -> KRAllocAt <$> normVar tok <*> pure lid <*> mapM normAtom mh <*> mapM normAtom as
      RField a i -> KRField <$> normAtom a <*> pure i
      RRel a i -> KRRel <$> normAtom a <*> pure i
      RHeader a sgn -> KRHeader <$> normAtom a <*> pure sgn
      RPushHandler cs lid -> KRPushHandler <$> mapM (\(op, a) -> (op,) <$> normAtom a) cs <*> pure lid
      RPopHandler a -> KRPopHandler <$> normAtom a
      RPerform op a -> KRPerform op <$> normAtom a
      RPerform2 op lid a b -> KRPerform2 op lid <$> normAtom a <*> normAtom b
      RCell k mv -> KRCell <$> normAtom k <*> mapM normAtom mv
      RConv it a -> KRConv it <$> normAtom a
      RFPrim p a b -> KRFPrim (kPrim p) <$> normAtom a <*> normAtom b
      RFOfInt it a -> KRFOfInt it <$> normAtom a
      RFloat op as -> KRFloat (kFloatOp op) <$> mapM normAtom as
      RArray op el as -> KRArray (kArrayOp op) (kElem el) <$> mapM normAtom as
      RArena open -> pure (KRArena open)
      RIndex a i el -> KRIndex <$> normAtom a <*> normAtom i <*> pure (kElem el)
      RJoin lo hi -> KRJoin <$> normAtom lo <*> normAtom hi

    normExpr :: Expr -> Norm KExpr
    normExpr e = case e of
      Ret a -> KRet <$> normAtom a
      Bind x rhs rest -> KBind <$> normVar x <*> normRhs rhs <*> normExpr rest
      BindIf x c a b rest -> KBindIf <$> normVar x <*> normAtom c <*> normExpr a <*> normExpr b <*> normExpr rest
      BindCase x sc bs rest ->
        KBindCase
          <$> normVar x
          <*> normAtom sc
          <*> mapM (\(tag, n, b) -> (tag,n,) <$> normExpr b) bs
          <*> normExpr rest
      Dup v rest -> KDup <$> normVar v <*> normExpr rest
      Drop v rest -> KDrop <$> normVar v <*> normExpr rest
      DropReuse v mask tok rest -> KDropReuse <$> normVar v <*> pure mask <*> normVar tok <*> normExpr rest

-- | Assign dense class numbers 0, 1, ... to items grouped by key.
stepAssign :: (Ord k) => [(Int, k)] -> (Int, IM.IntMap Int)
stepAssign items =
  let (nextC, _, pairs) = foldl' go (0, M.empty, []) items
      go (!n, !seen, !acc) (fid, k) = case M.lookup k seen of
        Just c -> (n, seen, (fid, c) : acc)
        Nothing -> (n + 1, M.insert k n seen, (fid, n) : acc)
   in (nextC, IM.fromList pairs)

-- | Merge identical functions in a lowered program (except @interruptDef@ and @lMain@).
fold :: LProg -> LProg
fold lp
  | M.null funs = lp
  | numC0 == M.size funs = lp
  | numFinal == M.size funs = lp
  | otherwise =
      lp
        { lFuns = M.fromList [(fid, f {funBody = rewriteExpr (funBody f)}) | (fid, f) <- funList, rep fid == fid]
        , lMain = (lMain lp) {funBody = rewriteExpr (funBody (lMain lp))}
        , lStatics = [(i, name, map rep fs) | (i, name, fs) <- lStatics lp]
        }
  where
    funs = lFuns lp
    funList = M.toList funs
    wide = lWide lp

    prepared =
      [ if funName f == interruptDef
          then (fid, Left fid, [])
          else let (kf, refs) = normFun wide f in (fid, Right kf, refs)
      | (fid, f) <- funList
      ]

    (numC0, classMap0) = stepAssign [(fid, k) | (fid, k, _) <- prepared]
    funRefs = [(fid, refs) | (fid, _, refs) <- prepared]

    (numFinal, finalClasses) = refine numC0 classMap0

    refine numC classMap
      | numC == M.size funs = (numC, classMap)
      | otherwise =
          let items =
                [ (fid, (classMap IM.! fid, map (\r -> IM.findWithDefault (-1 - r) r classMap) refs))
                | (fid, refs) <- funRefs
                ]
              (numC', classMap') = stepAssign items
           in if numC' == numC then (numC, classMap) else refine numC' classMap'

    repOfClass = IM.fromListWith min [(c, fid) | (fid, c) <- IM.toList finalClasses]
    repMap = IM.map (repOfClass IM.!) finalClasses
    rep fid = IM.findWithDefault fid fid repMap

    rewriteRhs r = case r of
      RAtom _ -> r
      RPrim {} -> r
      RCall _ _ -> r
      RCallKnown i as -> RCallKnown (rep i) as
      RClosure i fvs lid -> RClosure (rep i) fvs lid
      RCodata is fvs lid -> RCodata (map rep is) fvs lid
      RProj _ _ -> r
      RAlloc {} -> r
      RAllocAt {} -> r
      RField _ _ -> r
      RRel _ _ -> r
      RHeader _ _ -> r
      RPushHandler _ _ -> r
      RPopHandler _ -> r
      RPerform _ _ -> r
      RPerform2 {} -> r
      RCell _ _ -> r
      RConv _ _ -> r
      RFPrim {} -> r
      RFOfInt _ _ -> r
      RFloat _ _ -> r
      RArray {} -> r
      RArena _ -> r
      RIndex {} -> r
      RJoin {} -> r

    rewriteExpr e = case e of
      Ret _ -> e
      Bind x rhs rest -> Bind x (rewriteRhs rhs) (rewriteExpr rest)
      BindIf x c a b rest -> BindIf x c (rewriteExpr a) (rewriteExpr b) (rewriteExpr rest)
      BindCase x sc bs rest -> BindCase x sc [(tag, n, rewriteExpr b) | (tag, n, b) <- bs] (rewriteExpr rest)
      Dup v rest -> Dup v (rewriteExpr rest)
      Drop v rest -> Drop v (rewriteExpr rest)
      DropReuse v mask tok rest -> DropReuse v mask tok (rewriteExpr rest)
