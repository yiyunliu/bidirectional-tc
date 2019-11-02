{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}

module ArgFirst where

import Control.Applicative
import Control.Applicative
import Control.Category
import Control.Lens hiding (para)
import Control.Monad
import Control.Monad.Except
import Control.Monad.Fail
import Control.Monad.Reader
import Control.Monad.State
import Data.Functor.Foldable (Corecursive(..), Fix(..), cata, cataA, para)
import Data.Functor.Foldable.TH
import qualified Data.IntMap as I
import qualified Data.List as L
import Data.Maybe
import Data.Monoid
import Data.Text.Prettyprint.Doc
import Prelude hiding ((.), id)

type Subs = [(Int, EMonoType)]

data Expr
  = EVar Int
  | EInt Integer
  | ELam Int
         Expr
  | ELamAnn Int
            EType
            Expr
  | EApp Expr
         Expr
  deriving (Show, Eq)

data EType
  = TInt
  | TApp EType
         EType
  | TForall Int
            EType
  | TVar Int
  deriving (Show, Eq)

data EMonoType
  = MTInt
  | MTApp EMonoType
          EMonoType
  | MTVar Int
  deriving (Show, Eq)

makeBaseFunctor ''Expr

makeBaseFunctor ''EType

makeBaseFunctor ''EMonoType

instance Pretty EType where
  pretty = para f
    where
      f TIntF = "int"
      f (TAppF (tt, t0) (_, t1))
        | isAtom tt = t0 <+> "->" <+> t1
        | otherwise = enclose "(" ")" t0 <+> "->" <+> t1
      f (TForallF i (_, t)) =
        "∀" <+> ("t" <> pretty i) <+> "." <+> enclose "(" ")" t
      f (TVarF i) = pretty ("t" ++ show i)
      isAtom TInt = True
      isAtom (TVar _) = True
      isAtom _ = False

instance Pretty Expr where
  pretty = cata f
    where
      f (EVarF i) = pretty ("x" ++ show i)
      f (EIntF i) = pretty i
      f (ELamF i e) =
        enclose "(" ")" ("λ" <+> enclose "[" "]" ("x" <> pretty i) <+> e)
      f (ELamAnnF i t e) =
        enclose
          "("
          ")"
          ("λ" <+> enclose "[" "]" ("x" <> pretty i <+> ":" <+> pretty t) <+> e)
      f (EAppF e0 e1) = enclose "(" ")" (e0 <+> e1)

-- | prism that goes back and forth between types and mono types
typeMono :: Prism' EType EMonoType
typeMono = prism' inj proj
  where
    inj MTInt = TInt
    inj (MTApp m0 m1) = TApp (inj m0) (inj m1)
    inj (MTVar i) = TVar i
    proj TInt = Just MTInt
    proj (TApp t0 t1) = MTApp <$> proj t0 <*> proj t1
    proj (TForall _ _) = Nothing
    proj (TVar i) = Just $ MTVar i

-- | Typing Context
type TCtx = I.IntMap EType

-- | Application Context
type ACtx = [EType]

eId :: Expr
eId = ELam 0 (EVar 0)

realId :: Expr
realId = EApp (ELamAnn 0 (TForall 0 (TVar 0)) (EVar 0)) (ELam 0 (EVar 0))

eIdAnn :: Expr
eIdAnn = ELamAnn 0 (TForall 0 (TApp (TVar 0) (TVar 0))) (EVar 0)

-- eIdAnn' :: Expr
-- eIdAnn' = ELamAnn 0 (TForall 0 (TApp (TVar 0) (TVar 0))) (EVar 0)
eIdInt :: Expr
eIdInt = ELamAnn 0 TInt (EVar 0)

-- | Church encoding of 1 and 2
eCOne :: Expr
eCOne = ELam 0 (ELam 1 (EApp (EVar 0) (EVar 1)))

eCTwo :: Expr
eCTwo = ELam 0 (ELam 1 (EApp (EVar 0) (EApp (EVar 0) (EVar 1))))

eCTwoInt :: Expr
eCTwoInt =
  ELamAnn
    0
    (TApp TInt TInt)
    (ELamAnn 1 TInt (EApp (EVar 0) (EApp (EVar 0) (EVar 1))))

subst :: Subs -> EMonoType -> EMonoType
subst subs t = go t
  where
    go t@(MTVar i) = maybe t id (L.lookup i subs)
    go (MTApp t t') = MTApp (go t) (go t')
    go MTInt = MTInt

substP :: Subs -> EType -> EType
substP subs t = go t
  where
    go t@(TVar i) = maybe t id (L.lookup i subs')
    go (TForall i t) =
      TForall i (substP (subs ^.. folded . filtered (^. _1 . to (/= i))) t)
    go (TApp t t') = TApp (go t) (go t')
    go TInt = TInt
    subs' = over (mapped . _2) (^. re typeMono) subs

-- | Returns s' . s
subcomp :: Subs -> Subs -> Subs
subcomp s s' = [(x, subst s t) | (x, t) <- s']

-- -- | Returns a substitution that unifies two monotypes
-- unify :: (Monoid e, MonadError e m) => EMonoType -> EMonoType -> m Subs
-- unify (MTVar i) t' = pure [(i, t')]
-- unify t (MTVar i') = pure [(i', t)]
-- unify t t'
--   | t == t' = pure []
--   | MTApp t0 t1 <- t
--   , MTApp t0' t1' <- t' = do
--     s <- unify t0 t0'
--     s' <- unify (subst s t1) (subst s t1')
--     pure (subcomp s' s)
--   | otherwise = throwError mempty
data InferEnv = IEnv
  { _subs :: Subs
  , _freshCounter :: Int
  } deriving (Show, Eq)

makeLenses ''InferEnv

-- Some monadic predicates
-- | v not in subs
isMetaVar :: MonadState InferEnv m => Int -> m Bool
isMetaVar i = use $ subs . to (lookupOf folded i) . to (isn't _Nothing)

isMetaVarM :: MonadState InferEnv m => Int -> m (Maybe EMonoType)
isMetaVarM i = use $ subs . to (lookupOf folded i)

-- | v == v in subs
isUnboundMetaVar :: MonadState InferEnv m => Int -> m Bool
isUnboundMetaVar i =
  use $ subs . to (lookupOf folded i) . to (anyOf folded (== MTVar i))

-- | occurence check. stricter than the one on SPJ 2007 since I make sure all open variables are fresh
occurCheck :: Int -> EType -> Bool
occurCheck i = elemOf folded i . tftv

unifyFunc :: Int -> EType -> EType -> Subs -> Maybe Subs
unifyFunc fc t0 t1 s = evalStateT (unify t0 t1 >> use subs) (IEnv s fc)

utestt0 = TApp (TApp (TVar 0) (TVar 1)) (TVar 0)

utestt1 = TApp (TVar 2) (TVar 1)

utests :: Subs
utests = [(0, MTVar 0), (1, MTVar 1), (2, MTVar 2), (3, MTVar 3)]

-- | Monadic unification. It doesn't generate new types. Maybe I should refine InferEnv as HasSub
unify ::
     (Monoid e, MonadError e m, MonadState InferEnv m) => EType -> EType -> m ()
unify t0 t1
  -- handles both meta/non-meta cases
  | TInt <- t0
  , TInt <- t1 = pure ()
  | TVar i0 <- t0
  , TVar i1 <- t1
  , t0 == t1 = pure ()
  -- unequal
  | TVar i0 <- t0 =
    isMetaVarM i0 >>= \case
      Just t0'
            -- unbound
        | MTVar i0' <- t0'
        , i0' == i0 -> unifyUnboundVar i0 t1
            -- bound
        | otherwise -> unify (t0' ^. re typeMono) t1
      Nothing
        | TVar i1 <- t1 ->
          isMetaVarM i1 >>= \case
            Just t1'
              | MTVar i1' <- t1'
              , i1' == i1 -> unifyUnboundVar i1 t0
              | otherwise -> unify t0 (t1' ^. re typeMono)
            Nothing -> throwError mempty
        | otherwise -> throwError mempty
  -- invariant: t0 is not a variable
  | TVar i1 <- t1 =
    isMetaVarM i1 >>= \case
      Just t1'
        | MTVar i1' <- t1'
        , i1' == i1 -> unifyUnboundVar i1 t0
        | otherwise -> unify t0 (t1' ^. re typeMono)
          -- can't unify a non-flexible variable
      Nothing -> throwError mempty
  -- invariant: none of t0 t1 is a variable
  | TApp t00 t01 <- t0
  , TApp t10 t11 <- t1 = unify t00 t10 >> unify t01 t11
  | otherwise = throwError mempty

-- invariant: Var is flexible
unifyUnboundVar ::
     (Monoid e, MonadError e m, MonadState InferEnv m) => Int -> EType -> m ()
unifyUnboundVar i0 t1 =
  case occurCheck i0 t1 of
    True -> throwError mempty
    False ->
      case t1 ^? typeMono of
        Just t1' -> subs %= ((i0, t1') :)
        Nothing -> throwError mempty

-- unifyVar i0 t1
--   = isUnboundMetaVar i0 >>=
--     \case
--       True ->
freshVar :: (MonadState InferEnv m) => m Int
freshVar = freshCounter <<+= 1

gftv :: TCtx -> [Int]
gftv -- join . over mapped tftv . toListOf (folded . _2) . I.toList
 = view (to I.toList . folded . _2 . to tftv)

tftv :: EType -> [Int]
tftv t = runReader (act t) []
  where
    act t
      | TVar i <- t = do
        b <- asks (L.elem i)
        pure
          (if b
             then []
             else [i])
      | TApp t0 t1 <- t = liftA2 (++) (act t0) (act t1)
      | TForall i t0 <- t = local (i :) (act t0)
      | otherwise = pure []

-- T-GEN
tgen :: TCtx -> EType -> EType
tgen ctx t = L.foldr TForall t (tftv t L.\\ gftv ctx)
-- -- | alpha conversion for EType
-- refreshBody :: Int -> Int -> EType -> EType
-- refreshBody binder freshId = para f
--   where f TIntF = TInt
--         f (TVarF i)
--           | i == binder
--           = TVar freshId
--           | otherwise
--           = TVar i
--         f (TForallF i (old,e0))
--           | i == binder
--           = TForall i old
--           | otherwise
--           = TForall i e0
--         f (TAppF (_,e0) (_,e1))
--           = TApp e0 e1
-- inferType ::
--      (Monoid e, MonadError e m, MonadState Int m, MonadFail m)
--   => TCtx
--   -> ACtx
--   -> Expr
--   -> m EType
-- inferType ctx actx e
--   -- T-Var
--   | EVar i <- e
--   , Just a <- I.lookup i ctx = appSubtype actx a subs
--   -- T-INT
--   | EInt i <- e = pure (TInt, subs)
--   -- T-LAM
--   | ELam i e' <- e
--   , a:actx' <- actx = over _1 (TApp a) <$> inferType (I.insert i a ctx) actx' e' subs
--   -- T-LAM2
--   | ELam i e' <- e
--   -- guessing a random monotype
--    = do v <- freshVar
--         -- could add a precondition check
--         over _1 (TApp TInt) <$> inferType (I.insert i TInt ctx) actx e' ((v,MTVar v):subs)
--   -- T-LAMANN1
--   | ELamAnn i t e' <- e
--   , [] <- actx
--   -- T-LAMANN2
--    = over _1 (TApp t) <$> inferType (I.insert i t ctx) actx e' subs
--   | ELamAnn i t e' <- e
--   , a:actx' <- actx = do
--     (b, subs') <- isSubtype a t subs
--     unless b (throwError mempty)
--     over _1 (TApp a) <$> inferType (I.insert i t ctx) actx' e' subs'
--   -- T-APP
--   | EApp e0 e1 <- e = do
--     (a, subs') <- inferType ctx [] e1 subs
--     let b = tgen ctx a
--     (TApp _ c, subs'') <- inferType ctx (b : actx) e0 subs'
--     pure (c, subs'')
-- isSubtype :: (MonadState Int m) => EType -> EType -> Subs -> m (Bool, Subs)
-- isSubtype e0 e1 subs
--   -- S-INT
--   | TInt <- e0
--   , TInt <- e1 = pure (True, subs)
--   -- S-VAR
--   | TVar i <- e0
--   , TVar i' <- e1 = pure (i == i', subs)
--   -- S-FORALLR
--   | TForall i e1' <- e1
--   -- This version is wrong
--   -- , not (L.elem i (tftv e1')) = isSubtype e0 e1'
--   -- S-FORALLL
--   -- guessing Int
--   = do a <- freshVar
--        isSubtype e0 e1' subs
--   | TForall i e0' <- e0
--   = isSubtype (substP [(i, MTInt)] e0') e1 subs
--   | TApp t0 t1 <- e0
--   , TApp t0' t1' <- e1 = do
--       (b0, subs') <- isSubtype t0' t0 subs
--       (b1, subs'') <- isSubtype t1 t1' subs
--       pure ((b0 && b1), subs'')
--   | otherwise = pure (False, subs)
-- appSubtype ::
--      (Monoid e, MonadError e m, MonadState Int m) => ACtx -> EType -> Subs -> m (EType, Subs)
-- appSubtype actx t subs
--   -- S-EMPTY
--   | [] <- actx = pure t
--   -- S-FUN2
--   | a:actx' <- actx
--   , TApp t0 t1 <- t = do
--     b <- isSubtype a t0
--     unless b (throwError mempty)
--     TApp a <$> appSubtype actx' t1
--   -- S-FORALL2
--   | _:_ <- actx
--   , TForall i t1 <- t = appSubtype actx (substP [(i, MTInt)] t1)
--   | otherwise = throwError mempty
