{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}

module ArgFirst where

import Control.Applicative
import Control.Applicative
import Control.Category
import Control.Lens
import Control.Monad
import Control.Monad.Fail
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Functor.Foldable (Corecursive(..), Fix(..), cata, cataA, para)
import qualified Data.IntMap as I
import qualified Data.List as L
import Data.Maybe
import Data.Monoid
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
eCTwoInt = ELamAnn 0 (TApp TInt TInt) (ELamAnn 1 TInt (EApp (EVar 0) (EApp (EVar 0) (EVar 1))))

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
    go (TApp t t') = TApp (go t) (go t')
    go TInt = TInt
    subs' = over (mapped . _2) (^. re typeMono) subs

-- | Returns s' . s
subcomp :: Subs -> Subs -> Subs
subcomp s s' = [(x, subst s t) | (x, t) <- s']

-- | Returns a substitution that unifies two monotypes
unify :: (Monoid e, MonadError e m) => EMonoType -> EMonoType -> m Subs
unify (MTVar i) t' = pure [(i, t')]
unify t (MTVar i') = pure [(i', t)]
unify t t'
  | t == t' = pure []
  | MTApp t0 t1 <- t
  , MTApp t0' t1' <- t' = do
    s <- unify t0 t0'
    s' <- unify (subst s t1) (subst s t1')
    pure (subcomp s' s)
  | otherwise = throwError mempty

freshVar :: (MonadState Int m) => m Int
freshVar = do
  i <- get
  modify (+ 1)
  pure i

-- efv :: Expr -> [Int]
-- efv _ = _
gftv :: TCtx -> [Int]
gftv = join . over mapped tftv . toListOf (folded . _2) . I.toList

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


-- infer :: Expr -> Maybe EType
-- infer e = maximum 



inferType ::
     (Monoid e, MonadError e m, MonadState Int m, MonadFail m)
  => TCtx
  -> ACtx
  -> Expr
  -> m EType
inferType ctx actx e
  -- T-Var
  | EVar i <- e
  , Just a <- I.lookup i ctx = appSubtype actx a
  -- T-INT
  | EInt i <- e = pure TInt
  -- T-LAM
  | ELam i e' <- e
  , a:actx' <- actx = TApp a <$> inferType (I.insert i a ctx) actx' e'
  -- T-LAM2
  | ELam i e' <- e
  -- guessing a random monotype
   = TApp TInt <$> inferType (I.insert i TInt ctx) actx e'
  -- T-LAMANN1
  | ELamAnn i t e' <- e
  , [] <- actx
  -- T-LAMANN2
   = TApp t <$> inferType (I.insert i t ctx) actx e'
  | ELamAnn i t e' <- e
  , a:actx' <- actx = do
    b <- isSubtype a t
    unless b (throwError mempty)
    TApp a <$> inferType (I.insert i t ctx) actx' e'
  -- T-APP
  | EApp e0 e1 <- e = do
    a <- inferType ctx [] e1
    let b = tgen ctx a
    TApp _ c <- inferType ctx (b : actx) e0
    pure c


isSubtype :: (MonadState Int m) => EType -> EType -> m Bool
isSubtype e0 e1
  -- S-INT
  | TInt <- e0
  , TInt <- e1 = pure True
  -- S-VAR
  | TVar i <- e0
  , TVar i' <- e1 = pure (i == i')
  -- S-FORALLR
  | TForall i e1' <- e1
  , not (L.elem i (tftv e1')) = isSubtype e0 e1'
  -- S-FORALLL
  -- guessing Int
  | TForall i e0' <- e0 = isSubtype (substP [(i, MTInt)] e0') e1
  | TApp t0 t1 <- e0
  , TApp t0' t1' <- e1 = liftA2 (&&) (isSubtype t0' t0) (isSubtype t1 t1')
  | otherwise = pure False

appSubtype ::
     (Monoid e, MonadError e m, MonadState Int m) => ACtx -> EType -> m EType
appSubtype actx t
  -- S-EMPTY
  | [] <- actx = pure t
  -- S-FUN2
  | a:actx' <- actx
  , TApp t0 t1 <- t = do
    b <- isSubtype a t0
    unless b (throwError mempty)
    TApp a <$> appSubtype actx' t1
  -- S-FORALL2
  | _:_ <- actx
  , TForall i t1 <- t = appSubtype actx (substP [(i, MTInt)] t1)
  | otherwise = throwError mempty
