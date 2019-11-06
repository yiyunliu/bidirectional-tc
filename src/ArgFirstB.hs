{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}

module ArgFirstB where

import Bound
import Control.Lens hiding (para)
import Control.Monad.Except
import Control.Monad.State
import Data.Eq.Deriving (deriveEq1) -- these two are from the
import Data.Functor.Foldable.TH
import qualified Data.IntMap as I
import qualified Data.IntSet as IS
import qualified Data.List as L
import Text.Show.Deriving (deriveShow1) -- deriving-compat package

-- import Prelude hiding ((.), id)
-- -- inferTopP :: Expr -> Either String (Doc ann)
-- -- inferTopP e = inferTop e & _Right %~ pretty
data EType a
  = TInt
  | TApp (EType a)
         (EType a)
  | TForall (Scope () EType a)
  | TVar a
  deriving (Functor, Foldable, Traversable)

deriveEq1 ''EType

deriveShow1 ''EType

deriving instance (Show a) => Show (EType a)

deriving instance (Eq a) => Eq (EType a)

instance Applicative EType where
  pure = TVar
  (<*>) = ap

instance Monad EType where
  return = TVar
  TVar a >>= f = f a
  TApp e0 e1 >>= f = TApp (e0 >>= f) (e1 >>= f)
  TForall e >>= f = TForall (e >>>= f)
  TInt >>= _ = TInt

data EMonoType a
  = MTInt
  | MTApp (EMonoType a)
          (EMonoType a)
  | MTVar a
  deriving (Show, Eq, Functor, Foldable, Traversable)

instance Applicative EMonoType where
  pure = MTVar
  (<*>) = ap

instance Monad EMonoType where
  return = MTVar
  MTVar a >>= f = f a
  MTApp e0 e1 >>= f = MTApp (e0 >>= f) (e1 >>= f)
  MTInt >>= _ = MTInt

data Expr b a
  = EVar a
  | EInt Integer
  | ELam (Scope () (Expr b) a)
  | ELamAnn (EType b)
            (Scope () (Expr b) a)
  | EApp (Expr b a)
         (Expr b a)
  deriving (Functor, Foldable, Traversable)

instance Applicative (Expr b) where
  pure = EVar
  (<*>) = ap

instance Monad (Expr b) where
  return = EVar
  EVar a >>= f = f a
  EInt i >>= _ = EInt i
  ELam s >>= f = ELam (s >>>= f)
  ELamAnn t s >>= f = ELamAnn t (s >>>= f)
  EApp e0 e1 >>= f = EApp (e0 >>= f) (e1 >>= f)

deriveShow1 ''Expr

deriveEq1 ''Expr

deriving instance (Show a, Show b) => Show (Expr b a)

deriving instance (Eq a, Eq b) => Eq (Expr b a)

makeBaseFunctor ''Expr

makeBaseFunctor ''EType

makeBaseFunctor ''EMonoType

type Subs = I.IntMap (EMonoType Int)

-- -- instance Pretty a => Pretty (EType a) where
-- --   pretty = para f
-- --     where
-- --       f TIntF = "int"
-- --       f (TAppF (tt, t0) (_, t1))
-- --         | isAtom tt = t0 <+> "->" <+> t1
-- --         | otherwise = enclose "(" ")" t0 <+> "->" <+> t1
-- --       f (TForallF i (_, t)) = "∀" <+> ("t" <> pretty i) <+> "." <+> t
-- --       f (TVarF i) = "t" <> pretty i
-- --       isAtom TInt = True
-- --       isAtom (TVar _) = True
-- --       isAtom _ = False
-- -- instance Pretty a => Pretty (EMonoType a) where
-- --   pretty = views (re typeMono) pretty
-- -- instance Pretty a => Pretty (Expr a) where
-- --   pretty = cata f
-- --     where
-- --       f (EVarF i) = "x" <> pretty i
-- --       f (EIntF i) = pretty i
-- --       f (ELamF i e) =
-- --         enclose "(" ")" ("λ" <+> enclose "[" "]" ("x" <> pretty i) <+> e)
-- --       f (ELamAnnF i t e) =
-- --         enclose
-- --           "("
-- --           ")"
-- --           ("λ" <+> enclose "[" "]" ("x" <> pretty i <+> ":" <+> pretty t) <+> e)
-- --       f (EAppF e0 e1) = enclose "(" ")" (e0 <+> e1)
-- | prism that goes back and forth between types and mono types
typeMono :: Prism' (EType a) (EMonoType a)
typeMono = prism' inj proj
  where
    inj MTInt = TInt
    inj (MTApp m0 m1) = TApp (inj m0) (inj m1)
    inj (MTVar i) = TVar i
    proj TInt = Just MTInt
    proj (TApp t0 t1) = MTApp <$> proj t0 <*> proj t1
    proj (TForall _) = Nothing
    proj (TVar i) = Just $ MTVar i

-- | Typing Context
type TCtx = I.IntMap (EType Int)

-- | Application Context
type ACtx = [EType Int]

lam :: Eq a => a -> Expr b a -> Expr b a
lam v b = ELam (abstract1 v b)

lamAnn :: Eq a => a -> EType b -> Expr b a -> Expr b a
lamAnn v t b = ELamAnn t (abstract1 v b)

tforall :: Eq a => a -> EType a -> EType a
tforall v t = TForall (abstract1 v t)

eId :: Expr a Int
eId = lam 0 (EVar 0)

eIdAnn :: Expr Int Int
eIdAnn = lamAnn 0 (tforall 0 (TApp (TVar 0) (TVar 0))) (EVar 0)

-- eIdAnn' :: Expr b Int
-- eIdAnn' = lamAnn 0 (tforall 0 (TApp (TVar 0) (TVar 0))) (EVar 0)
eIdInt :: Expr b Int
eIdInt = lamAnn 0 TInt (EVar 0)

-- | Church encoding of 1 and 2
eCOne :: Expr b Int
eCOne = lam 0 (lam 1 (EApp (EVar 0) (EVar 1)))

eCTwo :: Expr b Int
eCTwo = lam 0 (lam 1 (EApp (EVar 0) (EApp (EVar 0) (EVar 1))))

eComp :: Expr b Int
eComp = lam 0 (lam 1 (lam 2 ((EApp (EVar 0) (EApp (EVar 1) (EVar 2))))))

eK2 :: Expr b Int
eK2 = lam 0 (EApp (EApp (EVar 0) eIdInt) (EInt 3))

eFst :: Expr b Int
eFst = lam 0 (lam 1 (EVar 0))

eSnd :: Expr b Int
eSnd = lam 0 (lam 1 (EVar 1))

eCar :: Expr b Int
eCar = lam 0 (EApp (EVar 0) eFst)

eCdr :: Expr b Int
eCdr = lam 0 (EApp (EVar 0) eSnd)

eInst2Fail :: Expr b Int
eInst2Fail =
  EApp
    eId
    (lam
       0
       (lam
          1
          (EApp (EApp (EVar 1) (EApp (EVar 0) (EInt 1))) (EApp (EVar 0) eIdInt))))

eInst2Success :: Expr Int Int
eInst2Success =
  EApp
    eId
    (lamAnn
       0
       (tforall 0 (TApp (TVar 0) (TVar 0)))
       (lam
          1
          (EApp (EApp (EVar 1) (EApp (EVar 0) (EInt 1))) (EApp (EVar 0) eIdInt))))

eCTwoInt :: Expr b Int
eCTwoInt =
  lamAnn
    0
    (TApp TInt TInt)
    (lamAnn 1 TInt (EApp (EVar 0) (EApp (EVar 0) (EVar 1))))

substMono :: Subs -> EMonoType Int -> EMonoType Int
substMono subs t =
  t >>= \x ->
    case subs ^. at x of
      Nothing -> pure x
      Just t -> t

substPoly :: Subs -> EType Int -> EType Int
substPoly subs t =
  t >>= \x ->
    case subs ^. at x of
      Nothing -> pure x
      Just t -> t ^. re typeMono

data InferEnv = IEnv
  { _subs :: Subs
  , _freshCounter :: Int
  } deriving (Show, Eq)

makeLenses ''InferEnv

-- Some monadic predicates
-- | v not in subs
isMetaVar :: MonadState InferEnv m => Int -> m Bool
isMetaVar i = use $ subs . at i . to (isn't _Nothing)

isMetaVarM :: MonadState InferEnv m => Int -> m (Maybe (EMonoType Int))
isMetaVarM i = use $ subs . at i

-- | v == v in subs
isUnboundMetaVar :: MonadState InferEnv m => Int -> m Bool
isUnboundMetaVar i = use $ subs . at i . to (anyOf folded (== MTVar i))

-- | occurence check. stricter than the one on SPJ 2007 since I make sure all open variables are fresh
occurCheck ::
     (MonadError String m, MonadState InferEnv m)
  => Int
  -> EMonoType Int
  -> m ()
occurCheck i t = do
  t' <- use $ subs . to (\s -> substMono s t)
  case elem i (t' ^.. folded) of
    True ->
      if (t' == MTVar i)
        then pure ()
        else throwError "occurCheck"
    False -> pure ()

-- | Monadic unification. It doesn't generate new types. Maybe I should refine InferEnv as HasSub
-- Really should take two MonoTypes
unify ::
     (MonadError String m, MonadState InferEnv m)
  => EType Int
  -> EType Int
  -> m ()
unify t0 t1
  -- handles both meta/non-meta cases
  | TInt <- t0
  , TInt <- t1 = pure ()
  | TVar i0 <- t0
  , TVar i1 <- t1
  , i0 == i1 = pure ()
  -- unequal
  | TVar i0 <- t0 =
    isMetaVarM i0 >>=
      -- i0 meta
     \case
      Just t0'
        -- unbound
        | MTVar i0' <- t0'
        , i0' == i0 -> unifyUnboundVar i0 t1
            -- bound
        | otherwise -> unify (t0' ^. re typeMono) t1
      -- i0 non-meta
      Nothing
        | TVar i1 <- t1 ->
          isMetaVarM i1 >>= \case
            Just t1'
              | MTVar i1' <- t1'
              , i1' == i1 -> unifyUnboundVar i1 t0
              | otherwise -> unify t0 (t1' ^. re typeMono)
            -- i1 non-meta
            Nothing -> throwError "Cannot unify two unequal non-meta variables"
        | otherwise -> throwError "i0 non-meta. RHS is not a variable"
  -- invariant: t0 is not a variable
  | TVar i1 <- t1 =
    isMetaVarM i1 >>= \case
      Just t1'
        | MTVar i1' <- t1'
        , i1' == i1 -> unifyUnboundVar i1 t0
        | otherwise -> unify t0 (t1' ^. re typeMono)
          -- can't unify a non-flexible variable
      Nothing -> throwError "i1 non-meta. LHS is not a variable"
  -- invariant: none of t0 t1 is a variable
  | TApp t00 t01 <- t0
  , TApp t10 t11 <- t1 = unify t00 t10 >> unify t01 t11
  | otherwise =
    throwError
      "unify catch-all case. probably trying to unify polymorphic types."

-- invariant: Var is flexible
unifyUnboundVar ::
     (MonadError String m, MonadState InferEnv m) => Int -> EType Int -> m ()
unifyUnboundVar i0 t1 = do
  case (t1) ^? typeMono of
    Just t1' -> do
      s <- use subs
      let t1'' = substMono s t1'
      occurCheck i0 t1''
      subs . mapped %= substMono (I.fromList [(i0, t1'')])
      subs . at i0 ?= t1''
    Nothing ->
      throwError
        "unable to coerce type to a monotype; this coercion should be removed soon"

freshVar :: (MonadState InferEnv m) => m Int
freshVar = freshCounter <+= 1

-- T-GEN
tgen :: (MonadState InferEnv m) => TCtx -> EType Int -> m (EType Int)
tgen ctx t = do
  s <- use subs
  let st = substPoly s t
      stfvars = st ^.. folded :: [Int]
      ctxfvars = ctx ^.. folded . to (substPoly s) . folded :: [Int]
      is = IS.toList . IS.fromList $ stfvars L.\\ ctxfvars
  pure $ foldrOf folded (\i e -> TForall (abstract1 i e)) st is

inferTop :: Expr Int Int -> Either String (EType Int)
inferTop e =
  runExcept (evalStateT (inferType mempty mempty (EApp eId e)) (IEnv mempty 0))

inferType ::
     (MonadError String m, MonadState InferEnv m)
  => TCtx
  -> ACtx
  -> Expr Int Int
  -> m (EType Int)
inferType ctx actx e
  -- T-Var
  | EVar i <- e
  , Just a <- I.lookup i ctx = appSubtype actx a
  -- T-INT
  | EVar _ <- e = throwError "free variable"
  | EInt _ <- e = pure TInt
  -- T-LAM
  | ELam e' <- e
  , a:actx' <- actx = do
    iF <- freshVar
    TApp a <$> inferType (I.insert iF a ctx) actx' (instantiate1 (EVar iF) e')
  -- T-LAM2
  | ELam e' <- e
  -- guessing a random monotype
   = do
    iF <- freshVar
        -- could add a precondition check
    subs . at iF ?= MTVar iF
    TApp (TVar iF) <$>
      inferType (I.insert iF (TVar iF) ctx) actx (instantiate1 (EVar iF) e')
  -- T-LAMANN1
  | ELamAnn t e' <- e
  , [] <- actx
  -- T-LAMANN2
   = do
    iF <- freshVar
    TApp t <$> inferType (I.insert iF t ctx) actx (instantiate1 (EVar iF) e')
  | ELamAnn t e' <- e
  , a:actx' <- actx = do
    isSubtype a t
    iF <- freshVar
    TApp a <$> inferType (I.insert iF t ctx) actx' (instantiate1 (EVar iF) e')
  -- T-APP
  | EApp e0 e1 <- e = do
    a <- inferType ctx [] e1
    b <- tgen ctx a
    t <- inferType ctx (b : actx) e0
    -- s <- use subs
    -- let t' = substP s t
    case t of
      TApp _ c -> pure c
      _ -> throwError "I have no idea how this could happen.. "

isSubtype ::
     (MonadState InferEnv m, MonadError String m)
  => EType Int
  -> EType Int
  -> m ()
isSubtype e0 e1
  -- S-INT
  | TInt <- e0
  , TInt <- e1 = pure ()
  -- S-VAR
  | TVar i <- e0
  , TVar i' <- e1
  , i == i' = pure ()
  -- S-FORALLR
  | TForall e1' <- e1 = do
    b <- freshVar
    let e1fb = instantiate1 (TVar b) e1'
    isSubtype e0 e1fb
    s <- use subs
    case substPoly s e0 ^.. folded & elem b of
      True ->
        throwError
          "not as polymorphic since a forall variable has been captured"
      False -> pure ()
  -- S-FORALLL
  | TForall e0' <- e0 = do
    iF <- freshVar
       -- refresh the type variable before opening
    let e0'' = instantiate1 (TVar iF) e0'
       -- extend the substitution environment
    subs . at iF ?= MTVar iF
    isSubtype e0'' e1
  | TApp t0 t1 <- e0
  , TApp t0' t1' <- e1 = do
    isSubtype t0' t0
    isSubtype t1 t1'
  -- S-FUNL
  | TVar i0 <- e0
  , TApp _ _ <- e1 =
    isMetaVarM i0 >>= \case
      Just _ -> do
        t00 <- freshVar
        t01 <- freshVar
        subs . at t00 ?= MTVar t00
        subs . at t01 ?= MTVar t01
        unify e0 (TApp (TVar t00) (TVar t01))
        unify e0 e1
        isSubtype (TApp (TVar t00) (TVar t01)) e1
      Nothing ->
        throwError
          "a forall variable cannot possibly be a subtype of an arrow type"
  -- S-FUNR
  | TVar i1 <- e1
  , TApp _ _ <- e0 =
    isMetaVarM i1 >>= \case
      Just _ -> do
        i10 <- freshVar
        i11 <- freshVar
        subs . at i10 ?= MTVar i10
        subs . at i11 ?= MTVar i11
        unify e1 (TApp (TVar i10) (TVar i11))
        unify e0 e1
        isSubtype e0 (TApp (TVar i10) (TVar i11))
      Nothing ->
        throwError
          "a forall variable cannot possibly be a subtype of an arrow type"
  | otherwise = unify e0 e1

appSubtype ::
     (MonadError String m, MonadState InferEnv m)
  => ACtx
  -> EType Int
  -> m (EType Int)
appSubtype actx t
  -- S-EMPTY
  | [] <- actx = pure t
  -- S-FUN2
  | a:actx' <- actx
  , TApp t0 t1 <- t = do
    isSubtype a t0
    TApp a <$> appSubtype actx' t1
  -- S-FORALL2
  | _:_ <- actx
  , TForall t1 <- t = do
    iF <- freshVar
       -- refresh the type variable before opening
    let t2 = instantiate1 (TVar iF) t1
    subs . at iF ?= MTVar iF
    appSubtype actx t2
  | _:_ <- actx
  , TVar i <- t =
    isMetaVarM i >>= \case
      Nothing ->
        throwError "appSubtype: cannot unify a forall var with a function type"
      Just _ -> do
        i0 <- freshVar
        i1 <- freshVar
        subs . at i0 ?= MTVar i0
        subs . at i1 ?= MTVar i1
        unify t (TApp (TVar i0) (TVar i1))
        appSubtype actx (TApp (TVar i0) (TVar i1))
  | otherwise = throwError "appSubtype catch-all case"
