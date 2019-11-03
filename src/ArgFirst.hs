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

type Subs = I.IntMap EMonoType

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
        "∀" <+> ("t" <> pretty i) <+> "." <+> t
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
    go t@(MTVar i) = fromMaybe t (subs ^. at i)
    go (MTApp t t') = MTApp (go t) (go t')
    go MTInt = MTInt

substP :: Subs -> EType -> EType
substP subs t = go t
  where
    go t@(TVar i) = maybe t id (subs' ^. at i)
    go (TForall i t) =
      TForall i (substP (subs & sans i) t)
    go (TApp t t') = TApp (go t) (go t')
    go TInt = TInt
    subs' = over mapped (^. re typeMono) subs


data InferEnv = IEnv
  { _subs :: Subs
  , _freshCounter :: Int
  } deriving (Show, Eq)

makeLenses ''InferEnv

-- Some monadic predicates
-- | v not in subs
isMetaVar :: MonadState InferEnv m => Int -> m Bool
isMetaVar i = use $ subs . at i . to (isn't _Nothing)

isMetaVarM :: MonadState InferEnv m => Int -> m (Maybe EMonoType)
isMetaVarM i = use $ subs . at i

-- | v == v in subs
isUnboundMetaVar :: MonadState InferEnv m => Int -> m Bool
isUnboundMetaVar i =
  use $ subs . at i . to (anyOf folded (== MTVar i))

-- | occurence check. stricter than the one on SPJ 2007 since I make sure all open variables are fresh
occurCheck :: (MonadError String m, MonadState InferEnv m) => Int -> EMonoType -> m ()
occurCheck i t = do
  t' <- use $ subs . to (\s -> subst s t )
  case elem i (mtftv t') of
    True -> throwError "occurCheck"
    False -> pure ()

-- unifyFunc :: Int -> EType -> EType -> Subs -> Maybe Subs
-- unifyFunc fc t0 t1 s = evalStateT (unify t0 t1 >> use subs) (IEnv s fc)

utestt0 = TApp (TApp (TVar 0) (TVar 1)) (TVar 0)

utestt1 = TApp (TVar 2) (TVar 1)

utests :: Subs
utests = I.fromList [(0, MTVar 0), (1, MTVar 1), (2, MTVar 2), (3, MTVar 3)]

-- | Monadic unification. It doesn't generate new types. Maybe I should refine InferEnv as HasSub
-- Really should take two MonoTypes
unify ::
     (MonadError String m, MonadState InferEnv m) => EType -> EType -> m ()
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
      -- i0 meta
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
  | otherwise = throwError "unify catch-all case. probably trying to unify polymorphic types."

-- invariant: Var is flexible
unifyUnboundVar ::
     (MonadError String m, MonadState InferEnv m) => Int -> EType -> m ()
unifyUnboundVar i0 t1 = do
  case t1 ^? typeMono of
    Just t1' -> do
      s <- use subs
      let t1'' = subst s t1'
      occurCheck i0 t1''
      subs . mapped %= subst (I.fromList [(i0,t1'')])
      subs . at i0 ?= t1''
    Nothing -> throwError "unable to coerce type to a monotype; this coercion should be removed soon"

-- unifyVar i0 t1
--   = isUnboundMetaVar i0 >>=
--     \case
--       True ->
freshVar :: (MonadState InferEnv m) => m Int
freshVar = freshCounter <+= 1

gftv :: TCtx -> [Int]
gftv -- join . over mapped tftv . toListOf (folded . _2) . I.toList
 = view (to I.toList . folded . _2 . to tftv)

mtftv :: EMonoType -> [Int]
mtftv = view (re typeMono . to tftv)

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
-- tgen :: TCtx -> EType -> EType
-- -- I don't think it is necessary to exclude subs
-- tgen ctx t = -- L.foldr TForall t ((tftv t L.\\ gftv ctx) L.\\ (subs ^.. folded . _1) )
--   L.foldr TForall t (L.nub $ tftv t L.\\ gftv ctx) 


tgen :: (MonadState InferEnv m) => TCtx -> EType -> m EType
tgen ctx t = do
  s <- use subs
  let st = substP s t
      is = L.nub $ tftv st L.\\ (ctx ^. folded . to (substP s) . to tftv)
  pure $ L.foldr TForall st is

-- | alpha conversion for EType
etAlpha :: Int -> Int -> EType -> EType
etAlpha binder freshId = para f
  where f TIntF = TInt
        f (TVarF i)
          | i == binder
          = TVar freshId
          | otherwise
          = TVar i
        f (TForallF i (old,e0))
          | i == binder
          = TForall i old
          | otherwise
          = TForall i e0
        f (TAppF (_,e0) (_,e1))
          = TApp e0 e1


-- -- top level infer
-- infer :: Expr -> EType
-- infer 
         
inferType ::
     (MonadError String m, MonadState InferEnv m)
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
   = do iF <- freshVar
        -- could add a precondition check
        subs . at iF  ?= MTVar iF
        TApp (TVar iF) <$> inferType (I.insert i (TVar iF) ctx) actx e'
  -- T-LAMANN1
  | ELamAnn i t e' <- e
  , [] <- actx
  -- T-LAMANN2
   = TApp t <$> inferType (I.insert i t ctx) actx e'
  | ELamAnn i t e' <- e
  , a:actx' <- actx = do
    isSubtype a t
    TApp a <$> inferType (I.insert i t ctx) actx' e'
  -- T-APP
  | EApp e0 e1 <- e = do
    a <- inferType ctx [] e1
    b <- tgen ctx a
    inferType ctx (b : actx) e0 >>=
      \case TApp _ c -> pure c
            _ -> throwError "I have no idea how this could happen.."


isSubtype :: (MonadState InferEnv m, MonadError String m) => EType -> EType -> m ()
isSubtype e0 e1
  -- S-INT
  | TInt <- e0
  , TInt <- e1 = pure ()
  -- S-VAR
  | TVar i <- e0
  , TVar i' <- e1
  , i == i'
  = pure ()
  -- S-FORALLR
  | TForall i e1' <- e1
  = do b <- freshVar
       let e1fb = etAlpha i b e1'
       isSubtype e0 e1fb
       s <- use subs
       case tftv (substP s e0) & elem b of
         True -> throwError "not as polymorphic since a forall variable has been captured"
         False -> pure ()
  -- S-FORALLL
  | TForall i e0' <- e0
  = do iF <- freshVar
       -- refresh the type variable before opening
       let e0'' = substP (I.fromList [(i, MTVar iF)]) e0'
       -- extend the substitution environment
       subs . at iF ?= MTVar iF
       isSubtype e0'' e1
  | TApp t0 t1 <- e0
  , TApp t0' t1' <- e1 = do
      isSubtype t0' t0 
      isSubtype t1 t1'
  -- S-FUNL
  | TVar i0 <- e0
  , TApp t10 t11 <- e1
  = isMetaVarM i0 >>=
    \case
      Just t0
        -> do t00 <- freshVar
              t01 <- freshVar
              subs . at t00 ?= MTVar t00
              subs . at t01 ?= MTVar t01
              unify e0 (TApp (TVar t00) (TVar t01))
              unify e0 e1
              isSubtype (TApp (TVar t00) (TVar t01)) e1
      Nothing
        -> throwError "a forall variable cannot possibly be a subtype of an arrow type"
  -- S-FUNR
  | TVar i1 <- e1
  , TApp t00 t01 <- e0
  = isMetaVarM i1 >>=
    \case
      Just t1
        -> do i10 <- freshVar
              i11 <- freshVar
              subs . at i10 ?= MTVar i10
              subs . at i11 ?= MTVar i11
              unify e1 (TApp (TVar i10) (TVar i11))
              unify e0 e1
              isSubtype e0 (TApp (TVar i10) (TVar i11))
  | otherwise = unify e0 e1

appSubtype ::
     (MonadError String m, MonadState InferEnv m) => ACtx -> EType -> m EType
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
  , TForall i t1 <- t = do
      iF <- freshVar
       -- refresh the type variable before opening
      let t2 = substP (I.fromList [(i, MTVar iF)]) t1
       -- extend the substitution environment
      subs . at iF ?= MTVar iF
      TForall iF <$> appSubtype actx t2
  | _:_ <- actx
  , TVar i <- t
  = isMetaVarM i >>=
    \case Nothing -> throwError "appSubtype: cannot unify a forall var with a function type"
          Just t' -> do
            i0 <- freshVar
            i1 <- freshVar
            subs . at i0 ?= MTVar i0
            subs . at i1 ?= MTVar i1
            unify t (TApp (TVar i0) (TVar i1))
            appSubtype actx (TApp (TVar i0) (TVar i1))
  | otherwise = throwError "appSubtype catch-all case"

utestt2 = TForall 0 (TForall 1 (TApp (TApp (TVar 0) (TVar 1)) (TApp (TVar 0) (TVar 1))) )
utestt3 = TForall 0 (TApp (TApp (TVar 0) (TVar 0)) (TApp (TVar 0) (TVar 0)))
