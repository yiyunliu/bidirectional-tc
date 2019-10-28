{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}

module Lib
  ( inferType
  , checkType
  , Expr (..)
  , TCtx
  , EType (..)
  ) where

import Control.Applicative
import Data.Functor.Foldable (Corecursive(..), Fix(..), cata, cataA, para)
import Data.Functor.Foldable.TH
import qualified Data.IntMap as I
import Data.Maybe
import Control.Monad

data Expr
  = EVar Int
  | EApp Expr
         Expr
  | ELam Int
         Expr
  | ETrue
  | EFalse
  | EIf Expr
        Expr
        Expr
  | EAnn Expr
         EType
  deriving (Show, Eq)

data EType
  = TBool
  | TApp EType
         EType
  deriving (Show, Eq)

makeBaseFunctor ''Expr

makeBaseFunctor ''EType

type TCtx = I.IntMap EType

checkType :: TCtx -> Expr -> EType -> Bool
checkType ctx (EIf eg e0 e1) t =
  checkType ctx eg TBool && checkType ctx e0 t && checkType ctx e1 t
checkType ctx (ELam x e) (TApp t0 t1) = checkType (I.insert x t0 ctx) e t1
-- -- YL: What happens if e0 can't be easily inferred? That when type annotations come to the rescue
-- checkType ctx (EApp e0 e1) t1 =
--   maybe False (\t0 -> checkType ctx e0 (TApp t0 t1)) (inferType ctx e1)
checkType ctx e t = maybe False (== t) (inferType ctx e)

inferType :: TCtx -> Expr -> Maybe EType
inferType _ ETrue = pure TBool
inferType _ EFalse = pure TBool
inferType ctx (EApp e0 e1) = do
  TApp t0 t1 <- inferType ctx e0
  guard (checkType ctx e1 t0)
  pure t1
    
inferType ctx (EVar i) = I.lookup i ctx
inferType ctx (EAnn e t)
  | checkType ctx e t = pure t
  | otherwise = Nothing
inferType _ _ = Nothing


