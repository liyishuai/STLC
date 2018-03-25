{-# LANGUAGE IncoherentInstances, ConstraintKinds, TypeFamilies, EmptyCase, TypeInType,
             TemplateHaskell, RankNTypes, ScopedTypeVariables, GADTs,
             TypeOperators, DataKinds, PolyKinds, MultiParamTypeClasses,
             FlexibleContexts, FlexibleInstances, UndecidableInstances #-}

{-# OPTIONS_GHC -Wincomplete-patterns #-}
-- {-# OPTIONS_GHC -ddump-splices #-}

module MySTLC where

import Prelude ()
import Data.Proxy
import Data.Kind (Type)
-- Mimics the Haskell Prelude, but with singleton types.
-- Includes the basic singleton definitions, specifically we use SList here
import Data.Singletons.Prelude hiding (Elem)
import Data.Singletons.SuppressUnusedWarnings
-- This module contains everything you need to derive your own singletons via Template Haskell.
import Data.Singletons.TH

data Var :: Type where
  Zero :: Var
  Succ :: Var -> Var

data Typ :: Type where
  TBool :: Typ
  TArr  :: Typ -> Typ -> Typ

data Either a b = Left a | Right b

-- Env xs x is a proof that x is in the list xs
data Elem :: [Typ] -> Typ -> Type where
  ZElem :: Elem (x ': xs) x
  SElem :: Elem xs x -> Elem (y ': xs) x

data Env :: [a] -> Type where
  ZEnv :: Env '[]
  SEnv :: Env xs -> Env (y ': xs)

type family xs ++ ys where
  '[]       ++ ys = ys
  (x ': xs) ++ ys = x ': (xs ++ ys)
infixr 5 ++

-- Expr is well typed with type Typ under context [Typ]
data Expr :: [Typ] -> Typ -> Type where
  EVar   :: Elem env typ -> Expr env typ
  EAbs   :: Expr (targ ': env) tres -> Expr env (TArr targ tres)
  EApp   :: Expr env (TArr targ tres) -> Expr env targ -> Expr env tres
  ETrue  :: Expr env TBool
  EFalse :: Expr env TBool
  EIf    :: Expr env TBool -> Expr env typ -> Expr env typ -> Expr env typ

data Val :: [Typ] -> Typ -> Type where
  VAbs   :: Expr (targ ': env) tres -> Val env (TArr targ tres)
  VTrue  :: Val env TBool
  VFalse :: Val env TBool

weakeningVar :: Proxy y -> Proxy env2 -> Env env1
  -> Elem (env1 ++ env2) x -> Elem (env1 ++ y ': env2) x
weakeningVar _ _ ZEnv ele = SElem ele -- by definition of Elem
weakeningVar _ _ (SEnv _) ZElem = ZElem
{-
  TODO: Question
-}
weakeningVar p1 p2 (SEnv env) (SElem ele) = SElem (weakeningVar p1 p2 env ele)
{-
  Elem (y ': (env1 ++ env2)) x = Elem ((y ': env1) ++ env2)
  weakeningVar p1 p2 env ele :: Elem (env1 ++ y ': env2) x
  SElem (weakeningVar p1 p2 env ele) :: Elem (z ': (env1 ++ y ': env2)) x = Elem ((z ': env1) ++ y ': env2)) x
-}

weakening :: Proxy x -> Proxy env2 -> Env env1
  -> Expr (env1 ++ env2) ty -> Expr (env1 ++ x ': env2) ty
weakening p1 p2 env (EVar v)       = EVar (weakeningVar p1 p2 env v)
weakening p1 p2 env (EAbs body)    = EAbs (weakening p1 p2 (SEnv env) body)
{-
SEnv env : Env (y ': env1)
body : targ ': env1 ++ env2
 => y = targ
weakening p1 p2 (SEnv env) body) = (targ ': env1) ++ x ': env2 =  targ ': (env1 ++ x ': env2) = env1 ++ x ': env2
-}
weakening p1 p2 env (EApp e1 e2)   = EApp (weakening p1 p2 env e1) (weakening p1 p2 env e2)
weakening _ _ _ ETrue              = ETrue
weakening _ _ _ EFalse             = EFalse
weakening p1 p2 env (EIf st e1 e2) = EIf (weakening p1 p2 env st) (weakening p1 p2 env e1) (weakening p1 p2 env e2)

{-
TODO: Question
-}
substVar :: Env env1 -> Expr env2 typ
  -> Elem (env1 ++ typ ': env2) typ' -> Expr (env1 ++ env2) typ'
substVar ZEnv expr ZElem = expr -- typ' = typ, so e = Elem env2 typ'
substVar ZEnv _ (SElem v) = EVar v -- v = Elem env2 typ'
-- Inversion of the typing relation
substVar (SEnv _) _ ZElem = EVar ZElem
substVar (SEnv env) expr (SElem v) = weakening Proxy Proxy ZEnv (substVar env expr v)

-- Lemma [Preservation of types under substitution]:
-- If Γ,x:S ⊢ t : T and Γ ⊢ s : S, then Γ ⊢ [x -> s] t : T.
-- | EVar x' -> if x = x' then e else e'
-- Equivalently, check if typ' = typ
subst :: Env env1 -> Expr env2 typ
  -> Expr (env1 ++ typ ': env2) typ' -> Expr (env1 ++ env2) typ'
subst env expr (EVar v)       = substVar env expr v
subst env expr (EAbs body)    = EAbs (subst (SEnv env) expr body)
subst env expr (EApp e1 e2)   = EApp (subst env expr e1) (subst env expr e2)
subst env expr ETrue          = ETrue
subst env expr EFalse         = EFalse
subst env expr (EIf st e1 e2) = EIf (subst env expr st) (subst env expr e1) (subst env expr e2)

step :: Expr '[] typ -> Either (Expr '[] typ) (Val '[] typ)
step (EVar v)       = case v of {}
step (EAbs body)    = Right (VAbs body)
step (EApp fun arg) = case step fun of
  Right (VAbs body) -> Left (subst ZEnv arg body)
  Left fun'         -> Left (EApp fun' arg)
step ETrue          = Right VTrue
step EFalse         = Right VFalse
step (EIf st e1 e2) = case step st of
  Right VTrue  -> Left e1
  Right VFalse -> Left e2
  Left st'   -> Left (EIf st' e1 e2)

bigstep :: Expr '[] typ -> Val '[] typ
bigstep expr = case step expr of
  Right val  -> val
  Left expr' -> bigstep expr'

eval :: Expr '[] typ -> Val '[] typ
eval (EVar v)       = case v of {} -- no variables in an empty context
eval (EAbs body)    = VAbs body
eval (EApp fun arg) = case eval fun of
  VAbs body -> eval (subst ZEnv arg body)
  -- no need to make sure arg is_value since Haskell allows non-termination where the base case for subst on Lam values are the cases when arg is value
eval ETrue          = VTrue
eval EFalse         = VFalse
eval (EIf e1 e2 e3) = case (eval e1) of
  VTrue  -> eval e2
  VFalse -> eval e3

{-
TODO: Questions
1. Proxy
2. weakeningVar
3. substVar
-}
