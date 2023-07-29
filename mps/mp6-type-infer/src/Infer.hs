module Infer where

import Common

import Control.Monad.Writer (listen)
import Control.Monad.Except (throwError)
import Data.Map.Strict as H (Map, insert, lookup, empty, fromList, singleton)

  {- question 1: fresh instance function -}

freshInst :: PolyTy -> Infer MonoTy
freshInst (Forall qVars tau) = do
  freshVars <- mapM (const freshTau) qVars
  let subst = H.fromList $ zip qVars freshVars
  return $ apply subst tau

  {- question 2: occurs check -}

occurs :: VarId -> MonoTy -> Bool
occurs i tau = i `elem` freeVars tau

  {- question 3: unification -}

unify :: [Constraint] -> Infer Substitution
unify [] = return substEmpty
unify ((s :~: t) : cs) 
  | s == t = unify cs
  | TyVar i <- s, not (i `occurs` t) = do
      let subst = substInit i t
      cs' <- apply subst cs
      subst' <- unify cs'
      return (substCompose subst' subst)
  | TyVar i <- t = unify ((t :~: s) : cs)
  | TyConst c1 args1 <- s, TyConst c2 args2 <- t, c1 == c2, length args1 == length args2 =
      unify ((zipWith (:~:) args1 args2) ++ cs)
  | otherwise = throwError (Can'tMatch s t)

  {- question 4: type inference -}

infer :: TypeEnv -> Exp -> Infer MonoTy
infer env (ConstExp c) = freshInst (constTySig c)

infer env (VarExp x) = case H.lookup x env of
  Nothing -> throwError (LookupError x)
  Just s -> freshInst s

infer env (LetExp x e1 e2) = do
  (tau1, constraints1) <- listen $ infer env e1
  substitution <- unify constraints1
  let tau1' = apply substitution tau1
  let env' = H.insert x (quantifyMonoTy tau1') env
  (tau2, constraints2) <- listen $ infer env' e2
  return (tau2, constraints1 ++ constraints2)

infer env (BinOpExp op e1 e2) = do
  tau1 <- infer env e1
  tau2 <- infer env e2
  tau <- freshTau
  let tySig = freshInst (binopTySig op)
  constrain tySig (TyConst "->" [TyConst "->" [tau1, tau2], tau])
  return tau

infer env (MonOpExp op e1) = do
  tau1 <- infer env e1
  tau <- freshTau
  tySig <- freshInst (monopTySig op)
  let constraint = tySig :~: (TyConst "->" [tau1, tau])
  (tau', constraints) <- listen $ infer env e1
  let constraints' = constraint : constraints
  substitution <- unify constraints'
  return (apply substitution tau', constraints')

infer env (IfExp e1 e2 e3) = do
  tau1 <- infer env e1
  tau2 <- infer env e2
  tau3 <- infer env e3
  constrain tau1 (TyConst "bool" [])
  constrain tau2 tau3
  return tau2

infer env (FunExp x e) = do
  tau1 <- freshTau
  let env' = H.insert x (quantifyMonoTy tau1) env
  tau2 <- infer env' e
  return (TyConst "->" [tau1, tau2])

infer env (AppExp e1 e2) = do
  tau1 <- infer env e1
  tau2 <- infer env e2
  tau <- freshTau
  constrain tau1 (TyConst "->" [tau2, tau])
  return tau

infer env (LetRecExp f x e1 e2) = do
  tau1 <- freshTau
  tau2 <- freshTau
  let env' = H.insert x (quantifyMonoTy tau1) . H.insert f (quantifyMonoTy $ TyConst "->" [tau1, tau2]) $ env
  (tau3, constraints1) <- listen $ infer env' e1
  substitution <- unify ((tau2 :~: tau3) : constraints1)
  let env'' = H.insert f (quantifyMonoTy $ apply substitution (TyConst "->" [tau1, tau2])) env
  (tau, constraints2) <- listen $ infer env'' e2
  return tau

inferInit :: TypeEnv -> Exp -> Infer PolyTy
inferInit env e = do
  (tau, constraints) <- listen $ infer env e
  substitution <- unify constraints
  return $ quantifyMonoTy $ apply substitution tau

inferDec :: TypeEnv -> Dec -> Infer (TypeEnv, PolyTy)
inferDec env (AnonDec e') = do
  tau <- inferInit env e'
  return (env, tau)
inferDec env (LetDec x e') = do
  tau <- inferInit env (LetExp x e' (VarExp x))
  return (H.insert x tau env, tau)
inferDec env (LetRec f x e') = do
  tau <- inferInit env (LetRecExp f x e' (VarExp f))
  return (H.insert f tau env, tau)
