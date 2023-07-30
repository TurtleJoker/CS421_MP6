module Infer where

import Common

import Control.Monad.Writer (listen)
import Control.Monad.Except (throwError)
import Data.Map.Strict as H (Map, insert, lookup, empty, fromList, singleton)

  {- question 1: fresh instance function -}

freshInst :: PolyTy -> Infer MonoTy
freshInst (Forall qVars tau) = do
  freshVars <- mapM (\_ -> freshTau) qVars
  let substitution = H.fromList (zip qVars freshVars)
  return (apply substitution tau)

  {- question 2: occurs check -}

occurs :: VarId -> MonoTy -> Bool
occurs i tau = i `elem` freeVars tau

  {- question 3: unification -}

unify :: [Constraint] -> Infer Substitution
unify [] = return H.empty
unify ((s :~: t):eqList) 
    | s == t = unify eqList -- Delete rule
    | otherwise = case (s, t) of
        (TyVar i, _) -> 
            if occurs i t then 
                throwError (InfiniteType i t) -- InfiniteType error
            else do
                sub <- unify (applySubst i t eqList) -- Eliminate rule
                return (H.insert i (apply sub t) sub)
        (_, TyVar i) -> unify ((t :~: s) : eqList) -- Orient rule
        (TyConst c1 args1, TyConst c2 args2) -> 
            if c1 == c2 then 
                unify (zipWith (:~:) args1 args2 ++ eqList) -- Decompose rule
            else 
                throwError (Can'tMatch s t) -- Can'tMatch error
        _ -> throwError (Can'tMatch s t) -- Can'tMatch error

applySubst :: VarId -> MonoTy -> [Constraint] -> [Constraint]
applySubst i t = map applyConstraint
    where 
        applyConstraint (a :~: b) = (applySingleSubst i t a) :~: (applySingleSubst i t b)
        applySingleSubst i t tau@(TyVar j) = if i == j then t else tau
        applySingleSubst i t (TyConst c args) = TyConst c (map (applySingleSubst i t) args)

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
