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
infer env (ConstExp c) = do
  tau <- freshInst (constTySig c)
  return tau

infer env (VarExp x) = case H.lookup x env of
  Just tau -> freshInst tau
  Nothing -> throwError (LookupError x)

infer env (LetExp x e1 e2) = do
  (tau1, phi1) <- listen $ infer env e1
  sub <- unify phi1
  let genType = gen (apply sub env) (apply sub tau1)
  tau <- infer (H.insert x genType env) e2
  return tau

infer env (BinOpExp op e1 e2) = do
  tau1 <- infer env e1
  tau2 <- infer env e2
  retType <- freshTau
  let signature = freshInst (binopTySig op)
  constrain signature (funTy tau1 (funTy tau2 retType))
  return retType

infer env (MonOpExp op e1) = do
  tau1 <- infer env e1
  retType <- freshTau
  let signature = freshInst (monopTySig op)
  constrain signature (funTy tau1 retType)
  return retType

infer env (IfExp e1 e2 e3) = do
  tau1 <- infer env e1
  tau2 <- infer env e2
  tau3 <- infer env e3
  constrain tau1 boolTy
  constrain tau2 tau3
  return tau2

infer env (FunExp x e) = do
  tau1 <- freshTau
  tau2 <- infer (H.insert x (Forall [] tau1) env) e
  return (funTy tau1 tau2)

infer env (AppExp f e) = do
  tau1 <- infer env f
  tau2 <- infer env e
  retType <- freshTau
  constrain tau1 (funTy tau2 retType)
  return retType

infer env (LetRecExp f x e1 e2) = do
  tau1 <- freshTau
  tau2 <- freshTau
  tau3 <- infer (H.insert x tau1 (H.insert f (funTy tau1 tau2) env)) e1
  phi1 <- listen $ constrain tau2 tau3
  sub <- unify (tau2 :~: tau3 : phi1)
  let genType = gen (apply sub env) (apply sub (funTy tau1 tau2))
  tau <- infer (H.insert f genType env) e2
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
