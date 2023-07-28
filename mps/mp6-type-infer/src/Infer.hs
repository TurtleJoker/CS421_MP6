module Infer where

import Common

import Control.Monad.Writer (listen)
import Control.Monad.Except (throwError)
import Data.Map.Strict as H (Map, insert, lookup, empty, fromList, singleton)

  {- question 1: fresh instance function -}

freshInst :: PolyTy -> Infer MonoTy
freshInst (Forall qVars tau) = do
    freshVars <- mapM (const freshTau) qVars
    let subst = zip qVars freshVars
    return $ applySubst subst tau

  {- question 2: occurs check -}

occurs :: VarId -> MonoTy -> Bool
occurs i tau = i `elem` freeVars tau

  {- question 3: unification -}

unify :: [Constraint] -> Infer Substitution
unify [] = return nullSubst
unify ((s, t) : cs)
  | s == t = unify cs
  | isVar s && not (isVar t) = unify ((t, s) : cs)
  | isVar s && s `occurs` t = throwError (InfiniteType s t)
  | isVar s && not (s `occurs` t) = do
      subst <- unify (applySubst [(s, t)] cs)
      return (composeSubst [(s, applySubst subst t)] subst)
  | isConstructor s && isConstructor t =
      if getConstructor s == getConstructor t
      then unify (zip (getArgs s) (getArgs t) ++ cs)
      else throwError (CantMatch s t)
  | otherwise = throwError (CantMatch s t)

  {- question 4: type inference -}

infer :: TypeEnv -> Exp -> Infer MonoTy
infer env (Const c) = 
    let ty = freshInst $ constTySig c 
    in return ty

infer env (Var x) = 
    case H.lookup x env of
        Nothing -> throwError $ LookupError x
        Just sch -> freshInst sch

infer env (LetInExp x e1 e2) = do
    (t1, cs1) <- listen $ infer env e1
    let sub = unify cs1
    let env' = H.insert x (GEN env sub t1) env
    (t, cs) <- listen $ infer env' e2
    return t `constrainedBy` (cs1 `union` cs)

infer env (FunExp x e) = do
    tv <- fresh
    let env' = H.insert x (Forall [] tv) env
    t2 <- infer env' e
    return (tv `fn` t2)

infer env (AppExp f e) = do
    tf <- infer env f
    te <- infer env e
    tv <- fresh
    constrain $ tf ~: (te `fn` tv)
    return tv

infer env (IfThenElseExp e1 e2 e3) = do
    t1 <- infer env e1
    t2 <- infer env e2
    t3 <- infer env e3
    constrain $ t1 ~: boolTy
    constrain $ t2 ~: t3
    return t2

infer env (BinOpExp op e1 e2) = do
    t1 <- infer env e1
    t2 <- infer env e2
    let opTy = freshInst $ binopTySig op
    constrain $ opTy ~: (t1 `fn` t2 `fn` fresh)
    return fresh

infer env (MonOpExp op e) = do
    t <- infer env e
    let opTy = freshInst $ monopTySig op
    constrain $ opTy ~: (t `fn` fresh)
    return fresh

infer env (LetRecInExp f x e1 e2) = do
    tv1 <- fresh
    tv2 <- fresh
    let env' = H.insert x (Forall [] tv1) 
             $ H.insert f (Forall [] (tv1 `fn` tv2)) env
    t1 <- infer env' e1
    constrain $ tv2 ~: t1
    let env'' = H.insert f (GEN env $ unify $ tv2 ~: t1) env
    t2 <- infer env'' e2
    return t2

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
