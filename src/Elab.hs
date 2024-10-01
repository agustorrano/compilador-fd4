{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-|
Module      : Elab
Description : Elabora un término fully named a uno locally closed.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite elaborar términos y declaraciones para convertirlas desde
fully named (@STerm) a locally closed (@Term@)
-}

module Elab (elab, elabTyDecl, elabTermDecl) where

import Lang
import Subst
import MonadFD4 (MonadFD4, failPosFD4, lookupTyDecl)
import Data.Maybe (fromJust)

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab :: MonadFD4 m => STerm -> m Term
elab = elab' []

elabTy :: MonadFD4 m => STy -> m Ty
elabTy SNatTy = return $ NatTy Nothing
elabTy (SFunTy st st') = 
  do
    t <- elabTy st
    t' <- elabTy st'
    return $ FunTy Nothing t t'
elabTy (SNameTy name) =
  do
    jt <- lookupTyDecl name
    let t = fromJust jt
    return t 


elab' :: MonadFD4 m => [Name] -> STerm -> m Term
elab' env (SV p v) =
  -- Tenemos que ver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.
  do
  if v `elem` env 
    then return $ V p (Free v)
    else return $ V p (Global v)

elab' _ (SConst p c) = do return $ Const p c

-- SLam
elab' env (SLam p [([x],ty)] t) = do 
  t' <- elab' (x:env) t
  ty' <- elabTy ty
  return $ Lam p x ty' (close x t')

elab' env (SLam p [(x:xs,ty)] t) = do
  t' <- elab' (x:env) (SLam p [(xs,ty)] t)
  ty' <- elabTy ty
  return $ Lam p x ty' (close x t')

elab' env (SLam p (([x],ty):ls) t) = do
  t' <- elab' (x:env) (SLam p ls t)
  ty' <- elabTy ty
  return $ Lam p x ty' (close x t')

elab' env (SLam p ((x:xs,ty):ls) t) = do
  t' <- elab' (x:env) (SLam p ((xs,ty):ls) t)
  ty' <- elabTy ty
  return $ Lam p x ty' (close x t')

--SFix
elab' env (SFix p (f,fty) [([x],ty)] t) = do
  t' <- elab' (x:f:env) t
  ty' <- elabTy ty
  fty' <- elabTy fty
  return $ Fix p f fty' x ty' (close2 f x t')

elab' env (SFix p (f,fty) [(x:xs,ty)] t) = do
  let t' = SLam p [(xs,ty)] t
  t'' <- elab' (x:f:env) t'
  ty' <- elabTy ty
  fty' <- elabTy fty
  return $ Fix p f fty' x ty' (close2 f x t'')

elab' env (SFix p (f,fty) (([x],ty):ls) t) = do
  let t' = SLam p ls t
  t'' <- elab' (x:f:env) t'
  ty' <- elabTy ty
  fty' <- elabTy fty
  return $ Fix p f fty' x ty' (close2 f x t'')

elab' env (SFix p (f,fty) ((x:xs,ty):ls) t) = do
  let t' = SLam p ((xs,ty):ls) t
  t'' <- elab' (x:f:env) t'
  ty' <- elabTy ty
  fty' <- elabTy fty
  return $ Fix p f fty' x ty' (close2 f x t'')

--SIfZ
elab' env (SIfZ p c t e) =
  do 
    t1 <- elab' env c
    t2 <- elab' env t
    t3 <- elab' env e
    return $ IfZ p t1 t2 t3

-- Operadores binarios
elab' env (SBinaryOp i o t u) =
  do
    t1 <- elab' env t
    t2 <- elab' env u
    return $ BinaryOp i o t1 t2

-- Operador Print
elab' env (SPrint i str t) =
  do
    t' <- elab' env t
    return $ Print i str t'

-- Aplicaciones generales
elab' env (SApp p h a) =
  do
    t <- elab' env h
    t' <- elab' env a
    return $ App p t t'

-- Let para variables
elab' env (SLet p b v [] vty def body) =  
  if b
  then failPosFD4 p "Let Recursivo sin argumentos"
  else
    do
      t <- elab' env def
      t' <- elab' (v:env) body
      vty' <- elabTy vty
      return $ Let p v vty' t (close v t')

-- Let para funciones
elab' env (SLet p False v xs vty def body) =  
  do
    t <- elab' env (SLam p xs def) 
    t' <- elab' (v:env) body
    let f = getType xs
    vty' <- elabTy (f vty)
    return $ Let p v vty' t (close v t')

-- Let Rec
elab' env (SLet p True v xs vty def body) =  
  do
    let vty' = getType xs vty
    t1 <- elab' env (SFix p (v,vty') xs def)
    t2 <- elab' (v:env) body
    vty'' <- elabTy vty'
    return $ Let p v vty'' t1 (close v t2)

elabTermDecl :: MonadFD4 m => SDecl ->  m (Ty ,Decl Term)
elabTermDecl (SDecl p b (v,vty) [] dec) = 
  if b
  then failPosFD4 p "Let Recursivo sin argumentos"
  else do
    t <- elab dec
    vty' <- elabTy vty
    return (vty', Decl p v t) 
elabTermDecl (SDecl p False (v,vty) xs dec) =
  do
    let vty' = getType xs vty 
    t <- elab (SLam p xs dec) 
    vty'' <- elabTy vty'
    return (vty'', Decl p v t)
elabTermDecl (SDecl p True l1@(v,vty) xs dec) =
  do
    let vty' = getType xs vty 
    t1 <- elab (SFix p (v, vty') xs dec)
    vty'' <- elabTy vty'
    return (vty'', Decl p v t1)

elabTyDecl :: MonadFD4 m => SDecl -> m (Decl Ty)
elabTyDecl (SDeclTy p n SNatTy) =
  do
    let ty = NatTy (Just n)
    return $ Decl p n ty 
elabTyDecl (SDeclTy p n (SFunTy sty sty')) =
  do 
    ty <- elabTy sty
    ty' <- elabTy sty'
    let fty = FunTy (Just n) ty ty'
    return $ Decl p n fty
elabTyDecl (SDeclTy p n (SNameTy n')) =
  do
    ty <- lookupTyDecl n'
    let ty' = change n (fromJust ty)
    return $ Decl p n ty'
  where
    change na (NatTy _) = NatTy (Just na)
    change na (FunTy _ a b) = FunTy (Just na) a b