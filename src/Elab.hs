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

module Elab ( elab, elabDecl) where

import Lang
import Subst
import MonadFD4 (MonadFD4,failPosFD4)

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab :: MonadFD4 m => STerm -> m Term
elab = elab' []

elab' :: MonadFD4 m => [Name] -> STerm -> m Term
elab' env (SV p v) =
  -- Tenemos que ver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.
  do
  if v `elem` env 
    then return $ V p (Free v)
    else return $ V p (Global v)

elab' _ (SConst p c) = do return $ Const p c
elab' env (SLam p [(v,ty)] t) = 
  do 
    t' <- elab' (v:env) t
    return $ Lam p v ty (close v t')
elab' env (SLam p ((v,ty):xs) t) =
  do
   t' <- elab' (v:env) (SLam p xs t)
   return $ Lam p v ty (close v t')
elab' env (SFix p (f,fty) [(x,xty)] t) =
  do
    t' <- elab' (x:f:env) t
    return $ Fix p f fty x xty (close2 f x t')
elab' env (SFix p (f,fty) ((x,xty):xs) t) =
  do
    let t' = SLam p xs t
    t'' <- elab' (x:f:env) t'
    return $ Fix p f fty x xty (close2 f x t'')
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
elab' env (SLet p b (v,vty) [] def body) =  
  if b
  then failPosFD4 p "Let Recursivo sin argumentos"
  else
    do
      t <- elab' env def
      t' <- elab' (v:env) body
      return $ Let p v vty t (close v t')
-- Let para funciones
elab' env (SLet p False (v,vty) xs def body) =  
  do
    t <- elab' env (SLam p xs def) 
    t' <- elab' (v:env) body
    return $ Let p v vty t (close v t')
-- Let Rec
elab' env (SLet p True l1@(v,vty) xs def body) =  
  do
    t1 <- elab' env (SFix p l1 xs def)
    t2 <- elab' (v:env) body
    return $ Let p v vty t1 (close v t2)

elabDecl :: MonadFD4 m => SDecl STerm ->  m (Decl Term)
elabDecl (SDecl p b (v,vty) [] dec) = 
  if b
  then failPosFD4 p "Let Recursivo sin argumentos"
  else do
    t <- elab dec
    return $ Decl p v t 
elabDecl (SDecl p False (v,vty) xs dec) =
  do
    t <- elab (SLam p xs dec) 
    return $ Decl p v t 
elabDecl (SDecl p True l1@(v,vty) xs dec) =
  do
    t1 <- elab (SFix p l1 xs dec)
    return $ Decl p v t1

-- elabDecl :: MonadFD4 m => SDecl STerm -> m (Decl Term)
-- elabDecl (SDecl p False (v,vty) [] dec) = 
--   do
--     t <- elab dec
--     return $ Decl p v t 
-- elabDecl (SDecl p True (v,vty) [] t) = 
--   failPosFD4 p "Let Recursivo sin argumentos"
-- elabDecl (SDecl p False (v,vty) xs dec) =
--   do 
--     t <- elab (SLam p xs dec)
--     return $ Decl p v t
-- elabDecl (SDecl p True l@(v,vty) xs dec) =
--   do
--     t <- elab dec
--     return $ Decl p v (SFix p l xs t)
