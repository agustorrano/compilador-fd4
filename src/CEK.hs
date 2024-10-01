{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module CEK where

import Lang
import Common 

import MonadFD4
import Eval (semOp)
import Subst (varChanger)
import Data.Maybe (fromJust)

type Env = [Val]

data Val =
    VNat Const
  | VClos Clos

data Clos =
    VClosfun Env Name Ty TTerm
  | VClosfix Env Name Ty Name Ty TTerm

instance (Show Val) where
  show (VNat (CNat n)) = show n
  show _ = undefined

data Frame =
    KArg Env TTerm
  | KClos Clos
  | KIfz Env TTerm TTerm
  | KBopt Env BinaryOp TTerm
  | KBopv Val BinaryOp 
  | KPrint String
  | KLet Env TTerm

type Kont = [Frame]

seek :: MonadFD4 m => TTerm -> Env -> Kont -> m Val
seek (V info (Bound n)) e k = destroy (e !! n) k
seek (V info (Global name)) e k = 
  do
    a <- lookupTermDecl name
    let t = fromJust a
    seek t e k
seek (Const _ c) e k = destroy (VNat c) k
seek (Lam _ n ty (Sc1 t)) e k = destroy (VClos (VClosfun e n ty t)) k
seek (App _ t1 t2) e k = seek t1 e (KArg e t2:k) 
seek (Print _ str t1) e k = seek t1 e (KPrint str:k)
seek (BinaryOp _ op t1 t2) e k = seek t1 e (KBopt e op t2:k)
seek (Fix _ f ty1 x ty2 (Sc2 t)) e k = destroy (VClos (VClosfix e f ty1 x ty2 t)) k 
seek (IfZ _ t1 i d) e k = seek t1 e (KIfz e i d:k)
seek (Let _ _ _ t (Sc1 t')) e k = seek t e (KLet e t':k)

destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy v [] = do return v
destroy (VClos c) (KArg e t:k) = seek t e (KClos c:k)
destroy v (KClos (VClosfun e _ _ t):k) = seek t (v:e) k
destroy v (KClos l@(VClosfix e _ _ _ _ t):k) = seek t (v:VClos l:e) k
destroy v (KPrint s:k) = do {printFD4 $ s ++ show v; destroy v k}
destroy v (KLet e t:k) = seek t (v:e) k
destroy n (KBopt e op t:k) = seek t e (KBopv n op:k)
destroy n (KBopv v op:k) =
  let f (VNat (CNat i)) = i
      j = f v
      j' = f n
  in  destroy (VNat (CNat $ semOp op j j')) k
destroy (VNat (CNat 0)) (KIfz e t1 _:k) = seek t1 e k    
destroy _ (KIfz e _ t1:k) = seek t1 e k    

evalCEK :: MonadFD4 m => TTerm -> m Val
evalCEK tt = seek tt [] []

fvInstance :: [Tm info Var] -> Tm info Var -> Tm info Var
fvInstance e = varChanger (\_ p n -> V p (Free n)) bnd
  where lim = length e 
        bnd _ p i | i < lim = e !! i
                  | otherwise = V p $ Bound (i - lim) 

transform :: MonadFD4 m => Val -> m TTerm
transform (VNat c) = do return  (Const (NoPos, NatTy Nothing) c) 
transform (VClos (VClosfun e x ty t)) = 
  do
    ts <- mapM transform e
    let t' = fvInstance ts t 
    let info = (NoPos, FunTy Nothing ty (getTy t'))
    return (Lam info x ty (Sc1 t'))
transform (VClos (VClosfix e f ty1 x ty2 t)) = 
  do
    ts <- mapM transform e
    let t' = fvInstance ts t 
    let info = (NoPos, ty1)
    return (Fix info f ty1 x ty2 (Sc2 t'))