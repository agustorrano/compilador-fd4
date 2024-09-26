{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module CEK where

import Lang
import Common 

import MonadFD4
import Eval (semOp)

type Env = [Val]

data Val =
    VNat Const
  | VClos Clos

data Clos =
    VClosfun Name Ty Env TTerm
  | VClosfix Name Ty Name Ty Env TTerm

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
seek (V info var) e k =
  case var of
    Bound n -> destroy (e !! n) k
    Global name ->
      do
        a <- lookupDecl name
        case a of
          Just t -> seek t e k
          Nothing -> failPosFD4 (fst info) "Esto esta mal"
seek (Const _ c) e k = destroy (VNat c) k
seek (Lam _ n ty (Sc1 tt)) e k = destroy (VClos (VClosfun n ty e tt)) k
seek (App _ t1 t2) e k = seek t1 e (KArg e t2:k) 
seek (Print _ str t1) e k = seek t1 e (KPrint str:k)
seek (BinaryOp _ op t1 t2) e k = seek t1 e (KBopt e op t2:k)
seek (Fix _ f ty1 x ty2 (Sc2 tt)) e k = destroy (VClos (VClosfix f ty1 x ty2 e tt)) k 
seek (IfZ _ t1 i d) e k = seek t1 e (KIfz e i d:k)
seek (Let _ _ _ t (Sc1 t')) e k = seek t e (KLet e t':k)

destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy v [] = do return v
destroy (VClos c) (KArg e t:k) = seek t e (KClos c:k)
destroy v (KClos (VClosfun _ _ e t):k) = seek t (v:e) k
destroy v (KClos l@(VClosfix _ _ _ _ e t):k) = seek t (v:VClos l:e) k
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

trash :: (Pos, Ty)
trash = (NoPos,NatTy)

-- TODO : TERMINAR :P
transform :: MonadFD4 m => Val -> m TTerm
transform (VNat c) = do return  (Const trash c) 
transform (VClos (VClosfun x ty e t)) = do return (Lam trash x ty (Sc1 t))
transform (VClos (VClosfix f ty1 x ty2 e t)) = do return (Fix trash f ty1 x ty2 (Sc2 t))