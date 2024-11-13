{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module ClosureConvert where

import Lang
import IR
import C

import Control.Monad.State
import Control.Monad.Writer

type CC = StateT Int (Writer [IrDecl])

irTy :: Ir -> CC IrTy
--irTy (IrVar n) = undefined
--irTy (IrGlobal n) = undefined
irTy (IrCall _ _ ty) = return ty
irTy (IrConst _) = return IrInt
irTy (IrPrint _ ir) = irTy ir
irTy IrBinaryOp {} = return IrInt 
irTy (IrLet _ _ _ ir) = irTy ir
irTy (IrIfZ _ ir _) = irTy ir
irTy (MkClosure _ (ir:_)) = irTy ir
irTy (IrAccess _ ty _) = return ty

getFreshName :: String -> CC String
getFreshName str = do
    n <- get
    put $ n + 1
    return $ str ++ show n

closureConvert :: Term -> CC Ir
closureConvert (V _ (Global n)) = return $ IrGlobal n
closureConvert (V _ (Free n)) = return $ IrVar n
closureConvert (V _ (Bound i)) = undefined
closureConvert (Const _ c) = return $ IrConst c
closureConvert (Lam _ n ty s@(Sc1 t)) = do
    ir <- closureConvert t
    ir' <- closureConvert (open n s)
    
closureConvert (App _ t t') = do
    ir1 <- closureConvert t
    ir2 <- closureConvert t'
    ty1 <- irTy ir1
    clos <- getFreshName "__clos"
    let ir3 = IrCall (IrAccess ir1 ty1 0) [ir1, ir2] IrInt
    return $ IrLet clos ty1 ir1 ir3
closureConvert (Print _ str t) = do
    ir <- closureConvert t
    return $ IrPrint str ir
closureConvert (BinaryOp _ op t t') = do
    ir1 <- closureConvert t
    ir2 <- closureConvert t'
    return $ IrBinaryOp op ir1 ir2
closureConvert (Fix _ n ty n' ty' (Sc2 t')) = undefined
closureConvert (IfZ _ t t' t'') = do
    ir1 <- closureConvert t
    ir2 <- closureConvert t'
    ir3 <- closureConvert t''
    return $ IrIfZ ir1 ir2 ir3
closureConvert (Let _ n ty t (Sc1 t')) = undefined