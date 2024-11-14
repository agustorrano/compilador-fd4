{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module ClosureConvert where

import Lang
import IR
import C
import Subst

import Control.Monad.State
import Control.Monad.Writer

type CC = StateT Int (Writer [IrDecl])

irTy :: Ty -> IrTy
irTy (NatTy _) = IrInt
irTy FunTy {} = IrClo

getFreshName :: String -> CC String
getFreshName str = do
    n <- get
    put $ n + 1
    return $ str ++ show n

var2ir :: [Name] -> Name -> Int -> Ir -> Ir
var2ir [] _ _ ir = ir
var2ir (n:ns) clos i ir =
    let ir' = IrAccess (IrVar clos) IrInt i 
    in IrLet n IrInt ir' (var2ir ns clos (i + 1) ir)


closureConvert' :: Term -> Name -> CC Ir
closureConvert' (Lam _ n _ s@(Sc1 t)) clos = do
    f <- getFreshName "__f"
    ir <- closureConvert (open n s)
    ir' <- closureConvert t
    let fv = freeVars t
        body = var2ir fv clos 1 ir
        decl = IrFun f IrInt [(n, IrInt)] body
    tell [decl]
    return $ MkClosure f (map IrVar fv)
closureConvert' (Fix _ f _ n ty' s@(Sc2 t)) clos = do
    ir <- closureConvert (open2 clos n s)
    ir' <- closureConvert t
    let fv = freeVars t
        body = var2ir fv clos 1 ir
        decl = IrFun f IrInt [(n, IrInt)] body
    tell [decl]
    return $ MkClosure f (map IrVar fv)

closureConvert :: Term -> CC Ir
closureConvert (V _ (Global n)) = return $ IrGlobal n
closureConvert (V _ (Free n)) = return $ IrVar n
closureConvert (V _ (Bound i)) = undefined
closureConvert (Const _ c) = return $ IrConst c
closureConvert' (Lam _ n _ s@(Sc1 t)) =
    clos <- 
closureConvert (App _ t t') = do
    clos <- getFreshName "__clos"
    ir1 <- closureConvert' t clos
    ir2 <- closureConvert t'
    let ir3 = IrCall (IrAccess (IrVar clos) IrFunTy 0) [IrVar clos, ir2] IrInt
    return $ IrLet clos IrClo ir1 ir3
closureConvert (Print _ str t) = do
    ir <- closureConvert t
    return $ IrPrint str ir
closureConvert (BinaryOp _ op t t') = do
    ir1 <- closureConvert t
    ir2 <- closureConvert t'
    return $ IrBinaryOp op ir1 ir2
closureConvert (IfZ _ t t' t'') = do
    ir1 <- closureConvert t
    ir2 <- closureConvert t'
    ir3 <- closureConvert t''
    return $ IrIfZ ir1 ir2 ir3
closureConvert (Let _ n ty t s) = do
    ir1 <- closureConvert t
    ir2 <- closureConvert (open n s)
    return $ IrLet n (irTy ty) ir1 ir2

runCC :: [Decl Term] -> [IrDecl]
runCC 
