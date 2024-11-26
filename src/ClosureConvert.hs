{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module ClosureConvert where

import Lang
import IR
import Subst

import Control.Monad.State
import Control.Monad.Writer


data IrEnv = IrEnv {
    closInt :: Int,
    funInt :: Int,
    varInt :: Int
}

type CC = StateT IrEnv (Writer [IrDecl])

initialIrEnv :: IrEnv
initialIrEnv = IrEnv 0 0 0

ty2irTy :: Ty -> IrTy
ty2irTy (NatTy _) = IrInt
ty2irTy FunTy {} = IrClo

getFreshNameClos :: CC String
getFreshNameClos = do
    n <- gets closInt
    modify (\s -> s { closInt = n + 1 })
    return $ "clos" ++ show n

getFreshNameFun :: CC String
getFreshNameFun = do
    n <- gets funInt
    modify (\s -> s { funInt = n + 1 })
    return $ "g" ++ show n

getFreshNameVar :: CC String
getFreshNameVar = do
    n <- gets varInt
    modify (\s -> s { varInt = n + 1 })
    return $ "x" ++ show n

var2ir :: [(Name,Ty)] -> Name -> Int -> Ir -> CC Ir
var2ir [] _ _ ir = return ir
var2ir ((n,ty):ns) clos i ir = do
    let irty = ty2irTy ty
        ir' = IrAccess (IrVar clos) irty i
    ir'' <- var2ir ns clos (i + 1) ir
    return $ IrLet n irty ir' ir''

closureConvert :: TTerm -> CC Ir
closureConvert (V _ (Global n)) = return $ IrGlobal n
closureConvert (V _ (Free n)) = return $ IrVar n
closureConvert (V _ (Bound i)) = undefined
closureConvert (Const _ c) = return $ IrConst c
closureConvert (Lam (_, FunTy _ _ ty') n ty s@(Sc1 t)) = do
    x <- getFreshNameVar
    f <- getFreshNameFun
    clos <- getFreshNameClos
    ir <- closureConvert (open x s)
    let fv = freeVarsTy t
    body <- var2ir fv clos 1 ir
    let decl = IrFun f (ty2irTy ty') [(clos, IrClo), (x, ty2irTy ty)] body
    tell [decl]
    return $ MkClosure f (map (IrVar . fst) fv)
closureConvert (App (_, ty) t t') = do
    clos <- getFreshNameClos
    ir1 <- closureConvert t
    ir2 <- closureConvert t'
    let ir3 = IrCall (IrAccess (IrVar clos) IrFunTy 0) [IrVar clos, ir2] (ty2irTy ty)
    return $ IrLet clos IrClo ir1 ir3
closureConvert w@(Print _ str t) = do
    x <- getFreshNameVar
    ir <- closureConvert t
    return $ IrLet x IrInt ir (IrPrint str (IrVar x))
closureConvert (BinaryOp _ op t t') = do
    ir1 <- closureConvert t
    ir2 <- closureConvert t'
    return $ IrBinaryOp op ir1 ir2
closureConvert(Fix (_, FunTy _ _ ty'') f ty n ty' s@(Sc2 t)) = do
    x <- getFreshNameVar
    f' <- getFreshNameFun
    clos <- getFreshNameClos
    ir <- closureConvert (open2 clos x s)
    let fv = freeVarsTy t
    body <- var2ir fv clos 1 ir
    let decl = IrFun f' (ty2irTy ty'') [(clos, IrClo), (x, ty2irTy ty')] body
    tell [decl]
    return $ MkClosure f' (map (IrVar . fst) fv)
closureConvert (IfZ _ t t' t'') = do
    ir1 <- closureConvert t
    ir2 <- closureConvert t'
    ir3 <- closureConvert t''
    return $ IrIfZ ir1 ir2 ir3
closureConvert (Let _ n ty t s) = do
    x <- getFreshNameVar
    ir1 <- closureConvert t
    ir2 <- closureConvert (open x s)
    return $ IrLet x (ty2irTy ty) ir1 ir2

term2irval :: Decl TTerm -> CC ()
term2irval (Decl _ n b) = do
    ir <- closureConvert b
    let decl = IrVal n (ty2irTy (getTy b)) ir
    tell [decl]

initCC :: [Decl TTerm] -> CC ()
initCC ls = do
    tell []
    mapM_ term2irval ls

runCC :: [Decl TTerm] -> [IrDecl]
runCC decls = execWriter $ runStateT (initCC decls) initialIrEnv
