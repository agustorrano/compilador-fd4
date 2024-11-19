module ClosureConvert where

import Lang
import IR
import Subst

import Control.Monad.State
import Control.Monad.Writer
import Data.Maybe ( fromJust )


data IrEnv = IrEnv {
    closInt :: Int,
    funInt :: Int,
    vars :: [(Name, IrTy)]
}

type CC = StateT IrEnv (Writer [IrDecl])

initialIrEnv :: IrEnv
initialIrEnv = IrEnv 0 0 []

ty2irTy :: Ty -> IrTy
ty2irTy (NatTy _) = IrInt
ty2irTy FunTy {} = IrClo

getFreshNameClos :: CC String
getFreshNameClos = do
    n <- gets closInt
    modify (\s -> s { closInt = n + 1 })
    return $ "__clos" ++ show n

getFreshNameFun :: CC String
getFreshNameFun = do
    n <- gets funInt
    modify (\s -> s { funInt = n + 1 })
    return $ "__f" ++ show n

addVars :: (Name, IrTy) -> CC ()
addVars (n, ty) = modify (\s -> s { vars = (n, ty) : vars s })

resetVars :: CC ()
resetVars = modify (\s -> s { vars = [] })

lookupTy :: Name -> CC IrTy
lookupTy nm = do
    gets (fromJust . lookup nm . vars)

var2ir :: [Name] -> Name -> Int -> Ir -> CC Ir
var2ir [] _ _ ir = return ir
var2ir (n:ns) clos i ir = do
    ty <- lookupTy n
    let ir' = IrAccess (IrVar clos) ty i
    ir'' <- var2ir ns clos (i + 1) ir
    return $ IrLet n ty ir' ir''

closureConvert :: TTerm -> CC Ir
closureConvert (V _ (Global n)) = return $ IrGlobal n
closureConvert (V _ (Free n)) = return $ IrVar n
closureConvert (V _ (Bound i)) = undefined
closureConvert (Const _ c) = return $ IrConst c
closureConvert (Lam _ n ty s@(Sc1 t)) = do
    f <- getFreshNameFun
    clos <- getFreshNameClos
    ir <- closureConvert (open n s)
    addVars (n, ty2irTy ty)
    let fv = freeVars t
    body <- var2ir fv clos 1 ir
    let decl = IrFun f IrInt [(clos, IrClo), (n, IrInt)] body
    tell [decl]
    return $ MkClosure f (map IrVar fv)
closureConvert (App _ t@Lam {} t') = do
    clos <- getFreshNameClos
    ir1 <- closureConvert t
    ir2 <- closureConvert t'
    let ir3 = IrCall (IrAccess (IrVar clos) IrFunTy 0) [IrVar clos, ir2] IrInt
    return $ IrLet clos IrClo ir1 ir3
closureConvert (App (_, ty) t t') = do
    ir1 <- closureConvert t
    ir2 <- closureConvert t'
    let ir3 = IrCall (IrAccess ir1 IrFunTy 0) [ir1, ir2] (ty2irTy ty)
    return ir3
closureConvert (Print _ str t) = do
    ir <- closureConvert t
    return $ IrPrint str ir
closureConvert (BinaryOp _ op t t') = do
    ir1 <- closureConvert t
    ir2 <- closureConvert t'
    return $ IrBinaryOp op ir1 ir2
closureConvert (Fix _ f ty n ty' s@(Sc2 t)) = do
    clos <- getFreshNameClos
    ir <- closureConvert (open2 f n s)
    addVars (n, ty2irTy ty')
    addVars (f, ty2irTy ty)
    let fv = freeVars t
    body <- var2ir fv clos 1 ir
    let decl = IrFun f IrInt [(clos, IrClo), (n, IrInt)] body
    tell [decl]
    return $ MkClosure f (map IrVar fv)
closureConvert (IfZ _ t t' t'') = do
    ir1 <- closureConvert t
    ir2 <- closureConvert t'
    ir3 <- closureConvert t''
    return $ IrIfZ ir1 ir2 ir3
closureConvert (Let _ n ty t s) = do
    ir1 <- closureConvert t
    ir2 <- closureConvert (open n s)
    addVars (n, ty2irTy ty)
    return $ IrLet n (ty2irTy ty) ir1 ir2

term2irval :: Decl TTerm -> CC ()
term2irval (Decl _ n b) = do
    ir <- closureConvert b
    resetVars
    let decl = IrVal n (ty2irTy (getTy b)) ir
    tell [decl]

initCC :: [Decl TTerm] -> CC ()
initCC ls = do
    tell []
    mapM_ term2irval ls

runCC :: [Decl TTerm] -> [IrDecl]
runCC decls = execWriter $ runStateT (initCC decls) initialIrEnv
