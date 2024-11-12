module ClosureConvert where

import Lang
import Ir
import C

import Control.Monad.State
import Control.Monad.Writer

closureConvert :: Term -> StateT Int (Writer [IrDecl]) Ir
closureConvert (V _ (Global n)) = undefined
closureConvert (V _ (Free n)) = undefined
closureConvert (V _ (Bound i)) = undefined
closureConvert (Const _ c) = return $ IrConst c
closureConvert (Lam _ n ty (Sc1 t)) = undefined
closureConvert (App _ t t') = undefined
closureConvert (Print _ str t) = undefined
closureConvert (BinaryOp _ op t t') = do
    ir1 <- closureConvert t
    ir2 <- closureConvert t'
    return $ IrBinaryOp op ir1 ir2
closureConvert (Fix _ n ty n ty' (Sc2 t')) = undefined
closureConvert (IfZ _ t t' t'') = do
    ir1 <- closureConvert t
    ir2 <- closureConvert t'
    ir3 <- closureConvert t''
    return $ IrIfZ ir1 ir2 ir3
closureConvert (Let _ n ty t (Sc1 t')) = undefined