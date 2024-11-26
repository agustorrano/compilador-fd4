{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

{-|
Module      : Lang
Description : AST de términos, declaraciones y tipos
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Definiciones de distintos tipos de datos:
  - AST de términos
  - Declaraciones
  - Tipos
  - Variables

-}

module Lang where

import           Common                         ( Pos )
import           Data.List.Extra                ( nubSort )

-- | AST the términos superficiales
data STm info ty var =
    SV info var
  | SConst info Const
  | SLam info [([var], ty)] (STm info ty var)  -- Ahora tenemos lista de variables 
  | SApp info (STm info ty var) (STm info ty var)
  | SPrint info String (STm info ty var)
  | SBinaryOp info BinaryOp (STm info ty var) (STm info ty var)
  | SFix info (var, ty) [([var], ty)] (STm info ty var)
  | SIfZ info (STm info ty var) (STm info ty var) (STm info ty var)
  | SLet info Bool var [([var], ty)] ty (STm info ty var) (STm info ty var) -- Bool -> Rec or Not Rec; [] -> Let variable; (a:as) -> Let fun
    deriving (Show, Functor)


-- | AST de Tipos Superficiales
data STy =
      SNatTy
    | SFunTy STy STy
    | SNameTy Name deriving (Show, Eq)


-- | AST de Tipos
data Ty =
      NatTy (Maybe Name)
    | FunTy (Maybe Name) Ty Ty
      deriving (Show)

instance Eq Ty where
  NatTy _ == NatTy _ = True
  FunTy _ t1 t2 == FunTy _ t1' t2' = 
    t1 == t1' && t2 == t2'

instance Ord Ty where
  ty <= ty' = True

type Name = String

type STerm = STm Pos STy Name -- ^ 'STm' tiene 'Name's como variables ligadas y libres y globales, guarda posición  

newtype Const = CNat Int
  deriving Show

data BinaryOp = Add | Sub
  deriving Show

-- | tipo de datos de declaraciones superficiales
-- data SDecl info var ty a = SDLet info Bool (var, ty) [(var, ty)] a
data SDecl = 
    SDecl
  {
    sdeclPos    :: Pos,
    sdeclRec    :: Bool,
    sdeclVarTy  :: (Name, STy),
    sdeclList   :: [([Name], STy)],
    sdeclBody   :: STerm
  } 
  | SDeclTy
  { 
    sdeclPosTy  :: Pos,
    sdeclName   :: Name,
    sdeclBodyTy :: STy
  } 
    deriving Show

-- | tipo de datos de declaraciones, parametrizado por el tipo del cuerpo de la declaración
data Decl a = 
    Decl
  { 
    declPos  :: Pos,
    declName :: Name,
    declBody :: a
  }
    deriving (Show, Functor)

-- | AST de los términos. 
--   - info es información extra que puede llevar cada nodo. 
--       Por ahora solo la usamos para guardar posiciones en el código fuente.
--   - var es el tipo de la variables. Es 'Name' para fully named y 'Var' para locally closed. 
data Tm info var =
    V info var
  | Const info Const
  | Lam info Name Ty (Scope info var)
  | App info (Tm info var) (Tm info var)
  | Print info String (Tm info var)
  | BinaryOp info BinaryOp (Tm info var) (Tm info var)
  | Fix info Name Ty Name Ty (Scope2 info var)
  | IfZ info (Tm info var) (Tm info var) (Tm info var)
  | Let info Name Ty (Tm info var) (Scope info var)
  deriving (Show, Functor)


type Term = Tm Pos Var       -- ^ 'Tm' con índices de De Bruijn como variables ligadas, y nombres para libres y globales, guarda posición
type TTerm = Tm (Pos,Ty) Var -- ^ 'Tm' con índices de De Bruijn como variables ligadas, y nombres para libres y globales, guarda posición y tipo

type Module = [Decl TTerm]

data Var =
    Bound !Int
  | Free Name
  | Global Name
    deriving Show

-- Scope es un término con una o dos variables que escapan.
newtype Scope info var = Sc1 (Tm info var)
  deriving Functor
newtype Scope2 info var = Sc2 (Tm info var)
  deriving Functor
    
instance (Show info, Show var) => Show (Scope info var) where
    show (Sc1 t) = "{"++show t++"}"

instance (Show info, Show var) => Show (Scope2 info var) where
    show (Sc2 t) = "{{"++show t++"}}"

-- | Obtiene la info en la raíz del término.
getInfo :: Tm info var -> info
getInfo (V     i _       ) = i
getInfo (Const i _       ) = i
getInfo (Lam i _ _ _     ) = i
getInfo (App   i _ _     ) = i
getInfo (Print i _ _     ) = i
getInfo (Fix i _ _ _ _ _ ) = i
getInfo (IfZ i _ _ _     ) = i
getInfo (Let i _ _ _ _   ) = i
getInfo (BinaryOp i _ _ _) = i

getTy :: TTerm -> Ty
getTy = snd . getInfo

getPos :: TTerm -> Pos
getPos = fst . getInfo

-- | map para la info de un término
mapInfo :: (a -> b) -> Tm a var -> Tm b var
mapInfo f (V i x) = V (f i) x
mapInfo f (Const i x) = Const (f i) x
mapInfo f (Lam i x ty (Sc1 y)) = Lam (f i) x ty (Sc1 $ mapInfo f y)
mapInfo f (App i x y ) = App (f i) (mapInfo f x) (mapInfo f y)
mapInfo f (Print i msg y) = Print (f i) msg (mapInfo f y)
mapInfo f (BinaryOp i x y z ) = BinaryOp (f i) x (mapInfo f y) (mapInfo f z)
mapInfo f (Fix i x xty y yty (Sc2 z)) = Fix (f i) x xty y yty (Sc2 $ mapInfo f z)
mapInfo f (IfZ i x y z) = IfZ (f i) (mapInfo f x) (mapInfo f y) (mapInfo f z)
mapInfo f (Let i x xty y (Sc1 z)) = Let (f i) x xty (mapInfo f y) (Sc1 $ mapInfo f z)

-- | Obtiene los nombres de variables (abiertas o globales) de un término.
freeVars :: Tm info Var -> [Name]
freeVars tm = nubSort $ go tm [] where
  go (V _ (Free   v)          ) xs = v : xs
  go (V _ (Global v)          ) xs = v : xs
  go (V _ _                   ) xs = xs
  go (Lam _ _ _ (Sc1 t)       ) xs = go t xs
  go (App   _ l r             ) xs = go l $ go r xs
  go (Print _ _ t             ) xs = go t xs
  go (BinaryOp _ _ t u        ) xs = go t $ go u xs
  go (Fix _ _ _ _ _ (Sc2 t)   ) xs = go t xs
  go (IfZ _ c t e             ) xs = go c $ go t $ go e xs
  go (Const _ _               ) xs = xs
  go (Let _ _ _ e (Sc1 t)     ) xs = go e (go t xs)

freeVarsTy :: TTerm -> [(Name, Ty)]
freeVarsTy tm = nubSort $ go tm [] where
  go (V (_,ty) (Free   v)          ) xs = (v, ty) : xs
  go (V (_,ty) (Global v)          ) xs = (v, ty) : xs
  go (V _ _                   ) xs = xs
  go (Lam _ _ _ (Sc1 t)       ) xs = go t xs
  go (App _ l r             ) xs = go l $ go r xs
  go (Print _ _ t             ) xs = go t xs
  go (BinaryOp i _ t u        ) xs = go t $ go u xs
  go (Fix _ _ _ _ _ (Sc2 t)   ) xs = go t xs
  go (IfZ _ c t e             ) xs = go c $ go t $ go e xs
  go (Const _ _               ) xs = xs
  go (Let _ _ _ e (Sc1 t)     ) xs = go e (go t xs)

-- Obtenemos el tipo de la función a partir de la lista de variables,
-- devolviendo una función para despues completar con el tipo de retorno.
getType :: [([Name],STy)] -> (STy -> STy)
getType [] = id
getType (([x],ty):ls) =
  let g = getType ls
  in SFunTy ty . g
getType ((x:xs,ty):ls) =
  let g = getType ((xs,ty):ls)
  in SFunTy ty . g

-- Obetemos el tipo de retorno, desarmando el tipo de la función por cada una
-- de las variables que toma com argumento.
unType :: STy -> [([Name],STy)] -> STy
unType ty [] = ty 
unType (SFunTy _ ty) (([x],ty'):xs) = unType ty xs
unType (SFunTy _ ty) ((x:xs',ty'):xs) = unType ty ((xs',ty'):xs)

-- Convertimos a términos azucarados, ya que openAll nos da la representación
-- sin azucar de STerm. 
resugaring :: STerm -> STerm
resugaring (SLam i [l@(xs,ty)] t) = 
  let t'' = resugaring t
  in case t'' of
    SLam _ ls@((xs',ty'):ps) t' ->
      if ty == ty'
      then SLam i ((xs ++ xs',ty):ps) t' 
      else SLam i (l:ls) t'
    _ -> 
      SLam i [l] t''

resugaring (SFix i (f, fty) [l@(xs,ty)] t) =
  let t'' = resugaring t
  in case t'' of
    SLam _ ls@((xs',ty'):ps) t' ->
      if ty == ty'
      then SFix i (f, fty) ((xs ++ xs',ty):ps) t'
      else SFix i (f, fty) (l:ls) t'
    _ -> 
      SFix i (f, fty) [l] t''

resugaring (SLet i False f [] fty t1 t2) =
  let (t1', t2') = (resugaring t1, resugaring t2)
  in case t1' of
    SLam _ ls t ->
      SLet i False f ls (unType fty ls) t t2'
    SFix _ _ ls t ->
      SLet i True f ls (unType fty ls) t t2' 
    _ -> 
      SLet i False f [] fty t1' t2'

resugaring t = t