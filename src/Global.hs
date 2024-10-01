{-|
Module      : Global
Description : Define el estado global del compilador
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}
module Global where

import Lang

data GlEnv = GlEnv {
  inter :: Bool,            --  ^ True, si estamos en modo interactivo.
                            -- Este parámetro puede cambiar durante la ejecución:
                            -- Es falso mientras se cargan archivos, pero luego puede ser verdadero.
  lfile :: String,          -- ^ Último archivo cargado.
  cantTermDecl :: Int,      -- ^ Cantidad de declaraciones de términos desde la última carga
  cantTyDecl :: Int,        -- ^ Cantidad de declaraciones de tipos desde la última carga
  glbTerm :: [Decl TTerm],  -- ^ Entorno con declaraciones globales
  glbTy :: [Decl Ty]        -- ^ Entorno con declaraciones globales
}

-- Entorno de tipado de declaraciones globales para términos
tyTermEnv :: GlEnv ->  [(Name,Ty)]
tyTermEnv g = map (\(Decl _ n ty _) -> (n, ty))  (glbTerm g)

tyEnv :: GlEnv -> [(Name, Ty)]
tyEnv g = map (\(Decl _ n ty _) -> (n, ty)) (glbTy g)

{-
 Tipo para representar las banderas disponibles en línea de comando.
-}
data Mode =
    Interactive
  | Typecheck
  | Eval
data Conf = Conf {
    opt :: Bool,          --  ^ True, si estan habilitadas las optimizaciones.
    modo :: Mode
}

-- | Valor del estado inicial
initialEnv :: GlEnv
initialEnv = GlEnv False "" 0 0 [] []
