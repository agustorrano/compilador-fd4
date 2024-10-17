{-|
Module      : Common
Description : Algunas operaciones generales
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Common where

--------------------------
-- Posición en un archivo
--------------------------
type Line = Int
type Column = Int

data Pos = NoPos             -- ^ No hay info de posición
         | Pos !Line !Column -- ^ Posición en un archivo.

instance Show Pos where
   show (Pos line column) = "("++show line++","++show column++")"
   show NoPos = ""

instance Semigroup Pos where
  i <> NoPos = i
  _ <> i     = i

instance Monoid Pos where
  mempty = NoPos
---------------------
-- Utility functions
--------------------
abort :: String -> a
abort s = error ("INTERNAL ERROR: " ++ s)

infixl 1 |>
(|>) :: a -> (a -> b) -> b
x |> f = f x

-- Asumimos que se recibe un string de la forma asdfsadf.algo
changeExtension :: String -> String -> String
changeExtension [] ext = ext
changeExtension ('.':rest) ext = ext
changeExtension (a:rest) ext = a :changeExtension rest ext
