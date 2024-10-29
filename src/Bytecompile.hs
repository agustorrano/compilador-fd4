{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-|
Module      : Bytecompile
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite compilar módulos a la Macchina. También provee
una implementación de la Macchina para ejecutar el bytecode.
-}
module Bytecompile
  (Bytecode, runBC, bcWrite, bcRead, bytecompileModule, showBC)
 where

import Lang
import Subst
import MonadFD4 ( failFD4, printFD4, printNoLnFD4, MonadFD4 )
import Eval

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le )
import Data.Binary.Get ( getWord32le, isEmpty )

import Data.List (intercalate)
import Data.Char

type Opcode = Int
type Bytecode = [Int]

newtype Bytecode32 = BC { un32 :: [Word32] }

data Val = I Int | Fun Env Bytecode | RA Env Bytecode
type Env = [Val]
type Stack = [Val]

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord32le bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord32le
                      BC xs <- go
                      return $ BC (x:xs)

{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:

   f (CALL : cs) = ...

 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.

 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern NULL     = 0
pattern RETURN   = 1
pattern CONST    = 2
pattern ACCESS   = 3
pattern FUNCTION = 4
pattern CALL     = 5
pattern ADD      = 6
pattern SUB      = 7
pattern FIX      = 9
pattern STOP     = 10
pattern SHIFT    = 11
pattern DROP     = 12
pattern PRINT    = 13
pattern PRINTN   = 14
pattern JUMP     = 15
pattern IFZ      = 16
pattern TAILCALL = 17

--función util para debugging: muestra el Bytecode de forma más legible.
showOps :: Bytecode -> [String]
showOps [] = []
showOps (NULL:xs)        = "NULL" : showOps xs
showOps (RETURN:xs)      = "RETURN" : showOps xs
showOps (CONST:i:xs)     = ("CONST " ++  show i) : showOps xs
showOps (ACCESS:i:xs)    = ("ACCESS " ++ show i) : showOps xs
showOps (FUNCTION:i:xs)  = ("FUNCTION len=" ++ show i) : showOps xs
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (FIX:xs)         = "FIX" : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
showOps (JUMP:i:xs)      = ("JUMP off=" ++ show i) : showOps xs
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (IFZ:xs)         = "IFZ" : showOps xs
showOps (PRINT:xs)       = let (msg,_:rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string msg)) : showOps rest
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (x:xs)           = show x : showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

bc :: MonadFD4 m => TTerm -> m Bytecode
bc tt = bcc tt []

bcc :: MonadFD4 m => TTerm -> Bytecode -> m Bytecode
bcc (V i (Bound n)) b = return (ACCESS:n:b)
bcc (V i (Free name)) b = do failFD4 "Variable libre encontrada bcc"
bcc (V i (Global name)) b = failFD4 "Variable global encontrada"
bcc (Const i (CNat n)) b = return (CONST:n:b)
bcc (Lam i n ty (Sc1 t)) b = do
  bco <- bct t []
  let l = length bco
  return $ (FUNCTION:l + 1:bco) ++ (RETURN:b)
bcc (App i t t') b = do
  be <- bcc t' (CALL:b)
  bcc t be 
bcc (Print i str t) b = do
  let strc = string2bc str
  let b' = (PRINT:strc) ++ (NULL:PRINTN:b) 
  bcc t b' 
bcc (BinaryOp i op t t') b = do
  let opc = aux op
  b' <- bcc t' (opc:b)
  bcc t b'
  where aux Add = ADD
        aux Sub = SUB
bcc (Fix i f fty x ty (Sc2 t)) b = do
  bco <- bc t
  let l = length bco
  return $ (FUNCTION:l+1:bco) ++ (RETURN:FIX:b)
bcc (IfZ i t1 t2 t3) b = do
  b'' <- bc t2 
  b''' <- bc t3
  let (l1,l2) = (length b'',length b''')
  bcc t1 $ (IFZ:l1+2:b'') ++ (JUMP:l2:b''') ++ b
bcc (Let i x ty t (Sc1 t')) b@[STOP] = do
  be <- bcc t' b
  bcc t (SHIFT:be)
bcc (Let i x ty t (Sc1 t')) b@(RETURN:_) = do
  be <- bcc t' b
  bcc t (SHIFT:be)
bcc (Let i x ty t (Sc1 t')) b = do
  be <- bcc t' (DROP:b)
  bcc t (SHIFT:be)

bct :: MonadFD4 m => TTerm -> Bytecode -> m Bytecode
bct (App i t t') b = do
  be <- bcc t' (TAILCALL:b)
  bcc t be
bct (IfZ i t1 t2 t3) b = do
  b'' <- bct t2 []
  b''' <- bct t3 []
  let l1 = length b''
  bcc t1 $ (IFZ:l1:b'') ++ b''' ++ b
bct (Let i x ty t (Sc1 t')) b = do
  be <- bct t' b
  bcc t (SHIFT:be)
bct t b = bcc t (RETURN:b)

-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-32 del caracter.
string2bc :: String -> Bytecode
string2bc = map ord

bc2string :: Bytecode -> String
bc2string = map chr

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule m = bcc (moduleTTerm (reverse m)) [STOP]

global2free :: TTerm -> TTerm
global2free (V i (Global n)) = V i (Free n)
global2free (V p v) = V p v
global2free (Lam p y ty (Sc1 t)) = Lam p y ty (Sc1 (global2free t))
global2free (App p l r) = App p (global2free l) (global2free r)
global2free (Fix p f fty x xty (Sc2 t)) = Fix p f fty x xty (Sc2 (global2free t))
global2free (IfZ p c t e) = IfZ p (global2free c) (global2free t) (global2free e)
global2free t@(Const _ _) = t
global2free (Print p str t) = Print p str (global2free t)
global2free (BinaryOp p op t u) = BinaryOp p op (global2free t) (global2free u)
global2free (Let p v vty m (Sc1 o)) = Let p v vty (global2free m) (Sc1 (global2free o))

moduleTTerm :: Module -> TTerm
moduleTTerm [Decl _ _ b] = global2free b
moduleTTerm ((Decl p n b):xs) = 
  Let (p, getTy b) n (getTy b) (global2free b) (close n (moduleTTerm xs))

-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------
-- * Ejecución de bytecode
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = (map fromIntegral <$> un32) . decode <$> BS.readFile filename

runBC :: MonadFD4 m => Bytecode -> m ()
runBC bcode = runBC' bcode [] []

runBC' :: MonadFD4 m => Bytecode -> Env -> Stack -> m ()
runBC' (STOP:ls) e s = do return ()
runBC' (ACCESS:n:c) e s = runBC' c e (e !! n:s)
runBC' (CONST:n:c) e s = runBC' c e (I n:s)
runBC' (ADD:c) e ((I n):(I m):s) = runBC' c e (I (semOp Add m n):s)
runBC' (SUB:c) e ((I n):(I m):s) = runBC' c e (I (semOp Sub m n):s)
runBC' (CALL:c) e (v:(Fun ef cf):s) = runBC' cf (v:ef) (RA e c:s)
runBC' (TAILCALL:c) e (arg:Fun eg cg:s) = runBC' cg (arg:eg) s
runBC' (FUNCTION:l:c) e s =
  let (cf, cr) = splitAt l c
  in runBC' cr e (Fun e cf:s)
runBC' (FIX:c) e (Fun _ cf:s) = do
  let efix = Fun efix cf : e
  runBC' c e (Fun efix cf:s)
runBC' (RETURN:_) _ (v:RA e c:s) = runBC' c e (v:s)
runBC' (SHIFT:c) e (v:s) = runBC' c (v:e) s
runBC' (DROP:c) (v:e) s = runBC' c e s 
runBC' (PRINTN:c) e (I n:s) = do
  printFD4 $ show n
  runBC' c e (I n:s)
runBC' (PRINT:c) e s = do
  let (bs, c') = aux [] c
  printNoLnFD4 $ bc2string bs
  runBC' c' e s
  where aux l (NULL:cont) = (reverse l,cont)
        aux l (str:cont) = aux (str:l) cont
runBC' (IFZ:l:c) e (I 0:s) = runBC' c e s
runBC' (IFZ:l:c) e (I _:s) =
  let c' = drop l c
  in runBC' c' e s
runBC' (JUMP:l:c) e s =
  let c' = drop l c
  in runBC' c' e s
runBC' bcode e s = 
  printFD4 (showBC bcode) >> failFD4 "Hasta acá llegué."
