{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}

{-|
Module      : MonadFD4
Description : Mónada con soporte para estado, errores, e IO.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Definimos la clase de mónadas 'MonadFD4' que abstrae las mónadas con soporte para estado, errores e IO,
y la mónada 'FD4' que provee una instancia de esta clase.
-}

module MonadFD4 (
  FD4,
  runFD4,
  lookupTermDecl,
  lookupTyDecl,
  lookupTermTy,
  printFD4,
  printNoLnFD4,
  setLastFile,
  getLastFile,
  setInter,
  getInter,
  getModule,
  getMode,
  getOpt,
  eraseLastFileDecls,
  failPosFD4,
  failFD4,
  addTermDecl,
  addTyDecl,
  catchErrors,
  MonadFD4,
  module Control.Monad.Except,
  module Control.Monad.State)
 where

import Common ( Pos(NoPos) )
import Lang
import Global
import Errors ( Error(..) )
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader
import System.IO

-- * La clase 'MonadFD4'

{-| La clase de mónadas 'MonadFD4' clasifica a las mónadas con soporte para una configuración Global 'Global.Conf', 
    para operaciones @IO@, estado de tipo 'Global.GlEnv', y errores de tipo 'Errors.Error'.

Las mónadas @m@ de esta clase cuentan con las operaciones:
   - @ask :: m Conf@
   - @get :: m GlEnv@
   - @put :: GlEnv -> m ()@
   - @throwError :: Error -> m a@
   - @catchError :: m a -> (Error -> m a) -> m a@
   - @liftIO :: IO a -> m a@

y otras operaciones derivadas de ellas, como por ejemplo
   - @modify :: (GlEnv -> GlEnv) -> m ()@
   - @gets :: (GlEnv -> a) -> m a@  
-}
class (MonadIO m, MonadState GlEnv m, MonadError Error m, MonadReader Conf m) => MonadFD4 m where

getOpt :: MonadFD4 m => m Bool
getOpt = asks opt

getMode :: MonadFD4 m => m Mode
getMode = asks modo

setInter :: MonadFD4 m => Bool -> m ()
setInter b = modify (\s-> s {inter = b})

getInter :: MonadFD4 m => m Bool
getInter = gets inter

getModule :: MonadFD4 m => m [Decl TTerm]
getModule = gets glbTerm

printFD4 :: MonadFD4 m => String -> m ()
printFD4 = liftIO . putStrLn

printNoLnFD4 :: MonadFD4 m => String -> m ()
printNoLnFD4 = liftIO . putStr

setLastFile :: MonadFD4 m => FilePath -> m ()
setLastFile filename = modify (\s -> s {lfile = filename , cantTermDecl = 0, cantTyDecl = 0})

getLastFile :: MonadFD4 m => m FilePath
getLastFile = gets lfile

addTermDecl :: MonadFD4 m => Decl TTerm -> m ()
addTermDecl d = modify (\s -> s { glbTerm = d : glbTerm s, cantTermDecl = cantTermDecl s + 1 })

addTyDecl :: MonadFD4 m => Decl Ty -> m ()
addTyDecl d = modify (\s -> s { glbTy = d : glbTy s, cantTyDecl = cantTyDecl s + 1 })

eraseLastFileDecls :: MonadFD4 m => m ()
eraseLastFileDecls = do
      s <- get
      let (n,m) = (cantTermDecl s, cantTyDecl s)
          (_,rem) = splitAt n (glbTerm s)
          (_,rem') = splitAt m (glbTy s)
      modify (\s -> s {glbTerm = rem, glbTy = rem', cantTermDecl = 0, cantTyDecl = 0})

hasName :: Name -> Decl a -> Bool
hasName nm (Decl { declName = nm' }) = nm == nm'

lookupTermDecl :: MonadFD4 m => Name -> m (Maybe TTerm)
lookupTermDecl nm = do
     s <- get
     case filter (hasName nm) (glbTerm s) of
       (Decl { declBody=e }):_ -> return (Just e)
       [] -> return Nothing

lookupTyDecl :: MonadFD4 m => Name -> m (Maybe Ty)
lookupTyDecl nm = do
    s <- get
    case filter (hasName nm) (glbTy s) of
        (Decl { declBody = ty}):_ -> return (Just ty)
        [] -> return Nothing


lookupTermTy :: MonadFD4 m => Name -> m (Maybe Ty)
lookupTermTy nm = do
      s <- get
      return $ lookup nm (tyTermEnv s)

failPosFD4 :: MonadFD4 m => Pos -> String -> m a
failPosFD4 p s = throwError (ErrPos p s)

failFD4 :: MonadFD4 m => String -> m a
failFD4 = failPosFD4 NoPos

catchErrors  :: MonadFD4 m => m a -> m (Maybe a)
catchErrors c = catchError (Just <$> c)
                           (\e -> liftIO $ hPrint stderr e
                              >> return Nothing)

----
-- Importante, no eta-expandir porque GHC no hace una
-- eta-contracción de sinónimos de tipos
-- y Main no va a compilar al escribir `InputT FD4 ()`

-- | El tipo @FD4@ es un sinónimo de tipo para una mónada construida usando dos transformadores de mónada sobre la mónada @IO@.
-- El transformador de mónad @ExcepT Error@ agrega a la mónada IO la posibilidad de manejar errores de tipo 'Errors.Error'.
-- El transformador de mónadas @StateT GlEnv@ agrega la mónada @ExcepT Error IO@ la posibilidad de manejar un estado de tipo 'Global.GlEnv'.
type FD4 = ReaderT Conf (StateT GlEnv (ExceptT Error IO))

-- | Esta es una instancia vacía, ya que 'MonadFD4' no tiene funciones miembro.
instance MonadFD4 FD4

-- 'runFD4\'' corre una computación de la mónad 'FD4' en el estado inicial 'Global.initialEnv' 
runFD4' :: FD4 a -> Conf -> IO (Either Error (a, GlEnv))
runFD4' c conf =  runExceptT $ runStateT (runReaderT c conf)  initialEnv

runFD4:: FD4 a -> Conf -> IO (Either Error a)
runFD4 c conf = fmap fst <$> runFD4' c conf
