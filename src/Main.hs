{-# LANGUAGE RecordWildCards #-}

{-|
Module      : Main
Description : Compilador de FD4.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Main where

import System.Console.Haskeline ( defaultSettings, getInputLine, runInputT, InputT )
import Control.Monad.Catch (MonadMask)

import Control.Monad.Trans
import Data.List ( nub, isPrefixOf, intercalate )
import Data.Char ( isSpace )
import Control.Exception ( catch , IOException )
import System.IO ( hPrint, stderr, hPutStrLn )
import Data.Maybe ( fromMaybe )
-- import Data.ByteString

import System.Exit ( exitWith, ExitCode(ExitFailure) )
import Options.Applicative

import Global
import Errors
import Lang
import CEK 
import IR
import C
import ClosureConvert
import Bytecompile
import Parse ( P, tm, program, declOrTm, runP )
import Elab ( elab, elabTermDecl, elabTyDecl )
import Eval ( eval )
import PPrint ( pp , ppTy, ppTermDecl)
import MonadFD4
    ( when,
      MonadError(throwError),
      MonadState(get),
      addTermDecl,
      addTyDecl,
      catchErrors,
      eraseLastFileDecls,
      getInter,
      getModule,
      getLastFile,
      getMode,
      lookupTermDecl,
      printFD4,
      runFD4,
      setInter,
      setLastFile,
      gets,
      FD4,
      MonadFD4 )
import TypeChecker ( tc, tcDecl )
import Common (changeExtension)

prompt :: String
prompt = "FD4> "

-- | Parser de banderas
parseMode :: Parser (Mode,Bool)
parseMode = (,) <$>
      (flag' Typecheck (long "typecheck" <> short 't' <> help "Chequear tipos e imprimir el término")
      <|> flag Interactive Interactive (long "interactive" <> short 'i' <> help "Ejecutar en forma interactiva")
      <|> flag Eval Eval (long "eval" <> short 'e' <> help "Evaluar programa")
      <|> flag CEK CEK (long "cek" <> short 'k' <> help "Evaluar programa con máquina abstracta CEK")
      <|> flag Bytecompile Bytecompile (long "bytecompile" <> short 'm' <> help "Compilar a la Macchina")
      <|> flag RunVM RunVM (long "runVM" <> short 'r' <> help "Ejecutar bytecode en la Macchina")
      <|> flag ClosConv ClosConv (long "cc" <> short 'c' <> help "Compilar código a C")
      )
   <*> pure False

-- | Parser de opciones general, consiste de un modo y una lista de archivos a procesar
parseArgs :: Parser (Mode,Bool, [FilePath])
parseArgs = (\(a,b) c -> (a,b,c)) <$> parseMode <*> many (argument str (metavar "FILES..."))

main :: IO ()
main = execParser opts >>= go
  where
    opts = info (parseArgs <**> helper)
      ( fullDesc
     <> progDesc "Compilador de FD4"
     <> header "Compilador de FD4 de la materia Compiladores 2022" )

    go :: (Mode,Bool,[FilePath]) -> IO ()
    go (Interactive, opt, files) =
              runOrFail (Conf opt Interactive) (runInputT defaultSettings (repl files))
    go (Bytecompile, opt, files) =
              runOrFail (Conf opt Bytecompile) $ mapM_ compileFileBC files
    go (RunVM, opt, files) =
              runOrFail (Conf opt RunVM) $ mapM_ compileFileRVM files
    go (ClosConv, opt, files) =
              runOrFail (Conf opt ClosConv) $ mapM_ compileC files
    go (m, opt, files) =
              runOrFail (Conf opt m) $ mapM_ compileFile files

runOrFail :: Conf -> FD4 a -> IO a
runOrFail c m = do
  r <- runFD4 m c
  case r of
    Left err -> do
      liftIO $ hPrint stderr err
      exitWith (ExitFailure 1)
    Right v -> return v

repl :: (MonadFD4 m, MonadMask m) => [FilePath] -> InputT m ()
repl args = do
       lift $ setInter True
       lift $ catchErrors $ mapM_ compileFile args
       s <- lift get
       when (inter s) $ liftIO $ putStrLn
         (  "Entorno interactivo para FD4.\n"
         ++ "Escriba :? para recibir ayuda.")
       loop
  where loop = do
           minput <- getInputLine prompt
           case minput of
               Nothing -> return ()
               Just "" -> loop
               Just x -> do
                       c <- liftIO $ interpretCommand x
                       b <- lift $ catchErrors $ handleCommand c
                       maybe loop (`when` loop) b

loadFile ::  MonadFD4 m => FilePath -> m [SDecl]
loadFile f = do
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStrLn stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err)
                         return "")
    setLastFile filename
    parseIO filename program x

compileFile ::  MonadFD4 m => FilePath -> m ()
compileFile f = do
    i <- getInter
    setInter False
    when i $ printFD4 ("Abriendo "++f++"...")
    decls <- loadFile f
    mapM_ handleDecl decls
    setInter i

compileFileBC ::  MonadFD4 m => FilePath -> m ()
compileFileBC f = do
    i <- getInter
    setInter False
    when i $ printFD4 ("Abriendo "++f++"...")
    decls <- loadFile f
    mapM_ handleDecl decls
    setInter i
    gt <- getModule
    bc <- bytecompileModule gt
    printFD4 $ showBC bc
    let bcf = changeExtension f ".bc"
    when i $ printFD4 ("Creando " ++ bcf ++ "...")
    liftIO (bcWrite bc bcf)
    

compileFileRVM ::  MonadFD4 m => FilePath -> m ()
compileFileRVM f = do
    i <- getInter
    setInter False
    when i $ printFD4 ("Abriendo "++f++"...")
    bc <- liftIO (bcRead f)
    setInter i
    runBC bc

compileC :: MonadFD4 m => FilePath -> m ()
compileC f = do
  i <- getInter
  setInter False
  when i $ printFD4 ("Abriendo "++f++"...")
  decls <- loadFile f
  mapM_ handleDecl decls
  setInter i
  dtt <- getModule
  let irdecls = runCC (reverse dtt)
      prog = ir2C (IrDecls irdecls)
      cf = changeExtension f ".c"
  when i $ printFD4 ("Creando " ++ cf ++ "...")
  liftIO (writeFile cf prog)

parseIO ::  MonadFD4 m => String -> P a -> String -> m a
parseIO filename p x = case runP p x filename of
                  Left e  -> throwError (ParseErr e)
                  Right r -> return r

evalDecl :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
evalDecl (Decl p x e) = do
    e' <- eval e
    return (Decl p x e')

typecheckDecl :: MonadFD4 m => SDecl -> m (Decl TTerm)
typecheckDecl ss = do
    (ty,t') <- elabTermDecl ss
    tcDecl ty t'

handleDecl ::  MonadFD4 m => SDecl -> m ()
handleDecl d@SDecl {..} = 
  do
    m <- getMode
    case m of
      Interactive -> do
        (Decl p x tt) <- typecheckDecl d
        te <- eval tt
        addTermDecl (Decl p x te)
      Typecheck -> do
        f <- getLastFile
        printFD4 ("Chequeando tipos de "++f)
        td <- typecheckDecl d
        addTermDecl td
        ppterm <- ppTermDecl td
        printFD4 ppterm
      Eval -> do
        td <- typecheckDecl d
        ed <- evalDecl td
        addTermDecl ed
      CEK -> do
        (Decl p x tt) <- typecheckDecl d
        val <- evalCEK tt
        te <- transform val
        addTermDecl (Decl p x te)
      Bytecompile -> do
        dt <- typecheckDecl d
        addTermDecl dt
      RunVM -> undefined
      ClosConv -> do
        td <- typecheckDecl d
        addTermDecl td
handleDecl d@SDeclTy {..} =
  do
    d' <- elabTyDecl d
    addTyDecl d'


data Command = Compile CompileForm
             | PPrint String
             | Type String
             | Reload
             | Browse
             | Quit
             | Help
             | Noop

data CompileForm = CompileInteractive  String
                 | CompileFile         String

data InteractiveCommand = Cmd [String] String (String -> Command) String

-- | Parser simple de comando interactivos
interpretCommand :: String -> IO Command
interpretCommand x
  =  if ":" `isPrefixOf` x then
       do  let  (cmd,t')  =  break isSpace x
                t         =  dropWhile isSpace t'
           --  find matching commands
           let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
           case matching of
             []  ->  do  putStrLn ("Comando desconocido `" ++ cmd ++ "'. Escriba :? para recibir ayuda.")
                         return Noop
             [Cmd _ _ f _]
                 ->  do  return (f t)
             _   ->  do  putStrLn ("Comando ambigüo, podría ser " ++
                                   intercalate ", " ([ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
                         return Noop

     else
       return (Compile (CompileInteractive x))

commands :: [InteractiveCommand]
commands
  =  [ Cmd [":browse"]      ""        (const Browse) "Ver los nombres en scope",
       Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                     "Cargar un programa desde un archivo",
       Cmd [":print"]       "<exp>"   PPrint          "Imprime un término y sus ASTs sin evaluarlo",
       Cmd [":reload"]      ""        (const Reload)         "Vuelve a cargar el último archivo cargado",
       Cmd [":type"]        "<exp>"   Type           "Chequea el tipo de una expresión",
       Cmd [":quit",":Q"]        ""        (const Quit)   "Salir del intérprete",
       Cmd [":help",":?"]   ""        (const Help)   "Mostrar esta lista de comandos" ]

helpTxt :: [InteractiveCommand] -> String
helpTxt cs
  =  "Lista de comandos:  Cualquier comando puede ser abreviado a :c donde\n" ++
     "c es el primer caracter del nombre completo.\n\n" ++
     "<expr>                  evaluar la expresión\n" ++
     "let <var> = <expr>      definir una variable\n" ++
     unlines (map (\ (Cmd c a _ d) ->
                   let  ct = intercalate ", " (map (++ if null a then "" else " " ++ a) c)
                   in   ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) cs)

-- | 'handleCommand' interpreta un comando y devuelve un booleano
-- indicando si se debe salir del programa o no.
handleCommand ::  MonadFD4 m => Command  -> m Bool
handleCommand cmd = do
   s@GlEnv {..} <- get
   case cmd of
       Quit   ->  return False
       Noop   ->  return True
       Help   ->  printFD4 (helpTxt commands) >> return True
       Browse ->  do  printFD4 (unlines (reverse (nub (map declName glbTerm))))
                      return True
       Compile c ->
                  do  case c of
                          CompileInteractive e -> compilePhrase e
                          CompileFile f        -> compileFile f
                      return True
       Reload ->  eraseLastFileDecls >> (getLastFile >>= compileFile) >> return True
       PPrint e   -> printPhrase e >> return True
       Type e    -> typeCheckPhrase e >> return True

compilePhrase ::  MonadFD4 m => String -> m ()
compilePhrase x = do
    dot <- parseIO "<interactive>" declOrTm x
    case dot of
      Left d  -> handleDecl d
      Right t -> handleTerm t

handleTerm ::  MonadFD4 m => STerm -> m ()
handleTerm t = do
         t' <- elab t
         s <- get
         tt <- tc t' (tyTermEnv s)
         te <- eval tt
         ppte <- pp te
         printFD4 (ppte ++ " : " ++ ppTy (getTy tt))

printPhrase   :: MonadFD4 m => String -> m ()
printPhrase x =
  do
    x' <- parseIO "<interactive>" tm x
    ex <- elab x'
    tyenv <- gets tyTermEnv
    tex <- tc ex tyenv
    t  <- case x' of
           (SV p f) -> fromMaybe tex <$> lookupTermDecl f
           _       -> return tex
    printFD4 "STerm:"
    printFD4 (show x')
    printFD4 "TTerm:"
    printFD4 (show t)

typeCheckPhrase :: MonadFD4 m => String -> m ()
typeCheckPhrase x = do
         t <- parseIO "<interactive>" tm x
         t' <- elab t
         s <- get
         tt <- tc t' (tyTermEnv s)
         let ty = getTy tt
         printFD4 (ppTy ty)
