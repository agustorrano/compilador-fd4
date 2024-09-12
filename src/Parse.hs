{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-|
Module      : Parse
Description : Define un parser de términos FD40 a términos fully named.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Parse (tm, Parse.parse, decl, runP, P, program, declOrTm) where

import Prelude hiding ( const )
import Lang hiding (getPos)
import Common
import Text.Parsec hiding (runP,parse)
--import Data.Char ( isNumber, ord )
import qualified Text.Parsec.Token as Tok
import Text.ParserCombinators.Parsec.Language --( GenLanguageDef(..), emptyDef )
import qualified Text.Parsec.Expr as Ex
import Text.Parsec.Expr (Operator, Assoc)
import Control.Monad.Identity (Identity)

type P = Parsec String ()

-----------------------
-- Lexer
-----------------------
-- | Analizador de Tokens
lexer :: Tok.TokenParser u
lexer = Tok.makeTokenParser langDef

langDef :: LanguageDef u
langDef = emptyDef {
         commentLine    = "#",
         reservedNames = ["let", "rec","fun", "fix", "then", "else","in",
                           "ifz", "print","Nat","type"],
         reservedOpNames = ["->",":","=","+","-"]
        }

whiteSpace :: P ()
whiteSpace = Tok.whiteSpace lexer

natural :: P Integer
natural = Tok.natural lexer

stringLiteral :: P String
stringLiteral = Tok.stringLiteral lexer

parens :: P a -> P a
parens = Tok.parens lexer

identifier :: P String
identifier = Tok.identifier lexer

reserved :: String -> P ()
reserved = Tok.reserved lexer

reservedOp :: String -> P ()
reservedOp = Tok.reservedOp lexer

tyIdentifier :: P String
tyIdentifier = Tok.lexeme lexer $ do
  c  <- upper
  cs <- many (identLetter langDef)
  return (c:cs)

-----------------------
-- Parsers
-----------------------

num :: P Int
num = fromInteger <$> natural

var :: P Name
var = identifier

getPos :: P Pos
getPos = do pos <- getPosition
            return $ Pos (sourceLine pos) (sourceColumn pos)

tyatom :: P Ty
tyatom = (reserved "Nat" >> return NatTy)
         <|> parens typeP

typeP :: P Ty
typeP = try (do
          x <- tyatom
          reservedOp "->"
          y <- typeP
          return (FunTy x y))
      <|> tyatom

const :: P Const
const = CNat <$> num

printOp :: P STerm
printOp = do
  i <- getPos
  reserved "print"
  str <- option "" stringLiteral
  a <- atom
  return (SPrint i str a)

printEthaOp :: P STerm
printEthaOp = do
  i <- getPos
  reserved "print"
  str <- option "" stringLiteral
  return (SLam i [("x",NatTy)] (SPrint i str (SV i "x")))

binary :: String -> BinaryOp -> Assoc -> Operator String () Identity STerm
binary s f = Ex.Infix (reservedOp s >> return (SBinaryOp NoPos f))

table :: [[Operator String () Identity STerm]]
table = [[binary "+" Add Ex.AssocLeft,
          binary "-" Sub Ex.AssocLeft]]

expr :: P STerm
expr = Ex.buildExpressionParser table tm

atom :: P STerm
atom =     (flip SConst <$> const <*> getPos)
       <|> flip SV <$> var <*> getPos
       <|> parens expr
       <|> (try printOp <|> printEthaOp)

-- parsea un par (variable : tipo)
binding :: P (Name, Ty)
binding = do v <- var
             reservedOp ":"
             ty <- typeP
             return (v, ty)

-- parsea una lista de pares (variable : tipo), encerrados por paréntesis
bindings :: P [(Name, Ty)]
bindings = 
  do
    xs <- parens multibindings
    xs' <- bindings
    return $ xs ++ xs'

multibindings :: P [(Name, Ty)]
multibindings =
  do
    xs <- many var
    reservedOp ":"
    ty <- typeP
    return [(y, ty) | y <- xs]

bindingstype :: P ([(Name, Ty)], Ty -> Ty)
bindingstype =
  (do
   (xs, ty) <- parens multitype
   (xs', f) <- bindingstype
   return (xs ++ xs', FunTy ty . f))
  <|>
  (do
    return ([], id))

multitype :: P ([(Name, Ty)], Ty)
multitype =
  do
   xs <- many var
   reservedOp ":"
   ty <- typeP
   let (ps, f) = multifun xs ty
   return (ps, f ty) 

multifun :: [Name] -> Ty -> ([(Name,Ty)], Ty -> Ty)
multifun [] ty = ([], id) 
multifun (x:xs) ty =
  let (ps, f) = multifun xs ty
  in ((x, ty):ps, FunTy ty . f)

lam :: P STerm
lam = do i <- getPos
         reserved "fun"
        --  (v,ty) <- parens binding
         xs <- bindings
         reservedOp "->"
         t <- expr
         return (SLam i xs t)

-- Nota el parser app también parsea un solo atom.
app :: P STerm
app = do i <- getPos
         f <- atom
         args <- many atom
         return (foldl (SApp i) f args)

ifz :: P STerm
ifz = do i <- getPos
         reserved "ifz"
         c <- expr
         reserved "then"
         t <- expr
         reserved "else"
         e <- expr
         return (SIfZ i c t e)

fix :: P STerm
fix = do i <- getPos
         reserved "fix"
         (f, fty) <- parens binding
         xs <- bindings
         reservedOp "->"
         t <- expr
         return (SFix i (f,fty) xs t)

let0 :: P ((Name, Ty), [(Name, Ty)])
let0 = do
  p <- parens binding
  return (p, [])

let1 :: P ((Name,Ty), [(Name,Ty)])
let1 = try (do
  t <- binding
  return (t, []))

let2 :: P ((Name,Ty), [(Name,Ty)])
let2 = do
  v <- var
  (xs, f) <- bindingstype
  reservedOp ":"
  ty <- typeP
  return ((v, f ty), xs)

letin :: P (STerm, STerm)
letin = do
  reservedOp "="
  t <- expr
  reserved "in"
  t' <- expr
  return (t, t')

-- letnoin :: P STerm
-- letnoin = do
--   reservedOp "="
--   expr
  

letbool :: P Bool
letbool =
  (do
    reserved "rec"
    return True)
  <|>
  (do
    return False)


letexp :: P STerm
letexp = do
  i <- getPos
  reserved "let"
  b <- letbool
  (p,xs) <- let0 <|> let1 <|> let2
  (t, t') <- letin
  return (SLet i b p xs t t')

-- | Parser de términos
tm :: P STerm
tm = app <|> lam <|> ifz <|> (try printOp <|> printEthaOp) <|> fix <|> letexp

-- | Parser de declaraciones
-- decl :: P (Decl STerm)
-- decl = do
--      i <- getPos
--      reserved "let"
--      v <- var
--      reservedOp "="
--      t <- expr
--      return (Decl i v t)
decl:: P (SDecl STerm)
decl = do
  reserved "let"
  i <- getPos
  b <- letbool
  (p,xs) <- let0 <|> let1 <|> let2
  reservedOp "="
  t <- expr
  return (SDecl i b p xs t)

-- | Parser de programas (listas de declaraciones) 
program :: P [SDecl STerm]
program = many decl

-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
declOrTm :: P (Either (SDecl STerm) STerm)
declOrTm =  try (Right <$> expr) <|> (Left <$> decl) 

-- Corre un parser, chequeando que se pueda consumir toda la entrada
runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s

--para debugging en uso interactivo (ghci)
parse :: String -> STerm
parse s = case runP expr s "" of
            Right t -> t
            Left e -> error ("no parse: " ++ show s)
