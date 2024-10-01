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

module Parse (tm, Parse.parse, declTerm, runP, P, program, declOrTm) where

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

tyatom :: P STy
tyatom = (reserved "Nat" >> return SNatTy)
         <|> parens typeP

typedef :: P STy
typedef = do
  s <- tyIdentifier
  return $ SNameTy s

typeP :: P STy
typeP = try (do
          x <- ty
          reservedOp "->"
          y <- typeP
          return (SFunTy x y))
      <|> ty
  where ty = tyatom <|> typedef

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
  return (SLam i [(["x"],SNatTy)] (SPrint i str (SV i "x")))

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
binding :: P (Name, STy)
binding = do
  v <- var
  reservedOp ":"
  ty <- typeP
  return (v, ty)

-- parsea una lista de pares ([variables] : tipo), encerrados por paréntesis
bindings :: P [([Name], STy)]
bindings = do
  xs <- parens multibindings
  try
    (do
    xs' <- bindings
    return $ xs:xs')
    <|>
    return [xs]

multibindings :: P ([Name], STy)
multibindings = do
  xs <- many var
  reservedOp ":"
  ty <- typeP
  return (xs,ty)

lam :: P STerm
lam = do
  i <- getPos
  reserved "fun"
  xs <- bindings
  reservedOp "->"
  t <- expr
  return (SLam i xs t)

-- Nota el parser app también parsea un solo atom.
app :: P STerm
app = do
  i <- getPos
  f <- atom
  args <- many atom
  return (foldl (SApp i) f args)

ifz :: P STerm
ifz = do
  i <- getPos
  reserved "ifz"
  c <- expr
  reserved "then"
  t <- expr
  reserved "else"
  e <- expr
  return (SIfZ i c t e)

fix :: P STerm
fix = do
  i <- getPos
  reserved "fix"
  (f, fty) <- parens binding
  xs <- bindings
  reservedOp "->"
  t <- expr
  return (SFix i (f,fty) xs t)

let0 :: P ((Name, STy), [([Name], STy)])
let0 = do
  p <- parens binding
  return (p, [])

let1 :: P ((Name,STy), [([Name],STy)])
let1 = try (do
  t <- binding
  return (t, []))

let2 :: P ((Name,STy), [([Name],STy)])
let2 = do
  v <- var
  xs <- bindings
  reservedOp ":"
  ty <- typeP
  return ((v, ty), xs)

letin :: P (STerm, STerm)
letin = do
  reservedOp "="
  t <- expr
  reserved "in"
  t' <- expr
  return (t, t')

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
  ((v,vty), xs) <- let0 <|> let1 <|> let2
  (t, t') <- letin
  return (SLet i b v xs vty t t')

-- | Parser de términos
tm :: P STerm
tm = app <|> lam <|> ifz <|> (try printOp <|> printEthaOp) <|> fix <|> letexp

declTerm:: P SDecl
declTerm = do
  reserved "let"
  i <- getPos
  b <- letbool
  (p,xs) <- let0 <|> let1 <|> let2
  reservedOp "="
  t <- expr
  return (SDecl i b p xs t)

declPTy :: P SDecl
declPTy = do 
  reserved "type"
  i <- getPos
  n <- tyIdentifier
  reservedOp "="
  ty <- typeP
  return (SDeclTy i n ty)

-- | Parser de programas (listas de declaraciones) 
program :: P [SDecl]
program = many (declTerm <|> declPTy)

-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
declOrTm :: P (Either SDecl STerm)
declOrTm =  try (Right <$> expr) <|> (Left <$> (declTerm <|> declPTy))

-- Corre un parser, chequeando que se pueda consumir toda la entrada
runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s

--para debugging en uso interactivo (ghci)
parse :: String -> STerm
parse s = case runP expr s "" of
            Right t -> t
            Left e -> error ("no parse: " ++ show s)
