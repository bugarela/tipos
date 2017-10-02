module Parser where
import Text.Parsec
import Text.Parsec.Token
import Text.Parsec.Language
import Data.Char
import Head

import Control.Monad.Identity (Identity)

{-# LANGUAGE NoMonomorphismRestriction #-}

parseExpr e = parse expr "Erro:" e

reservados = "{},;()\n "

expr :: Parsec String () (Expr)
expr = do l <- lam
          return l
       <|>
       do apps <- many1 term
          return $ foldl1 App apps

term :: Parsec String () (Expr)
term = do {i <- ifex; return i}
       <|>
       do {c <- caseex; return c}
       <|>
       do {v <- var; return v}

alt :: Parsec String () (Pat, Expr)
alt = do p <- pat
         spaces
         string "->"
         spaces
         e <- expr
         return (p,e)

pat :: Parsec String () (Pat)
pat = do {p <- plit; return p}
      <|>
      do {p <- pcon; return p}
      <|>
      do {p <- pvar; return p}

lam :: Parsec String () (Expr)
lam = do char '\\'
         var <- letter
         char '.'
         e <- expr
         return (Lam [var] e)

ifex :: Parsec String () (Expr)
ifex = do string "if "
          e1 <- expr
          string " then "
          e2 <- expr
          string " else "
          e3 <- expr
          return (If e1 e2 e3)

caseex :: Parsec String () (Expr)
caseex = do string "case "
            e <- expr
            string " of {"
            ps <- alt `sepBy` (char ';')
            char '}'
            return (Case e ps)

var :: Parsec String () (Expr)
var = do var <- noneOf reservados
         return (Var [var])

pvar :: Parsec String () (Pat)
pvar = do var <- noneOf reservados
          return (PVar [var])

plit :: Parsec String () (Pat)
plit = do digits <- many1 digit
          let n = foldl (\x d -> 10*x + toInteger (digitToInt d)) 0 digits
          return (PLit (TInt (fromInteger n)))
       <|>
       do a <- string "True"
          return (PLit (TBool True))
       <|>
       do a <- string "False"
          return (PLit (TBool False))

pcon :: Parsec String () (Pat)
pcon = do var <- many1 letter
          spaces
          ps <- pat `sepBy` (char ' ')
          return (PCon var ps)
