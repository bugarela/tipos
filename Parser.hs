module Parser where
import Text.Parsec
import Text.Parsec.Token
import Text.Parsec.Language
import Data.Char as T
import Head

import Control.Monad.Identity (Identity)

{-# LANGUAGE NoMonomorphismRestriction #-}

avaliarExpr e = parse expr "Erro:" e

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
alt = do return (PVar "a",Var "a")

lam :: Parsec String () (Expr)
lam = do char '\\'
         var <- letter
         char '.'
         e <- expr
         return (Lam (show var) e)

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
            ps <- many1 alt
            char '}'
            return (Case e ps)

var :: Parsec String () (Expr)
var = do var <- letter
         return (Var (show var))
