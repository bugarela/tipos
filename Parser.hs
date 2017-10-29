module Parser where
import Text.Parsec
import Text.Parsec.Token
import Text.Parsec.Language
import Data.Char
import Head

import Control.Monad.Identity (Identity)

{-# LANGUAGE NoMonomorphismRestriction #-}

parseExpr e = parse expr "Erro:" e

reservados = "=->{},;()\n "
operators = map varof ["+","-","*","/","==",">","<",">=","<="]
opsymbols = "><=-+*/"

varof c = Var c

---------------- TO DO: tuples ---------------

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
       do {l <- letex; return l}
       <|>
       do {a <- apps; return a}

alt :: Parsec String () (Pat, Expr)
alt = do p <- pat
         string "-> "
         e <- singleExpr
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
          e1 <- singleExpr
          string "then "
          e2 <- singleExpr
          string "else "
          e3 <- singleExpr
          return (If e1 e2 e3)

caseex :: Parsec String () (Expr)
caseex = do string "case "
            e <- singleExpr
            string "of {"
            ps <- alt `sepBy` (char ';')
            char '}'
            return (Case e ps)

letex :: Parsec String () (Expr)
letex = do string "let "
           v <- many1 (noneOf reservados)
           char '='
           e <- singleExpr
           string "in "
           e' <- expr
           return (Let (v,e) e')

apps :: Parsec String () (Expr)
apps = do as <- many1 singleExpr
          return (foldApp as)

singleExpr :: Parsec String () (Expr)
singleExpr = do char '('
                e <- expr
                char ')'
                spaces
                return e
             <|>
             do l <- lit
                return l
             <|>
             do var <- varReservada
                return (var)
             <|>
             do var <- noneOf reservados
                spaces
                return (Var [var])


lit :: Parsec String () (Expr)
lit = do digits <- many1 digit
         let n = foldl (\x d -> 10*x + toInteger (digitToInt d)) 0 digits
         spaces
         return (Lit (TInt (fromInteger n)))
      <|>
      do a <- string "True"
         spaces
         return (Lit (TBool True))
      <|>
      do a <- string "False"
         spaces
         return (Lit (TBool False))

pvar :: Parsec String () (Pat)
pvar = do var <- noneOf reservados
          spaces
          return (PVar [var])

plit :: Parsec String () (Pat)
plit = do digits <- many1 digit
          let n = foldl (\x d -> 10*x + toInteger (digitToInt d)) 0 digits
          spaces
          return (PLit (TInt (fromInteger n)))
       <|>
       do a <- string "True"
          spaces
          return (PLit (TBool True))
       <|>
       do a <- string "False"
          spaces
          return (PLit (TBool False))

pcon :: Parsec String () (Pat)
pcon = do var <- conName
          ps <- many pat
          return (PCon var ps)

varReservada :: Parsec String () (Expr)
varReservada = do {con <- conName; return (Var con)}
               <|>
               do op <- many1 (oneOf opsymbols)
                  spaces
                  return (varof op)



conName :: Parsec String () ([Char])
conName = do {string "Just"; spaces; return "Just"}
          <|>
          do {string "Nothing"; spaces; return "Nothing"}
          <|>
          do {string "Left"; spaces; return "Left"}
          <|>
          do {string "Right"; spaces; return "Right"}

foldApp :: [Expr] -> Expr
foldApp [x] = x
foldApp [f,g] = if g `elem` operators then (App g f) else (App f g)
foldApp (f:(g:as)) = if g `elem` operators then App (App g f) (foldApp as) else App (App f g) (foldApp as)
