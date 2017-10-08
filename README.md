# Tipos

My journey studying type inference in Haskell.

You can find here an implementation of a very simple type inferer for the following:

- [x] Lambda abstractions
- [x] `+`, `-`, `*`, `/`, `==`, `>=`, `<=`, `>` and `<` operators
- [x] `if` and `case` expressions
- [ ] `let` expressions

# Parser

This: `parseExpr  "\\x.\\y.x+y"`

Will give you this: `Right (Lam "x" (Lam "y" (App (App (Var "+") (Var "x")) (Var "y"))))`

# Type inferer

This: `typeOf  "\\x.\\y.x+y"`

Will give you this: `Int->Int->Int`
