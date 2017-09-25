import Type

data Expr =  Var Id
            | App Expr Expr
            | Lam Id Expr
            | If Expr Expr Expr
            | Case Expr [(Pat,Expr)]
            deriving (Eq, Show)

tiContext g i = let (_ :>: t) = head (dropWhile (\(i' :>: _) -> i /= i' ) g) in t

tiExpr g (Var i) = return (tiContext g i, [])
tiExpr g (App e e') = do (t, s1) <- tiExpr g e
                         (t', s2) <- tiExpr (apply s1 g) e'
                         b <- freshVar
                         let s3 = unify (apply s2 t) (t' --> b) 
                         return (apply s3 b, s3 @@ s2 @@ s1)
tiExpr g (Lam i e) = do b <- freshVar
                        (t, s)  <- tiExpr (g++[i:>:b]) e
                        return (apply s (b --> t), s)
tiExpr g (If s t e) = do (a, s1) <- tiExpr g s
                         let u1 = unify (apply s1 a) (Lit Bool)
                         (b, s2) <- tiExpr (apply u1 (apply s1 g)) t
                         (c, s3) <- tiExpr (apply s2 (apply u1 (apply s1 g))) e 
                         let s = s1 @@ s2 @@ s3 @@ u1
                         let u2 = unify (apply s b) (apply s c)
                         return (apply u2 (apply s3 (apply s2 (apply u1 (apply s1 b)))), s3 @@ s2 @@ s1 @@ u1 @@ u2)
--tiExpr g (Case x ls) = do (a,s1) <- tiExpr g x
--                          let s2 = tiExpr' (apply s1 g) ls
--                          return (apply s2 (apply s1 a), s1 @@ s2)
--tiExpr' :: [Assump] -> [(Pat,Expr)] -> TI Subst
--tiExpr' g [(x,y)] = [snd (tiExpr g y)]
--tiExpr' g ((x,y):ls) = do let s1 = [snd (tiExpr g y)]
--                          let s2 = tiExpr' (apply s1 g) ls
--                          return (s1 @@ s2)


                                   


ex1 = Lam "f" (Lam "x" (App (Var "f") (Var "x")))
ex2 = Lam "x" (App (Var "x") (Var "x")) -- impossible
ex3 = Lam "g" (Lam "f" (Lam "x" (App (Var "g") (App (Var "f") (Var "x")))))
ex4 = Lam "x" (App (App (Var "+") (Var "x")) (Var "x"))
ex5 = Lam "x" (Lam "y" (If (Var "x") (Var "x") (Var "y")))
ex6 = Lam "x" (Lam "y" (If (App (App (Var "==") (Var "x")) (Var "y")) (App (App (Var "+") (Var "x")) (Var "y")) (App (App (Var "*") (Var "x")) (Var "y"))))
ex7 = Lam "x" (Lam "y" (If (App (App (Var "==") (Var "x")) (Var "y")) (Var "True") (Var "x"))) -- impossible
ex8 = Lam "x" (Lam "y" (If (App (App (Var "==") (Var "x")) (Var "y")) (Var "True") (Var "False")))
ex9 = Lam "y" (Case (Var "y") [(PCon "Just" [(PVar "x")],(Var "x")),(PCon "Nothing" [],Var "y")])

contexto = ["Just":>:(TArr (TVar "a") (TApp (TCon "Maybe") (TVar "a"))),
            "Nothing":>: (TApp (TCon "Maybe") (TVar "a")),
            "+":>: (TArr (Lit Int) (TArr (Lit Int) (Lit Int))),
            "-":>: (TArr (Lit Int) (TArr (Lit Int) (Lit Int))),
            "*":>: (TArr (Lit Int) (TArr (Lit Int) (Lit Int))),
            "/":>: (TArr (Lit Int) (TArr (Lit Int) (Lit Int))),
            "True":>: Lit Bool,
            "False":>: Lit Bool,
            "==":>: (TArr (Lit Int) (TArr (Lit Int) (Lit Bool)))]

infer e = runTI (tiExpr contexto e)
magic e = fst (infer e)
