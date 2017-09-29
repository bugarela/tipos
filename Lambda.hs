import Type

data Expr =  Var Id
            | App Expr Expr
            | Lam Id Expr
            | If Expr Expr Expr
            | Case Expr [(Pat,Expr)]
            deriving (Eq, Show)

tiContext g i = let (_ :>: t) = head (dropWhile (\(i' :>: _) -> i /= i' ) g) in t

divide (TArr a b) = (a,b)

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
tiExpr g (Case x ls) = (tiAlts g x ls)

tiPat :: [Assump] -> Pat -> TI (SimpleType,[Assump])
tiPat g (PVar i) = return (TVar i, g++[i:>:(TVar i)])
tiPat g (PLit tipo) = return (Lit tipo, g)
tiPat g (PCon i []) = do let t = tiContext g i
                         return (t, g)
tiPat g (PCon i xs) = do let c = (tiContext g i)
                         return (tiPats g c xs)
                             --(t,g') <- tiPat g x
                             --let u = unify t (fst (divide c))
                             --let p =
                             --return (tiPat (apply u (g++g')) (PCon (snd (divide c)) xs))

tiPats :: [Assump] -> SimpleType -> [Pat] -> TI (SimpleType,[Assump])
tiPats g (TArr a (TApp b a')) c (p:ps) = do (t,g') <- (tiPat g p)
                                            let u = unify t a
                                            return (TApp b (apply u a), apply u g')
--tiPats g (TArr a (TArr b e)) c (p:ps) = do  (t,g') <- (tiPat g p)
--                                            let u = unify t a
--                                            (t2,g2) <- tiPats
--                                            return (TApp b (apply u a), apply u g')

tiAlts :: [Assump] -> Expr -> [(Pat,Expr)] -> TI (SimpleType,Subst)
tiAlts g x [(p,e)] = do (tx,s1) <- tiExpr g x
                        (tp,g') <- tiPat (apply s1 g) p
                        let u = unify tx tp
                        (te,s2) <- tiExpr (apply u (g'++g)) e
                        let s = s1 @@ s2 @@ u
                        return (apply s te, s)

tiAlts g x ((p,e):ls) = do (tx,s1) <- tiExpr g x
                           (tp,g') <- tiPat (apply s1 g) p
                           let u = (unify tx tp) @@ s1
                           (te,s2) <- tiExpr (apply u (g'++g)) e
                           let s = s2 @@ u
                           (t,s') <- (tiAlts (apply s (g'++g)) x ls)
                           let u' = unify (apply s te) t
                           let su = s @@ s1 @@ u'
                           return (apply su t, su)

ex1 = Lam "f" (Lam "x" (App (Var "f") (Var "x")))
ex2 = Lam "x" (App (Var "x") (Var "x")) -- impossible
ex3 = Lam "g" (Lam "f" (Lam "x" (App (Var "g") (App (Var "f") (Var "x")))))
ex4 = Lam "x" (App (App (Var "+") (Var "x")) (Var "x"))
ex5 = Lam "x" (Lam "y" (If (Var "x") (Var "x") (Var "y")))
ex6 = Lam "x" (Lam "y" (If (App (App (Var "==") (Var "x")) (Var "y")) (App (App (Var "+") (Var "x")) (Var "y")) (App (App (Var "*") (Var "x")) (Var "y"))))
ex7 = Lam "x" (Lam "y" (If (App (App (Var "==") (Var "x")) (Var "y")) (Var "True") (Var "x"))) -- impossible
ex8 = Lam "x" (Lam "y" (If (App (App (Var "==") (Var "x")) (Var "y")) (Var "True") (Var "False")))
ex9 = Lam "y" (Case (Var "y") [(PCon "Just" [(PVar "x")],(App (Var "Just") (Var "x"))),(PCon "Nothing" [],Var "y")])
ex9' = Lam "y" (Case (Var "y") [(PCon "Nothing" [],Var "y"),(PCon "Just" [(PVar "x")],(App (Var "Just") (Var "x")))])
ex10 = Lam "y" (Case (Var "y") [(PCon "Just" [(PVar "x")],Var "x"),(PCon "Nothing" [],Var "y")]) -- impossible
ex11 = Lam "y" (Case (Var "y") [(PLit (TInt 1),Var "y"),(PLit (TInt 2),(App (App (Var "+") (Var "y")) (Var "y")))])
ex12 = Lam "y" (Case (Var "y") [(PLit Int,Var "y")])

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
