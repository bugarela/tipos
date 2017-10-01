import Head
import Type
import Parser

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
tiExpr g (Case x ls) = tiAlts g x ls

tiPat :: [Assump] -> Pat -> TI (SimpleType,[Assump])
tiPat g (PVar i) = return (TVar i, g++[i:>:TVar i])
tiPat g (PLit tipo) = return (Lit tipo, g)
tiPat g (PCon i []) = do let t = tiContext g i
                         return (t, g)
tiPat g (PCon i xs) = do (t,g') <- (tiPats g xs)
                         let tc = tiContext g i
                         let c = appParametros tc t
                         return (c, g')

tiPats :: [Assump] -> [Pat] -> TI ([SimpleType],[Assump])
tiPats g [] = return ([],g)
tiPats g (p:ps) = do (t1,g1) <- (tiPat g p)
                     (t2,g2) <- (tiPats (g++g1) ps)
                     return (t2++[t1], g2)

tiAlts :: [Assump] -> Expr -> [(Pat,Expr)] -> TI (SimpleType,Subst)
tiAlts g x [(p,e)] = do (tx,s1) <- tiExpr g x
                        (tp,g') <- tiPat (apply s1 g) p
                        let u = unify tx tp @@ s1
                        (te,s2) <- tiExpr (apply u (g'++g)) e
                        let s = s1 @@ s2 @@ u
                        return (apply s te, s)

tiAlts g x ((p,e):ls) = do (tx,s1) <- tiExpr g x
                           (tp,g') <- tiPat (apply s1 g) p
                           let u = unify tx tp @@ s1
                           (te,s2) <- tiExpr (apply u (g'++g)) e
                           let s = s2 @@ u
                           (t,s') <- (tiAlts (apply s (g'++g)) x ls)
                           let u' = unify (apply s te) t
                           let su = s @@ s1 @@ u'
                           return (apply su t, su)

ex1 = Lam "f" (Lam "x" (App (Var "f") (Var "x")))
ex2 = Lam "g" (Lam "f" (Lam "x" (App (Var "g") (App (Var "f") (Var "x")))))
ex3 = Lam "x" (App (App (Var "+") (Var "x")) (Var "x"))
ex4 = Lam "x" (Lam "y" (If (Var "x") (Var "x") (Var "y")))
ex5 = Lam "x" (Lam "y" (If (App (App (Var "==") (Var "x")) (Var "y")) (App (App (Var "+") (Var "x")) (Var "y")) (App (App (Var "*") (Var "x")) (Var "y"))))
ex6 = Lam "x" (Lam "y" (If (App (App (Var "==") (Var "x")) (Var "y")) (Var "True") (Var "False")))
ex7 = Lam "y" (Case (Var "y") [(PCon "Just" [(PVar "x")],(App (Var "Just") (Var "x"))),(PCon "Nothing" [],Var "y")])
ex8 = Lam "y" (Case (Var "y") [(PLit (TInt 1),Var "y"),(PLit (TInt 2),(App (App (Var "+") (Var "y")) (Var "y")))])
ex9 = Lam "y" (Case (Var "y") [(PLit Int,Var "y")])

--This are examples that should get an error
bad1 = Lam "x" (App (Var "x") (Var "x"))
bad2 = Lam "x" (Lam "y" (If (App (App (Var "==") (Var "x")) (Var "y")) (Var "True") (Var "x")))
bad3 = Lam "y" (Case (Var "y") [(PCon "Just" [(PVar "x")],(Var "y")),(PCon "Nothing" [],(Var "True"))])
bad4 = Lam "y" (Case (Var "y") [(PCon "Nothing" [],Var "y"),(PCon "Just" [(PVar "x")],(App (Var "Just") (Var "y")))])

-- I don't know
what = Lam "y" (Case (Var "y") [(PCon "Just" [(PVar "x")],Var "x"),(PCon "Nothing" [],Var "y")])

-- This won't work: \y->(case y of {Left x -> (x,'a');Right x -> (True,x)}) :: Either Bool Char -> (Bool, Char)

contexto = ["Just":>:TArr (TVar "a") (TApp (TCon "Maybe") (TVar "a")),
            "Nothing":>: TApp (TCon "Maybe") (TVar "a"),
            "+":>: TArr (Lit Int) (TArr (Lit Int) (Lit Int)),
            "-":>: TArr (Lit Int) (TArr (Lit Int) (Lit Int)),
            "*":>: TArr (Lit Int) (TArr (Lit Int) (Lit Int)),
            "/":>: TArr (Lit Int) (TArr (Lit Int) (Lit Int)),
            "True":>: Lit Bool,
            "False":>: Lit Bool,
            "==":>: TArr (Lit Int) (TArr (Lit Int) (Lit Bool)),
            ">=":>: TArr (Lit Int) (TArr (Lit Int) (Lit Bool)),
            "<=":>: TArr (Lit Int) (TArr (Lit Int) (Lit Bool)),
            ">":>: TArr (Lit Int) (TArr (Lit Int) (Lit Bool)),
            "<":>: TArr (Lit Int) (TArr (Lit Int) (Lit Bool)),
            "1":>: Lit Int,
            "2":>: Lit Int]

infer e = runTI (tiExpr contexto e)
magic e = fst (infer e)
