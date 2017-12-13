import Head
import Type
import Parser

fromRight (Right x) = x

typeOf s = case parseExpr s of
              Right e -> print (magic e)
              Left err -> print err

typeOfWithSubst s = case parseExpr s of
                        Right e -> print (infer [] e)
                        Left err -> print err

magicFile = do a <- parseFile
               inferFile' a magic'
               return()

inferFile = do a <- parseFile
               inferFile' a infer
               return()

inferFile' (ds,e) f = case e of
                      Left err -> print err
                      Right e -> case (extract ds) of
                                    Right s -> print (f (foldr1 (++) s) e)
                                    Left errs -> print errs

extract ds = if (extract' ds) then Right (map fromRight ds) else Left ([extractErr ds])

extract' [] = True
extract' (d:ds) = case d of
                  Left err -> False
                  Right a -> True && (extract' ds)

extractErr (d:ds) = case d of
                     Left err -> err
                     Right a -> extractErr ds

tiContext g i = if l /= [] then (freshInstance t) else error ("Variavel " ++ i ++ " indefinida\n")
    where
        l = dropWhile (\(i' :>: _) -> i /= i' ) g
        (_ :>: t) = head l

tiExpr g (Var i) = do r <- tiContext g i
                      return (r, [])
tiExpr g (Lit u) = return (TLit u, [])
tiExpr g (App e e') = do (t, s1) <- tiExpr g e
                         (t', s2) <- tiExpr (apply s1 g) e'
                         b <- freshVar
                         let u = unify (apply s1 t) (t' --> b)
                         let s = u @@ s2 @@ s1
                         return (apply s b, s)
tiExpr g (Lam i e) = do b <- freshVar
                        (t, s)  <- tiExpr (g /+/ [i:>:(Forall b)]) e
                        return (apply s (b --> t), s)
tiExpr g (If s t e) = do (a, s1) <- tiExpr g s
                         let u1 = unify (apply s1 a) (TLit Bool)
                         (b, s2) <- tiExpr (apply (u1 @@ s1) g) t
                         (c, s3) <- tiExpr (apply (u1 @@ s2 @@ s1) g) e
                         let s = u1 @@ s3 @@ s2 @@ s1
                         let u2 = unify (apply s b) (apply s c)
                         return (apply (u2 @@ s) b, u2 @@ s)
tiExpr g (Case x ls) = tiAlts g x ls
tiExpr g (Let (i,e) e') = do (t,s1) <- tiExpr g e
                             let q = quantify (tv t) t
                             (t',s2) <- tiExpr (apply s1 (g /+/ [i:>:q])) e'
                             return (apply (s2 @@ s1) t', s2 @@ s1)

tiPat :: [Assump] -> Pat -> TI (SimpleType,[Assump])
tiPat g (PVar i) = do b <- freshVar
                      return (b, g /+/ [i:>:(Forall b)])
tiPat g (PLit tipo) = return (TLit tipo, g)
tiPat g (PCon i []) = do t <- tiContext g i
                         return (t, g)
tiPat g (PCon i xs) = do (ts,g') <- (tiPats g xs)
                         tc <- tiContext g' i
                         r <- freshVar
                         let ta = foldr1 TArr (ts ++ [r])
                         let u = unify tc ta
                         return (apply u r, apply u g')

tiPats :: [Assump] -> [Pat] -> TI ([SimpleType],[Assump])
tiPats g [] = return ([],g)
tiPats g (p:ps) = do (t1,g1) <- (tiPat g p)
                     (t2,g2) <- (tiPats (g /+/ g1) ps)
                     return ([t1] ++ t2, g2)

tiAlts :: [Assump] -> Expr -> [(Pat,Expr)] -> TI (SimpleType,Subst)
tiAlts g x [(p,e)] = do (tx,s1) <- tiExpr g x
                        (tp,g') <- tiPat (apply s1 g) p
                        let u = unify tx tp
                        (te,s2) <- tiExpr (apply u g') e
                        let s = s2 @@ u @@ s1
                        return (apply s te, s)

tiAlts g x ((p,e):ls) = do (tx,s1) <- tiExpr g x
                           (tp,g') <- tiPat (apply s1 g) p
                           let u = (unify tx tp) @@ s1
                           (te,s2) <- tiExpr (apply u g') e
                           let s = s2 @@ u
                           (t,s') <- (tiAlts (apply s g) x ls)
                           let u' = unify (apply s' te) t
                           let su = u' @@ s' @@ s
                           return (apply su t, su)

ex1 = Lam "f" (Lam "x" (App (Var "f") (Var "x")))
ex2 = Lam "g" (Lam "f" (Lam "x" (App (Var "g") (App (Var "f") (Var "x")))))
ex3 = Lam "x" (App (App (Var "+") (Var "x")) (Var "x"))
ex4 = Lam "x" (Lam "y" (If (Var "x") (Var "x") (Var "y")))
ex5 = Lam "x" (Lam "y" (If (App (App (Var "==") (Var "x")) (Var "y")) (App (App (Var "+") (Var "x")) (Var "y")) (App (App (Var "*") (Var "x")) (Var "y"))))
ex6 = Lam "x" (Lam "y" (If (App (App (Var "==") (Var "x")) (Var "y")) (Lit (TBool True)) (Lit (TBool False))))
ex7 = Lam "y" (Case (Var "y") [(PCon "Just" [(PVar "x")],(App (Var "Just") (Var "x"))),(PCon "Nothing" [],Var "y")])
ex8 = Lam "y" (Case (Var "y") [(PLit (TInt 1),Var "y"),(PLit (TInt 2),(App (App (Var "+") (Var "y")) (Var "y")))])
ex9 = Lam "y" (Case (Var "y") [(PLit Int,Var "y")])
ex10 = (Lam "x" (Lam "w"(If (App (App (Var "==") (Var "x")) (Lit (TInt 1))) (Lam "y" (Var "x")) (Lam "z" (Var "w")))))
ex11 = (Lam "x" (Let ("y",(App (App (Var "+") (Var "x")) (Var "x"))) (App (App (Var "+") (Var "y")) (Var "y"))))
ex12 = (Lam "x" (Let ("y",(App (Var "+") (Var "x"))) (App (Var "y") (Lit (TInt 1)))))

--This are examples that should get an error
bad1 = Lam "x" (App (Var "x") (Var "x"))
bad2 = Lam "x" (Lam "y" (If (App (App (Var "==") (Var "x")) (Var "y")) (Var "True") (Var "x")))
bad3 = Lam "y" (Case (Var "y") [(PCon "Just" [(PVar "x")],(Var "y")),(PCon "Nothing" [],(Var "True"))])
bad4 = Lam "y" (Case (Var "y") [(PCon "Nothing" [],Var "y"),(PCon "Just" [(PVar "x")],(App (Var "Just") (Var "y")))])

-- I don't know
what = Lam "y" (Case (Var "y") [(PCon "Just" [(PVar "x")],Var "x"),(PCon "Nothing" [],Var "y")])

-- either example: "\\y.case y of {Left x ->x;Right x -> 1}"

infer ds e = runTI (tiExpr (quantifiedContext ds) e)
magic e = magic' [] e
magic' ds e = fst (infer ds e)
