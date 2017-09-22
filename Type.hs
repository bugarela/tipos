module Type where
import Data.List(nub, intersect, union)

type Index = Int
type Id = String
data TI a = TI (Index -> (a, Index))
type Subst  = [(Id, SimpleType)]
data Assump = Id :>: SimpleType deriving (Eq, Show)

data Literal = Int | Bool deriving (Eq, Show)

data SimpleType  = TVar Id
                  | TArr  SimpleType SimpleType
                  | Lit Literal
                  | TCon Id
                  | TApp SimpleType SimpleType
                  deriving Eq

instance Show SimpleType where
   show (TVar i) = i
   show (TArr (TVar i) t) = i++"->"++show t   
   show (TArr t t') = "("++show t++")"++"->"++show t'
   show (TCon i) = show i
   show (TApp c v) = show c ++ " " ++ show v
   show (Lit tipo) = show tipo				  
--------------------------	  

instance Monad TI where 
   return x = TI (\e -> (x, e))
   TI m >>= f  = TI (\e -> let (a, e') = m e; TI fa = f a in fa e')

freshVar :: TI SimpleType
freshVar = TI (\e -> let v = "t"++show e in (TVar v, e+1))

runTI (TI m) = let (t, _) = m 0 in t 

----------------------------
t --> t' = TArr t t' 

infixr 4 @@
(@@)       :: Subst -> Subst -> Subst
s1 @@ s2    = [ (u, apply s1 t) | (u,t) <- s2 ] ++ s1

---------------------------- 
class Subs t where
  apply :: Subst -> t -> t
  tv    :: t -> [Id]

instance Subs SimpleType where
  apply s (TVar u)  =   
                    case lookup u s of
                       Just t  -> t
                       Nothing -> TVar u
  apply s (TCon u)  =   
                    case lookup u s of
                       Just t  -> t
                       Nothing -> TCon u
  apply s (Lit u)  = (Lit u)

  apply s (TArr l r) =  (TArr (apply s l) (apply s r))
  apply s (TApp c v) =  (TApp (apply s c) (apply s v))


  tv (TVar u)  = [u]
  tv (TArr l r) = tv l `union` tv r
  tv (TApp c v) = tv c `union` tv v
  tv (TCon u) = [u]
  tv (Lit u) = []


instance Subs a => Subs [a] where
  apply s     = map (apply s)
  tv          = nub . concat . map tv
  
instance Subs Assump where
  apply s (i:>:t) = i:>:apply s t
  tv (i:>:t) = tv t
  
------------------------------------
varBind :: Id -> SimpleType -> Maybe Subst
varBind u t | t == TVar u   = Just []
            | t == TCon u   = Just []
            | u `elem` tv t = Nothing
            | otherwise     = Just [(u, t)]
			
mgu (TArr l r,  TArr l' r') = do s1 <- mgu (l,l')
                                 s2 <- mgu ((apply s1 r) ,  (apply s1 r'))
                                 return (s2 @@ s1)
mgu (TApp c v, TApp c' v')  = do s1 <- mgu (c,c')
                                 s2 <- mgu ((apply s1 v) ,  (apply s1 v'))
                                 return (s2 @@ s1)
mgu (t,        TVar u   )   =  varBind u t
mgu (TVar u,   t        )   =  varBind u t
mgu (t,        TCon u   )   =  varBind u t
mgu (TCon u,   t        )   =  varBind u t
mgu (t,        Lit u    )   =  Just []
mgu (Lit u,    t        )   =  Just []



unify t t' =  case mgu (t,t') of
    Nothing -> error ("unification: trying to unify\n" ++ (show t) ++ "\nand\n" ++
                      (show t'))
    Just s  -> s
 