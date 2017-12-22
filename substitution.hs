-- Type substitutions

import Data.Map (Map, (!))
import qualified Data.Map as Map

import qualified Text.PrettyPrint as PP

data Type = TVar String
          | TInt
          | TBool
          | TFun Type Type deriving (Eq, Ord)

type Subst = Map.Map String Type

nullSubst :: Subst
nullSubst = Map.empty

apply :: Subst -> Type -> Type
apply s (TVar n) = case Map.lookup n s of
						Nothing -> TVar n
						Just t -> t
apply s (TFun t1 t2) = TFun (apply s t1) (apply s t2)
apply s t = t

composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = Map.union (Map.map (apply s2) s1) s2
-- composeSubst s1 s2 = Map.union (Map.map (apply s1) s2) s1 (wrong !!!)

-- tests
test1 = 
	do
		let s = Map.insert "b" (TFun (TVar "b") (TVar "r")) (Map.insert "a" (TFun (TVar "a") (TVar "b")) nullSubst)
		let t = (TFun (TVar "a") (TVar "b"))
		putStrLn $ "S: " ++ show s
		putStrLn $ "t: " ++ show t
		putStrLn $ "S(t): " ++ show (apply s t)

test2 = 
	do
		let s1 = (Map.insert "a" (TFun (TVar "a1") (TVar "a2")) (Map.insert "b" (TVar "r") nullSubst))
		let s2 = (Map.insert "a1" (TVar "b") (Map.insert "b" (TVar "a2") nullSubst))
		putStrLn $ "S1: " ++ show s1
		putStrLn $ "S2: " ++ show s2
		putStrLn $ "compose S1 and S2: " ++ show (composeSubst s1 s2)
		
		
-- Pretty-priinting
instance Show Type where
	showsPrec _ x = shows (prType x)

prType :: Type -> PP.Doc
prType (TVar n)    = PP.text n
prType TInt        = PP.text "Int"
prType TBool       = PP.text "Bool"
prType (TFun t s)  = prParenType t PP.<+> PP.text "->" PP.<+> prType s

prParenType ::  Type -> PP.Doc
prParenType t = 
	case t of
		TFun _ _  -> PP.parens (prType t)
		_         -> prType t
