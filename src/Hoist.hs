module Hoist where
import Control.Monad.Writer
import Control.Monad.State
import Lang
import Subst ( open )

data IrDecl = IrVal {irDeclName :: Name, irDeclDef :: Ir}
            | IrFun {irDeclName :: Name, irDeclArity :: Nat, irDeclArgNames :: [Name], irDeclBody :: Ir} -- Ver tipo irDeclArity
            deriving Show

data Ir = IrVar Name
        | IrCall Ir [Ir]
        | IrConst Const
        | IrUnaryOp UnaryOp Ir
        | IrBinaryOp BinaryOp Ir Ir
        | IrLet Name Ir Ir
        | IrIfZ Ir Ir Ir
        | MkClosure Name [Ir]
        | IrAccess Ir Int
        deriving Show


{-
data Tm info var = 
    V info var
  | Const info Const
  | Lam info Name Ty (Tm info var)
  | App info (Tm info var) (Tm info var)
  | UnaryOp info UnaryOp (Tm info var)
  | BinaryOp info BinaryOp (Tm info var) (Tm info var)
  | Fix info Name Ty Name Ty (Tm info var)
  | IfZ info (Tm info var) (Tm info var) (Tm info var)
  | Let info Name Ty (Tm info var) (Tm info var)
  deriving (Show, Functor)
-}

closureConvert :: Term -> StateT Int (Writer [IrDecl]) Ir
closureConvert (V _ (Free n)) = return (IrVar n)
closureConvert (Const _ c) = return (IrConst c)
closureConvert (Lam _ x _ t) = do s <- get
                                  put (s + 2)
                                  t'' <- closureConvert (open x t)
                                  lift $ tell (IrFun f 2 ["__clo", x'] t'') -- ver clo!!!
                                  let f = ("__" ++ (show s))
                                  let x'= ("__"++x ++ (show (s + 1))--cual viene primero, el nombre de funcion o la variable x? (para el indice del state)
                                  return (MkClosure f [IrVar x']) 
closureConvert (App _ t1 t2) = do (MkClosure name _) <- closureConvert t1 --ilegal?
                                  t2' <- closureConvert t2
                                  return (IrLet name t1' ((IrCall (IrAccess (IrVar name) 0) [IrVar name, t2'])))
closureConvert (UnaryOp _ op t) = do t' <- closureConvert t
                                     return (IrUnaryOp op t')
closureConvert (BinaryOp _ op t1 t2) = do t1' <- closureConvert t1
                                          t2' <- closureConvert t2
                                          return (IrBinaryOp op t1' t2')
closureConvert (Fix _ f _ x _ t) = -- ???
closureConvert (Ifz _ c t1 t2) = do c' <- closureConvert c
                                    t1' <- closureConvert t1
                                    t2' <- closureConvert t2
                                    return (IrIfZ c' t1' t2')
closureConvert (Let _ n _ t1 t2) = -- ???


{- Decl { declPos :: Pos, declName :: Name, declType :: Ty, declBody :: a } -} 
runCC :: [Decl Term] -> [IrDecl]
runCC = undefined



$ cat test.pcf 
let x : Nat = 1

let y : Nat = 2 + x

let f (y:Nat) : Nat = 1 + x

let suma (x y : Nat) : Nat = x + y

let suma5 : Nat -> Nat = suma 5

let rec countdown (n:Nat) : Nat =
  ifz n then 0 else countdown (n-1)

$ stack run -- --cc test.pcf
Resultado de CC:
IrVal {irDeclName = "x", irDeclDef = IrConst (CNat 1)}
IrVal {irDeclName = "y", irDeclDef = IrBinaryOp Add (IrConst (CNat 2)) (IrVar "x")}
IrFun {irDeclName = "__0", irDeclArity = 2, irDeclArgNames = ["__clo2","__y1"], irDeclBody = IrBinaryOp Add (IrConst (CNat 1)) (IrVar "x")}
IrVal {irDeclName = "f", irDeclDef = MkClosure "__0" []}
IrFun {irDeclName = "__5", irDeclArity = 2, irDeclArgNames = ["__clo7","__y6"], irDeclBody = IrLet "__x4" (IrAccess (IrVar "__clo7") 1) (IrBinaryOp Add (IrVar "__x4") (IrVar "__y6"))}
IrFun {irDeclName = "__3", irDeclArity = 2, irDeclArgNames = ["__clo8","__x4"], irDeclBody = MkClosure "__5" [IrVar "__x4"]}
IrVal {irDeclName = "suma", irDeclDef = MkClosure "__3" []}
IrVal {irDeclName = "suma5", irDeclDef = IrCall (IrAccess (IrVar "suma") 0) [IrVar "suma",IrConst (CNat 5)]}
IrFun {irDeclName = "__10", irDeclArity = 2, irDeclArgNames = ["__clo14","__n12"], irDeclBody = IrLet "__countdown11" (IrVar "__clo14") (IrIfZ (IrVar "__n12") (IrConst (CNat 0)) (IrCall (IrAccess (IrVar "__countdown11") 0) [IrVar "__countdown11",IrBinaryOp Sub (IrVar "__n12") (IrConst (CNat 1))]))}
IrVal {irDeclName = "countdown", irDeclDef = MkClosure "__10" []}














{-
closureConvert (App _ t1 t2) = do (MkClosure n (ir:irs)) <- closureConvert t1
                                  t2' <- closureConvert t2
                                  return (IrCall (IrAccess (IrVar n) 0) [(IrVar n),])
-}
{-let, mkclosure,  access0, clos-}