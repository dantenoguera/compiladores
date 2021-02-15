module Hoist where
import Control.Monad.Writer
import Control.Monad.State
import Lang
import Subst ( open, openN )
import Data.List

data IrDecl = IrVal {irDeclName :: Name, irDeclDef :: Ir}
            | IrFun {irDeclName :: Name, irDeclArgNames :: [Name], irDeclBody :: Ir}
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


fresh :: Monad m => String -> StateT Int m Name
fresh n = do s <- get
             modify (+1)
             return ("__" ++ n ++ show s)

mkIr :: Ir -> Name -> [Name] -> Ir
mkIr t clo vs = go t clo vs 1
        where go t clo (v : vs) i = IrLet v (IrAccess (IrVar clo) i) (go t clo vs (i + 1))
              go t _ [] _ = t

closureConvert :: Term -> StateT Int (Writer [IrDecl]) Ir
closureConvert (V _ (Free n)) = return (IrVar n)
closureConvert (Const _ c) = return (IrConst c)
closureConvert (Lam _ x _ t) = do x' <- fresh x
                                  f <- fresh ""
                                  clo <- fresh "clo"
                                  let fvars = (map head . group . sort) $ filter (isPrefixOf "__") (freeVars t)
                                  t' <- closureConvert (open x' t)
                                  lift $ tell [IrFun f [clo, x'] (mkIr t' clo fvars)]
                                  return (MkClosure f (map IrVar fvars))
closureConvert (App _ t1 t2) = do t1' <- closureConvert t1
                                  t2' <- closureConvert t2
                                  name <- fresh "clo"
                                  let clo = IrVar name
                                  return (IrLet name t1' (IrCall (IrAccess clo 0) [clo, t2']))
closureConvert (UnaryOp _ op t) = do t' <- closureConvert t
                                     return (IrUnaryOp op t')
closureConvert (BinaryOp _ op t1 t2) = do t1' <- closureConvert t1
                                          t2' <- closureConvert t2
                                          return (IrBinaryOp op t1' t2')
closureConvert (Fix _ f _ x _ t) = do f' <- fresh ""
                                      x' <- fresh x
                                      clo <- fresh "clo"
                                      r <- fresh f 
                                      let fvars = (map head . group . sort) $ filter (isPrefixOf "__") (freeVars t)
                                      t' <- closureConvert (openN [r, x'] t)
                                      lift $ tell [IrFun f' [clo, x'] (mkIr t' clo (r : fvars))]
                                      return (MkClosure f' (map IrVar fvars))
closureConvert (IfZ _ c t1 t2) = do c' <- closureConvert c
                                    t1' <- closureConvert t1
                                    t2' <- closureConvert t2
                                    return (IrIfZ c' t1' t2')
closureConvert (Let _ n _ t1 t2) = do n' <- fresh n 
                                      t1' <- closureConvert t1
                                      t2' <- closureConvert (open n' t2)
                                      return (IrLet n' t1' t2') -- cambiar el n?

runCC :: [Decl Term] -> [IrDecl]
runCC ds = go ds 0
           where go ((Decl _ name _ t) : xs) n = let ((ir, s), irDecls) = runWriter (runStateT (closureConvert t) n)
                                                in (irDecls ++ [IrVal name ir]) ++ go xs s
                 go [] _ = []

{-
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
-}

{-
IrVal {irDeclName = "x", irDeclDef = IrConst (CNat 1)}
IrVal {irDeclName = "y", irDeclDef = IrBinaryOp Sum (IrConst (CNat 2)) (IrVar "x")}
IrFun {irDeclName = "__1", irDeclArgNames = ["__clo2","__y0"], irDeclBody = IrBinaryOp Sum (IrConst (CNat 1)) (IrVar "x")}
IrVal {irDeclName = "f", irDeclDef = MkClosure "__1" []}
IrFun {irDeclName = "__7", irDeclArgNames = ["__clo8","__y6"], irDeclBody = IrLet "__x3" (IrAccess (IrVar "__clo8") 1) (IrBinaryOp Sum (IrVar "__x3") (IrVar "__y6"))}
IrFun {irDeclName = "__4", irDeclArgNames = ["__clo5","__x3"], irDeclBody = MkClosure "__7" [IrVar "__x3"]}
IrVal {irDeclName = "suma", irDeclDef = MkClosure "__4" []}
IrVal {irDeclName = "suma5", irDeclDef = IrLet "__clo9" (IrVar "suma") (IrCall (IrAccess (IrVar "__clo9") 0) [IrVar "__clo9",IrConst (CNat 5)])}
IrFun {irDeclName = "__10", irDeclArgNames = ["__clo12","__n11"], irDeclBody = IrLet "__countdown13" (IrAccess (IrVar "__clo12") 1) (IrIfZ (IrVar "__n11") (IrConst (CNat 0)) (IrLet "__clo14" (IrVar "__countdown13") (IrCall (IrAccess (IrVar "__clo14") 0) [IrVar "__clo14",IrBinaryOp Sub (IrVar "__n11") (IrConst (CNat 1))])))}
IrVal {irDeclName = "countdown", irDeclDef = MkClosure "__10" []}
-}