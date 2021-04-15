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

mkIrFix :: Ir -> Name -> [Name] -> Ir
mkIrFix t clo vs = go t clo vs 1
        where go t clo (r : vs) i = IrLet r (IrVar clo) (go t clo vs (i + 1))
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
                                      lift $ tell [IrFun f' [clo, x'] (mkIrFix t' clo (r : fvars))]
                                      return (MkClosure f' (map IrVar fvars))
closureConvert (IfZ _ c t1 t2) = do c' <- closureConvert c
                                    t1' <- closureConvert t1
                                    t2' <- closureConvert t2
                                    return (IrIfZ c' t1' t2')
closureConvert (Let _ n _ t1 t2) = do n' <- fresh n 
                                      t1' <- closureConvert t1
                                      t2' <- closureConvert (open n' t2)
                                      return (IrLet n' t1' t2')
                                      
runCC :: [Decl Term] -> [IrDecl]
runCC ds = go ds 0
           where go ((Decl _ name _ t) : xs) n = let ((ir, s), irDecls) = runWriter (runStateT (closureConvert t) n)
                                                in (irDecls ++ [IrVal name ir]) ++ go xs s
                 go [] _ = []