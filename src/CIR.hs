module CIR where

import Lang ( BinaryOp, Name, UnaryOp, Const(..) )
import Data.List (intercalate)
import Hoist ( Ir(..), IrDecl(..) )
import Control.Monad.State
import Control.Monad.Writer


newtype Reg = Temp String
  deriving Show

data Val = R Reg | C Int | G Name
  deriving Show

type Loc = String

data Inst =
    Assign Reg Expr
  | Store Name Expr
  deriving Show

data Expr =
    BinOp BinaryOp Val Val
  | UnOp UnaryOp Val
  | Phi [(Loc, Val)]
  | Call Val [Val]
  | MkClosure Loc [Val]
  | V Val
  | Access Val Int
  deriving Show

data Terminator =
    Jump Loc
  | CondJump Cond Loc Loc
  | Return Val
  deriving Show

data Cond =
    Eq Val Val
  deriving Show

type BasicBlock = (Loc, [Inst], Terminator)
type Blocks = [BasicBlock]

type CanonFun = (String, [String], [BasicBlock])
type CanonVal = String -- Sólo el nombre, tipo puntero siempre
newtype CanonProg = CanonProg [Either CanonFun CanonVal]


-- IrVal {irDeclName = "d", irDeclDef = IrConst (CNat 50)}
-- IrVal {irDeclName = "c", irDeclDef = IrBinaryOp Sum (IrVar "d") (IrConst (CNat 1))}

runCanon :: [IrDecl] -> CanonProg
runCanon ds = let (pcfmainBody, prog) = go ds 0
              in CanonProg (Left ("pcfmain", [], pcfmainBody) : prog)-- ver el orden en que se guardan las cosas, sino se cambia
              where go (d : ds) n = case d of
                                      IrVal name def -> let ((def', s), blocks) = runWriter (runStateT (blocksConvert def) n)
                                                            ((_, s'), pcfblock) = runWriter (runStateT (pcfmainBlockBuild name def') s)
                                                            (pcfmainBody, prog) = go ds s'
                                                        in (blocks ++ pcfblock ++ pcfmainBody, Right name : prog)
                                      IrFun name args body -> let ((_, s), blocks) = runWriter (runStateT (blocksConvert body) n)
                                                                  (pcfmainBody, prog) = go ds s
                                                              in (pcfmainBody, Left (name, args, blocks) : prog)
                    go [] _ = ([], [])

pcfmainBlockBuild :: Name -> Expr -> StateT Int (Writer Blocks) ()
pcfmainBlockBuild n e = do l <- freshLocName
                           tell [(l,
                                 [Store n e],
                                 Return (G n))]
                       
freshRegisterName :: Monad m => StateT Int m String
freshRegisterName = do s <- get
                       modify (+1)
                       return ("t" ++ show s)

freshLocName :: Monad m => StateT Int m String
freshLocName = do s <- get
                  modify (+1)
                  return ("L" ++ show s)

blocksConvert :: Ir -> StateT Int (Writer Blocks) Expr
blocksConvert (IrVar name) = return (V (G name))
blocksConvert (IrConst (CNat n)) = return (V (C n))
blocksConvert (IrBinaryOp op e1 e2) = do e1' <- blocksConvert e1
                                         e2' <- blocksConvert e2
                                         t1 <- freshRegisterName
                                         t2 <- freshRegisterName
                                         t3 <- freshRegisterName
                                         loc <- freshLocName
                                         let r1 = Temp t1
                                         let r2 = Temp t2
                                         let r3 = Temp t3
                                         tell [(loc, 
                                               [Assign r1 e1',
                                                Assign r2 e2',
                                                Assign r3 (BinOp op (R r1) (R r2))],
                                                Return (R r3))]
                                         return (V (R r3))
blocksConvert (IrUnaryOp op e) = do e' <- blocksConvert e
                                    t <- freshRegisterName
                                    tr <- freshRegisterName
                                    loc <- freshLocName
                                    let r = Temp t
                                    let rr = Temp tr
                                    tell [(loc, 
                                           [Assign r e',
                                            Assign rr (UnOp op (R r))],
                                            Return (R rr))]
                                    return (V (R rr))
blocksConvert (IrIfZ e1 e2 e3) = do phi <- freshLocName
                                    e2' <- blocksConvert e2
                                    t2 <- freshRegisterName
                                    l2 <- freshLocName
                                    tell [(l2,
                                           [Assign (Temp t2) e2'],
                                           Jump phi)]
                                    e3' <- blocksConvert e3
                                    t3 <- freshRegisterName
                                    l3 <- freshLocName
                                    tell [(l3,
                                           [Assign (Temp t3) e3'],
                                           Jump phi)]
                                    e1' <- blocksConvert e1
                                    t1 <- freshRegisterName
                                    entry <- freshLocName
                                    tell [(entry,
                                           [Assign (Temp t1) e1'],
                                           CondJump (Eq (C 0) (extractValue e1')) l2 l3)]
                                    t <- freshRegisterName
                                    tell [(phi,
                                          [Assign (Temp t) (Phi [(l2, R (Temp t2)), (l3, R (Temp t3))])],
                                          Return (R (Temp t)))]
                                    return (V (R (Temp t)))
blocksConvert (IrCall e es) = do e' <- blocksConvert e
                                 --t1 <- freshRegisterName
                                 --l1 <- freshLocName
                                 --tell [(l1,
                                 --     [Assign (Temp t1) e'],
                                 --     Return (R (Temp t1)))]
                                 vals <- aux es
                                 t2 <- freshRegisterName
                                 l2 <- freshLocName
                                 tell [(l2,
                                       [Assign (Temp t2) (Call (extractValue e') vals)],
                                       Return (R (Temp t2)))] --ver como poner jump aca
                                 return (V (R (Temp t2)))
blocksConvert (IrLet name e1 e2) = do e1' <- blocksConvert e1
                                      l1 <- freshLocName
                                      tell [(l1,
                                             [Store name e1'],
                                             Return (extractValue e1'))]
                                      e2' <- blocksConvert e2
                                      l2 <- freshLocName
                                      t <- freshRegisterName
                                      tell [(l2,
                                           [Assign (Temp t) e2'],
                                           Return (R (Temp t)))]
                                      return (V (R (Temp t)))
blocksConvert (IrAccess e n) = do e' <- blocksConvert e
                                  l <- freshLocName
                                  t <- freshRegisterName
                                  tell [(l,
                                         [Assign (Temp t) (Access (extractValue e') n)],
                                         Return (extractValue e'))]
                                  return (V (R (Temp t)))
blocksConvert (Hoist.MkClosure name es) = do vals <- aux es
                                             l <- freshLocName
                                             tell [(l,
                                                  [Store name (CIR.MkClosure l vals)],-- ver que tiene que ser el loc este, si se puede utilizar el l que tenemos
                                                   Return (G name))]
                                             return (V (G name))
                                             

extractValue :: Expr -> Val
extractValue (V v) = v
extractValue _ = undefined -- mejorar esto


aux (e : es) = do e' <- blocksConvert e
                  es' <- aux es
                  return (extractValue e' : es')
aux [] = return []



print :: (Blocks, [Inst], Val) -> String
print (bs, is, v) =
  concatMap printBlock bs ++ show is ++ "\n" ++ show v ++ "\n"

printBlock :: BasicBlock -> String
printBlock (loc, is, t) =
  loc ++ ":\n" ++
  concatMap (\i -> "  " ++ show i ++ "\n") is ++
  show t ++ "\n"

instance Show CanonProg where
  show (CanonProg prog) = concatMap pr1 prog where
    pr1 (Left (f, args, blocks)) =
      f ++ "(" ++ intercalate ", " args ++ ") {\n"
        ++ concatMap printBlock blocks ++ "}\n\n"

    pr1 (Right v) =
      "declare " ++ v ++ "\n\n"