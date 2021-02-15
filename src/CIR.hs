module CIR where

import Lang ( BinaryOp, Name, UnaryOp, Const(..) )
import Data.List (intercalate, isPrefixOf)
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

-- IrVal {irDeclName = "a", irDeclDef = IrConst (CNat 5)}
-- IrVal {irDeclName = "b", irDeclDef = IrBinaryOp Sum (IrVar "a") (IrConst (CNat 3))}

runCanon :: [IrDecl] -> CanonProg -- (resetear estado entre declaraciones???)
runCanon ds = let (blocks, prog, s, v) = go ds (0, "Init",[]) (C 0) -- declaraciones/estado inicial/retorno del main
                  ((_, _), lastBlock) = runWriter (runStateT (closeBlock (Return v)) s)
              in CanonProg (prog ++ [Left ("pcfmain", [], blocks ++ lastBlock)])-- ver el orden en que se guardan las cosas, sino se cambia
              where go (d : ds) init ret = case d of
                                      IrVal name def -> let ((v, s), blocks) = runWriter (runStateT (blocksConvert def) init)
                                                            ((_, s'), lastBlock) = runWriter (runStateT (addInst (Store name (V v))) s) -- VER TERMINADOR
                                                            (blockslist, prog, s'', v')  = go ds s' v
                                                        in (blocks ++ lastBlock ++ blockslist, Right name : prog, s'', v')

                                      IrFun name args body -> let ((v, s), blocks) = runWriter (runStateT (blocksConvert body) init)
                                                                  ((_, s'), lastBlock) = runWriter (runStateT (closeBlock (Return v)) s) -- VER TERMINADOR
                                                                  (blockslist, prog, s'', v')  = go ds s' ret
                                                              in (blockslist, Left (name, args, blocks ++ lastBlock) : prog, s'', v')
                    go [] s ret = ([], [], s, ret)


pcfmainBlockBuild :: [Inst] -> StateT (Int, Loc, [Inst]) (Writer Blocks) ()
pcfmainBlockBuild stores = do l <- freshLoc "pcfmain"
                              tell [(l,
                                    stores,
                                    Return (C 0))] --Ver que devolvemos

freshRegister :: Monad m => StateT (Int, Loc, [Inst]) m Reg
freshRegister = do (n, _, _) <- get
                   modify (\(n, l, is) -> (n + 1, l, is))
                   return (Temp ("t" ++ show n))


freshLoc :: Monad m => String -> StateT (Int, Loc, [Inst]) m String
freshLoc str = do (n, _, _) <- get
                  modify (\(n, l, is) -> (n + 1, l, is))
                  return (str ++ show n)

addInst :: Monad m => Inst -> StateT (Int, Loc, [Inst]) m ()
addInst i = do (_, _, is) <- get
               modify (\(n, l, is) -> (n, l, is ++ [i]))

closeBlock :: Terminator -> StateT (Int, Loc, [Inst]) (Writer Blocks) ()
closeBlock t = do (_, l, is) <- get
                  tell [(l,is,t)]
                  modify (\(n, l, _) -> (n, l, []))

changeLoc :: Monad m => Loc -> StateT (Int, Loc, [Inst]) m ()
changeLoc l = modify (\(n, _, is) -> (n, l, is))

blocksConvert :: Ir -> StateT (Int, Loc, [Inst]) (Writer Blocks) Val
blocksConvert (IrVar name) = if "__" `isPrefixOf` name 
                              then return (R (Temp name)) 
                              else return (G name)
blocksConvert (IrConst (CNat n)) = return (C n)
blocksConvert (IrUnaryOp op e) = do v <- blocksConvert e
                                    t <- freshRegister
                                    tr <- freshRegister
                                    addInst (Assign t (V v))
                                    addInst (Assign tr (UnOp op (R t)))
                                    return (R tr)
blocksConvert (IrBinaryOp op e1 e2) = do v1 <- blocksConvert e1
                                         v2 <- blocksConvert e2
                                         t1 <- freshRegister
                                         t2 <- freshRegister
                                         t3 <- freshRegister
                                         addInst (Assign t1 (V v1))
                                         addInst (Assign t2 (V v2))
                                         addInst (Assign t3 (BinOp op (R t1) (R t2)))
                                         return (R t3)
blocksConvert (IrIfZ e1 e2 e3) = do entry <- freshLoc "entry"
                                    closeBlock (Jump entry)
                                    changeLoc entry
                                    v1 <- blocksConvert e1
                                    then' <- freshLoc "then"
                                    else' <- freshLoc "else"
                                    ifcont <- freshLoc "ifcont"
                                    t1 <- freshRegister
                                    addInst (Assign t1 (V v1))
                                    closeBlock (CondJump (Eq (C 0) v1) then' else')
                                    changeLoc then'
                                    v2 <- blocksConvert e2
                                    t2 <- freshRegister
                                    addInst (Assign t2 (V v2))
                                    closeBlock (Jump ifcont)
                                    changeLoc else'
                                    v3 <- blocksConvert e3
                                    t3 <- freshRegister
                                    addInst (Assign t3 (V v3))
                                    closeBlock (Jump ifcont)
                                    changeLoc ifcont
                                    t <- freshRegister
                                    addInst (Assign t (Phi [(then', R t2), (else', R t3)]))
                                    return (R t)
blocksConvert (IrAccess e n) = do v <- blocksConvert e
                                  t <- freshRegister
                                  addInst (Assign t (Access v n))
                                  return (R t)
blocksConvert (IrCall e es) = do v <- blocksConvert e
                                 vs  <- mapM blocksConvert es
                                 t <- freshRegister
                                 addInst (Assign t (Call v vs))
                                 return (R t)
blocksConvert (IrLet name e1 e2) = do v1 <- blocksConvert e1
                                      let r = Temp name
                                      addInst (Assign r (V v1))
                                      blocksConvert e2
blocksConvert (Hoist.MkClosure name es) = do vs <- mapM blocksConvert es
                                             t <- freshRegister
                                             addInst (Assign t (CIR.MkClosure name vs))
                                             return (R t)


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

{-
declare a

declare b

pcfmain() {
Init:
  Assign (Temp "t0") (V (C 2))
  Assign (Temp "t1") (V (C 3))
  Assign (Temp "t2") (BinOp Sum (R (Temp "t0")) (R (Temp "t1")))
  Assign (Temp "t3") (V (C 1))
  Assign (Temp "t4") (V (R (Temp "t2")))
  Assign (Temp "t5") (BinOp Sum (R (Temp "t3")) (R (Temp "t4")))
  Store "a" (V (R (Temp "t5")))
  Assign (Temp "t6") (V (C 1))
  Assign (Temp "t7") (UnOp Succ (R (Temp "t6")))
  Store "b" (V (R (Temp "t7")))
Return (R (Temp "t7"))
}

let a : Nat = 1 + (2 + 3)
let b : Nat = succ 1
let c : Nat = ifz 0 then a else b

declare a

declare b

declare c

pcfmain() {
Init:
  Assign (Temp "t0") (V (C 2))
  Assign (Temp "t1") (V (C 3))
  Assign (Temp "t2") (BinOp Sum (R (Temp "t0")) (R (Temp "t1")))
  Assign (Temp "t3") (V (C 1))
  Assign (Temp "t4") (V (R (Temp "t2")))
  Assign (Temp "t5") (BinOp Sum (R (Temp "t3")) (R (Temp "t4")))
  Store "a" (V (R (Temp "t5")))
  Assign (Temp "t6") (V (C 1))
  Assign (Temp "t7") (UnOp Succ (R (Temp "t6")))
  Store "b" (V (R (Temp "t7")))
Jump "entry8"
entry8:
  Assign (Temp "t12") (V (C 0))
CondJump (Eq (C 0) (C 0)) "then9" "else10"
then9:
  Assign (Temp "t13") (V (G "a"))
Jump "ifcont11"
else10:
  Assign (Temp "t14") (V (G "b"))
Jump "ifcont11"
ifcont11:
  Assign (Temp "t15") (Phi [("then9",R (Temp "t13")),("else10",R (Temp "t14"))])
  Store "c" (V (R (Temp "t15")))
Return (R (Temp "t15"))
}

-}