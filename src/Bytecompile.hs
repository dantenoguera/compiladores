{-# LANGUAGE PatternSynonyms #-}
{-|
Module      : Byecompile
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental
Este módulo permite compilar módulos a la BVM. También provee una implementación de la BVM 
para ejecutar bytecode.
-}
module Bytecompile
  (Bytecode, bytecompileModule, runBC, bcWrite, bcRead)
 where

import Lang 
import Subst
import MonadPCF
import Common

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le )
import Data.Binary.Get ( getWord32le, isEmpty )

type Opcode = Int
type Bytecode = [Int]
type Module = [Decl Term]

newtype Bytecode32 = BC { un32 :: [Word32] }

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord32le bs
  get = go 
    where go =  
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord32le
                      BC xs <- go
                      return $ BC (x:xs)

{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:
 
   f (CALL : cs) = ...
 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.
 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern RETURN   = 1
pattern CONST    = 2
pattern ACCESS   = 3
pattern FUNCTION = 4
pattern CALL     = 5
pattern SUCC     = 6
pattern PRED     = 7
pattern IFZ      = 8
pattern FIX      = 9
pattern STOP     = 10
pattern JUMP     = 11
pattern SHIFT    = 12
pattern DROP     = 13
pattern PRINT    = 14
pattern SUM      = 15
pattern SUB      = 16


bc :: MonadPCF m => Term -> m Bytecode
bc (V _ (Bound i)) = return [ACCESS, i]
bc (Const _ (CNat c)) = return [CONST, c]
bc (Lam _ _ _ t) = do t' <- bc t
                      return ([FUNCTION, length t' + 1] ++ t' ++ [RETURN])
bc (App _ t1 t2) =  do t1' <- bc t1
                       t2' <- bc t2
                       return (t1'++ t2'++ [CALL])
bc (UnaryOp _ Succ t) = do t' <- bc t
                           return (t' ++ [SUCC])
bc (UnaryOp _ Pred t) = do t' <- bc t
                           return (t' ++ [PRED])
bc (Fix _ _ _ _ _ t) = do t' <- bc t
                          return ([FUNCTION, length t' + 1] ++ t' ++ [RETURN, FIX])
bc (IfZ _ c t1 t2) = do c' <- bc c
                        t1' <- bc t1
                        t2' <- bc t2
                        return (c' ++ [IFZ] ++ [JUMP, length t1' + 2] ++ t1' ++ [JUMP, length t2'] ++ t2')
bc (Let _ _ _ t1 t2) = do t1' <- bc t1
                          t2' <- bc t2
                          return (t1' ++ [SHIFT] ++ t2' ++ [DROP])
bc (BinaryOp _ op t1 t2) = do  t1' <- bc t1
                               t2' <- bc t2
                               return (t2'++t1'++[f op])
                               where f Sum = SUM
                                     f Sub = SUB
                          

nestDecl :: Module -> Term
nestDecl [(Decl p n ty b)] = close n (Let p n ty b (V NoPos (Free n)))
nestDecl ((Decl p n ty b) : ds) = close n (Let p n ty b (nestDecl ds))

bytecompileModule :: MonadPCF m => Module -> m Bytecode
bytecompileModule mod = bc (nestDecl mod)

-- | Toma un bytecode, lo codifica y lo escribe un archivo 
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs++[PRINT,STOP])

---------------------------
-- * Ejecución de bytecode
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = map fromIntegral <$> un32  <$> decode <$> BS.readFile filename

type Env = [Val]
data Val = I Int | Fun Env Bytecode | RA Env Bytecode

runBC :: MonadPCF m => Bytecode -> m ()
runBC bc = runBC' bc [] []

runBC' :: MonadPCF m => Bytecode -> [Val] -> [Val] -> m ()
runBC' (CONST:c:xs) e s = runBC' xs e ((I c):s)
runBC' (ACCESS:i:xs) e s = runBC' xs e ((e!!i):s)
runBC' (FUNCTION:l:xs) e s = runBC' (drop l xs) e ((Fun e (take l xs)):s)
runBC' (RETURN:_) _ (v:(RA e bc):s) = runBC' bc e (v:s)
runBC' (RETURN:_) _ _ = error "Error RETURN"
runBC' (CALL:xs) e (v:(Fun ef bc):s) = runBC' bc (v:ef) ((RA e xs):s)
runBC' (CALL:_) _ _ = error "Error CALL"
runBC' (SUCC:xs) e ((I n):s) = runBC' xs e ((I (n+1)):s)
runBC' (SUCC:_) _ _ = error "Error SUCC"
runBC' (PRED:xs) e ((I n):s) = case n of
                                0 -> runBC' xs e ((I 0):s)
                                x -> runBC' xs e ((I (x-1)):s)
runBC' (PRED:_) _ _ = error "Error PRED"
runBC' (SUM:xs) e ((I m):(I n):s) = runBC' xs e ((I (m + n)):s)
runBC' (SUM:_) _ _ = error "Error SUM"
runBC' (SUB:xs) e ((I m):(I n):s) = if (m>n) then runBC' xs e ((I (m - n)):s) else runBC' xs e ((I 0):s)
runBC' (SUB:_) _ _ = error "Error SUB"

runBC' (FIX:xs) e ((Fun e' bc):s) = runBC' xs e ((Fun ((Fun efix bc):e) bc):s)
                                    where efix = (Fun efix bc):e
runBC' (IFZ:xs) e ((I c):s) = case c of
                                  0 -> runBC' (tail (tail xs)) e s
                                  _ -> runBC' xs e s
runBC' (IFZ:_) _ _ = error "Error IFZ"
runBC' (SHIFT:xs) e (v:s) = runBC' xs (v:e) s
runBC' (DROP:xs) (v:e) s = runBC' xs e s
runBC' (JUMP:n:xs) e s = runBC' (drop n xs) e s
runBC' (PRINT:xs) e ((I n):s) = do printPCF (show n)
                                   runBC' xs e ((I n):s)
runBC' (PRINT:_) _ _ = error "Error PRINT"
runBC' (STOP:_) _ _ = return ()
