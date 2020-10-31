{-|
Module      : CEK
Description : Evalúa un término con la máquina CEK
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, Dante Noguera, Nicolás Navall, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar, dnoguera@fceia.unr.edu.ar, niconavall@gmail.com
Stability   : experimental

Este módulo realizara la aplicacion de la maquina CEK en nuestros terminos
-}

module CEK (seek, destroy, valToTerm) where

import Subst ( substN )
import Common
import Lang
import MonadPCF ( MonadPCF, lookupDecl, failPCF, printPCF )
import PPrint ( ppName )

type Env = [Val]

data Val = 
    N Const 
    | C Clos 
    deriving Show

data Clos = 
    CFun Env Name Ty Term 
    | CFix Env Name Ty Name Ty Term
    deriving Show

data Fr = 
    HApp Env Term 
    | HClos Clos
    | HUnaryOp UnaryOp
    | HBinaryOpLeft BinaryOp Const
    | HBinaryOpRight Env BinaryOp Term
    | HIfz Env Term Term

type Kont = [Fr]

seek :: MonadPCF m => Term -> Env -> Kont -> m Val
seek (UnaryOp _ op t) p k = seek t p ((HUnaryOp op):k)
seek (BinaryOp _ op t1 t2) p k = seek t1 p ((HBinaryOpRight p op t2):k)
seek (IfZ _ t1 t2 t3) p k   = seek t1 p ((HIfz p t2 t3):k)
seek (App _ t1 t2) p k      = seek t1 p ((HApp p t2):k)
seek (V _ (Free nm)) p k    = do
    -- unfold and keep going
    mtm <- lookupDecl nm 
    case mtm of 
      Nothing -> failPCF $ "Error de ejecución: variable no declarada: " ++ ppName nm 
      Just t -> seek t p k
seek (V _ (Bound n)) p k = destroy (p!!n) k
seek (Const _ (CNat n)) p k = destroy (N (CNat n)) k
seek (Lam _ x ty t) p k = destroy (C (CFun p x ty t)) k
seek (Fix _ f fty x xty t) p k = destroy (C (CFix p f fty x xty t)) k
seek (Let i n ty t1 t2) p k = seek (App i (Lam i n ty t2) t1) p k


destroy :: MonadPCF m => Val -> Kont -> m Val
destroy (N (CNat 0)) ((HUnaryOp Pred):k) = destroy (N (CNat 0)) k
destroy (N (CNat np)) ((HUnaryOp Pred):k) = destroy (N (CNat (np-1))) k
destroy (N (CNat n)) ((HUnaryOp Succ):k) = destroy (N (CNat (n+1))) k
destroy (C c) ((HUnaryOp _):k) = abort("Error de tipo en runtime en op. unaria")
--destroy (N (CNat 0)) ((HBinaryOpRight _ Sub _):k) = destroy (N (CNat 0)) k
destroy (N (CNat np)) ((HBinaryOpRight p op t):k) = seek t p ((HBinaryOpLeft op (CNat np)):k)
destroy (N (CNat n)) ((HBinaryOpLeft Sub (CNat np)):k) = if (np>n) then destroy (N (CNat (np-n))) k else destroy (N (CNat 0)) k
--destroy (N (CNat n)) ((HBinaryOpRight p Sum t):k) = seek t p ((HBinaryOpLeft Sum n):k) --no es necesario por la otra linea que cubre el caso
destroy (N (CNat n)) ((HBinaryOpLeft Sum (CNat n')):k) = destroy (N (CNat (n'+n))) k
destroy (C c) ((HBinaryOpRight _ _ _):k) = abort("Error de tipo en runtime de operacion binaria")
destroy (C c) ((HBinaryOpLeft _ _):k) = abort("Error de tipo en runtime de operacion binaria")
destroy (N (CNat 0)) ((HIfz p t1 t2):k) = seek t1 p k
destroy (N (CNat np)) ((HIfz p t1 t2):k) = seek t2 p k
destroy (C c) ((HIfz p t1 t2):k) = abort("Error de tipo en runtime en ifz")
destroy (C c) ((HApp p2 t2):k) = seek t2 p2 ((HClos c):k)
destroy (N (CNat n)) ((HApp p2 t2):k) = abort("Error de tipo en runtime en app" ++ show (n, t2)) --ecuacion agregada por nosotros
destroy v ((HClos (CFun p x _ t)):k) = seek t (v:p) k --ver el tema de x->v en p
destroy v ((HClos (CFix p f fty x xty t)):k) = seek t ((v:(C (CFix p f fty x xty t)):p)) k
destroy v [] = return v


valToTerm :: Val -> Term
valToTerm (N (CNat n)) = Const NoPos (CNat n)
valToTerm (C (CFun p x xty t)) = substN (map valToTerm p) (Lam NoPos x xty t)
valToTerm (C (CFix p f fty x xty t)) =  substN (map valToTerm p) (Fix NoPos f fty x xty t)