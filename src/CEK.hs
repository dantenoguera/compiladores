{-|
Module      : CEK
Description : Evalúa un término con la máquina CEK
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, Dante Noguera, Nicolás Navall, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar, dnoguera@fceia.unr.edu.ar, niconavall@gmail.com
Stability   : experimental

Este módulo realizara la aplicacion de la maquina CEK en nuestros terminos
-}

module CEK (seek, destroy) where

import Lang
import MonadPCF ( MonadPCF, lookupDecl, failPCF )
import PPrint ( ppName )

type Env = [Val]

data Val = N Const | C Clos

data Clos = CFun Env Name Term | CFix Env Name Name Term

data Fr = 
    HApp Env Term 
    | HClos Clos
    | HUnaryOp UnaryOp
    | HIfz Env Term Term

type Kont = [Fr]

seek :: MonadPCF m => Term -> Env -> Kont -> m Val
seek (UnaryOp _ Pred t) p k = seek t p ((HUnaryOp Pred):k)
seek (UnaryOp _ Succ t) p k = seek t p ((HUnaryOp Succ):k)
seek (IfZ _ t1 t2 t3) p k   = seek t1 p ((HIfz p t2 t3):k)
seek (App _ t1 t2) p k      = seek t1 p ((HApp p t2):k)
seek (V _ (Free nm)) p k    = do
    -- unfold and keep going
    mtm <- lookupDecl nm 
    case mtm of 
      Nothing -> failPCF $ "Error de ejecución: variable no declarada: " ++ ppName nm 
      Just t -> seek t p k
seek (V _ (Bound n)) p k = destroy (p!!n) k -- bound respeta que las listas se indexen desde 0?
seek (Const _ (CNat n)) p k = destroy (N (CNat n)) k
seek (Lam _ x _ t) p k = destroy (C (CFun p x t)) k
seek (Fix _ f _ x _ t) p k = destroy (C (CFix p f x t)) k


destroy :: MonadPCF m => Val -> Kont -> m Val
destroy (N (CNat 0)) ((HUnaryOp Pred):k) = return (N (CNat 0))
destroy (N (CNat np)) ((HUnaryOp Pred):k) = return (N (CNat (np-1)))
destroy (N (CNat n)) ((HUnaryOp Succ):k) = return (N (CNat (n+1)))
destroy (N (CNat 0)) ((HIfz p t1 t2):k) = seek t1 p k
destroy (N (CNat np)) ((HIfz p t1 t2):k) = seek t2 p k
destroy (C c) ((HApp p2 t2):k) = seek t2 p2 ((HClos c):k)
destroy v ((HClos (CFun p x t)):k) = seek t (v:p) k --ver el tema de x->v en p
destroy v ((HClos (CFix p f x t)):k) = seek t (((C (CFix p f x t)):v:p)) k