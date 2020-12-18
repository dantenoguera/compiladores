{-|
Module      : Eval
Description : Evalúa un término siguiendo la semántica big-step
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo evaluá términos siguiendo la semántica big-step (estrategia CBV)
-}

module Eval where

import Common ( abort )
import Lang
import Subst ( substN, subst )
import MonadPCF ( MonadPCF, lookupDecl, failPCF )
import PPrint ( ppName )

-- | Evaluador de términos CBV
eval ::  MonadPCF m => Term -> m Term
eval (V _ (Free nm)) = do
  -- unfold and keep going
  mtm <- lookupDecl nm 
  case mtm of 
    Nothing -> failPCF $ "Error de ejecución: variable no declarada: " ++ ppName nm 
    Just t -> eval t

eval (App p l r) = do
     le <- eval l
     re <- eval r
     case (le, re) of
        (Lam _ y _ m, n) ->
           eval (subst n m)
        (ff@(Fix p f _ _ _ t), n) ->
           eval (substN [ff, n] t)
        _ ->
           abort("Error de tipo en runtime " ++ show (le, re))

eval (UnaryOp p Succ t) = do
        te <- eval t
        case te of
          Const _ (CNat n) -> return (Const p (CNat (n+1)))
          _                -> abort "Error de tipo en runtime!"
eval (UnaryOp p Pred t) = do
        te <- eval t
        case te of
          Const _ (CNat n) -> return (Const p (CNat (max 0 (n-1))))
          _                -> abort "Error de tipo en runtime!"
eval (BinaryOp p Sum t1 t2) = do
        t1e <- eval t1
        case t1e of
           Const _ (CNat n) -> do t2e <- eval t2
                                  case t2e of
                                     Const _ (CNat m) -> return (Const p (CNat (n + m)))
                                     _ -> abort "Error de tipo en runtime!"
           _ -> abort "Error de tipo en runtime!"
eval (BinaryOp p Sub t1 t2) = do
      t1e <- eval t1
      case t1e of
         Const _ (CNat n) -> do t2e <- eval t2
                                case t2e of
                                    Const _ (CNat m) -> return (Const p (CNat (max 0 (n - m))))
                                    _ -> abort "Error de tipo en runtime!"
         _ -> abort "Error de tipo en runtime!"
eval (IfZ p c t e) = do
     ce <- eval c
     case ce of
       Const _ (CNat 0) -> eval t
       Const _ (CNat _) -> eval e
       c' -> abort "Error de tipo en runtime!"
eval (Let p _ _ t1 t2) = do te1 <- eval t1
                            eval (subst t2 te1)
-- nada más para reducir
eval t = return t
