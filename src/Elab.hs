{-|
Module      : Elab
Description : Elabora un término fully named a uno locally closed.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite elaborar términos y declaraciones para convertirlas desde
fully named (@NTerm) a locally closed (@Term@) 
-}

module Elab ( elab, elab_decl ) where

import Lang
import Subst

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab :: NTerm -> Term
elab (V p v)               = V p (Free v)
elab (Const p c)           = Const p c
elab (Lam p v ty t)        = Lam p v ty (close v (elab t))
elab (App p h a)           = App p (elab h) (elab a)
elab (Fix p f fty x xty t) = Fix p f fty x xty (closeN [f, x] (elab t))
elab (IfZ p c t e)         = IfZ p (elab c) (elab t) (elab e)
elab (UnaryOp i o t)       = UnaryOp i o (elab t)

elab_decl :: Decl NSTerm STy -> Decl Term Ty
elab_decl = (fmap elab) . desugarDecl 

desugarDecl :: Decl NSTerm STy -> Decl NTerm Ty
desugarDecl (Decl p n ty t) =  Decl p n (desugarType ty) (desugarTerm t)
desugarDecl (DeclLetf p n args ty t) = (Decl p n (desugarType (foldr f' ty args)) (desugarTerm (SFun p args t)))
                                                where f' (n:ns,xty) tx = f' (ns,xty) (FunTy xty tx)--no hago desugar type por que lo hago en el tipo resultante
                                                      f' ([],xty) tx   = tx
desugarDecl (DeclLetRec p n [(x,xty)] ty t) = Decl p n (desugarType (STyFun xty ty)) (desugarTerm (SFix p n (STyFun xty ty) x xty t))
desugarDecl (DeclLetRec p n (x:xs) ty t) = desugarDecl (DeclLetRec p n x (foldr f' ty xs) (SFun p xs t))
                                                where f' (n:ns,xty) tx = f' (ns,xty) (STyFun xty tx) --no tengo que hacer desugar type por que lo hago en el caso base
                                                      f' ([],xty) tx   = tx
desugarDecl (Eval t) = Eval (desugarTerm t)


desugarTerm :: NSTerm -> NTerm
desugarTerm (SV p v) = V p v
desugarTerm (SConst p c) = Const p c
desugarTerm (SLam p n sty t) = Lam p n (desugarType sty) (desugarTerm t)
desugarTerm (SApp p t1 t2) = App p (desugarTerm t1) (desugarTerm t2)
desugarTerm (SUnaryOp p op t) = UnaryOp p op (desugarTerm t)
desugarTerm (SFix p f styf x styx t) = Fix p f (desugarType styf) x (desugarType styx) (desugarTerm t)
desugarTerm (SIfZ p t1 t2 t3) = IfZ p (desugarTerm t1) (desugarTerm t2) (desugarTerm t3)

desugarType :: STy -> Ty
desugarType STyNat = NatTy
desugarType (STyFun st1 st2) = FunTy (desugarType st1) (desugarType st2)
--desugarType (STyVar n) = undefined