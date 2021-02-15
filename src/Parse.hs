{-|
Module      : Parse
Description : Define un parser de términos PCF0 a términos fully named.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Parse (tm, Parse.parse, decl, runP, P, program, declOrTm) where

import Prelude hiding ( const )
import Lang
import Common
import Text.Parsec hiding (runP)
import Data.Char ( isNumber, ord, isUpper, isLower )
import qualified Text.Parsec.Token as Tok
import Text.ParserCombinators.Parsec.Language ( GenLanguageDef(..), emptyDef )

type P = Parsec String ()

-----------------------
-- Lexer
-----------------------
-- | Analizador de Tokens
lexer :: Tok.TokenParser u
lexer = Tok.makeTokenParser $
        emptyDef {
         commentLine    = "#",
         reservedNames = ["let", "fun", "fix", "then", "else", 
                          "succ", "pred", "ifz", "Nat", "rec", 
                          "type", "in", "rec"],
         reservedOpNames = ["->",":","=", "+", "-"]
        }

whiteSpace :: P ()
whiteSpace = Tok.whiteSpace lexer

natural :: P Integer 
natural = Tok.natural lexer

parens :: P a -> P a
parens = Tok.parens lexer

identifier :: P String
identifier = Tok.identifier lexer

reserved :: String -> P ()
reserved = Tok.reserved lexer

reservedOp :: String -> P ()
reservedOp = Tok.reservedOp lexer

-----------------------
-- Parsers
-----------------------

num :: P Int
num = fromInteger <$> natural

var :: P Name
var = Tok.lexeme lexer $ do -- antes era identifier
  (c:cs) <- identifier
  if isLower c then return (c:cs) else parserZero

getPos :: P Pos
getPos = do pos <- getPosition
            return $ Pos (sourceLine pos) (sourceColumn pos)

tyvar :: P Name
tyvar = Tok.lexeme lexer $ do
  (c:cs) <- identifier
  if isUpper c then return (c:cs) else parserZero
                    
tyatom :: P Ty
tyatom = (do reserved "Nat"
             return NatTy) <|>
         (do v <- tyvar
             return (NameTy v)) <|>
         parens typeP

typeP :: P Ty
typeP = try (do 
          x <- tyatom
          reservedOp "->"
          y <- typeP
          return (FunTy x y))
      <|> tyatom
          
const :: P Const
const = CNat <$> num


unaryOpName :: P UnaryOp
unaryOpName =
      (reserved "succ" >> return Succ)
  <|> (reserved "pred" >> return Pred)


unaryOpFree :: P NSTerm
unaryOpFree = do
  i <- getPos
  o <- unaryOpName
  return (SUnaryOpFree i o)

binaryOpName :: P BinaryOp
binaryOpName =
      (reservedOp "+" >> return Sum)
  <|> (reservedOp "-" >> return Sub)

binaryOp :: P NSTerm
binaryOp = do
  i <- getPos
  op <- binaryOpName
  return (SBinaryOp i op)
  
atom :: P NSTerm
atom =     (flip SConst <$> const <*> getPos)
       <|> flip SV <$> var <*> getPos
       <|> parens tm
       <|> unaryOpFree
       <|> binaryOp

binding :: P ([Name], Ty)
binding = parens $ do vars <- many1 var
                      reservedOp ":"
                      ty <- typeP
                      return (vars, ty)

bindingFix :: P (Name, Ty) --binding que solo acepta una variable (solo para fix)
bindingFix = parens $ do v <- var
                         reservedOp ":"
                         ty <- typeP
                         return (v, ty)

binders :: P [([Name], Ty)]
binders = many1 binding

lam :: P NSTerm
lam = do i <- getPos
         reserved "fun"
         xs <- binders
         reservedOp "->"
         t <- tm
         return (SLam i xs t)

-- Nota el parser app también parsea un solo atom.
app :: P NSTerm
app = (do i <- getPos
          f <- atom
          args <- many atom
          return (foldl (SApp i) f args))

ifz :: P NSTerm
ifz = do i <- getPos
         reserved "ifz"
         c <- tm
         reserved "then"
         t <- tm
         reserved "else"
         e <- tm
         return (SIfZ i c t e)

fix :: P NSTerm
fix = do i <- getPos
         reserved "fix"
         (f, fty) <- bindingFix
         (x, xty) <- bindingFix
         reservedOp "->"
         t <- tm
         return (SFix i f fty x xty t)

letP :: P NSTerm
letP = do i <- getPos
          reserved "let"
          v <- identifier
          reservedOp ":"
          ty <- typeP
          reservedOp "="
          t1 <- tm
          reserved "in"
          t2 <- tm
          return (SLet i v ty t1 t2)

letrec :: P NSTerm
letrec = do i <- getPos
            reserved "let"
            reserved "rec"
            v <- identifier
            xs <- binders
            reservedOp ":"
            ty <- typeP
            reservedOp "="
            t1 <- tm
            reserved "in"
            t2 <- tm
            return (SLetRec i v xs ty t1 t2)
   
letf :: P NSTerm
letf = do i <- getPos
          reserved "let"
          v <- identifier
          xs <- binders
          reservedOp ":"
          ty <- typeP
          reservedOp "="
          t1 <- tm
          reserved "in"
          t2 <- tm
          return (SLetf i v xs ty t1 t2)

-- | Parser de términos
tm :: P NSTerm
tm = app <|> lam <|> ifz <|> fix <|> (try letP <|> try letf <|> letrec)

-- | Parser de declaraciones
decl :: P (Decl NSTerm)
decl = do
  i <- getPos
  (do 
    reserved "let"
    try (do
      v <- var
      reservedOp ":"
      ty <- typeP
      reservedOp "="
      t <- tm
      return (Decl i v ty t)) 
      <|> (do
            f <- var --usar otra funcion para parsear nombre de funcion sino
            b <- binders
            reservedOp ":"
            ty <- typeP
            reservedOp "="
            t <- tm
            return (DeclLetf i f b ty t))
      <|> (do 
            reserved "rec"
            f <- var --usar otra funcion para parsear nombre de funcion sino
            b <- binders
            reservedOp ":"
            ty <- typeP
            reservedOp "="
            t <- tm
            return (DeclLetRec i f b ty t)))
      <|> (do 
            reserved "type"
            n <- tyvar
            reservedOp "="
            ty <- typeP
            return (DeclType i n ty))

  

-- | Parser de programas (listas de declaraciones) 
program :: P [Decl NSTerm]
program = many decl

-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
declOrTm :: P (Either (Decl NSTerm) NSTerm)
declOrTm =  try (Right <$> tm) <|> (Left <$> decl)

-- Corre un parser, chequeando que se pueda consumir toda la entrada
runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s

--para debugging (solo terminos!) en uso interactivo (ghci)
parse :: String -> NSTerm
parse s = case runP tm s "" of
            Right t -> t
            Left e -> error ("no parse: " ++ show s)
