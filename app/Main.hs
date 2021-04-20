{-# LANGUAGE RecordWildCards #-}

{-|
Module      : Main
Description : Compilador de PCF.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental
-}

module Main where

import System.Console.Haskeline ( defaultSettings, getInputLine, runInputT, InputT )
import Control.Monad.Catch (MonadMask)

--import Control.Monad
import Control.Monad.Trans
import Data.List (nub,  intersperse, isPrefixOf )
import Data.Char ( isSpace )
import Control.Exception ( catch , IOException )
import System.Environment ( getArgs )
import System.IO ( stderr, hPutStr )
import System.Process

import Global ( GlEnv(..) )
import Errors
import Lang
import Parse ( P, tm, program, declOrTm, runP )
import Elab ( elab, elab_decl )
import Eval ( eval )
import PPrint ( pp , ppTy )
import MonadPCF
import TypeChecker ( tc, tcDecl )
import CEK ( seek, destroy, valToTerm )
import Bytecompile
import Hoist ( runCC )
import CIR ( runCanon )
import InstSel ( codegen )

import Data.Text.Lazy.IO as TIO ( writeFile )
--import LLVM.AST -- necesario para pretty printing?
import LLVM.Pretty ( ppllvm )


import Options.Applicative hiding ( Const )


-- lineas de comandos
data Mode = Interactive
          | Typecheck
          | Bytecompile
          | Run
          | ClosureConvert
          | LLVMcompile


-- | Parser de banderas
parseMode :: Parser Mode
parseMode =
    flag' Typecheck ( long "typecheck" <> short 't' <> help "Solo chequear tipos")
    <|> flag' Bytecompile (long "bytecompile" <> short 'c' <> help "Compilar a la BVM")
    <|> flag' Run (long "run" <> short 'r' <> help "Ejecutar bytecode en la BVM")
    <|> flag Interactive Interactive ( long "interactive" <> short 'i'
                                                          <> help "Ejecutar en forma interactiva" )
    <|> flag' ClosureConvert (long "closureconvert" <> short 'a' <> help "Aplicar conversion de clausuras y hosting")
    <|> flag' LLVMcompile (long "llvmcompile" <> short 'l' <> help "Compila a codigo LLVM")


-- | Parser de opciones general, consiste de un modo y una lista de archivos a procesar
parseArgs :: Parser (Mode, [FilePath])
parseArgs = (,) <$> parseMode <*> many (argument str (metavar "FILES..."))


-- | Parser de programas
parseIO ::  MonadPCF m => String -> P a -> String -> m a
parseIO filename p x = case runP p x filename of
                  Left e  -> throwError (ParseErr e)
                  Right r -> return r


parseFile :: MonadPCF m => FilePath -> m [Decl NSTerm]
parseFile f = do
    printPCF ("Abriendo "++f++"...")
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStr stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err ++"\n")
                         return "")
    decls <- parseIO filename program x
    return decls


main :: IO ()
main = execParser opts >>= go
  where
    opts = info (parseArgs <**> helper)
                ( fullDesc
                  <> progDesc "Compilador de PCF"
                  <> header "Compilador de PCF de la materia Compiladores 2020" )


go :: (Mode,[FilePath]) -> IO ()
go (Interactive,files) =
  do runPCF (runInputT defaultSettings (main' files))
     return ()
go (Typecheck, files) = do runPCF $ catchErrors $ typeCheckFiles files
                           return ()
go (Bytecompile, files) = do runPCF $ catchErrors $  byteCompileFiles files
                             return ()
go (Run, files) = runFiles files
go (ClosureConvert, files) = do runPCF $ catchErrors $ closureConvertFiles files
                                return ()
go (LLVMcompile, files) = do runPCF $ catchErrors $ llvmCompileFiles files
                             return ()

------------------
-- LLVM COMPILE
------------------
llvmCompileFiles :: MonadPCF m => [FilePath] -> m()
llvmCompileFiles = mapM_ llvmCompileFile


llvmCompileFile :: MonadPCF m => FilePath -> m()
llvmCompileFile f =  do decls <- parseFile f
                        decls' <- handle decls
                        -- printPCF $ show (runCanon (runCC decls'))
                        let llvm = codegen (runCanon (runCC decls'))
                        let commandline = "clang -Wno-override-module output.ll src/runtime.c -lgc -o prog"
                        liftIO $ TIO.writeFile "output.ll" (ppllvm llvm)
                        liftIO $ system commandline
                        return ()
                        where handle ((DeclType p n ty): ds) = do addTy n ty
                                                                  handle ds
                              handle (dn : ds) = do dn' <- desugarDecl dn
                                                    let d = elab_decl dn'
                                                    tcDecl d
                                                    ds' <- handle ds
                                                    return (d : ds')
                              handle [] = return []

------------------
-- CLOSURE CONVERT
------------------
closureConvertFiles :: MonadPCF m => [FilePath] -> m()
closureConvertFiles = mapM_ closureConvertFile

closureConvertFile :: MonadPCF m => FilePath -> m ()
closureConvertFile f = do decls <- parseFile f
                          decls' <- handle decls
                          print (runCC decls')
                          where handle ((DeclType p n ty): ds) = do addTy n ty
                                                                    handle ds
                                handle (dn : ds) = do dn' <- desugarDecl dn
                                                      let d = elab_decl dn'
                                                      tcDecl d
                                                      ds' <- handle ds
                                                      return (d : ds')
                                handle [] = return []
                                print (d : ds) = do printPCF (show d)
                                                    print ds
                                print [] = return ()



---------------
-- TYPECHECKING
---------------
typeCheckFiles :: MonadPCF m => [FilePath] -> m ()
typeCheckFiles = mapM_ typeCheckFile

typeCheckFile :: MonadPCF m => FilePath -> m ()
typeCheckFile f = do
  decls <- parseFile f
  handle decls
  where handle ((DeclType p n ty): ds) = do addTy n ty
                                            handle ds
        handle (dn : ds) = do --printPCF (show dn)
                              --printPCF "\n"
                              dn' <- desugarDecl dn
                              --printPCF (show dn')
                              let d = elab_decl dn'
                              tcDecl d
                              addDecl d
                              handle ds
        handle [] = return ()

--------------
-- COMPILACION
--------------
byteCompileFiles :: MonadPCF m => [FilePath] -> m ()
byteCompileFiles = mapM_ byteCompileFile

byteCompileFile :: MonadPCF m => FilePath -> m ()
byteCompileFile f = do
  decls <- parseFile f
  decls' <- handle decls
  c <- bytecompileModule decls'
  liftIO $ bcWrite c (f ++ ".byte")
  return ()
  where handle ((DeclType p n ty): ds) = do addTy n ty
                                            handle ds
        handle (dn : ds) = do dn' <- desugarDecl dn
                              let d = elab_decl dn'
                              tcDecl d
                              addDecl d
                              ds' <- handle ds
                              return (d : ds')
        handle [] = return []


--------------
-- RUN
--------------
runFiles :: [FilePath] -> IO ()
runFiles (f:fs) = do b <- bcRead f
                     runPCF (runBC b)
                     runFiles fs
runFiles [] = return ()


--------------
-- INTERPRETE
--------------
data Command = Compile CompileForm
             | Print String
             | Type String
             | Browse
             | Quit
             | Help
             | Noop


data CompileForm = CompileInteractive  String
                 | CompileFile         String


data InteractiveCommand = Cmd [String] String (String -> Command) String


prompt :: String
prompt = "PCF> "


main' :: (MonadPCF m, MonadMask m) => [String] -> InputT m ()
main' args = do
        lift $ catchErrors $ compileFiles args
        s <- lift $ get
        when (inter s) $ liftIO $ putStrLn
          (  "Entorno interactivo para PCF0.\n"
          ++ "Escriba :? para recibir ayuda.")
        loop
  where loop = do
           minput <- getInputLine prompt
           case minput of
               Nothing -> return ()
               Just "" -> loop
               Just x -> do
                       c <- liftIO $ interpretCommand x
                       b <- lift $ catchErrors $ handleCommand c
                       maybe loop (flip when loop) b


compileFiles ::  MonadPCF m => [String] -> m ()
compileFiles []     = return ()
compileFiles (x:xs) = do
        modify (\s -> s { lfile = x, inter = False })
        compileFile x
        compileFiles xs


compileFile ::  MonadPCF m => String -> m ()
compileFile f = do
    decls <- parseFile f
    mapM_ handleDecl decls


handleDecl ::  MonadPCF m => Decl NSTerm -> m ()
handleDecl (DeclType p n ty) = addTy n ty
handleDecl ndecl = do
        ndecl' <- desugarDecl ndecl
        let decl@(Decl p x ty t) = elab_decl ndecl'
        tcDecl decl
        te <- runCEK t
        addDecl (Decl p x ty te)


-- | Parser simple de comando interactivos
interpretCommand :: String -> IO Command
interpretCommand x
  =  if isPrefixOf ":" x then
       do  let  (cmd,t')  =  break isSpace x
                t         =  dropWhile isSpace t'
           --  find matching commands
           let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
           case matching of
             []  ->  do  putStrLn ("Comando desconocido `" ++ cmd ++ "'. Escriba :? para recibir ayuda.")
                         return Noop
             [Cmd _ _ f _]
                 ->  do  return (f t)
             _   ->  do  putStrLn ("Comando ambigüo, podría ser " ++
                                   concat (intersperse ", " [ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
                         return Noop

     else
       return (Compile (CompileInteractive x))


commands :: [InteractiveCommand]
commands
  =  [ Cmd [":browse"]      ""        (const Browse) "Ver los nombres en scope",
       Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                     "Cargar un programa desde un archivo",
       Cmd [":print"]       "<exp>"   Print          "Imprime un término y sus ASTs sin evaluarlo",
       Cmd [":type"]        "<exp>"   Type           "Chequea el tipo de una expresión",
       Cmd [":quit",":Q"]        ""        (const Quit)   "Salir del intérprete",
       Cmd [":help",":?"]   ""        (const Help)   "Mostrar esta lista de comandos" ]


helpTxt :: [InteractiveCommand] -> String
helpTxt cs
  =  "Lista de comandos:  Cualquier comando puede ser abreviado a :c donde\n" ++
     "c es el primer caracter del nombre completo.\n\n" ++
     "<expr>                  evaluar la expresión\n" ++
     "let <var> = <expr>      definir una variable\n" ++
     unlines (map (\ (Cmd c a _ d) ->
                   let  ct = concat (intersperse ", " (map (++ if null a then "" else " " ++ a) c))
                   in   ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) cs)


-- | 'handleCommand' interpreta un comando y devuelve un booleano
-- indicando si se debe salir del programa o no.
handleCommand ::  MonadPCF m => Command  -> m Bool
handleCommand cmd = do
   s@GlEnv {..} <- get
   case cmd of
       Quit   ->  return False
       Noop   ->  return True
       Help   ->  printPCF (helpTxt commands) >> return True
       Browse ->  do  --printPCF (unlines [ s | s <- reverse (nub (map declName glb)) ])
                      printPCF (unlines [ s | s <- reverse (nub (map (\(n,t) -> n ++ ": " ++ (ppTy t)) tyEnv)) ])
                      return True
       Compile c ->
                  do  case c of
                          CompileInteractive e -> compilePhrase e
                          CompileFile f        -> put (s {lfile=f}) >> compileFile f
                      return True
       Print e   -> printPhrase e >> return True
       Type e    -> typeCheckPhrase e >> return True


compilePhrase ::  MonadPCF m => String -> m ()
compilePhrase x =
  do
    dot <- parseIO "<interactive>" declOrTm x
    case dot of
      Left d  -> handleDecl d
      Right t -> handleTerm t


handleTerm ::  MonadPCF m => NSTerm -> m ()
handleTerm t = do
         t' <- desugarTerm t
         let tt = elab t'
         s <- get
         ty <- tc tt (tyEnv s)
         te <- runCEK tt
         printPCF (pp te ++ " : " ++ ppTy ty)


printPhrase :: MonadPCF m => String -> m ()
printPhrase x =
  do
    x' <- parseIO "<interactive>" tm x
    x'' <- desugarTerm x'
    let  ex = elab x''
    t  <- case x'' of
           (V p f) -> maybe ex id <$> lookupDecl f
           _       -> return ex
    printPCF "NTerm:"
    printPCF (show x')
    printPCF "\nTerm:"
    printPCF (show t)


typeCheckPhrase :: MonadPCF m => String -> m ()
typeCheckPhrase x = do
         t <- parseIO "<interactive>" tm x
         t' <- desugarTerm t
         let tt = elab t'
         s <- get
         ty <- tc tt (tyEnv s)
         printPCF (ppTy ty)


runCEK :: MonadPCF m => Term -> m Term
runCEK t = do val <- seek t [] []
              return (valToTerm val)


----------
-- DESUGAR
----------
typeVariableExpand :: ([Name], Ty) -> Ty -> Ty
typeVariableExpand (n : ns, xty) tx = typeVariableExpand (ns,xty) (FunTy xty tx)
typeVariableExpand ([], xty) tx = tx

desugarDecl :: MonadPCF m => Decl NSTerm -> m (Decl NTerm)
desugarDecl (Decl p n ty t) =  do ty' <- desugarTy ty
                                  t' <- desugarTerm t
                                  return (Decl p n ty' t')
desugarDecl (DeclLetf p n args ty t) = do ty' <- desugarTy (foldr typeVariableExpand ty args)
                                          t' <- desugarTerm (SLam p args t)
                                          return (Decl p n ty' t')
desugarDecl (DeclLetRec p n [([x],xty)] ty t) = do ty' <- desugarTy ty
                                                   xty' <- desugarTy xty
                                                   t' <- desugarTerm (SFix p n (FunTy xty' ty') x xty' t) 
                                                   return (Decl p n (FunTy xty' ty') t')
desugarDecl (DeclLetRec p n ((x1 : rest, t1) : xs) ty t) = case rest of
                                                            [] -> do desugarDecl (DeclLetRec p n [([x1], t1)] 
                                                                      (foldr typeVariableExpand ty xs) 
                                                                      (SLam p xs t))
                                                            s -> do desugarDecl (DeclLetRec p n [([x1], t1)] 
                                                                      (foldr typeVariableExpand ty ((s, t1) : xs))
                                                                      (SLam p ((s, t1) : xs) t))
desugarDecl (Eval t) = do t' <- desugarTerm t
                          return (Eval t')

desugarTerm :: MonadPCF m => NSTerm -> m NTerm
desugarTerm (SV p v) = return (V p v)
desugarTerm (SConst p c) = return (Const p c)
desugarTerm (SApp p (SUnaryOpFree _ op) t2) = do t2' <- desugarTerm t2
                                                 return (UnaryOp p op t2')
desugarTerm (SApp _ (SApp p t1 (SBinaryOp _ op)) t2) = do t1' <- desugarTerm t1
                                                          t2' <- desugarTerm t2
                                                          return (BinaryOp p op t1' t2')
desugarTerm (SApp p t1 t2) = do t1' <- desugarTerm t1
                                t2' <- desugarTerm t2
                                return (App p t1' t2')
desugarTerm (SFix p f tyf x tyx t) = do tyf' <- desugarTy tyf
                                        tyx' <- desugarTy tyx
                                        t' <- desugarTerm t
                                        return (Fix p f tyf' x tyx' t')
desugarTerm (SIfZ p t1 t2 t3) = do t1' <- desugarTerm t1
                                   t2' <- desugarTerm t2
                                   t3' <- desugarTerm t3
                                   return (IfZ p t1' t2' t3')
desugarTerm (SLet p n ty t1 t2) = do ty' <- desugarTy ty
                                     t1' <- desugarTerm t1
                                     t2' <- desugarTerm t2
                                     return (Let p n ty' t1' t2')
desugarTerm (SLetf p f xs ty t1 t2) = desugarTerm (SLet p f (foldr typeVariableExpand ty xs) (SLam p xs t1) t2)
desugarTerm (SLam p xs t) = do t' <- desugarTerm t
                               let (Lam p' n' nty t'') = f p xs t'
                               nty' <- desugarTy nty
                               return (Lam p' n' nty' t'')
                               where f p ((n:ns,nty):xs) t = Lam p n nty (f p ((ns, nty):xs) t)
                                     f p (([],nty):xs) t = f p xs t
                                     f p [] t = t
desugarTerm (SUnaryOpFree p op) = return (Lam p "x" NatTy (UnaryOp p op (V p "x")))
desugarTerm (SLetRec p f [([x],xty)] ty t1 t2) = desugarTerm (SLet p f (FunTy xty ty) (SFix p f (FunTy xty ty) x xty t1) t2)
desugarTerm (SLetRec p f ((x1:rest, ty1):xs) ty t1 t2) | null rest = desugarTerm (SLetRec p f [([x1], ty1)] (foldr typeVariableExpand ty xs) (SLam p xs t1) t2)
                                                       | otherwise = desugarTerm (SLetRec  p f [([x1], ty1)] (foldr typeVariableExpand ty ((rest, ty1):xs)) (SLam p ((rest, ty1):xs) t1) t2)

desugarTy :: MonadPCF m => Ty -> m Ty
desugarTy (NameTy n) = do t <- lookupTy n
                          case t of
                            Just t' -> desugarTy t'
                            Nothing -> failPCF ("Error: No se encontro el tipo de nombre "++ n)
desugarTy NatTy = return NatTy
desugarTy (FunTy t1 t2) = do t1' <- desugarTy t1
                             t2' <- desugarTy t2
                             return (FunTy t1' t2')
