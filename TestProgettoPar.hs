-- Progetto LC 2021 -- Mansi/Cagnoni UNIUD --

module Main where

import Prelude
  (($)
  , Either(..)
  , Int, (>)
  , String, (++), unlines
  , Char
  , Show, show
  , IO, (>>), (>>=), (==), (||), (&&) , mapM_, putStrLn
  , FilePath
  , getContents, readFile, showString)

import System.Environment (getArgs)
import System.Exit        (exitFailure, exitSuccess)
import Control.Monad      (when)

import AbsProgettoPar   as Abs (S (StartCode), STATEMENTS (ListStatements, EmptyStatement), STATEMENT (..), B (BlockStatement), ELSESTATEMENT (..), CONDITIONALSTATE(..)) 
import LexProgettoPar   (Token, Posn)
import ParProgettoPar   (pS, myLexer)
import PrintProgettoPar (Print, printTree)
import SkelProgettoPar  ()
import TypeChecker
import Type
import Data.Map

type Err        = Either String
type ParseFun a = [Token] -> Err a
type Verbosity  = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

runFile :: Verbosity -> ParseFun (S Posn) -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run v p

run :: Verbosity -> ParseFun (S Posn) -> String -> IO ()
run v p s =
  case p ts of
    Left err -> do
      putStrLn "\nParse            Failed :( ...\n"
      putStrV v "Tokens:"
      putStrV v $ show ts
      putStrLn err
      exitFailure
    Right tree -> do
      putStrLn "\nParse Successful!"
      Main.showTree v tree
      let typecheckRes = TypeChecker.executeTypeChecking tree (Data.Map.fromList []) in 
        putStrLn (show typecheckRes)

      putStrLn "\n\n[Statements TypeChecker Result]\n"

      let typecheckRes = TypeChecker.executeTypeChecking tree (Data.Map.fromList []) in
        putStrLn (showTypeCheckResult typecheckRes)

      exitSuccess  

  where
  ts = myLexer (pointersSyntaxPreprocessing s [] [])

----------------------------------------------------------------------------------------------------
--- TYPE CHECKING RESULTS PRINTING (Prints TCheckResults + env for each statement (recursively)) ---
----------------------------------------------------------------------------------------------------

showTypeCheckResult:: (Show attr) => (Abs.S attr) -> String
showTypeCheckResult (Abs.StartCode result statements) = showTypeCheckResultStatements statements ""

showTypeCheckResultStatements :: (Show attr) => (Abs.STATEMENTS attr) -> String -> String
showTypeCheckResultStatements (Abs.ListStatements result statement statements) spacer = "\n" ++ spacer ++ show result ++ case statement of
                                                                                               (Abs.ProcedureStatement res id params stats) -> (showTypeCheckResultStatement statement spacer)  ++ (showTypeCheckResultStatements statements spacer) 
                                                                                               (Abs.FunctionStatement res id params ty stats) -> (showTypeCheckResultStatement statement spacer) ++ (showTypeCheckResultStatements statements spacer)
                                                                                               (Abs.Statement res (Abs.BlockStatement _ stats)) -> (showTypeCheckResultStatement statement spacer) ++ (showTypeCheckResultStatements statements spacer)  -- block case
                                                                                               (Abs.ConditionalStatement res conditionalState) -> (showTypeCheckResultStatement statement spacer) ++ (showTypeCheckResultStatements statements spacer)
                                                                                               _ -> case statements of
                                                                                                      (Abs.EmptyStatement result) -> ""
                                                                                                      _ -> (showTypeCheckResultStatements statements spacer)
showTypeCheckResultStatements (Abs.EmptyStatement result) spacer = ""   -- gestione empty

showTypeCheckResultStatement :: (Show attr) => (Abs.STATEMENT attr) -> String -> String
showTypeCheckResultStatement (Abs.ProcedureStatement res id params stats) spacer = showTypeCheckResultStatements stats (spacer ++ "---")
showTypeCheckResultStatement (Abs.FunctionStatement res id params ty stats) spacer = showTypeCheckResultStatements stats (spacer ++ "---")
showTypeCheckResultStatement (Abs.Statement res (Abs.BlockStatement _ stats)) spacer = showTypeCheckResultStatements stats (spacer ++ "---") -- block
showTypeCheckResultStatement (Abs.ConditionalStatement res conditionalState) spacer = case conditionalState of 
                                                                                        -- with else
                                                                                        (Abs.ConditionalStatementSimpleThen res _ stat (Abs.ElseState r elsestat)) -> (showTypeCheckResultStatement stat (spacer ++ "---")) ++ (showTypeCheckResultStatement elsestat (spacer ++ "---"))
                                                                                        (Abs.ConditionalStatementSimpleWThen res _ (Abs.BlockStatement _ bstats) (Abs.ElseState r elsestat)) -> (showTypeCheckResultStatements bstats (spacer ++ "---")) ++ (showTypeCheckResultStatement elsestat (spacer ++ "---"))
                                                                                        (Abs.ConditionalStatementCtrlThen res _ stat (Abs.ElseState r elsestat)) -> (showTypeCheckResultStatement stat (spacer ++ "---")) ++ (showTypeCheckResultStatement elsestat (spacer ++ "---"))
                                                                                        (Abs.ConditionalStatementCtrlWThen res _ (Abs.BlockStatement _ bstats) (Abs.ElseState r elsestat)) -> (showTypeCheckResultStatements bstats (spacer ++ "---")) ++ (showTypeCheckResultStatement elsestat (spacer ++ "---"))
                                                                                        -- without else
                                                                                        (Abs.ConditionalStatementSimpleThen res _ stat _) -> (showTypeCheckResultStatement stat (spacer ++ "---")) 
                                                                                        (Abs.ConditionalStatementSimpleWThen res _ (Abs.BlockStatement _ bstats)_) -> (showTypeCheckResultStatements bstats (spacer ++ "---")) 
                                                                                        (Abs.ConditionalStatementCtrlThen res _ stat _) -> (showTypeCheckResultStatement stat (spacer ++ "---")) 
                                                                                        (Abs.ConditionalStatementCtrlWThen res _ (Abs.BlockStatement _ bstats) _) -> (showTypeCheckResultStatements bstats (spacer ++ "---")) 
                                                                                        _ -> "asd"
showTypeCheckResultStatement (Abs.VariableDeclarationStatement res _ _) spacer = "\n" ++ spacer ++ show res
                                                                                        

--------------------------------------------------------------------------------
--- Preprocessing of the input for multiple pointers compatibility "*******" ---
--------------------------------------------------------------------------------

pointersSyntaxPreprocessing :: String -> String -> String -> String
pointersSyntaxPreprocessing [] [] output = output
pointersSyntaxPreprocessing [] zs output = output
pointersSyntaxPreprocessing (x:xs) zs output= if x==' ' || x=='*' || x==':'
                          then
                            if x==' '
                              then
                                if last zs ' '=='='
                                  then
                                    pointersSyntaxPreprocessing xs zs (output++[x])
                                  else
                                    pointersSyntaxPreprocessing xs [] (output++[x])
                              else
                                if x==':'
                                  then
                                    pointersSyntaxPreprocessing xs [] (output++[x])
                                  else
                                    if x=='*'
                                      then
                                        if zs=="int" || zs=="bool" || zs=="real" || zs=="string" || zs=="char"
                                          then
                                            pointersSyntaxPreprocessing xs zs ((output++[x] ) ++ [' '] )
                                          else
                                            pointersSyntaxPreprocessing xs [] (output++[x])
                                      else
                                        pointersSyntaxPreprocessing xs [] (output++[x])
                          else
                            if x=='&' && last zs ' '=='='
                              then
                                pointersSyntaxPreprocessing xs zs (output++[x]++[' '])
                              else
                                pointersSyntaxPreprocessing xs (zs++[x]) (output++[x])

last :: String -> Char -> Char
last [] e = e
last [x] e = last [] x
last (x:xs) e = last xs x


showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree = do
  putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
  putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely."
    , "  (files)         Parse content of files verbosely."
    , "  -s (files)      Silent mode. Parse content of files silently."
    ]
  exitFailure

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    []         -> getContents >>= run 2 pS
    "-s":fs    -> mapM_ (runFile 0 pS) fs
    fs         -> mapM_ (runFile 2 pS) fs

