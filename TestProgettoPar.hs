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

import AbsProgettoPar   as Abs (S (StartCode), STATEMENTS (ListStatements, EmptyStatement), DOSTATEMENT (..), FORALLSTATEMENT (..), STATEMENT (..),
                                B (BlockStatement), FORSTATEMENT (..), ELSESTATEMENT (..), CONDITIONALSTATE(..), WHILESTATEMENT (..)) 
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

      -- Naive code for brutal Abs print with Tcheck results (too heavy syntax)
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

-- Given an AbstractSyntaxTree it prints, for each statement its attributes (used for tcheck result print-debugging).
-- If a statement has child-statements (for example a function with n statements in its block) it prints recursively those statements attrs (with spacer for depth recognition)
showTypeCheckResult:: (Show attr) => (Abs.S attr) -> String
showTypeCheckResult (Abs.StartCode result statements) = showTypeCheckResultStatements statements ""

-- Given an Abs node of type STATEMENTS it prints the result of the first one + its child 
-- (if it has childs statements) and recursively call the func on the remaining statements
showTypeCheckResultStatements :: (Show attr) => (Abs.STATEMENTS attr) -> String -> String
showTypeCheckResultStatements (Abs.ListStatements result statement statements) spacer = "\n" ++ spacer ++ show result ++ case statement of
                                                                                               (Abs.ProcedureStatement res id params stats) -> (showTypeCheckResultStatement statement spacer)  ++ (showTypeCheckResultStatements statements spacer) 
                                                                                               (Abs.FunctionStatement res id params ty stats) -> (showTypeCheckResultStatement statement spacer) ++ (showTypeCheckResultStatements statements spacer)
                                                                                               (Abs.Statement res (Abs.BlockStatement _ stats)) -> (showTypeCheckResultStatement statement spacer) ++ (showTypeCheckResultStatements statements spacer)  -- block case
                                                                                               (Abs.ConditionalStatement res conditionalState) -> (showTypeCheckResultStatement statement spacer) ++ (showTypeCheckResultStatements statements spacer)
                                                                                               (Abs.WhileDoStatement res whilestat) -> (showTypeCheckResultStatement statement spacer) ++ (showTypeCheckResultStatements statements spacer)
                                                                                               (Abs.DoWhileStatement res dostat) -> (showTypeCheckResultStatement statement spacer) ++ (showTypeCheckResultStatements statements spacer)
                                                                                               (Abs.ForStatement res forstats) -> (showTypeCheckResultStatement statement spacer) ++ (showTypeCheckResultStatements statements spacer)
                                                                                               (Abs.ForAllStatement res forallstats) -> (showTypeCheckResultStatement statement spacer) ++ (showTypeCheckResultStatements statements spacer)
                                                                                               _ -> case statements of
                                                                                                      (Abs.EmptyStatement result) -> ""
                                                                                                      _ -> (showTypeCheckResultStatements statements spacer)
showTypeCheckResultStatements (Abs.EmptyStatement result) spacer = ""   -- gestione empty

-- Given an Abs node of type STATEMENT (single stat) it prints it's attribute
showTypeCheckResultStatement :: (Show attr) => (Abs.STATEMENT attr) -> String -> String
showTypeCheckResultStatement (Abs.ProcedureStatement res id params stats) spacer = showTypeCheckResultStatements stats (spacer ++ "---") -- procedure case
showTypeCheckResultStatement (Abs.FunctionStatement res id params ty stats) spacer = showTypeCheckResultStatements stats (spacer ++ "---") -- function case
showTypeCheckResultStatement (Abs.Statement res (Abs.BlockStatement _ stats)) spacer = showTypeCheckResultStatements stats (spacer ++ "---") -- block case
showTypeCheckResultStatement (Abs.ConditionalStatement res conditionalState) spacer = case conditionalState of  -- if-then-else case
                                                                                        -- with else statements
                                                                                        (Abs.ConditionalStatementSimpleThen res _ stat (Abs.ElseState r elsestat)) -> (showTypeCheckResultStatement stat (spacer ++ "---")) ++ (showTypeCheckResultStatement elsestat (spacer ++ "---"))
                                                                                        (Abs.ConditionalStatementSimpleWThen res _ (Abs.BlockStatement _ bstats) (Abs.ElseState r elsestat)) -> (showTypeCheckResultStatements bstats (spacer ++ "---")) ++ (showTypeCheckResultStatement elsestat (spacer ++ "---"))
                                                                                        (Abs.ConditionalStatementCtrlThen res _ stat (Abs.ElseState r elsestat)) -> (showTypeCheckResultStatement stat (spacer ++ "---")) ++ (showTypeCheckResultStatement elsestat (spacer ++ "---"))
                                                                                        (Abs.ConditionalStatementCtrlWThen res _ (Abs.BlockStatement _ bstats) (Abs.ElseState r elsestat)) -> (showTypeCheckResultStatements bstats (spacer ++ "---")) ++ (showTypeCheckResultStatement elsestat (spacer ++ "---"))
                                                                                        -- without else statements
                                                                                        (Abs.ConditionalStatementSimpleThen res _ stat _) -> (showTypeCheckResultStatement stat (spacer ++ "---")) 
                                                                                        (Abs.ConditionalStatementSimpleWThen res _ (Abs.BlockStatement _ bstats) _) -> (showTypeCheckResultStatements bstats (spacer ++ "---")) 
                                                                                        (Abs.ConditionalStatementCtrlThen res _ stat _) -> (showTypeCheckResultStatement stat (spacer ++ "---")) 
                                                                                        (Abs.ConditionalStatementCtrlWThen res _ (Abs.BlockStatement _ bstats) _) -> (showTypeCheckResultStatements bstats (spacer ++ "---")) 
showTypeCheckResultStatement (Abs.WhileDoStatement res whilestat) spacer = case whilestat of -- while statements
                                                                                        (Abs.WhileStateSimpleDo res _ stat) -> (showTypeCheckResultStatement stat (spacer ++ "---")) 
                                                                                        (Abs.WhileStateSimpleWDo res _ (Abs.BlockStatement _ bstats)) -> (showTypeCheckResultStatements bstats (spacer ++ "---")) 
                                                                                        (Abs.WhileStateCtrlDo res _ stat) -> (showTypeCheckResultStatement stat (spacer ++ "---")) 
                                                                                        (Abs.WhileStateCtrlWDo res _ (Abs.BlockStatement _ bstats)) -> (showTypeCheckResultStatements bstats (spacer ++ "---"))                                                              
showTypeCheckResultStatement (Abs.DoWhileStatement res (Abs.DoWhileState _ dostat _)) spacer = (showTypeCheckResultStatement dostat (spacer ++ "---")) -- do-while statements
showTypeCheckResultStatement (Abs.ForStatement res forstats) spacer = case forstats of -- for statements
                                                                                        (Abs.ForStateIndexDo res _ _ stat) -> (showTypeCheckResultStatement stat (spacer ++ "---"))
                                                                                        (Abs.ForStateIndexWDo res _ _ (Abs.BlockStatement _ bstats)) -> (showTypeCheckResultStatements bstats (spacer ++ "---"))                                                              
                                                                                        (Abs.ForStateExprDo res _ stat) -> (showTypeCheckResultStatement stat (spacer ++ "---"))
                                                                                        (Abs.ForStateExprWDo res _ (Abs.BlockStatement _ bstats)) -> (showTypeCheckResultStatements bstats (spacer ++ "---"))                                                              
showTypeCheckResultStatement (Abs.ForAllStatement res forallstats) spacer = case forallstats of -- forall statements
                                                                                        (Abs.ForAllStateIndexDo res _ _ stat) -> (showTypeCheckResultStatement stat (spacer ++ "---"))
                                                                                        (Abs.ForAllStateIndexWDo res _ _ (Abs.BlockStatement _ bstats)) -> (showTypeCheckResultStatements bstats (spacer ++ "---"))
                                                                                        (Abs.ForAllStateExprDo res _ stat) -> (showTypeCheckResultStatement stat (spacer ++ "---"))
                                                                                        (Abs.ForAllStateExprWDo res _ (Abs.BlockStatement _ bstats)) -> (showTypeCheckResultStatements bstats (spacer ++ "---"))
-- Non-recursive cases of statements (no child statements)
showTypeCheckResultStatement (Abs.VariableDeclarationStatement res _ _) spacer  = "\n" ++ spacer ++ show res -- var. decl. case
showTypeCheckResultStatement (Abs.ExpressionStatement res _) spacer             = "\n" ++ spacer ++ show res -- expr. case
showTypeCheckResultStatement (Abs.AssignmentStatement res _ _ _) spacer         = "\n" ++ spacer ++ show res -- assignment case
showTypeCheckResultStatement (Abs.BreakStatement res) spacer                    = "\n" ++ spacer ++ show res -- break case
showTypeCheckResultStatement (Abs.ContinueStatement res ) spacer                = "\n" ++ spacer ++ show res -- continue case
showTypeCheckResultStatement (Abs.ReturnStatement res _) spacer                 = "\n" ++ spacer ++ show res -- return case
                                                                                        
--------------------------------------------------------------------------------
--- Preprocessing of the input for multiple pointers compatibility "*******" ---
--------------------------------------------------------------------------------

-- PreProcessing for pointer compatibility
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

