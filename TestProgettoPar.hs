-- Progetto LC 2021 -- Mansi/Cagnoni UNIUD --

module Main where

import Prelude
  (($)
  , Either(..)
  , Int, (>), (+)
  , String, (++), unlines
  , Char
  , Show, show
  , IO, (>>), (>>=), (==), (||), (&&) , mapM_, putStrLn, putStr, read
  , FilePath, Bool (..)
  , getContents, readFile, showString)

import System.Environment (getArgs)
import System.Exit        (exitFailure, exitSuccess)
import Control.Monad      (when)

import AbsProgettoPar   as Abs (S (StartCode), STATEMENTS (ListStatements, EmptyStatement), DOSTATEMENT (..), STATEMENT (..),
                                B (BlockStatement), FORSTATEMENT (..), ELSESTATEMENT (..), CONDITIONALSTATE(..), WHILESTATEMENT (..)) 
import LexProgettoPar   (Token, Posn)
import ParProgettoPar   (pS, myLexer)
import PrintProgettoPar (Print, printTree)
import SkelProgettoPar  ()
import TypeChecker
import Type
import AbsTac
import Data.Map
import TacGen

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
    Right tree -> do
      putStrLn "\n > Parse Successful! :) "
      Main.showTree v tree
      
      let typecheckRes = TypeChecker.executeTypeChecking tree (Data.Map.fromList []) in
        let tacgeneration = TacGen.genTAC typecheckRes in
          do
            putStrLn (show typecheckRes)
            putStrLn "\n\n[Statements TypeChecker Result]\n   For each statements it shows the TCheckResult (env+infos)\n"
            putStrLn (showTypeCheckResult typecheckRes True)
            putStrLn "\n\n[Compiler Errors]\n"        
            let compilerErrors = (showTypeCheckResult typecheckRes False) in
              if compilerErrors == ""
              then putStrLn (compilerErrors ++ "\n\n[TAC]\n" ++ (show tacgeneration) ++"\n\n[TAC in code]\n" ++ (showTac tacgeneration))
              else putStrLn (compilerErrors ++ "\n\n[TAC]\n" ++ " Cannot generate TAC with compiler errors!\n")
  where
  ts = myLexer (pointersSyntaxPreprocessing s [])

-- Given a path of test files, execute all of them
runTests :: Prelude.Int -> Verbosity -> [String] -> IO()
runTests index v (x:xs) = do
                      putStrLn "\n\n---------------------------------------------------------------------------------------------"
                      putStrLn ("------------ TEST n° " ++ show index ++ "-----------------------------------------------------------------------")
                      putStrLn "---------------------------------------------------------------------------------------------"
                      x <- readFile x
                      run v pS x

                      runTests (index + 1) v xs -- next test
runTests index v [] =  do
                      putStrLn "\n\n >>>>>>> End of testing Phase <<<<<<<\n"
                      putStrLn " For adding new test cases:\n   - create a new file n.txt with input code inside tests folder\n   - n must be the next number from the list\n   - modify variable \"numberOfTest\" with the new n-value in file TestProgettoPar.hs\n   - Rebuild and execute\n\n"

numberOfTests = 11
testFilesPaths = ["tests/" ++ (show x) ++ ".txt"| x <- [1..numberOfTests]]

----------------------------------------------------------------------------------------------------
--- TYPE CHECKING RESULTS PRINTING (Prints TCheckResults + env for each statement (recursively)) ---
----------------------------------------------------------------------------------------------------

-- if flag == true: given an AbstractSyntaxTree it prints, for each statement its attributes (used for tcheck result print-debugging).
-- If a statement has child-statements (for example a function with n statements in its block) it prints recursively those statements attrs (with spacer for depth recognition)
-- if flag == false: it does the same but prints ONLY ERRORS. It is used to show compiler errors at the end of execution.
showTypeCheckResult:: (Abs.S TCheckResult) -> Bool -> String
showTypeCheckResult (Abs.StartCode result statements) flag = showTypeCheckResultStatements statements "" flag

-- Given an Abs node of type STATEMENTS it prints the result of the first one + its child 
-- (if it has childs statements) and recursively call the func on the remaining statements
showTypeCheckResultStatements :: (Abs.STATEMENTS TCheckResult) -> String -> Bool -> String
showTypeCheckResultStatements (Abs.ListStatements result statement statements) spacer flag =  (if flag then "\n" ++ spacer ++ show result else printErr result) ++ case statement of
                                                                                               (Abs.ProcedureStatement res id params stats) -> (showTypeCheckResultStatement statement spacer flag)  ++ (showTypeCheckResultStatements statements spacer flag) 
                                                                                               (Abs.FunctionStatement res id params ty stats) -> (showTypeCheckResultStatement statement spacer flag) ++ (showTypeCheckResultStatements statements spacer flag)
                                                                                               (Abs.Statement res (Abs.BlockStatement _ stats)) -> (showTypeCheckResultStatement statement spacer flag) ++ (showTypeCheckResultStatements statements spacer flag)  -- block case
                                                                                               (Abs.ConditionalStatement res conditionalState) -> (showTypeCheckResultStatement statement spacer flag) ++ (showTypeCheckResultStatements statements spacer flag)
                                                                                               (Abs.WhileDoStatement res whilestat) -> (showTypeCheckResultStatement statement spacer flag) ++ (showTypeCheckResultStatements statements spacer flag)
                                                                                               (Abs.DoWhileStatement res dostat) -> (showTypeCheckResultStatement statement spacer flag) ++ (showTypeCheckResultStatements statements spacer flag)
                                                                                               (Abs.ForStatement res forstats) -> (showTypeCheckResultStatement statement spacer flag) ++ (showTypeCheckResultStatements statements spacer flag)
                                                                                               _ -> case statements of
                                                                                                      (Abs.EmptyStatement result) -> ""
                                                                                                      _ -> (showTypeCheckResultStatements statements spacer flag)
showTypeCheckResultStatements (Abs.EmptyStatement result) spacer flag = ""   -- gestione empty

printErr :: TCheckResult -> String
printErr (TError (x:xs)) = " " ++ x ++"\n"++ printErr (TError xs)
printErr _ = ""

-- Given an Abs node of type STATEMENT (single stat) it prints it's attribute
showTypeCheckResultStatement :: (Abs.STATEMENT TCheckResult) -> String -> Bool -> String
showTypeCheckResultStatement (Abs.ProcedureStatement res id params stats) spacer flag = showTypeCheckResultStatements stats (spacer ++ "---") flag -- procedure case
showTypeCheckResultStatement (Abs.FunctionStatement res id params ty stats) spacer flag = showTypeCheckResultStatements stats (spacer ++ "---") flag -- function case
showTypeCheckResultStatement (Abs.Statement res (Abs.BlockStatement _ stats)) spacer flag = showTypeCheckResultStatements stats (spacer ++ "---") flag -- block case
showTypeCheckResultStatement (Abs.ConditionalStatement res conditionalState) spacer flag = case conditionalState of  -- if-then-else case
                                                                                        -- with else statements
                                                                                        (Abs.ConditionalStatementSimpleThen res _ stat (Abs.ElseState r elsestat)) -> (showTypeCheckResultStatement stat (spacer ++ "---") flag) ++ (showTypeCheckResultStatement elsestat (spacer ++ "---") flag) 
                                                                                        (Abs.ConditionalStatementSimpleWThen res _ (Abs.BlockStatement _ bstats) (Abs.ElseState r elsestat)) ->  (showTypeCheckResultStatements bstats (spacer ++ "---") flag) ++ (showTypeCheckResultStatement elsestat (spacer ++ "---") flag) 
                                                                                        (Abs.ConditionalStatementCtrlThen res _ stat (Abs.ElseState r elsestat)) ->  (showTypeCheckResultStatement stat (spacer ++ "---") flag) ++ (showTypeCheckResultStatement elsestat (spacer ++ "---") flag) 
                                                                                        (Abs.ConditionalStatementCtrlWThen res _ (Abs.BlockStatement _ bstats) (Abs.ElseState r elsestat)) -> (showTypeCheckResultStatements bstats (spacer ++ "---") flag) ++ (showTypeCheckResultStatement elsestat (spacer ++ "---") flag)
                                                                                        -- without else statements
                                                                                        (Abs.ConditionalStatementSimpleThen res _ stat _) -> (showTypeCheckResultStatement stat (spacer ++ "---") flag)
                                                                                        (Abs.ConditionalStatementSimpleWThen res _ (Abs.BlockStatement _ bstats) _) -> (showTypeCheckResultStatements bstats (spacer ++ "---") flag)
                                                                                        (Abs.ConditionalStatementCtrlThen res _ stat _) ->(showTypeCheckResultStatement stat (spacer ++ "---") flag)
                                                                                        (Abs.ConditionalStatementCtrlWThen res _ (Abs.BlockStatement _ bstats) _) -> (showTypeCheckResultStatements bstats (spacer ++ "---") flag)
showTypeCheckResultStatement (Abs.WhileDoStatement res whilestat) spacer flag = case whilestat of -- while statements
                                                                                        (Abs.WhileStateSimpleDo res _ stat) -> (showTypeCheckResultStatement stat (spacer ++ "---") flag)
                                                                                        (Abs.WhileStateSimpleWDo res _ (Abs.BlockStatement _ bstats)) -> (showTypeCheckResultStatements bstats (spacer ++ "---") flag)
                                                                                        (Abs.WhileStateCtrlDo res _ stat) ->  (showTypeCheckResultStatement stat (spacer ++ "---") flag)
                                                                                        (Abs.WhileStateCtrlWDo res _ (Abs.BlockStatement _ bstats)) -> (showTypeCheckResultStatements bstats (spacer ++ "---") flag)                                                           
showTypeCheckResultStatement (Abs.DoWhileStatement res (Abs.DoWhileState _ dostat _)) spacer flag =  (showTypeCheckResultStatement dostat (spacer ++ "---") flag)-- do-while statements
showTypeCheckResultStatement (Abs.ForStatement res forstats) spacer flag = case forstats of -- for statements
                                                                                        (Abs.ForStateIndexDo res _ _ stat) -> (showTypeCheckResultStatement stat (spacer ++ "---") flag)
                                                                                        (Abs.ForStateIndexWDo res _ _ (Abs.BlockStatement _ bstats)) -> (showTypeCheckResultStatements bstats (spacer ++ "---") flag)                                                            
                                                                                        (Abs.ForStateExprDo res _ stat) -> (showTypeCheckResultStatement stat (spacer ++ "---") flag)
                                                                                        (Abs.ForStateExprWDo res _ (Abs.BlockStatement _ bstats)) -> (showTypeCheckResultStatements bstats (spacer ++ "---") flag)                                                        
-- Non-recursive cases of statements (no child statements)
showTypeCheckResultStatement (Abs.VariableDeclarationStatement res _ _) spacer flag   = if flag then "\n" ++ spacer ++ show res else printErr res -- var. decl. case
showTypeCheckResultStatement (Abs.ExpressionStatement res _) spacer flag              = if flag then "\n" ++ spacer ++ show res else printErr res -- expr. case
showTypeCheckResultStatement (Abs.AssignmentStatement res _ _ _) spacer flag          = if flag then "\n" ++ spacer ++ show res else printErr res -- assignment case
showTypeCheckResultStatement (Abs.BreakStatement res) spacer flag                     = if flag then "\n" ++ spacer ++ show res else printErr res -- break case
showTypeCheckResultStatement (Abs.ContinueStatement res ) spacer flag                 = if flag then "\n" ++ spacer ++ show res else printErr res -- continue case
showTypeCheckResultStatement (Abs.ReturnStatement res _) spacer flag                  = if flag then "\n" ++ spacer ++ show res else printErr res -- return case

----------------------------------------------------------------------------------------------------
--- TAC CODE PRINTING  ---
---------------------------------------------------------------------------------------------------- 

showTac :: S TAC -> String
showTac (Abs.StartCode tac@(TAC x) _) = showContent x

showContent :: [TACEntry] -> String
showContent (x:xs) = case x of
                      TacAssignBinaryOp id op fst scnd ty -> showAddrContent id++" "   ++genAssignEq ty++ " "  ++ showAddrContent fst ++" " ++ show op       ++" "++showAddrContent scnd  ++"\n"    ++ showContent xs
                      TacAssignRelOp id op fst scnd ty    -> showAddrContent id++" "   ++genAssignEq ty++ " " ++ showAddrContent fst ++" " ++show op       ++" "++showAddrContent scnd  ++"\n"    ++ showContent xs
                      TacAssignUnaryOp id op fst ty       -> showAddrContent id++" "   ++genAssignEq ty++" " ++ show op             ++" " ++showAddrContent fst  ++"\n"   ++ showContent xs
                      TacAssignNullOp id fst ty           -> showAddrContent id++" "   ++genAssignEq ty++" " ++ showAddrContent fst                              ++"\n"   ++ showContent xs
                      TacLabel (Label l)                  -> l  ++" "++showContent xs
                      ExitTac                             -> "" ++"\n\n"

genAssignEq:: Type -> String
genAssignEq ty = case ty of
  B_type Type_Integer  -> "=int"
  B_type Type_Boolean  -> "=bool"
  B_type Type_Char     -> "=char"
  B_type Type_String   -> "=string"
  B_type Type_Void     -> "=void" -- not reachable
  B_type Type_Real     -> "=real"


--------------------------------------------------------------------------------
--- Preprocessing of the input for multiple pointers compatibility "$$$$$$$" ---
--------------------------------------------------------------------------------

-- PreProcessing for pointer compatibility
pointersSyntaxPreprocessing :: String -> String -> String
pointersSyntaxPreprocessing [] output = output
pointersSyntaxPreprocessing (x:xs) output= if x=='$'
                                              then
                                                pointersSyntaxPreprocessing xs (output++[x]++" ")
                                              else
                                                pointersSyntaxPreprocessing xs (output++[x])


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
    , "  --test          Execute a list of tests located in tests folder."
    ]
  exitFailure

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    ["--test"]  -> runTests 1 2 testFilesPaths
    []         -> getContents >>= run 2 pS
    "-s":fs    -> mapM_ (runFile 0 pS) fs
    fs         -> mapM_ (runFile 2 pS) fs

