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
import LexProgettoPar   (Token, Posn (..))
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
      putStrLn "\n[Parsing]"
      putStrLn "\n   Parse            Failed :( ...\n"
      putStrV v "Tokens:"
      putStrV v $ show ts
      putStrLn err
    Right tree -> do
      putStrLn "\n[Parsing]"
      putStrLn "\n   Parse Successful! :) "
      let includeDebugInfo = False in -- flag for complete or pretty printing
        let start_env = startEnv in   -- (Data.Map.fromList []) in -- substitute with startEnv for including pre-defined functions
          let typecheckRes = TypeChecker.executeTypeChecking tree start_env in 
            let tacgeneration = TacGen.genTAC typecheckRes in
              ------------------------------------------------------------------------
              if (includeDebugInfo) then do -- include more informations for debugging
                  putStrLn "\n[Input Code]\n"
                  putStrLn s
                  Main.showTree v tree
                  putStrLn "\n[TCheckResult extended]\n"
                  putStrLn (show typecheckRes)
                  putStrLn "\n\n[Statements TypeChecker Result]\n   For each statements it shows the TCheckResult (env+infos)\n"
                  putStrLn (showTypeCheckResult typecheckRes True)
                  putStrLn "\n\n[Compiler Errors]\n"        
                  let compilerErrors = (showTypeCheckResult typecheckRes False) in
                    if compilerErrors == "" -- Set "TRUE" to ignore compiler errors and force TAC generation
                    then putStrLn (compilerErrors ++ "   No compiler errors. \n\n[TAC]\n\n" ++ (show tacgeneration) ++"\n\n[TAC in code]\n" ++ (showTac tacgeneration))
                    else putStrLn (compilerErrors ++ "\n\n[TAC]\n\n" ++ " Cannot generate TAC with compiler errors!\n")
                ------------------------------------------------------------------------
                else do -- pretty print with no debug infos
                  putStrLn ("\n[Input Code]\n\n" ++ s)
                  putStrLn ("\n[Linearized tree]\n\n" ++ printTree tree)
                  if (printTree tree == printTree (case (p (myLexer (printTree tree))) of -- CHECK IF LINEARIZED CODE IS LEGAL SYNTAX
                                                    Left e -> (Abs.StartCode (Pn 0 0 0) (Abs.EmptyStatement (Pn 0 0 0)))
                                                    Right newTree -> newTree))
                    then putStrLn "\n Serialization of abstract syntax tree produced legal concrete syntax!" 
                    else putStrLn "\n WARNING: Serialization of abstract syntax tree DID NOT produce legal concrete syntax!" 
                  putStrLn "\n[Compiler Errors]\n"        
                  let compilerErrors = (showTypeCheckResult typecheckRes False) in
                    if compilerErrors == "" -- Set "TRUE" to ignore compiler errors and force TAC generation
                    then putStrLn (compilerErrors ++ "   No compiler errors. \n\n[TAC]\n\n   Tac of pre-defined functions is not included.\n" ++ (showTac tacgeneration))
                    else putStrLn (compilerErrors ++ "\n\n[TAC]\n\n" ++ " Cannot generate TAC with compiler errors!\n")
  where
  ts = myLexer (pointersSyntaxPreprocessing s [])

-- Given a path of test files, execute all of them
runTests :: Prelude.Int -> Verbosity -> [String] -> IO()
runTests index v (x:xs) = do
                      putStrLn "\n\n---------------------------------------------------------------------------------------------"
                      putStrLn    ("------------ TEST n° " ++ show index ++ "-----------------------------------------------------------------------")
                      putStrLn     "---------------------------------------------------------------------------------------------"
                      x <- readFile x
                      run v pS x

                      runTests (index + 1) v xs -- next test
runTests index v [] =  do
                      putStrLn "\n\n >>>>>>> End of testing Phase <<<<<<<\n"
                      putStrLn " For adding new test cases:\n   - create a new file n.txt with input code inside tests folder\n   - n must be the next number from the list\n   - modify variable \"numberOfTest\" with the new n-value in file TestProgettoPar.hs\n   - Rebuild and execute\n\n"

numberOfTests = 11  -- must be set to the number of files in the tests folder. Tests files must be of consecutive ints: 1.txt 2.txt 3.txt etc.
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
--- TAC CODE PRINTING  -----------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------- 

showTac :: S TAC -> String
showTac (Abs.StartCode tac@(TAC code funcs) _) = "\n----------- Functions declarations ----------- \n" ++ showContent funcs ++ "\n\n-------------------- Code -------------------- \n" ++ showContent code 
                                                 
showContent :: [TACEntry] -> String
showContent (x:xs) = case x of
                      TacAssignBinaryOp id op fst scnd ty     -> "\n" ++ "\t  " ++ showAddrContent id ++ " "   ++ buildEqOperator ty ++ " " ++ showAddrContent fst ++ " " ++ show op           ++ " " ++ showAddrContent scnd ++ showContent xs
                      TacAssignRelOp id op fst scnd ty        -> "\n" ++ "\t  " ++ showAddrContent id ++ " "   ++ buildEqOperator ty ++ " " ++ showAddrContent fst ++ " " ++ show op           ++ " " ++ showAddrContent scnd ++ showContent xs
                      TacAssignUnaryOp id op fst ty           -> "\n" ++ "\t  " ++ showAddrContent id ++ " "   ++ buildEqOperator ty ++ " " ++ show op             ++ " " ++ showAddrContent fst  ++ showContent xs
                      TacAssignNullOp id fst ty               -> "\n" ++ "\t  " ++ showAddrContent id ++ " "   ++ buildEqOperator ty ++ " " ++ showAddrContent fst                                ++ showContent xs
                      TacLabel (Label l)                      -> "\n" ++ l ++ ":" ++ showContent xs
                      TacJump  (Label l)                      -> "\n" ++ "\t  goto " ++ l ++ showContent xs
                      TacProcCall id                          -> "\n" ++ "\t  " ++ "pcall " ++ showAddrContent id ++ showContent xs
                      TacFuncCallLeft id                      -> "\n" ++ "\t  " ++ "fcall " ++ showAddrContent id ++ showContent xs
                      TacFuncCall id retAddr ty               -> "\n" ++ "\t  " ++ showAddrContent retAddr ++ " " ++ buildEqOperator ty ++ " fcall " ++ showAddrContent id ++ showContent xs
                      TacParam addr ty                        -> "\n" ++ "\t  " ++ "param_" ++ show ty ++ " " ++ showAddrContent addr ++ showContent xs
                      TacReturnVoid                           -> "\n" ++ "\t  " ++ "return_void" ++ showContent xs
                      TacReturn addr ty                       -> "\n" ++ "\t  " ++ "return_" ++ show ty ++ " " ++ showAddrContent addr ++ showContent xs
                      TacCastConversion addr fst tfrom tto    -> "\n" ++ "\t  " ++ (showAddrContent addr ++) " " ++ (buildEqOperator tto) ++ " " ++ (buildCastOperator tfrom tto) ++ " " ++  (showAddrContent fst) ++ showContent xs
                      TacConditionalJump (Label lab) flag addr -> case flag of
                          True ->  "\n" ++ "\t  if "       ++ (showAddrContent addr) ++ " goto " ++ lab  ++ showContent xs
                          False -> "\n" ++ "\t  if_false " ++ (showAddrContent addr) ++ " goto " ++ lab  ++ showContent xs
                      TacRelConditionalJump (Label lab) flag relop laddr raddr -> case flag of
                          True ->  "\n" ++ "\t  if "       ++ (showAddrContent laddr) ++ " " ++ (show relop) ++ " " ++ (showAddrContent raddr) ++ " goto " ++ lab ++ showContent xs
                          False -> "\n" ++ "\t  if_false " ++ (showAddrContent laddr) ++ " " ++ (show relop) ++ " " ++ (showAddrContent raddr) ++ " goto " ++ lab ++ showContent xs
                      TacComment comment -> "\t  \t # "   ++ comment ++ showContent xs 
                      ExitTac -> "" ++"\n\n"
showContent [] = ""

-- Given a type, return the right equal (assign) operator string
buildEqOperator :: Type -> String
buildEqOperator ty = case ty of
  B_type Type_Integer  -> "=int"
  B_type Type_Boolean  -> "=bool"
  B_type Type_Char     -> "=char"
  B_type Type_String   -> "=str"
  B_type Type_Void     -> "=void" -- should not be reached!
  B_type Type_Real     -> "=real"

-- Given a from-type and a to-type generates the right convert (coertion/casting) operator string
buildCastOperator :: Type -> Type -> String
buildCastOperator tfrom tto = "convert-" ++ show tfrom ++ "-to-" ++ show tto

--------------------------------------------------------------------------------------------------
--- Preprocessing of the input for multiple pointers compatibility "$$$$$$$" ---------------------
--------------------------------------------------------------------------------------------------

-- PreProcessing for pointer compatibility
pointersSyntaxPreprocessing :: String -> String -> String
pointersSyntaxPreprocessing [] output = output
pointersSyntaxPreprocessing (x:xs) output= if x=='$'
                                              then
                                                pointersSyntaxPreprocessing xs (output++[x]++" ")
                                              else
                                                pointersSyntaxPreprocessing xs (output++[x])
--------------------------------------------------------------------------------------------------

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
    , "\nFor adding new tests:     \n   - create a new file n.txt with input code inside tests folder\n   - n must be the next number from the list\n   - modify variable \"numberOfTest\" with the new n-value in file TestProgettoPar.hs\n   - Rebuild and execute\n\n"
    ]
  exitFailure


-- Starting point of execution
main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"]  -> usage
    ["--test"]  -> runTests 1 2 testFilesPaths
    []          -> getContents >>= run 2 pS
    "-s":fs     -> mapM_ (runFile 0 pS) fs
    fs          -> mapM_ (runFile 2 pS) fs

