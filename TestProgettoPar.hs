-- Program to test parser, automatically generated by BNF Converter.

module Main where

import Prelude
  ( ($)
  , Either(..)
  , Int, (>)
  , String, (++), unlines
  , Show, show
  , IO, (>>), (>>=), (==), (||), mapM_, putStrLn
  , FilePath
  , getContents, readFile
  )
import System.Environment ( getArgs )
import System.Exit        ( exitFailure, exitSuccess )
import Control.Monad      ( when )

import AbsProgettoPar   ()
import LexProgettoPar   ( Token )
import ParProgettoPar   ( pS, myLexer )
import PrintProgettoPar ( Print, printTree )
import SkelProgettoPar  ()

type Err        = Either String
type ParseFun a = [Token] -> Err a
type Verbosity  = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

runFile :: (Print a, Show a) => Verbosity -> ParseFun a -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run v p

run :: (Print a, Show a) => Verbosity -> ParseFun a -> String -> IO ()
run v p s =
  case p ts of
    Left err -> do
      putStrLn "\nParse              Failed...\n"
      putStrV v "Tokens:"
      putStrV v $ show ts
      putStrLn err
      exitFailure
    Right tree -> do
      putStrLn "\nParse Successful!"
      showTree v tree
      exitSuccess
  where
  ts = myLexer (pointersSyntaxPreprocessing s [] [])

-- Preprocessing of the input for multiple pointers compatibility "*******"
pointersSyntaxPreprocessing :: String -> String -> String -> String
pointersSyntaxPreprocessing [] [] output = output
pointersSyntaxPreprocessing [] zs output = output
pointersSyntaxPreprocessing (x:xs) zs output= if x==' ' || x=='*' || x==':'
                          then
                            if x==' '
                              then
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
                            pointersSyntaxPreprocessing xs (zs++[x]) (output++[x])

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

