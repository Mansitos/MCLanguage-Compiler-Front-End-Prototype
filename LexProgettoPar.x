-- -*- haskell -*-
-- This Alex file was machine-generated by the BNF converter
{
{-# OPTIONS -fno-warn-incomplete-patterns #-}
{-# OPTIONS_GHC -w #-}
module LexProgettoPar where

import Prelude

import qualified Data.Bits
import Data.Word (Word8)
import Data.Char (ord)
}


$c = [A-Z\192-\221] # [\215]  -- capital isolatin1 letter (215 = \times) FIXME
$s = [a-z\222-\255] # [\247]  -- small   isolatin1 letter (247 = \div  ) FIXME
$l = [$c $s]         -- letter
$d = [0-9]           -- digit
$i = [$l $d _ ']     -- identifier character
$u = [. \n]          -- universal: any character

@rsyms =    -- symbols and non-identifier-like reserved words
   \{ | \} | \; | \( | \) | \: | \, | \= | \+ \= | \- \= | \* \= | \/ \= | \% \= | \* \* \= | \[ | \] | \* | \. \. | \+ | \- | \! | \& | \/ | \% | \* \* | \& \& | \| \| | \= \= | \! \= | \> \= | \> | \< \= | \< | \$

:-

-- Line comments
"//" [.]* ;
"/*" [$u]* "*/" ;

$white+ ;

@rsyms
    { tok (\p s -> PT p (eitherResIdent TV s)) }

$l $i*
    { tok (\p s -> PT p (eitherResIdent TV s)) }
\" ([$u # [\" \\ \n]] | (\\ (\" | \\ | \' | n | t | r | f)))* \"
    { tok (\p s -> PT p (TL $ unescapeInitTail s)) }
\' ($u # [\' \\] | \\ [\\ \' n t r f]) \'
    { tok (\p s -> PT p (TC s))  }
$d+
    { tok (\p s -> PT p (TI s))    }
$d+ \. $d+ (e (\-)? $d+)?
    { tok (\p s -> PT p (TD s)) }

{

tok :: (Posn -> String -> Token) -> (Posn -> String -> Token)
tok f p s = f p s

data Tok =
   TS !String !Int    -- reserved words and symbols
 | TL !String         -- string literals
 | TI !String         -- integer literals
 | TV !String         -- identifiers
 | TD !String         -- double precision float literals
 | TC !String         -- character literals

 deriving (Eq,Show,Ord)

data Token =
   PT  Posn Tok
 | Err Posn
  deriving (Eq,Show,Ord)

printPosn :: Posn -> String
printPosn (Pn _ l c) = "line " ++ show l ++ ", column " ++ show c

tokenPos :: [Token] -> String
tokenPos (t:_) = printPosn (tokenPosn t)
tokenPos [] = "end of file"

tokenPosn :: Token -> Posn
tokenPosn (PT p _) = p
tokenPosn (Err p) = p

tokenLineCol :: Token -> (Int, Int)
tokenLineCol = posLineCol . tokenPosn

posLineCol :: Posn -> (Int, Int)
posLineCol (Pn _ l c) = (l,c)

mkPosToken :: Token -> ((Int, Int), String)
mkPosToken t@(PT p _) = (posLineCol p, tokenText t)

tokenText :: Token -> String
tokenText t = case t of
  PT _ (TS s _) -> s
  PT _ (TL s)   -> show s
  PT _ (TI s)   -> s
  PT _ (TV s)   -> s
  PT _ (TD s)   -> s
  PT _ (TC s)   -> s
  Err _         -> "#error"

prToken :: Token -> String
prToken t = tokenText t

data BTree = N | B String Tok BTree BTree deriving (Show)

eitherResIdent :: (String -> Tok) -> String -> Tok
eitherResIdent tv s = treeFind resWords
  where
  treeFind N = tv s
  treeFind (B a t left right) | s < a  = treeFind left
                              | s > a  = treeFind right
                              | s == a = t

resWords :: BTree
resWords = b "[" 31 (b "-" 16 (b ")" 8 (b "%" 4 (b "!=" 2 (b "!" 1 N N) (b "$" 3 N N)) (b "&&" 6 (b "%=" 5 N N) (b "(" 7 N N))) (b "*=" 12 (b "**" 10 (b "*" 9 N N) (b "**=" 11 N N)) (b "+=" 14 (b "+" 13 N N) (b "," 15 N N)))) (b "<=" 24 (b "/=" 20 (b ".." 18 (b "-=" 17 N N) (b "/" 19 N N)) (b ";" 22 (b ":" 21 N N) (b "<" 23 N N))) (b ">=" 28 (b "==" 26 (b "=" 25 N N) (b ">" 27 N N)) (b "True" 30 (b "False" 29 N N) N)))) (b "int" 46 (b "do" 39 (b "char" 35 (b "bool" 33 (b "]" 32 N N) (b "break" 34 N N)) (b "const" 37 (b "checked" 36 N N) (b "continue" 38 N N))) (b "function" 43 (b "false" 41 (b "else" 40 N N) (b "for" 42 N N)) (b "in" 45 (b "if" 44 N N) N))) (b "valres" 54 (b "return" 50 (b "proc" 48 (b "param" 47 N N) (b "real" 49 N N)) (b "then" 52 (b "string" 51 N N) (b "true" 53 N N))) (b "{" 58 (b "void" 56 (b "var" 55 N N) (b "while" 57 N N)) (b "}" 60 (b "||" 59 N N) N))))
   where b s n = let bs = s
                 in  B bs (TS bs n)

unescapeInitTail :: String -> String
unescapeInitTail = id . unesc . tail . id
  where
  unesc s = case s of
    '\\':c:cs | elem c ['\"', '\\', '\''] -> c : unesc cs
    '\\':'n':cs  -> '\n' : unesc cs
    '\\':'t':cs  -> '\t' : unesc cs
    '\\':'r':cs  -> '\r' : unesc cs
    '\\':'f':cs  -> '\f' : unesc cs
    '"':[]    -> []
    c:cs      -> c : unesc cs
    _         -> []

-------------------------------------------------------------------
-- Alex wrapper code.
-- A modified "posn" wrapper.
-------------------------------------------------------------------

data Posn = Pn !Int !Int !Int
      deriving (Eq,Ord)
 
instance Show Posn where
  show pos = case pos of
              Pn abs row col -> "Row: " ++ show row ++ " | Col: " ++ show col

alexStartPos :: Posn
alexStartPos = Pn 0 1 1

alexMove :: Posn -> Char -> Posn
alexMove (Pn a l c) '\t' = Pn (a+1)  l     (((c+7) `div` 8)*8+1)
alexMove (Pn a l c) '\n' = Pn (a+1) (l+1)   1
alexMove (Pn a l c) _    = Pn (a+1)  l     (c+1)

type Byte = Word8

type AlexInput = (Posn,     -- current position,
                  Char,     -- previous char
                  [Byte],   -- pending bytes on the current char
                  String)   -- current input string

tokens :: String -> [Token]
tokens str = go (alexStartPos, '\n', [], str)
    where
      go :: AlexInput -> [Token]
      go inp@(pos, _, _, str) =
               case alexScan inp 0 of
                AlexEOF                   -> []
                AlexError (pos, _, _, _)  -> [Err pos]
                AlexSkip  inp' len        -> go inp'
                AlexToken inp' len act    -> act pos (take len str) : (go inp')

alexGetByte :: AlexInput -> Maybe (Byte,AlexInput)
alexGetByte (p, c, (b:bs), s) = Just (b, (p, c, bs, s))
alexGetByte (p, _, [], s) =
  case s of
    []  -> Nothing
    (c:s) ->
             let p'     = alexMove p c
                 (b:bs) = utf8Encode c
              in p' `seq` Just (b, (p', c, bs, s))

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar (p, c, bs, s) = c

-- | Encode a Haskell String to a list of Word8 values, in UTF8 format.
utf8Encode :: Char -> [Word8]
utf8Encode = map fromIntegral . go . ord
 where
  go oc
   | oc <= 0x7f       = [oc]

   | oc <= 0x7ff      = [ 0xc0 + (oc `Data.Bits.shiftR` 6)
                        , 0x80 + oc Data.Bits..&. 0x3f
                        ]

   | oc <= 0xffff     = [ 0xe0 + (oc `Data.Bits.shiftR` 12)
                        , 0x80 + ((oc `Data.Bits.shiftR` 6) Data.Bits..&. 0x3f)
                        , 0x80 + oc Data.Bits..&. 0x3f
                        ]
   | otherwise        = [ 0xf0 + (oc `Data.Bits.shiftR` 18)
                        , 0x80 + ((oc `Data.Bits.shiftR` 12) Data.Bits..&. 0x3f)
                        , 0x80 + ((oc `Data.Bits.shiftR` 6) Data.Bits..&. 0x3f)
                        , 0x80 + oc Data.Bits..&. 0x3f
                        ]
}
