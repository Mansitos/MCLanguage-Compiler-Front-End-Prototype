-- Progetto LC Cagnoni Mansi

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

-- | Pretty-printer for PrintProgettoPar.
--   Generated by the BNF converter.

module PrintProgettoPar where

import Prelude
  ( ($), (.)
  , Bool(..), (==), (<)
  , Int, Integer, Double, (+), (-), (*)
  , String, (++)
  , ShowS, showChar, showString, show, Show
  , all, dropWhile, elem, foldr, id, map, null, replicate, shows, span
  )
import Data.Char ( Char, isSpace )
import qualified AbsProgettoPar
import LexProgettoPar (Posn(..))

-- | The top-level printing method.

printTree :: Print a => a -> String 
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 (map ($ "") $ d []) "" where
  rend i = \case
    "["      :ts -> showChar '[' . rend i ts
    "("      :ts -> showChar '(' . rend i ts
    "{"      :ts -> showChar '{' . new (i+1) . rend (i+1) ts
    "}" : ";":ts -> new (i-1) . space "}" . showChar ';' . new (i-1) . rend (i-1) ts
    "}"      :ts -> new (i-1) . showChar '}' . new (i-1) . rend (i-1) ts
    [";"]        -> showChar ';'
    ";"      :ts -> showChar ';' . new i . rend i ts
    t  : ts@(p:_) | closingOrPunctuation p -> showString t . rend i ts
    t        :ts -> space t . rend i ts
    _            -> id
  new i     = showChar '\n' . replicateS (2*i) (showChar ' ') . dropWhile isSpace
  space t s =
    case (all isSpace t', null spc, null rest) of
      (True , _   , True ) -> []              -- remove trailing space
      (False, _   , True ) -> t'              -- remove trailing space
      (False, True, False) -> t' ++ ' ' : s   -- add space if none
      _                    -> t' ++ s
    where
      t'          = showString t []
      (spc, rest) = span isSpace s

  closingOrPunctuation :: String -> Bool
  closingOrPunctuation [c] = c `elem` closerOrPunct
  closingOrPunctuation _   = False

  closerOrPunct :: String
  closerOrPunct = ")],;"

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- | The printer class does the job.

class Print a where
  prt :: Int -> a -> Doc
  prtList :: Int -> [a] -> Doc
  prtList i = concatD . map (prt i)

instance {-# OVERLAPPABLE #-} Print a => Print [a] where
  prt = prtList

instance Print Char where
  prt     _ s = doc (showChar '\'' . mkEsc '\'' s . showChar '\'')
  prtList _ s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q = \case
  s | s == q -> showChar '\\' . showChar s
  '\\' -> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  s -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j < i then parenth else id

instance Print Integer where
  prt _ x = doc (shows x)

instance Print Double where
  prt _ x = doc (shows x)

instance Print (AbsProgettoPar.Ident attr) where
  prt _ (AbsProgettoPar.Ident i _) = doc $ showString i

instance Print (AbsProgettoPar.Boolean attr) where
  prt i = \case
    AbsProgettoPar.Boolean_true _-> prPrec i 0 (concatD [doc (showString "true")])
    AbsProgettoPar.Boolean_false _-> prPrec i 0 (concatD [doc (showString "false")])
    AbsProgettoPar.Boolean_True _-> prPrec i 0 (concatD [doc (showString "True")])
    AbsProgettoPar.Boolean_False _-> prPrec i 0 (concatD [doc (showString "False")])

instance Print (AbsProgettoPar.S attr) where
  prt i = \case
    AbsProgettoPar.StartCode _ statements -> prPrec i 0 (concatD [prt 0 statements])

instance Print (AbsProgettoPar.STATEMENTS attr) where
  prt i = \case
    AbsProgettoPar.ListStatements _ statement statements -> prPrec i 0 (concatD [prt 0 statement, prt 0 statements])
    AbsProgettoPar.EmptyStatement _ -> prPrec i 0 (concatD [])

instance Print (AbsProgettoPar.B attr) where
  prt i = \case
    AbsProgettoPar.BlockStatement _ statements -> prPrec i 0 (concatD [doc (showString "{"), prt 0 statements, doc (showString "}")])

instance Print (AbsProgettoPar.STATEMENT attr) where
  prt i = \case
    AbsProgettoPar.Statement _ b -> prPrec i 0 (concatD [prt 0 b])
    AbsProgettoPar.ExpressionStatement _ expressionstatement -> prPrec i 0 (concatD [prt 0 expressionstatement, doc (showString ";")])
    AbsProgettoPar.AssignmentStatement _ lvalueexpression assignop expression -> prPrec i 0 (concatD [prt 0 lvalueexpression, prt 0 assignop, prt 0 expression, doc (showString ";")])
    AbsProgettoPar.ConditionalStatement _ conditionalstate -> prPrec i 0 (concatD [prt 0 conditionalstate])
    AbsProgettoPar.WhileDoStatement _ whilestatement -> prPrec i 0 (concatD [prt 0 whilestatement])
    AbsProgettoPar.DoWhileStatement _ dostatement -> prPrec i 0 (concatD [prt 0 dostatement])
    AbsProgettoPar.ForStatement _ forstatement -> prPrec i 0 (concatD [prt 0 forstatement])
    AbsProgettoPar.BreakStatement _ -> prPrec i 0 (concatD [doc (showString "break"), doc (showString ";")])
    AbsProgettoPar.ContinueStatement _ -> prPrec i 0 (concatD [doc (showString "continue"), doc (showString ";")])
    AbsProgettoPar.ReturnStatement _ returnstatement -> prPrec i 0 (concatD [prt 0 returnstatement, doc (showString ";")])
    AbsProgettoPar.VariableDeclarationStatement _ variabletype vardeclist -> prPrec i 0 (concatD [prt 0 variabletype, prt 0 vardeclist, doc (showString ";")])
    AbsProgettoPar.ProcedureStatement _ id_ parameters statements -> prPrec i 0 (concatD [doc (showString "proc"), prt 0 id_, doc (showString "("), prt 0 parameters, doc (showString ")"), doc (showString ":"), doc (showString "void"), doc (showString "{"), prt 0 statements, doc (showString "}")])
    AbsProgettoPar.FunctionStatement _ id_ parameters primitivetype statements -> prPrec i 0 (concatD [doc (showString "function"), prt 0 id_, doc (showString "("), prt 0 parameters, doc (showString ")"), doc (showString ":"), prt 0 primitivetype, doc (showString "{"), prt 0 statements, doc (showString "}")])

instance Print (AbsProgettoPar.PARAMETERS attr) where
  prt i = \case
    AbsProgettoPar.ParameterList _ parameter parameters -> prPrec i 0 (concatD [prt 0 parameter, doc (showString ","), prt 0 parameters])
    AbsProgettoPar.ParameterListSingle _ parameter -> prPrec i 0 (concatD [prt 0 parameter])
    AbsProgettoPar.ParameterListEmpty _ -> prPrec i 0 (concatD [])

instance Print (AbsProgettoPar.PARAMETER attr) where
  prt i = \case
    AbsProgettoPar.Parameter _ id_ primitivetype -> prPrec i 0 (concatD [prt 0 id_, doc (showString ":"), prt 0 primitivetype])
    AbsProgettoPar.ParameterPointer _ id_ primitivetype pointer -> prPrec i 0 (concatD [prt 0 id_, doc (showString ":"), prt 0 primitivetype, prt 0 pointer])

instance Print (AbsProgettoPar.ASSIGNOP attr) where
  prt i = \case
    AbsProgettoPar.AssignOperationEq _ -> prPrec i 0 (concatD [doc (showString "=")])
    AbsProgettoPar.AssignOperationEqPlus _ -> prPrec i 0 (concatD [doc (showString "+=")])
    AbsProgettoPar.AssignOperationEqMinus _ -> prPrec i 0 (concatD [doc (showString "-=")])
    AbsProgettoPar.AssignOperationEqProd _ -> prPrec i 0 (concatD [doc (showString "*=")])
    AbsProgettoPar.AssignOperationEqFract _ -> prPrec i 0 (concatD [doc (showString "/=")])
    AbsProgettoPar.AssignOperationEqPercent _ -> prPrec i 0 (concatD [doc (showString "%=")])
    AbsProgettoPar.AssignOperationEqPower _ -> prPrec i 0 (concatD [doc (showString "**=")])

instance Print (AbsProgettoPar.VARIABLETYPE attr) where
  prt i = \case
    AbsProgettoPar.VariableTypeParam _ -> prPrec i 0 (concatD [doc (showString "param")])
    AbsProgettoPar.VariableTypeConst _ -> prPrec i 0 (concatD [doc (showString "const")])
    AbsProgettoPar.VariableTypeVar _ -> prPrec i 0 (concatD [doc (showString "var")])
    AbsProgettoPar.VariableTypeRef _ -> prPrec i 0 (concatD [doc (showString "ref")])
    AbsProgettoPar.VariableTypeConstRef _ -> prPrec i 0 (concatD [doc (showString "const"), doc (showString "ref")])

instance Print (AbsProgettoPar.VARDECLIST attr) where
  prt i = \case
    AbsProgettoPar.VariableDeclarationSingle _ vardecid -> prPrec i 0 (concatD [prt 0 vardecid])

instance Print (AbsProgettoPar.VARDECID attr) where
  prt i = \case
    AbsProgettoPar.VariableDeclaration _ identlist typepart initpart -> prPrec i 0 (concatD [prt 0 identlist, prt 0 typepart, prt 0 initpart])

instance Print (AbsProgettoPar.IDENTLIST attr) where
  prt i = \case
    AbsProgettoPar.IdentifierList _ id_ identlist -> prPrec i 0 (concatD [prt 0 id_, doc (showString ","), prt 0 identlist])
    AbsProgettoPar.IdentifierSingle _ id_ -> prPrec i 0 (concatD [prt 0 id_])

instance Print (AbsProgettoPar.TYPEPART attr) where
  prt i = \case
    AbsProgettoPar.TypePart _ typeexpression -> prPrec i 0 (concatD [doc (showString ":"), prt 0 typeexpression])

instance Print (AbsProgettoPar.INITPART attr) where
  prt i = \case
    AbsProgettoPar.InitializzationPart _ expression -> prPrec i 0 (concatD [doc (showString "="), prt 0 expression])
    AbsProgettoPar.InitializzationPartArray _ arrayinit -> prPrec i 0 (concatD [doc (showString "="), prt 0 arrayinit])
    AbsProgettoPar.InitializzationPartEmpty _ -> prPrec i 0 (concatD [])

instance Print (AbsProgettoPar.ARRAYINIT attr) where
  prt i = \case
    AbsProgettoPar.ArrayInitSingle _ arrayinit -> prPrec i 0 (concatD [doc (showString "["), prt 0 arrayinit ,doc (showString "]")])
    AbsProgettoPar.ArrayInit _ arrayinit1 arrayinit2 -> prPrec i 0 (concatD [doc (showString "["), prt 0 arrayinit1 ,doc (showString ","), prt 0 arrayinit2 , doc (showString "]")])
    AbsProgettoPar.ArrayInitSingleElems _ listelementarray -> prPrec i 0 (concatD [doc (showString "["), prt 0 listelementarray ,doc (showString "]")])
    AbsProgettoPar.ArrayInitElems _ listelementarray arrayinit -> prPrec i 0 (concatD [doc (showString "["), prt 0 listelementarray ,doc (showString "],"),prt 0 arrayinit])

instance Print (AbsProgettoPar.LISTELEMENTARRAY attr) where
  prt i = \case
    AbsProgettoPar.ListElementsOfArray _ expression listelementarray -> prPrec i 0 (concatD [prt 0 expression, doc (showString ","), prt 0 listelementarray])
    AbsProgettoPar.ListElementOfArray _ expression -> prPrec i 0 (concatD [prt 0 expression])

instance Print (AbsProgettoPar.TYPEEXPRESSION attr) where
  prt i = \case
    AbsProgettoPar.TypeExpression _ primitivetype -> prPrec i 0 (concatD [prt 0 primitivetype])
    AbsProgettoPar.TypeExpressionArraySimple _ rangeexp typeexpression -> prPrec i 0 (concatD [doc (showString "["), prt 0 rangeexp, doc (showString "]"), prt 0 typeexpression])
    AbsProgettoPar.TypeExpressionArray _ rangeexp typeexpression -> prPrec i 0 (concatD [doc (showString "["), doc (showString "{"), prt 0 rangeexp, doc (showString "}"), doc (showString "]"), prt 0 typeexpression])
    AbsProgettoPar.TypeExpressionPointer _ primitivetype pointer -> prPrec i 0 (concatD [prt 0 primitivetype, prt 0 pointer])
    AbsProgettoPar.TypeExpressionPointerOfArray _ typeexpression pointer -> prPrec i 0 (concatD [doc (showString "("), prt 0 typeexpression,  doc (showString ")"), prt 0 pointer])

instance Print (AbsProgettoPar.POINTER attr) where
  prt i = \case
    AbsProgettoPar.PointerSymbol _ pointer -> prPrec i 0 (concatD [prt 0 pointer, doc (showString "*")])
    AbsProgettoPar.PointerSymbolSingle _ -> prPrec i 0 (concatD [doc (showString "*")])

instance Print (AbsProgettoPar.RANGEEXP attr) where
  prt i = \case
    AbsProgettoPar.RangeExpression _ expression1 expression2 rangeexp -> prPrec i 0 (concatD [prt 0 expression1, doc (showString ".."), prt 0 expression2, doc (showString ","), prt 0 rangeexp])
    AbsProgettoPar.RangeExpressionSingle _ expression1 expression2 -> prPrec i 0 (concatD [prt 0 expression1, doc (showString ".."), prt 0 expression2])

instance Print (AbsProgettoPar.PRIMITIVETYPE attr) where
  prt i = \case
    AbsProgettoPar.PrimitiveTypeVoid _ -> prPrec i 0 (concatD [doc (showString "void")])
    AbsProgettoPar.PrimitiveTypeBool _ -> prPrec i 0 (concatD [doc (showString "bool")])
    AbsProgettoPar.PrimitiveTypeInt _ -> prPrec i 0 (concatD [doc (showString "int")])
    AbsProgettoPar.PrimitiveTypeReal _ -> prPrec i 0 (concatD [doc (showString "real")])
    AbsProgettoPar.PrimitiveTypeString _ -> prPrec i 0 (concatD [doc (showString "string")])
    AbsProgettoPar.PrimitiveTypeChar _ -> prPrec i 0 (concatD [doc (showString "char")])
    AbsProgettoPar.TypeArray _ primitivetype -> prPrec i 0 (concatD [doc (showString "["), doc (showString "]"), prt 0 primitivetype])

instance Print (AbsProgettoPar.CONDITIONALSTATE attr) where
  prt i = \case
    AbsProgettoPar.ConditionalStatementSimpleThen _ expression statement elsestatement -> prPrec i 0 (concatD [doc (showString "if"), prt 0 expression, doc (showString "then"), prt 0 statement, prt 0 elsestatement])
    AbsProgettoPar.ConditionalStatementSimpleWThen _ expression b elsestatement -> prPrec i 0 (concatD [doc (showString "if"), prt 0 expression, prt 0 b, prt 0 elsestatement])
    AbsProgettoPar.ConditionalStatementCtrlThen _ ctrldecstatement statement elsestatement -> prPrec i 0 (concatD [doc (showString "if"), prt 0 ctrldecstatement, doc (showString "then"), prt 0 statement, prt 0 elsestatement])
    AbsProgettoPar.ConditionalStatementCtrlWThen _ ctrldecstatement b elsestatement -> prPrec i 0 (concatD [doc (showString "if"), prt 0 ctrldecstatement, prt 0 b, prt 0 elsestatement])

instance Print (AbsProgettoPar.WHILESTATEMENT attr) where
  prt i = \case
    AbsProgettoPar.WhileStateSimpleDo _ expression statement -> prPrec i 0 (concatD [doc (showString "while"), prt 0 expression, doc (showString "do"), prt 0 statement])
    AbsProgettoPar.WhileStateSimpleWDo _ expression b -> prPrec i 0 (concatD [doc (showString "while"), prt 0 expression, prt 0 b])
    AbsProgettoPar.WhileStateCtrlDo _ ctrldecstatement statement -> prPrec i 0 (concatD [doc (showString "while"), prt 0 ctrldecstatement, doc (showString "do"), prt 0 statement])
    AbsProgettoPar.WhileStateCtrlWDo _ ctrldecstatement b -> prPrec i 0 (concatD [doc (showString "while"), prt 0 ctrldecstatement, prt 0 b])

instance Print (AbsProgettoPar.DOSTATEMENT attr) where
  prt i = \case
    AbsProgettoPar.DoWhileState _ statement expression -> prPrec i 0 (concatD [doc (showString "do"), prt 0 statement, doc (showString "while"), prt 0 expression, doc (showString ";")])

instance Print (AbsProgettoPar.FORSTATEMENT attr) where
  prt i = \case
    AbsProgettoPar.ForStateIndexDo _ indexvardec rangexp statement -> prPrec i 0 (concatD [doc (showString "for"), prt 0 indexvardec, doc (showString "in"), prt 0 rangexp, doc (showString "do"), prt 0 statement])
    AbsProgettoPar.ForStateIndexWDo _ indexvardec rangexp b -> prPrec i 0 (concatD [doc (showString "for"), prt 0 indexvardec, doc (showString "in"), prt 0 rangexp, prt 0 b])
    AbsProgettoPar.ForStateExprDo _ rangexp statement -> prPrec i 0 (concatD [doc (showString "for"), prt 0 rangexp, doc (showString "do"), prt 0 statement])
    AbsProgettoPar.ForStateExprWDo _ rangexp b -> prPrec i 0 (concatD [doc (showString "for"), prt 0 rangexp, prt 0 b])

instance Print (AbsProgettoPar.INDEXVARDEC attr) where
  prt i = \case
    AbsProgettoPar.IndexVarDeclaration _ id_ -> prPrec i 0 (concatD [prt 0 id_])

instance Print (AbsProgettoPar.ELSESTATEMENT attr) where
  prt i = \case
    AbsProgettoPar.ElseStateEmpty _ -> prPrec i 0 (concatD [])
    AbsProgettoPar.ElseState _ statement -> prPrec i 0 (concatD [doc (showString "else"), prt 0 statement])

instance Print (AbsProgettoPar.RETURNSTATEMENT attr) where
  prt i = \case
    AbsProgettoPar.ReturnState _ expression -> prPrec i 0 (concatD [doc (showString "return"), prt 0 expression])
    AbsProgettoPar.ReturnStateEmpty _ -> prPrec i 0 (concatD [doc (showString "return")])

instance Print (AbsProgettoPar.CTRLDECSTATEMENT attr) where
  prt i = \case
    AbsProgettoPar.CtrlDecStateVar _ id_ typerpart expression -> prPrec i 0 (concatD [doc (showString "var"),prt 0 id_, prt 0 typerpart, doc (showString "="), prt 0 expression])
    AbsProgettoPar.CtrlDecStateConst _ id_ typerpart expression -> prPrec i 0 (concatD [doc (showString "const"), prt 0 id_, prt 0 typerpart, doc (showString "="), prt 0 expression])

instance Print (AbsProgettoPar.EXPRESSIONSTATEMENT attr) where
  prt i = \case
    AbsProgettoPar.VariableExpression _ id_ -> prPrec i 0 (concatD [prt 0 id_])
    AbsProgettoPar.CallExpression _ callexpression -> prPrec i 0 (concatD [prt 0 callexpression])

instance Print (AbsProgettoPar.CALLEXPRESSION attr) where
  prt i = \case
    AbsProgettoPar.CallExpressionParentheses _ id_ namedexpressionlist -> prPrec i 0 (concatD [prt 0 id_, doc (showString "("), prt 0 namedexpressionlist, doc (showString ")")])

instance Print (AbsProgettoPar.NAMEDEXPRESSIONLIST attr) where
  prt i = \case
    AbsProgettoPar.NamedExpressionList _ namedexpression -> prPrec i 0 (concatD [prt 0 namedexpression])
    AbsProgettoPar.NamedExpressionListEmpty _-> prPrec i 0 (concatD [])
    AbsProgettoPar.NamedExpressionLists _ namedexpression namedexpressionlist -> prPrec i 0 (concatD [prt 0 namedexpression, doc (showString ","), prt 0 namedexpressionlist])

instance Print (AbsProgettoPar.NAMEDEXPRESSION attr) where
  prt i = \case
    AbsProgettoPar.NamedExpression _ expression -> prPrec i 0 (concatD [prt 0 expression])

instance Print (AbsProgettoPar.EXPRESSIONS attr) where
  prt i = \case
    AbsProgettoPar.Expressions _ expression expressions -> prPrec i 0 (concatD [prt 0 expression,doc (showString ","), prt 0 expressions])
    AbsProgettoPar.Expression _ expression -> prPrec i 0 (concatD [prt 0 expression])
    AbsProgettoPar.ExpressionEmpty _ -> prPrec i 0 (concatD [])

instance Print (AbsProgettoPar.EXPRESSION attr) where
  prt i = \case
    AbsProgettoPar.ExpressionIdent _ id_ arrayindexelement -> prPrec i 0 (concatD [prt 0 id_, prt 0 arrayindexelement])
    AbsProgettoPar.ExpressionInteger _ n -> prPrec i 0 (concatD [prt 0 (AbsProgettoPar.valueInt n)])
    AbsProgettoPar.ExpressionReal _ d -> prPrec i 0 (concatD [prt 0 (AbsProgettoPar.valueReal  d)])
    AbsProgettoPar.ExpressionString _ str -> prPrec i 0 (concatD [prt 0 (AbsProgettoPar.valueString  str)])
    AbsProgettoPar.ExpressionChar _ c -> prPrec i 0 (concatD [prt 0 (AbsProgettoPar.valueChar  c)])
    AbsProgettoPar.ExpressionBoolean _ boolean -> prPrec i 0 (concatD [prt 0 boolean])
    AbsProgettoPar.ExpressionBinary _ default_ binaryop expression -> prPrec i 0 (concatD [prt 0 default_, prt 0 binaryop, prt 0 expression])
    AbsProgettoPar.ExpressionUnary _ unaryop default_ -> prPrec i 0 (concatD [prt 0 unaryop, prt 0 default_])
    AbsProgettoPar.ExpressionCast _ default_ primitivetype -> prPrec i 0 (concatD [prt 0 default_, doc (showString ":"), prt 0 primitivetype])
    AbsProgettoPar.ExpressionBracket _ expression -> prPrec i 0 (concatD [doc (showString "("), prt 0 expression, doc (showString ")")])
    AbsProgettoPar.ExpressionCall _ id_ expressions -> prPrec i 0 (concatD [prt 0 id_,doc (showString "("), prt 0 expressions,doc (showString ")")])

instance Print (AbsProgettoPar.DEFAULT attr) where
  prt i = \case
    AbsProgettoPar.ExpressionIdentD _ id_ arrayindexelement -> prPrec i 0 (concatD [prt 0 id_, prt 0 arrayindexelement])
    AbsProgettoPar.ExpressionIntegerD _ n -> prPrec i 0 (concatD [prt 0 (AbsProgettoPar.valueInt n)])
    AbsProgettoPar.ExpressionRealD _ d -> prPrec i 0 (concatD [prt 0 (AbsProgettoPar.valueReal  d)])
    AbsProgettoPar.ExpressionStringD _ str -> prPrec i 0 (concatD [prt 0 (AbsProgettoPar.valueString  str)])
    AbsProgettoPar.ExpressionCharD _ c -> prPrec i 0 (concatD [prt 0 (AbsProgettoPar.valueChar  c)])
    AbsProgettoPar.ExpressionBooleanD _ boolean -> prPrec i 0 (concatD [prt 0 boolean])
    AbsProgettoPar.ExpressionBracketD _ expression -> prPrec i 0 (concatD [doc (showString "("), prt 0 expression, doc (showString ")")])
    AbsProgettoPar.ExpressionCastD _ default_ primitivetype -> prPrec i 0 (concatD [prt 0 default_, doc (showString ":"), prt 0 primitivetype])
    AbsProgettoPar.ExpressionCallD _ id_ expressions -> prPrec i 0 (concatD [prt 0 id_,doc (showString "("), prt 0 expressions,doc (showString ")")])
    AbsProgettoPar.ExpressionUnaryD _ unaryop default_ -> prPrec i 0 (concatD [prt 0 unaryop, prt 0 default_])

instance Print (AbsProgettoPar.UNARYOP attr) where
  prt i = \case
    AbsProgettoPar.UnaryOperationPositive _ -> prPrec i 0 (concatD [doc (showString "+")])
    AbsProgettoPar.UnaryOperationNegative _ -> prPrec i 0 (concatD [doc (showString "-")])
    AbsProgettoPar.UnaryOperationNot _ -> prPrec i 0 (concatD [doc (showString "!")])
    AbsProgettoPar.UnaryOperationPointer _ -> prPrec i 0 (concatD [doc (showString "*")])

instance Print (AbsProgettoPar.BINARYOP attr) where
  prt i = \case
    AbsProgettoPar.BinaryOperationPlus _ -> prPrec i 0 (concatD [doc (showString "+")])
    AbsProgettoPar.BinaryOperationMinus _ -> prPrec i 0 (concatD [doc (showString "-")])
    AbsProgettoPar.BinaryOperationProduct _ -> prPrec i 0 (concatD [doc (showString "*")])
    AbsProgettoPar.BinaryOperationDivision _ -> prPrec i 0 (concatD [doc (showString "/")])
    AbsProgettoPar.BinaryOperationModule _ -> prPrec i 0 (concatD [doc (showString "%")])
    AbsProgettoPar.BinaryOperationPower _ -> prPrec i 0 (concatD [doc (showString "**")])
    AbsProgettoPar.BinaryOperationAnd _ -> prPrec i 0 (concatD [doc (showString "&&")])
    AbsProgettoPar.BinaryOperationOr _ -> prPrec i 0 (concatD [doc (showString "||")])
    AbsProgettoPar.BinaryOperationEq _ -> prPrec i 0 (concatD [doc (showString "==")])
    AbsProgettoPar.BinaryOperationNotEq _ -> prPrec i 0 (concatD [doc (showString "!=")])
    AbsProgettoPar.BinaryOperationGratherEq _ -> prPrec i 0 (concatD [doc (showString ">=")])
    AbsProgettoPar.BinaryOperationGrather _ -> prPrec i 0 (concatD [doc (showString ">")])
    AbsProgettoPar.BinaryOperationLessEq _ -> prPrec i 0 (concatD [doc (showString "<=")])
    AbsProgettoPar.BinaryOperationLess _ -> prPrec i 0 (concatD [doc (showString "<")])

instance Print (AbsProgettoPar.LVALUEEXPRESSION attr) where
  prt i = \case
    AbsProgettoPar.LvalueExpressions _ id_ arrayindexelement lvalueexpression -> prPrec i 0 (concatD [prt 0 id_, prt 0 arrayindexelement, doc (showString ","), prt 0 lvalueexpression])
    AbsProgettoPar.LvalueExpression _ id_ arrayindexelement -> prPrec i 0 (concatD [prt 0 id_, prt 0 arrayindexelement])

instance Print (AbsProgettoPar.ARRAYINDEXELEMENT attr) where
  prt i = \case
    AbsProgettoPar.ArrayIndexElement _ typeindex -> prPrec i 0 (concatD [doc (showString "["), prt 0 typeindex, doc (showString "]")])
    AbsProgettoPar.ArrayIndexElementEmpty _ -> prPrec i 0 (concatD [])

instance Print (AbsProgettoPar.TYPEINDEX attr) where
  prt i = \case
    AbsProgettoPar.TypeOfIndexInt _ typeindex n -> prPrec i 0 (concatD [prt 0 typeindex, doc (showString ","), prt 0 (AbsProgettoPar.valueInt n)])
    AbsProgettoPar.TypeOfIndexIntSingle _ n -> prPrec i 0 (concatD [prt 0 (AbsProgettoPar.valueInt n)])
    AbsProgettoPar.TypeOfIndexVar _ typeindex id_ index -> prPrec i 0 (concatD [prt 0 typeindex, doc (showString ","), prt 0 id_, prt 0 index])
    AbsProgettoPar.TypeOfIndexVarSingle _ id_ index-> prPrec i 0 (concatD [prt 0 id_, prt 0 index])
    AbsProgettoPar.TypeOfIndexPointer _ typeindex unaryop def_-> prPrec i 0 (concatD [prt 0 typeindex, doc (showString ","), prt 0 unaryop, prt 0 def_])
    AbsProgettoPar.TypeOfIndexPointerSingle _ unaryop def_-> prPrec i 0 (concatD [prt 0 unaryop, prt 0 def_])
    AbsProgettoPar.TypeOfIndexBinary _ typeindex def_ binaryop exp -> prPrec i 0 (concatD [prt 0 typeindex, doc (showString ","), prt 0 def_, prt 0 binaryop, prt 0 exp])
    AbsProgettoPar.TypeOfIndexBinarySingle _ def_ binaryop exp -> prPrec i 0 (concatD [prt 0 def_, prt 0 binaryop, prt 0 exp])
    AbsProgettoPar.TypeOfIndexExpressionCall _ typeindex id_ exps -> prPrec i 0 (concatD [prt 0 typeindex, doc (showString ","), prt 0 id_, prt 0 exps])
    AbsProgettoPar.TypeOfIndexExpressionCallSingle _ id_ exps -> prPrec i 0 (concatD [prt 0 id_, prt 0 exps])
    AbsProgettoPar.TypeOfIndexExpressionBracket _ typeindex exp -> prPrec i 0 (concatD [prt 0 typeindex, doc (showString ","), prt 0 exp])
    AbsProgettoPar.TypeOfIndexExpressionBracketSingle _  exp -> prPrec i 0 (concatD [prt 0 exp])