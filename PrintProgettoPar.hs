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
  , ShowS, showChar, showString
  , all, dropWhile, elem, foldr, id, map, null, replicate, shows, span
  )
import Data.Char ( Char, isSpace )
import qualified AbsProgettoPar

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
    AbsProgettoPar.StartCode statements -> prPrec i 0 (concatD [prt 0 statements])

instance Print (AbsProgettoPar.STATEMENTS attr) where
  prt i = \case
    AbsProgettoPar.ListStatements statement statements -> prPrec i 0 (concatD [prt 0 statement, prt 0 statements])
    AbsProgettoPar.EmptyStatement -> prPrec i 0 (concatD [])

instance Print (AbsProgettoPar.B attr) where
  prt i = \case
    AbsProgettoPar.BlockStatement statements -> prPrec i 0 (concatD [doc (showString "{"), prt 0 statements, doc (showString "}")])

instance Print (AbsProgettoPar.STATEMENT attr) where
  prt i = \case
    AbsProgettoPar.Statement b -> prPrec i 0 (concatD [prt 0 b])
    AbsProgettoPar.ExpressionStatement expressionstatement -> prPrec i 0 (concatD [prt 0 expressionstatement, doc (showString ";")])
    AbsProgettoPar.AssignmentStatement lvalueexpression assignop expression -> prPrec i 0 (concatD [prt 0 lvalueexpression, prt 0 assignop, prt 0 expression, doc (showString ";")])
    AbsProgettoPar.ConditionalStatement conditionalstate -> prPrec i 0 (concatD [prt 0 conditionalstate])
    AbsProgettoPar.WhileDoStatement whilestatement -> prPrec i 0 (concatD [prt 0 whilestatement])
    AbsProgettoPar.DoWhileStatement dostatement -> prPrec i 0 (concatD [prt 0 dostatement])
    AbsProgettoPar.ForStatement forstatement -> prPrec i 0 (concatD [prt 0 forstatement])
    AbsProgettoPar.BreakStatement -> prPrec i 0 (concatD [doc (showString "break"), doc (showString ";")])
    AbsProgettoPar.ContinueStatement -> prPrec i 0 (concatD [doc (showString "continue"), doc (showString ";")])
    AbsProgettoPar.ReturnStatement returnstatement -> prPrec i 0 (concatD [prt 0 returnstatement, doc (showString ";")])
    AbsProgettoPar.VariableDeclarationStatement variabletype vardeclist -> prPrec i 0 (concatD [prt 0 variabletype, prt 0 vardeclist, doc (showString ";")])
    AbsProgettoPar.ForAllStatement forallstatement -> prPrec i 0 (concatD [prt 0 forallstatement])
    AbsProgettoPar.ProcedureStatement id_ parameters statements -> prPrec i 0 (concatD [doc (showString "proc"), prt 0 id_, doc (showString "("), prt 0 parameters, doc (showString ")"), doc (showString ":"), doc (showString "void"), doc (showString "{"), prt 0 statements, doc (showString "}")])
    AbsProgettoPar.FunctionStatement id_ parameters primitivetype statements -> prPrec i 0 (concatD [doc (showString "function"), prt 0 id_, doc (showString "("), prt 0 parameters, doc (showString ")"), doc (showString ":"), prt 0 primitivetype, doc (showString "{"), prt 0 statements, doc (showString "}")])

instance Print (AbsProgettoPar.PARAMETERS attr) where
  prt i = \case
    AbsProgettoPar.ParameterList parameter parameters -> prPrec i 0 (concatD [prt 0 parameter, doc (showString ","), prt 0 parameters])
    AbsProgettoPar.ParameterListEmpty -> prPrec i 0 (concatD [])

instance Print (AbsProgettoPar.PARAMETER attr) where
  prt i = \case
    AbsProgettoPar.Parameter id_ primitivetype -> prPrec i 0 (concatD [prt 0 id_, doc (showString ":"), prt 0 primitivetype])

instance Print (AbsProgettoPar.ASSIGNOP attr) where
  prt i = \case
    AbsProgettoPar.AssignOperationEq -> prPrec i 0 (concatD [doc (showString "=")])
    AbsProgettoPar.AssignOperationEqPlus -> prPrec i 0 (concatD [doc (showString "+=")])
    AbsProgettoPar.AssignOperationEqMinus -> prPrec i 0 (concatD [doc (showString "-=")])
    AbsProgettoPar.AssignOperationEqProd -> prPrec i 0 (concatD [doc (showString "*=")])
    AbsProgettoPar.AssignOperationEqFract -> prPrec i 0 (concatD [doc (showString "/=")])
    AbsProgettoPar.AssignOperationEqPercent -> prPrec i 0 (concatD [doc (showString "%=")])
    AbsProgettoPar.AssignOperationEqPower -> prPrec i 0 (concatD [doc (showString "**=")])

instance Print (AbsProgettoPar.VARIABLETYPE attr) where
  prt i = \case
    AbsProgettoPar.VariableTypeParam -> prPrec i 0 (concatD [doc (showString "param")])
    AbsProgettoPar.VariableTypeConst -> prPrec i 0 (concatD [doc (showString "const")])
    AbsProgettoPar.VariableTypeVar -> prPrec i 0 (concatD [doc (showString "var")])
    AbsProgettoPar.VariableTypeRef -> prPrec i 0 (concatD [doc (showString "ref")])
    AbsProgettoPar.VariableTypeConstRef -> prPrec i 0 (concatD [doc (showString "const"), doc (showString "ref")])

instance Print (AbsProgettoPar.VARDECLIST attr) where
  prt i = \case
    AbsProgettoPar.VariableDeclarationSingle vardecid -> prPrec i 0 (concatD [prt 0 vardecid])

instance Print (AbsProgettoPar.VARDECID attr) where
  prt i = \case
    AbsProgettoPar.VariableDeclaration identlist typepart initpart -> prPrec i 0 (concatD [prt 0 identlist, prt 0 typepart, prt 0 initpart])

instance Print (AbsProgettoPar.IDENTLIST attr) where
  prt i = \case
    AbsProgettoPar.IdentifierList id_ identlist -> prPrec i 0 (concatD [prt 0 id_, doc (showString ","), prt 0 identlist])
    AbsProgettoPar.IdentifierSingle id_ -> prPrec i 0 (concatD [prt 0 id_])

instance Print (AbsProgettoPar.TYPEPART attr) where
  prt i = \case
    AbsProgettoPar.TypePart typeexpression -> prPrec i 0 (concatD [doc (showString ":"), prt 0 typeexpression])

instance Print (AbsProgettoPar.INITPART attr) where
  prt i = \case
    AbsProgettoPar.InitializzationPart expression -> prPrec i 0 (concatD [doc (showString "="), prt 0 expression])
    AbsProgettoPar.InitializzationPartArray listelementarray -> prPrec i 0 (concatD [doc (showString "="), doc (showString "["), prt 0 listelementarray])
    AbsProgettoPar.InitializzationPartEmpty -> prPrec i 0 (concatD [])

instance Print (AbsProgettoPar.LISTELEMENTARRAY attr) where
  prt i = \case
    AbsProgettoPar.ListElementsOfArray expression listelementarray -> prPrec i 0 (concatD [prt 0 expression, doc (showString ","), prt 0 listelementarray])
    AbsProgettoPar.ListElementOfArray expression -> prPrec i 0 (concatD [prt 0 expression, doc (showString "]")])

instance Print (AbsProgettoPar.TYPEEXPRESSION attr) where
  prt i = \case
    AbsProgettoPar.TypeExpression primitivetype -> prPrec i 0 (concatD [prt 0 primitivetype])
    AbsProgettoPar.TypeExpressionArraySimple rangeexp primitivetype -> prPrec i 0 (concatD [doc (showString "["), prt 0 rangeexp, doc (showString "]"), prt 0 primitivetype])
    AbsProgettoPar.TypeExpressionArray rangeexp primitivetype -> prPrec i 0 (concatD [doc (showString "["), doc (showString "{"), prt 0 rangeexp, doc (showString "}"), doc (showString "]"), prt 0 primitivetype])
    AbsProgettoPar.TypeExpressionPointer primitivetype pointer -> prPrec i 0 (concatD [prt 0 primitivetype, prt 0 pointer])

instance Print AbsProgettoPar.POINTER where
  prt i = \case
    AbsProgettoPar.PointerSymbol pointer -> prPrec i 0 (concatD [prt 0 pointer, doc (showString "*")])
    AbsProgettoPar.PointerSymbolSingle -> prPrec i 0 (concatD [doc (showString "*")])

instance Print (AbsProgettoPar.RANGEEXP attr) where
  prt i = \case
    AbsProgettoPar.RangeExpression expression1 expression2 rangeexp -> prPrec i 0 (concatD [prt 0 expression1, doc (showString ".."), prt 0 expression2, doc (showString ","), prt 0 rangeexp])
    AbsProgettoPar.RangeExpressionSingle expression1 expression2 -> prPrec i 0 (concatD [prt 0 expression1, doc (showString ".."), prt 0 expression2])

instance Print (AbsProgettoPar.PRIMITIVETYPE attr) where
  prt i = \case
    AbsProgettoPar.PrimitiveTypeVoid -> prPrec i 0 (concatD [doc (showString "void")])
    AbsProgettoPar.PrimitiveTypeBool -> prPrec i 0 (concatD [doc (showString "bool")])
    AbsProgettoPar.PrimitiveTypeInt -> prPrec i 0 (concatD [doc (showString "int")])
    AbsProgettoPar.PrimitiveTypeReal -> prPrec i 0 (concatD [doc (showString "real")])
    AbsProgettoPar.PrimitiveTypeString -> prPrec i 0 (concatD [doc (showString "string")])
    AbsProgettoPar.PrimitiveTypeChar -> prPrec i 0 (concatD [doc (showString "char")])
    AbsProgettoPar.TypeArray primitivetype -> prPrec i 0 (concatD [doc (showString "["), doc (showString "]"), prt 0 primitivetype])

instance Print (AbsProgettoPar.CONDITIONALSTATE attr) where
  prt i = \case
    AbsProgettoPar.ConditionalStatementSimpleThen expression statement elsestatement -> prPrec i 0 (concatD [doc (showString "if"), prt 0 expression, doc (showString "then"), prt 0 statement, prt 0 elsestatement])
    AbsProgettoPar.ConditionalStatementSimpleWThen expression b elsestatement -> prPrec i 0 (concatD [doc (showString "if"), prt 0 expression, prt 0 b, prt 0 elsestatement])
    AbsProgettoPar.ConditionalStatementCtrlThen ctrldecstatement statement elsestatement -> prPrec i 0 (concatD [doc (showString "if"), prt 0 ctrldecstatement, doc (showString "then"), prt 0 statement, prt 0 elsestatement])
    AbsProgettoPar.ConditionalStatementCtrlWThen ctrldecstatement b elsestatement -> prPrec i 0 (concatD [doc (showString "if"), prt 0 ctrldecstatement, prt 0 b, prt 0 elsestatement])

instance Print (AbsProgettoPar.WHILESTATEMENT attr) where
  prt i = \case
    AbsProgettoPar.WhileStateSimpleDo expression statement -> prPrec i 0 (concatD [doc (showString "while"), prt 0 expression, doc (showString "do"), prt 0 statement])
    AbsProgettoPar.WhileStateSimpleWDo expression b -> prPrec i 0 (concatD [doc (showString "while"), prt 0 expression, prt 0 b])
    AbsProgettoPar.WhileStateCtrlDo ctrldecstatement statement -> prPrec i 0 (concatD [doc (showString "while"), prt 0 ctrldecstatement, doc (showString "do"), prt 0 statement])
    AbsProgettoPar.WhileStateCtrlWDo ctrldecstatement b -> prPrec i 0 (concatD [doc (showString "while"), prt 0 ctrldecstatement, prt 0 b])

instance Print (AbsProgettoPar.DOSTATEMENT attr) where
  prt i = \case
    AbsProgettoPar.DoWhileState statement expression -> prPrec i 0 (concatD [doc (showString "do"), prt 0 statement, doc (showString "while"), prt 0 expression, doc (showString ";")])

instance Print (AbsProgettoPar.FORSTATEMENT attr) where
  prt i = \case
    AbsProgettoPar.ForStateIndexDo indexvardec expression statement -> prPrec i 0 (concatD [doc (showString "for"), prt 0 indexvardec, doc (showString "in"), prt 0 expression, doc (showString "do"), prt 0 statement])
    AbsProgettoPar.ForStateIndexWDo indexvardec expression b -> prPrec i 0 (concatD [doc (showString "for"), prt 0 indexvardec, doc (showString "in"), prt 0 expression, prt 0 b])
    AbsProgettoPar.ForStateExprDo expression statement -> prPrec i 0 (concatD [doc (showString "for"), prt 0 expression, doc (showString "do"), prt 0 statement])
    AbsProgettoPar.ForStateExprWDo expression b -> prPrec i 0 (concatD [doc (showString "for"), prt 0 expression, prt 0 b])

instance Print (AbsProgettoPar.FORALLSTATEMENT attr) where
  prt i = \case
    AbsProgettoPar.ForAllStateIndexDo indexvardec expression statement -> prPrec i 0 (concatD [doc (showString "forall"), prt 0 indexvardec, doc (showString "in"), prt 0 expression, doc (showString "do"), prt 0 statement])
    AbsProgettoPar.ForAllStateIndexWDo indexvardec expression b -> prPrec i 0 (concatD [doc (showString "forall"), prt 0 indexvardec, doc (showString "in"), prt 0 expression, prt 0 b])
    AbsProgettoPar.ForAllStateExprDo expression statement -> prPrec i 0 (concatD [doc (showString "forall"), prt 0 expression, doc (showString "do"), prt 0 statement])
    AbsProgettoPar.ForAllStateExprWDo expression b -> prPrec i 0 (concatD [doc (showString "forall"), prt 0 expression, prt 0 b])

instance Print (AbsProgettoPar.INDEXVARDEC attr) where
  prt i = \case
    AbsProgettoPar.IndexVarDeclaration id_ -> prPrec i 0 (concatD [prt 0 id_])

instance Print (AbsProgettoPar.ELSESTATEMENT attr) where
  prt i = \case
    AbsProgettoPar.ElseStateEmpty -> prPrec i 0 (concatD [])
    AbsProgettoPar.ElseState statement -> prPrec i 0 (concatD [doc (showString "else"), prt 0 statement])

instance Print (AbsProgettoPar.RETURNSTATEMENT attr) where
  prt i = \case
    AbsProgettoPar.ReturnState expression -> prPrec i 0 (concatD [doc (showString "return"), prt 0 expression])
    AbsProgettoPar.ReturnStateEmpty -> prPrec i 0 (concatD [doc (showString "return")])

instance Print (AbsProgettoPar.CTRLDECSTATEMENT attr) where
  prt i = \case
    AbsProgettoPar.CtrlDecStateVar id_ expression -> prPrec i 0 (concatD [doc (showString "var"), prt 0 id_, doc (showString "="), prt 0 expression])
    AbsProgettoPar.CtrlDecStateConst id_ expression -> prPrec i 0 (concatD [doc (showString "const"), prt 0 id_, doc (showString "="), prt 0 expression])

instance Print (AbsProgettoPar.EXPRESSIONSTATEMENT attr) where
  prt i = \case
    AbsProgettoPar.VariableExpression id_ -> prPrec i 0 (concatD [prt 0 id_])
    AbsProgettoPar.CallExpression callexpression -> prPrec i 0 (concatD [prt 0 callexpression])

instance Print (AbsProgettoPar.CALLEXPRESSION attr) where
  prt i = \case
    AbsProgettoPar.CallExpressionParentheses id_ namedexpressionlist -> prPrec i 0 (concatD [prt 0 id_, doc (showString "("), prt 0 namedexpressionlist, doc (showString ")")])
    AbsProgettoPar.CallExpressionQuadre id_ namedexpressionlist -> prPrec i 0 (concatD [prt 0 id_, doc (showString "["), prt 0 namedexpressionlist, doc (showString "]")])

instance Print (AbsProgettoPar.NAMEDEXPRESSIONLIST attr) where
  prt i = \case
    AbsProgettoPar.NamedExpressionList namedexpression -> prPrec i 0 (concatD [prt 0 namedexpression])
    AbsProgettoPar.NamedExpressionLists namedexpression namedexpressionlist -> prPrec i 0 (concatD [prt 0 namedexpression, doc (showString ","), prt 0 namedexpressionlist])
    AbsProgettoPar.NamedExpressionAssigned id_ expression -> prPrec i 0 (concatD [prt 0 id_, doc (showString "="), prt 0 expression])

instance Print (AbsProgettoPar.NAMEDEXPRESSION attr) where
  prt i = \case
    AbsProgettoPar.NamedExpression expression -> prPrec i 0 (concatD [prt 0 expression])

instance Print (AbsProgettoPar.EXPRESSION attr) where
  prt i = \case
    AbsProgettoPar.ExpressionIdent id_ arrayindexelement -> prPrec i 0 (concatD [prt 0 id_, prt 0 arrayindexelement])
    AbsProgettoPar.ExpressionInteger n -> prPrec i 0 (concatD [prt 0 (AbsProgettoPar.valueInt n)])
    AbsProgettoPar.ExpressionReal d -> prPrec i 0 (concatD [prt 0 (AbsProgettoPar.valueReal  d)])
    AbsProgettoPar.ExpressionString str -> prPrec i 0 (concatD [prt 0 (AbsProgettoPar.valueString  str)])
    AbsProgettoPar.ExpressionChar c -> prPrec i 0 (concatD [prt 0 (AbsProgettoPar.valueChar  c)])
    AbsProgettoPar.ExpressionBoolean boolean -> prPrec i 0 (concatD [prt 0 boolean])
    AbsProgettoPar.ExpressionBinary default_ binaryop expression -> prPrec i 0 (concatD [prt 0 default_, prt 0 binaryop, prt 0 expression])
    AbsProgettoPar.ExpressionUnary unaryop expression -> prPrec i 0 (concatD [prt 0 unaryop, prt 0 expression])
    AbsProgettoPar.ExpressionCast default_ primitivetype -> prPrec i 0 (concatD [prt 0 default_, doc (showString ":"), prt 0 primitivetype])
    AbsProgettoPar.ExpressionBracket expression -> prPrec i 0 (concatD [doc (showString "("), prt 0 expression, doc (showString ")")])

instance Print (AbsProgettoPar.DEFAULT attr) where
  prt i = \case
    AbsProgettoPar.ExpressionIdentD id_ arrayindexelement -> prPrec i 0 (concatD [prt 0 id_, prt 0 arrayindexelement])
    AbsProgettoPar.ExpressionIntegerD n -> prPrec i 0 (concatD [prt 0 (AbsProgettoPar.valueInt n)])
    AbsProgettoPar.ExpressionRealD d -> prPrec i 0 (concatD [prt 0 (AbsProgettoPar.valueReal  d)])
    AbsProgettoPar.ExpressionStringD str -> prPrec i 0 (concatD [prt 0 (AbsProgettoPar.valueString  str)])
    AbsProgettoPar.ExpressionCharD c -> prPrec i 0 (concatD [prt 0 (AbsProgettoPar.valueChar  c)])
    AbsProgettoPar.ExpressionBooleanD boolean -> prPrec i 0 (concatD [prt 0 boolean])
    AbsProgettoPar.ExpressionBracketD expression -> prPrec i 0 (concatD [doc (showString "("), prt 0 expression, doc (showString ")")])

instance Print (AbsProgettoPar.UNARYOP attr) where
  prt i = \case
    AbsProgettoPar.UnaryOperationPositive -> prPrec i 0 (concatD [doc (showString "+")])
    AbsProgettoPar.UnaryOperationNegative -> prPrec i 0 (concatD [doc (showString "-")])
    AbsProgettoPar.UnaryOperationNot -> prPrec i 0 (concatD [doc (showString "!")])
    AbsProgettoPar.UnaryOperationPointer -> prPrec i 0 (concatD [doc (showString "&")])

instance Print (AbsProgettoPar.BINARYOP attr) where
  prt i = \case
    AbsProgettoPar.BinaryOperationPlus -> prPrec i 0 (concatD [doc (showString "+")])
    AbsProgettoPar.BinaryOperationMinus -> prPrec i 0 (concatD [doc (showString "-")])
    AbsProgettoPar.BinaryOperationProduct -> prPrec i 0 (concatD [doc (showString "*")])
    AbsProgettoPar.BinaryOperationDivision -> prPrec i 0 (concatD [doc (showString "/")])
    AbsProgettoPar.BinaryOperationModule -> prPrec i 0 (concatD [doc (showString "%")])
    AbsProgettoPar.BinaryOperationPower -> prPrec i 0 (concatD [doc (showString "**")])
    AbsProgettoPar.BinaryOperationAnd -> prPrec i 0 (concatD [doc (showString "&&")])
    AbsProgettoPar.BinaryOperationOr -> prPrec i 0 (concatD [doc (showString "||")])
    AbsProgettoPar.BinaryOperationEq -> prPrec i 0 (concatD [doc (showString "==")])
    AbsProgettoPar.BinaryOperationNotEq -> prPrec i 0 (concatD [doc (showString "!=")])
    AbsProgettoPar.BinaryOperationGratherEq -> prPrec i 0 (concatD [doc (showString ">=")])
    AbsProgettoPar.BinaryOperationGrather -> prPrec i 0 (concatD [doc (showString ">")])
    AbsProgettoPar.BinaryOperationLessEq -> prPrec i 0 (concatD [doc (showString "<=")])
    AbsProgettoPar.BinaryOperationLess -> prPrec i 0 (concatD [doc (showString "<")])

instance Print (AbsProgettoPar.LVALUEEXPRESSION attr) where
  prt i = \case
    AbsProgettoPar.LvalueExpressions id_ arrayindexelement lvalueexpression -> prPrec i 0 (concatD [prt 0 id_, prt 0 arrayindexelement, doc (showString ","), prt 0 lvalueexpression])
    AbsProgettoPar.LvalueExpression id_ arrayindexelement -> prPrec i 0 (concatD [prt 0 id_, prt 0 arrayindexelement])

instance Print (AbsProgettoPar.ARRAYINDEXELEMENT attr) where
  prt i = \case
    AbsProgettoPar.ArrayIndexElement typeindex -> prPrec i 0 (concatD [doc (showString "["), prt 0 typeindex, doc (showString "]")])
    AbsProgettoPar.ArrayIndexElementEmpty -> prPrec i 0 (concatD [])

instance Print (AbsProgettoPar.TYPEINDEX attr) where
  prt i = \case
    AbsProgettoPar.TypeOfIndexInt typeindex n -> prPrec i 0 (concatD [prt 0 typeindex, doc (showString ","), prt 0 (AbsProgettoPar.valueInt n)])
    AbsProgettoPar.TypeOfIndexIntSingle n -> prPrec i 0 (concatD [prt 0 (AbsProgettoPar.valueInt n)])
    AbsProgettoPar.TypeOfIndexVar typeindex id_ -> prPrec i 0 (concatD [prt 0 typeindex, doc (showString ","), prt 0 id_])
    AbsProgettoPar.TypeOfIndexVarSingle id_ -> prPrec i 0 (concatD [prt 0 id_])

