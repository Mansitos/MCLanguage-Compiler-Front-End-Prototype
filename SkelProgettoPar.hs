-- Haskell module generated by the BNF converter

{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module SkelProgettoPar where

import Prelude (($), Either(..), String, (++), Show, show)
import qualified AbsProgettoPar

type Err = Either String
type Result = Err String

failure :: Show a => a -> Result
failure x = Left $ "Undefined case: " ++ show x

transIdent :: Show attr => (AbsProgettoPar.Ident attr) -> Result
transIdent x = case x of
  AbsProgettoPar.Ident string _-> failure x

transBoolean :: Show attr => (AbsProgettoPar.Boolean attr) -> Result
transBoolean x = case x of
  AbsProgettoPar.Boolean_true _-> failure x
  AbsProgettoPar.Boolean_false _-> failure x
  AbsProgettoPar.Boolean_True _-> failure x
  AbsProgettoPar.Boolean_False _-> failure x

transS :: Show attr => (AbsProgettoPar.S attr) -> Result
transS x = case x of
  AbsProgettoPar.StartCode statements -> failure x

transSTATEMENTS :: Show attr => (AbsProgettoPar.STATEMENTS attr) -> Result
transSTATEMENTS x = case x of
  AbsProgettoPar.ListStatements statement statements -> failure x
  AbsProgettoPar.EmptyStatement -> failure x

transB :: Show attr => (AbsProgettoPar.B attr) -> Result
transB x = case x of
  AbsProgettoPar.BlockStatement statements -> failure x

transSTATEMENT :: Show attr => (AbsProgettoPar.STATEMENT attr) -> Result
transSTATEMENT x = case x of
  AbsProgettoPar.Statement b -> failure x
  AbsProgettoPar.ExpressionStatement expressionstatement -> failure x
  AbsProgettoPar.AssignmentStatement lvalueexpression assignop expression -> failure x
  AbsProgettoPar.ConditionalStatement conditionalstate -> failure x
  AbsProgettoPar.WhileDoStatement whilestatement -> failure x
  AbsProgettoPar.DoWhileStatement dostatement -> failure x
  AbsProgettoPar.ForStatement forstatement -> failure x
  AbsProgettoPar.BreakStatement -> failure x
  AbsProgettoPar.ContinueStatement -> failure x
  AbsProgettoPar.ReturnStatement returnstatement -> failure x
  AbsProgettoPar.VariableDeclarationStatement variabletype vardeclist -> failure x
  AbsProgettoPar.ForAllStatement forallstatement -> failure x
  AbsProgettoPar.ProcedureStatement ident parameters statements -> failure x
  AbsProgettoPar.FunctionStatement ident parameters primitivetype statements -> failure x

transPARAMETERS :: Show attr => (AbsProgettoPar.PARAMETERS attr) -> Result
transPARAMETERS x = case x of
  AbsProgettoPar.ParameterList parameter parameters -> failure x
  AbsProgettoPar.ParameterListSingle parameter -> failure x
  AbsProgettoPar.ParameterListEmpty -> failure x

transPARAMETER :: Show attr => (AbsProgettoPar.PARAMETER attr) -> Result
transPARAMETER x = case x of
  AbsProgettoPar.Parameter ident primitivetype -> failure x

transASSIGNOP :: Show attr => (AbsProgettoPar.ASSIGNOP attr) -> Result
transASSIGNOP x = case x of
  AbsProgettoPar.AssignOperationEq -> failure x
  AbsProgettoPar.AssignOperationEqPlus -> failure x
  AbsProgettoPar.AssignOperationEqMinus -> failure x
  AbsProgettoPar.AssignOperationEqProd -> failure x
  AbsProgettoPar.AssignOperationEqFract -> failure x
  AbsProgettoPar.AssignOperationEqPercent -> failure x
  AbsProgettoPar.AssignOperationEqPower -> failure x

transVARIABLETYPE :: Show attr => (AbsProgettoPar.VARIABLETYPE attr) -> Result
transVARIABLETYPE x = case x of
  AbsProgettoPar.VariableTypeParam -> failure x
  AbsProgettoPar.VariableTypeConst -> failure x
  AbsProgettoPar.VariableTypeVar -> failure x
  AbsProgettoPar.VariableTypeRef -> failure x
  AbsProgettoPar.VariableTypeConstRef -> failure x

transVARDECLIST :: Show attr => (AbsProgettoPar.VARDECLIST attr) -> Result
transVARDECLIST x = case x of
  AbsProgettoPar.VariableDeclarationSingle vardecid -> failure x

transVARDECID :: Show attr => (AbsProgettoPar.VARDECID attr) -> Result
transVARDECID x = case x of
  AbsProgettoPar.VariableDeclaration identlist typepart initpart -> failure x

transIDENTLIST :: Show attr => (AbsProgettoPar.IDENTLIST attr) -> Result
transIDENTLIST x = case x of
  AbsProgettoPar.IdentifierList ident identlist -> failure x
  AbsProgettoPar.IdentifierSingle ident -> failure x

transTYPEPART :: Show attr => (AbsProgettoPar.TYPEPART attr) -> Result
transTYPEPART x = case x of
  AbsProgettoPar.TypePart typeexpression -> failure x

transINITPART :: Show attr => (AbsProgettoPar.INITPART attr) -> Result
transINITPART x = case x of
  AbsProgettoPar.InitializzationPart expression -> failure x
  AbsProgettoPar.InitializzationPartArray listelementarray -> failure x
  AbsProgettoPar.InitializzationPartEmpty -> failure x

transLISTELEMENTARRAY :: Show attr => (AbsProgettoPar.LISTELEMENTARRAY attr) -> Result
transLISTELEMENTARRAY x = case x of
  AbsProgettoPar.ListElementsOfArray expression listelementarray -> failure x
  AbsProgettoPar.ListElementOfArray expression -> failure x

transTYPEEXPRESSION :: Show attr => (AbsProgettoPar.TYPEEXPRESSION attr) -> Result
transTYPEEXPRESSION x = case x of
  AbsProgettoPar.TypeExpression primitivetype -> failure x
  AbsProgettoPar.TypeExpressionArraySimple rangeexp primitivetype -> failure x
  AbsProgettoPar.TypeExpressionArray rangeexp primitivetype -> failure x
  AbsProgettoPar.TypeExpressionPointer primitivetype pointer -> failure x

transPOINTER :: AbsProgettoPar.POINTER -> Result
transPOINTER x = case x of
  AbsProgettoPar.PointerSymbol pointer -> failure x
  AbsProgettoPar.PointerSymbolSingle -> failure x

transRANGEEXP :: Show attr => (AbsProgettoPar.RANGEEXP attr) -> Result
transRANGEEXP x = case x of
  AbsProgettoPar.RangeExpression expression1 expression2 rangeexp -> failure x
  AbsProgettoPar.RangeExpressionSingle expression1 expression2 -> failure x

transPRIMITIVETYPE :: Show attr => (AbsProgettoPar.PRIMITIVETYPE attr) -> Result
transPRIMITIVETYPE x = case x of
  AbsProgettoPar.PrimitiveTypeVoid -> failure x
  AbsProgettoPar.PrimitiveTypeBool -> failure x
  AbsProgettoPar.PrimitiveTypeInt -> failure x
  AbsProgettoPar.PrimitiveTypeReal -> failure x
  AbsProgettoPar.PrimitiveTypeString -> failure x
  AbsProgettoPar.PrimitiveTypeChar -> failure x
  AbsProgettoPar.TypeArray primitivetype -> failure x

transCONDITIONALSTATE :: Show attr => (AbsProgettoPar.CONDITIONALSTATE attr) -> Result
transCONDITIONALSTATE x = case x of
  AbsProgettoPar.ConditionalStatementSimpleThen expression statement elsestatement -> failure x
  AbsProgettoPar.ConditionalStatementSimpleWThen expression b elsestatement -> failure x
  AbsProgettoPar.ConditionalStatementCtrlThen ctrldecstatement statement elsestatement -> failure x
  AbsProgettoPar.ConditionalStatementCtrlWThen ctrldecstatement b elsestatement -> failure x

transWHILESTATEMENT :: Show attr => (AbsProgettoPar.WHILESTATEMENT attr) -> Result
transWHILESTATEMENT x = case x of
  AbsProgettoPar.WhileStateSimpleDo expression statement -> failure x
  AbsProgettoPar.WhileStateSimpleWDo expression b -> failure x
  AbsProgettoPar.WhileStateCtrlDo ctrldecstatement statement -> failure x
  AbsProgettoPar.WhileStateCtrlWDo ctrldecstatement b -> failure x

transDOSTATEMENT :: Show attr => (AbsProgettoPar.DOSTATEMENT attr) -> Result
transDOSTATEMENT x = case x of
  AbsProgettoPar.DoWhileState statement expression -> failure x

transFORSTATEMENT :: Show attr => (AbsProgettoPar.FORSTATEMENT attr) -> Result
transFORSTATEMENT x = case x of
  AbsProgettoPar.ForStateIndexDo indexvardec expression statement -> failure x
  AbsProgettoPar.ForStateIndexWDo indexvardec expression b -> failure x
  AbsProgettoPar.ForStateExprDo expression statement -> failure x
  AbsProgettoPar.ForStateExprWDo expression b -> failure x

transFORALLSTATEMENT :: Show attr => (AbsProgettoPar.FORALLSTATEMENT attr) -> Result
transFORALLSTATEMENT x = case x of
  AbsProgettoPar.ForAllStateIndexDo indexvardec expression statement -> failure x
  AbsProgettoPar.ForAllStateIndexWDo indexvardec expression b -> failure x
  AbsProgettoPar.ForAllStateExprDo expression statement -> failure x
  AbsProgettoPar.ForAllStateExprWDo expression b -> failure x

transINDEXVARDEC :: Show attr => (AbsProgettoPar.INDEXVARDEC attr) -> Result
transINDEXVARDEC x = case x of
  AbsProgettoPar.IndexVarDeclaration ident -> failure x

transELSESTATEMENT :: Show attr => (AbsProgettoPar.ELSESTATEMENT attr) -> Result
transELSESTATEMENT x = case x of
  AbsProgettoPar.ElseStateEmpty -> failure x
  AbsProgettoPar.ElseState statement -> failure x

transRETURNSTATEMENT :: Show attr => (AbsProgettoPar.RETURNSTATEMENT attr) -> Result
transRETURNSTATEMENT x = case x of
  AbsProgettoPar.ReturnState expression -> failure x
  AbsProgettoPar.ReturnStateEmpty -> failure x

transCTRLDECSTATEMENT :: Show attr => (AbsProgettoPar.CTRLDECSTATEMENT attr) -> Result
transCTRLDECSTATEMENT x = case x of
  AbsProgettoPar.CtrlDecStateVar ident expression -> failure x
  AbsProgettoPar.CtrlDecStateConst ident expression -> failure x

transEXPRESSIONSTATEMENT :: Show attr => (AbsProgettoPar.EXPRESSIONSTATEMENT attr) -> Result
transEXPRESSIONSTATEMENT x = case x of
  AbsProgettoPar.VariableExpression ident -> failure x
  AbsProgettoPar.CallExpression callexpression -> failure x

transCALLEXPRESSION :: Show attr => (AbsProgettoPar.CALLEXPRESSION attr) -> Result
transCALLEXPRESSION x = case x of
  AbsProgettoPar.CallExpressionParentheses ident namedexpressionlist -> failure x
  AbsProgettoPar.CallExpressionQuadre ident namedexpressionlist -> failure x

transNAMEDEXPRESSIONLIST :: Show attr => (AbsProgettoPar.NAMEDEXPRESSIONLIST attr) -> Result
transNAMEDEXPRESSIONLIST x = case x of
  AbsProgettoPar.NamedExpressionList namedexpression -> failure x
  AbsProgettoPar.NamedExpressionLists namedexpression namedexpressionlist -> failure x
  AbsProgettoPar.NamedExpressionAssigned ident expression -> failure x

transNAMEDEXPRESSION :: Show attr => (AbsProgettoPar.NAMEDEXPRESSION attr) -> Result
transNAMEDEXPRESSION x = case x of
  AbsProgettoPar.NamedExpression expression -> failure x

transEXPRESSION :: Show attr => (AbsProgettoPar.EXPRESSION attr) -> Result
transEXPRESSION x = case x of
  AbsProgettoPar.ExpressionIdent ident arrayindexelement -> failure x
  AbsProgettoPar.ExpressionInteger integer -> failure x
  AbsProgettoPar.ExpressionReal double -> failure x
  AbsProgettoPar.ExpressionString string -> failure x
  AbsProgettoPar.ExpressionChar char -> failure x
  AbsProgettoPar.ExpressionBoolean boolean -> failure x
  AbsProgettoPar.ExpressionBinary default_ binaryop expression -> failure x
  AbsProgettoPar.ExpressionUnary unaryop expression -> failure x
  AbsProgettoPar.ExpressionCast default_ primitivetype -> failure x
  AbsProgettoPar.ExpressionBracket expression -> failure x

transDEFAULT :: Show attr => (AbsProgettoPar.DEFAULT attr) -> Result
transDEFAULT x = case x of
  AbsProgettoPar.ExpressionIdentD ident arrayindexelement -> failure x
  AbsProgettoPar.ExpressionIntegerD integer -> failure x
  AbsProgettoPar.ExpressionRealD double -> failure x
  AbsProgettoPar.ExpressionStringD string -> failure x
  AbsProgettoPar.ExpressionCharD char -> failure x
  AbsProgettoPar.ExpressionBooleanD boolean -> failure x
  AbsProgettoPar.ExpressionBracketD expression -> failure x

transUNARYOP :: Show attr => (AbsProgettoPar.UNARYOP attr) -> Result
transUNARYOP x = case x of
  AbsProgettoPar.UnaryOperationPositive -> failure x
  AbsProgettoPar.UnaryOperationNegative -> failure x
  AbsProgettoPar.UnaryOperationNot -> failure x
  AbsProgettoPar.UnaryOperationPointer -> failure x

transBINARYOP :: Show attr => (AbsProgettoPar.BINARYOP attr)  -> Result
transBINARYOP x = case x of
  AbsProgettoPar.BinaryOperationPlus -> failure x
  AbsProgettoPar.BinaryOperationMinus -> failure x
  AbsProgettoPar.BinaryOperationProduct -> failure x
  AbsProgettoPar.BinaryOperationDivision -> failure x
  AbsProgettoPar.BinaryOperationModule -> failure x
  AbsProgettoPar.BinaryOperationPower -> failure x
  AbsProgettoPar.BinaryOperationAnd -> failure x
  AbsProgettoPar.BinaryOperationOr -> failure x
  AbsProgettoPar.BinaryOperationEq -> failure x
  AbsProgettoPar.BinaryOperationNotEq -> failure x
  AbsProgettoPar.BinaryOperationGratherEq -> failure x
  AbsProgettoPar.BinaryOperationGrather -> failure x
  AbsProgettoPar.BinaryOperationLessEq -> failure x
  AbsProgettoPar.BinaryOperationLess -> failure x

transLVALUEEXPRESSION :: Show attr => (AbsProgettoPar.LVALUEEXPRESSION attr) -> Result
transLVALUEEXPRESSION x = case x of
  AbsProgettoPar.LvalueExpressions ident arrayindexelement lvalueexpression -> failure x
  AbsProgettoPar.LvalueExpression ident arrayindexelement -> failure x

transARRAYINDEXELEMENT :: Show attr => (AbsProgettoPar.ARRAYINDEXELEMENT attr) -> Result
transARRAYINDEXELEMENT x = case x of
  AbsProgettoPar.ArrayIndexElement typeindex -> failure x
  AbsProgettoPar.ArrayIndexElementEmpty -> failure x

transTYPEINDEX :: Show attr => (AbsProgettoPar.TYPEINDEX attr) -> Result
transTYPEINDEX x = case x of
  AbsProgettoPar.TypeOfIndexInt typeindex integer -> failure x
  AbsProgettoPar.TypeOfIndexIntSingle integer -> failure x
  AbsProgettoPar.TypeOfIndexVar typeindex ident -> failure x
  AbsProgettoPar.TypeOfIndexVarSingle ident -> failure x
