-- Progetto Linguaggi e Compilatori parte 3 - UNIUD 2021
-- Andrea Mansi & Christian Cagnoni
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
  AbsProgettoPar.StartCode _ statements -> failure x

transSTATEMENTS :: Show attr => (AbsProgettoPar.STATEMENTS attr) -> Result
transSTATEMENTS x = case x of
  AbsProgettoPar.ListStatements _ statement statements -> failure x
  AbsProgettoPar.EmptyStatement _ -> failure x

transB :: Show attr => (AbsProgettoPar.B attr) -> Result
transB x = case x of
  AbsProgettoPar.BlockStatement _ statements -> failure x

transSTATEMENT :: Show attr => (AbsProgettoPar.STATEMENT attr) -> Result
transSTATEMENT x = case x of
  AbsProgettoPar.Statement _ b -> failure x
  AbsProgettoPar.ExpressionStatement _ expressionstatement -> failure x
  AbsProgettoPar.AssignmentStatement _ lvalueexpression assignop expression -> failure x
  AbsProgettoPar.ConditionalStatement _ conditionalstate -> failure x
  AbsProgettoPar.WhileDoStatement _ whilestatement -> failure x
  AbsProgettoPar.DoWhileStatement _ dostatement -> failure x
  AbsProgettoPar.ForStatement _ forstatement -> failure x
  AbsProgettoPar.BreakStatement _ -> failure x
  AbsProgettoPar.ContinueStatement _ -> failure x
  AbsProgettoPar.ReturnStatement _ returnstatement -> failure x
  AbsProgettoPar.VariableDeclarationStatement _ variabletype vardeclist -> failure x
  AbsProgettoPar.ProcedureStatement _ ident parameters statements -> failure x
  AbsProgettoPar.FunctionStatement _ ident parameters typeexpressionfunc statements -> failure x

transPARAMETERS :: Show attr => (AbsProgettoPar.PARAMETERS attr) -> Result
transPARAMETERS x = case x of
  AbsProgettoPar.ParameterList _ parameter parameters -> failure x
  AbsProgettoPar.ParameterListValRes _ parameter parameters -> failure x
  AbsProgettoPar.ParameterListSingle _ parameter -> failure x
  AbsProgettoPar.ParameterListSingleValRes _ parameter -> failure x
  AbsProgettoPar.ParameterListEmpty _ -> failure x

transPARAMETER :: Show attr => (AbsProgettoPar.PARAMETER attr) -> Result
transPARAMETER x = case x of
  AbsProgettoPar.Parameter _ ident ty -> failure x

transASSIGNOP :: Show attr => (AbsProgettoPar.ASSIGNOP attr) -> Result
transASSIGNOP x = case x of
  AbsProgettoPar.AssignOperationEq _ -> failure x
  AbsProgettoPar.AssignOperationEqPlus _ -> failure x
  AbsProgettoPar.AssignOperationEqMinus _ -> failure x
  AbsProgettoPar.AssignOperationEqProd _ -> failure x
  AbsProgettoPar.AssignOperationEqFract _ -> failure x
  AbsProgettoPar.AssignOperationEqPercent _ -> failure x
  AbsProgettoPar.AssignOperationEqPower _ -> failure x

transVARIABLETYPE :: Show attr => (AbsProgettoPar.VARIABLETYPE attr) -> Result
transVARIABLETYPE x = case x of
  AbsProgettoPar.VariableTypeParam _ -> failure x
  AbsProgettoPar.VariableTypeConst _ -> failure x
  AbsProgettoPar.VariableTypeVar _ -> failure x
  AbsProgettoPar.VariableTypeRef _ -> failure x
  AbsProgettoPar.VariableTypeConstRef _ -> failure x

transVARDECLIST :: Show attr => (AbsProgettoPar.VARDECLIST attr) -> Result
transVARDECLIST x = case x of
  AbsProgettoPar.VariableDeclarationSingle _ vardecid -> failure x

transVARDECID :: Show attr => (AbsProgettoPar.VARDECID attr) -> Result
transVARDECID x = case x of
  AbsProgettoPar.VariableDeclaration _ identlist typepart initpart -> failure x
  AbsProgettoPar.VariableDeclarationChecked _ identlist typepart initpart -> failure x

transIDENTLIST :: Show attr => (AbsProgettoPar.IDENTLIST attr) -> Result
transIDENTLIST x = case x of
  AbsProgettoPar.IdentifierList _ ident identlist -> failure x
  AbsProgettoPar.IdentifierSingle _ ident -> failure x

transTYPEPART :: Show attr => (AbsProgettoPar.TYPEPART attr) -> Result
transTYPEPART x = case x of
  AbsProgettoPar.TypePart _ typeexpression -> failure x

transINITPART :: Show attr => (AbsProgettoPar.INITPART attr) -> Result
transINITPART x = case x of
  AbsProgettoPar.InitializzationPart _ expression -> failure x
  AbsProgettoPar.InitializzationPartArray _ arrayinit -> failure x
  AbsProgettoPar.InitializzationPartEmpty _ -> failure x

transLISTELEMENTARRAY :: Show attr => (AbsProgettoPar.LISTELEMENTARRAY attr) -> Result
transLISTELEMENTARRAY x = case x of
  AbsProgettoPar.ListElementsOfArray _ expression listelementarray -> failure x
  AbsProgettoPar.ListElementOfArray _ expression -> failure x

transARRAYINIT :: Show attr => (AbsProgettoPar.ARRAYINIT attr) -> Result
transARRAYINIT x = case x of
    AbsProgettoPar.ArrayInitSingle _ arrayinit -> failure x
    AbsProgettoPar.ArrayInit _ arrayinit1 arrayinit2 -> failure x
    AbsProgettoPar.ArrayInitElems _ listelementarray -> failure x

transTYPEEXPRESSIONFUNC :: Show attr => (AbsProgettoPar.TYPEEXPRESSIONFUNC attr) -> Result
transTYPEEXPRESSIONFUNC x = case x of
    AbsProgettoPar.TypeExpressionArrayOfPointer _ typeexpression -> failure x
    AbsProgettoPar.TypeExpressionFunction _ typeexpression -> failure x

transTYPEEXPRESSION :: Show attr => (AbsProgettoPar.TYPEEXPRESSION attr) -> Result
transTYPEEXPRESSION x = case x of
    AbsProgettoPar.TypeExpression _ primitivetype -> failure x
    AbsProgettoPar.TypeExpressionArraySimple _ rangeexp typeexpression -> failure x
    AbsProgettoPar.TypeExpressionArray _ rangeexp typeexpression -> failure x
    AbsProgettoPar.TypeExpressionPointer _ primitivetype pointer -> failure x
    AbsProgettoPar.TypeExpressionPointerOfArray _ typeexpression pointer -> failure x

transPOINTER :: Show attr => (AbsProgettoPar.POINTER attr) -> Result
transPOINTER x = case x of
  AbsProgettoPar.PointerSymbol _ pointer -> failure x
  AbsProgettoPar.PointerSymbolSingle _ -> failure x

transRANGEEXP :: Show attr => (AbsProgettoPar.RANGEEXP attr) -> Result
transRANGEEXP x = case x of
  AbsProgettoPar.RangeExpression _ expression1 expression2 rangeexp -> failure x
  AbsProgettoPar.RangeExpressionSingle _ expression1 expression2 -> failure x

transPRIMITIVETYPE :: Show attr => (AbsProgettoPar.PRIMITIVETYPE attr) -> Result
transPRIMITIVETYPE x = case x of
  AbsProgettoPar.PrimitiveTypeVoid _ -> failure x
  AbsProgettoPar.PrimitiveTypeBool _ -> failure x
  AbsProgettoPar.PrimitiveTypeInt _ -> failure x
  AbsProgettoPar.PrimitiveTypeReal _ -> failure x
  AbsProgettoPar.PrimitiveTypeString _ -> failure x
  AbsProgettoPar.PrimitiveTypeChar _ -> failure x
  AbsProgettoPar.TypeArray primitivetype _ -> failure x

transCONDITIONALSTATE :: Show attr => (AbsProgettoPar.CONDITIONALSTATE attr) -> Result
transCONDITIONALSTATE x = case x of
  AbsProgettoPar.ConditionalStatementSimpleThen _ expression statement elsestatement -> failure x
  AbsProgettoPar.ConditionalStatementSimpleWThen _ expression b elsestatement -> failure x
  AbsProgettoPar.ConditionalStatementCtrlThen _ ctrldecstatement statement elsestatement -> failure x
  AbsProgettoPar.ConditionalStatementCtrlWThen _ ctrldecstatement b elsestatement -> failure x

transWHILESTATEMENT :: Show attr => (AbsProgettoPar.WHILESTATEMENT attr) -> Result
transWHILESTATEMENT x = case x of
  AbsProgettoPar.WhileStateSimpleDo _ expression statement -> failure x
  AbsProgettoPar.WhileStateSimpleWDo _ expression b -> failure x
  AbsProgettoPar.WhileStateCtrlDo _ ctrldecstatement statement -> failure x
  AbsProgettoPar.WhileStateCtrlWDo _ ctrldecstatement b -> failure x

transDOSTATEMENT :: Show attr => (AbsProgettoPar.DOSTATEMENT attr) -> Result
transDOSTATEMENT x = case x of
  AbsProgettoPar.DoWhileState _ statement expression -> failure x

transFORSTATEMENT :: Show attr => (AbsProgettoPar.FORSTATEMENT attr) -> Result
transFORSTATEMENT x = case x of
  AbsProgettoPar.ForStateIndexDo _ indexvardec rangexp statement -> failure x
  AbsProgettoPar.ForStateIndexWDo _ indexvardec rangexp b -> failure x
  AbsProgettoPar.ForStateExprDo _ rangexp statement -> failure x
  AbsProgettoPar.ForStateExprWDo _ rangexp b -> failure x

transINDEXVARDEC :: Show attr => (AbsProgettoPar.INDEXVARDEC attr) -> Result
transINDEXVARDEC x = case x of
  AbsProgettoPar.IndexVarDeclaration _ ident -> failure x

transELSESTATEMENT :: Show attr => (AbsProgettoPar.ELSESTATEMENT attr) -> Result
transELSESTATEMENT x = case x of
  AbsProgettoPar.ElseStateEmpty _ -> failure x
  AbsProgettoPar.ElseState statement _ -> failure x

transRETURNSTATEMENT :: Show attr => (AbsProgettoPar.RETURNSTATEMENT attr) -> Result
transRETURNSTATEMENT x = case x of
  AbsProgettoPar.ReturnState _ expression -> failure x
  AbsProgettoPar.ReturnStateEmpty _ -> failure x

transCTRLDECSTATEMENT :: Show attr => (AbsProgettoPar.CTRLDECSTATEMENT attr) -> Result
transCTRLDECSTATEMENT x = case x of
  AbsProgettoPar.CtrlDecStateVar _ ident typepart expression -> failure x
  AbsProgettoPar.CtrlDecStateConst _ ident typepart expression -> failure x

transEXPRESSIONSTATEMENT :: Show attr => (AbsProgettoPar.EXPRESSIONSTATEMENT attr) -> Result
transEXPRESSIONSTATEMENT x = case x of
  AbsProgettoPar.VariableExpression _ ident -> failure x
  AbsProgettoPar.CallExpression _ callexpression -> failure x

transCALLEXPRESSION :: Show attr => (AbsProgettoPar.CALLEXPRESSION attr) -> Result
transCALLEXPRESSION x = case x of
  AbsProgettoPar.CallExpressionParentheses _ ident namedexpressionlist -> failure x

transNAMEDEXPRESSIONLIST :: Show attr => (AbsProgettoPar.NAMEDEXPRESSIONLIST attr) -> Result
transNAMEDEXPRESSIONLIST x = case x of
  AbsProgettoPar.NamedExpressionList _ namedexpression -> failure x
  AbsProgettoPar.NamedExpressionListEmpty _-> failure x
  AbsProgettoPar.NamedExpressionLists _ namedexpression namedexpressionlist -> failure x

transNAMEDEXPRESSION :: Show attr => (AbsProgettoPar.NAMEDEXPRESSION attr) -> Result
transNAMEDEXPRESSION x = case x of
  AbsProgettoPar.NamedExpression _ expression -> failure x

transEXPRESSIONS :: Show attr => (AbsProgettoPar.EXPRESSIONS attr) -> Result
transEXPRESSIONS x = case x of
  AbsProgettoPar.Expressions _ expression expressions -> failure x
  AbsProgettoPar.Expression _ expression -> failure x
  AbsProgettoPar.ExpressionEmpty _ -> failure x

transEXPRESSION :: Show attr => (AbsProgettoPar.EXPRESSION attr) -> Result
transEXPRESSION x = case x of
  AbsProgettoPar.ExpressionIdent _ ident arrayindexelement -> failure x
  AbsProgettoPar.ExpressionInteger _ integer -> failure x
  AbsProgettoPar.ExpressionReal _ double -> failure x
  AbsProgettoPar.ExpressionString _ string -> failure x
  AbsProgettoPar.ExpressionChar _ char -> failure x
  AbsProgettoPar.ExpressionBoolean _ boolean -> failure x
  AbsProgettoPar.ExpressionBinaryPlus _ exp1 exp2 -> failure x
  AbsProgettoPar.ExpressionBinaryMinus _ exp1 exp2 -> failure x
  AbsProgettoPar.ExpressionBinaryProduct _ exp1 exp2 -> failure x
  AbsProgettoPar.ExpressionBinaryDivision _ exp1 exp2 -> failure x
  AbsProgettoPar.ExpressionBinaryModule _ exp1 exp2 -> failure x
  AbsProgettoPar.ExpressionBinaryPower _ exp1 exp2 -> failure x
  AbsProgettoPar.ExpressionBinaryAnd _ exp1 exp2 -> failure x
  AbsProgettoPar.ExpressionBinaryOr _ exp1 exp2 -> failure x
  AbsProgettoPar.ExpressionBinaryEq _ exp1 exp2 -> failure x
  AbsProgettoPar.ExpressionBinaryNotEq _ exp1 exp2 -> failure x
  AbsProgettoPar.ExpressionBinaryGratherEq _ exp1 exp2 -> failure x
  AbsProgettoPar.ExpressionBinaryGrather _ exp1 exp2 -> failure x
  AbsProgettoPar.ExpressionBinaryLessEq _ exp1 exp2 -> failure x
  AbsProgettoPar.ExpressionBinaryLess _ exp1 exp2 -> failure x
  AbsProgettoPar.ExpressionUnary _ unaryop default_ -> failure x
  AbsProgettoPar.ExpressionCast _ default_ primitivetype -> failure x
  AbsProgettoPar.ExpressionBracket _ expression -> failure x
  AbsProgettoPar.ExpressionCall _ ident expressions -> failure x

transDEFAULT :: Show attr => (AbsProgettoPar.DEFAULT attr) -> Result
transDEFAULT x = case x of
  AbsProgettoPar.ExpressionIdentD _ ident arrayindexelement -> failure x
  AbsProgettoPar.ExpressionIntegerD _ integer -> failure x
  AbsProgettoPar.ExpressionRealD _ double -> failure x
  AbsProgettoPar.ExpressionStringD _ string -> failure x
  AbsProgettoPar.ExpressionCharD _ char -> failure x
  AbsProgettoPar.ExpressionBooleanD _ boolean -> failure x
  AbsProgettoPar.ExpressionBracketD _ expression -> failure x
  AbsProgettoPar.ExpressionCallD _ ident expressions -> failure x
  AbsProgettoPar.ExpressionCastD _ default_ primitivetype -> failure x
  AbsProgettoPar.ExpressionUnaryD _ unaryop default_ -> failure x

transUNARYOP :: Show attr => (AbsProgettoPar.UNARYOP attr) -> Result
transUNARYOP x = case x of
  AbsProgettoPar.UnaryOperationPositive _ -> failure x
  AbsProgettoPar.UnaryOperationNegative _ -> failure x
  AbsProgettoPar.UnaryOperationNot _ -> failure x
  AbsProgettoPar.UnaryOperationPointer _ -> failure x

transBINARYOP :: Show attr => (AbsProgettoPar.BINARYOP attr)  -> Result
transBINARYOP x = case x of
  AbsProgettoPar.BinaryOperationPlus _ -> failure x
  AbsProgettoPar.BinaryOperationMinus _ -> failure x
  AbsProgettoPar.BinaryOperationProduct _ -> failure x
  AbsProgettoPar.BinaryOperationDivision _ -> failure x
  AbsProgettoPar.BinaryOperationModule _ -> failure x
  AbsProgettoPar.BinaryOperationPower _ -> failure x
  AbsProgettoPar.BinaryOperationAnd _ -> failure x
  AbsProgettoPar.BinaryOperationOr _ -> failure x
  AbsProgettoPar.BinaryOperationEq _ -> failure x
  AbsProgettoPar.BinaryOperationNotEq _ -> failure x
  AbsProgettoPar.BinaryOperationGratherEq _ -> failure x
  AbsProgettoPar.BinaryOperationGrather _ -> failure x
  AbsProgettoPar.BinaryOperationLessEq _ -> failure x
  AbsProgettoPar.BinaryOperationLess _ -> failure x

transLVALUEEXPRESSION :: Show attr => (AbsProgettoPar.LVALUEEXPRESSION attr) -> Result
transLVALUEEXPRESSION x = case x of
  AbsProgettoPar.LvalueExpressions _ ident arrayindexelement lvalueexpression -> failure x
  AbsProgettoPar.LvalueExpression _ ident arrayindexelement -> failure x
  AbsProgettoPar.LvalueExpressionDeref _ lvalues -> failure x

transARRAYINDEXELEMENT :: Show attr => (AbsProgettoPar.ARRAYINDEXELEMENT attr) -> Result
transARRAYINDEXELEMENT x = case x of
  AbsProgettoPar.ArrayIndexElement _ typeindex -> failure x
  AbsProgettoPar.ArrayIndexElements _ elements typeindex -> failure x
  AbsProgettoPar.ArrayIndexElementEmpty _ -> failure x

transARRAYINDEXELEMENTS :: Show attr => (AbsProgettoPar.ARRAYINDEXELEMENTS attr) -> Result
transARRAYINDEXELEMENTS x = case x of 
  AbsProgettoPar.ArrayIndexElementsSingle _ typeindex -> failure x
  AbsProgettoPar.ArrayIndexElementsMultiple _ elements typeindex  -> failure x

transTYPEINDEX :: Show attr => (AbsProgettoPar.TYPEINDEX attr) -> Result
transTYPEINDEX x = case x of
  AbsProgettoPar.TypeOfIndexInt _ typeindex integer -> failure x
  AbsProgettoPar.TypeOfIndexIntSingle _ integer -> failure x
  AbsProgettoPar.TypeOfIndexVar _ typeindex ident index -> failure x
  AbsProgettoPar.TypeOfIndexVarSingle _ ident index -> failure x
  AbsProgettoPar.TypeOfIndexPointer _ typeindex unaryop def_-> failure x
  AbsProgettoPar.TypeOfIndexPointerSingle _ unaryop def_-> failure x
  AbsProgettoPar.TypeOfIndexBinaryPlus _ typeindex expr1 expr2 -> failure x
  AbsProgettoPar.TypeOfIndexBinaryPlusSingle _ expr1 expr2 -> failure x
  AbsProgettoPar.TypeOfIndexBinaryMinus _ typeindex expr1 expr2 -> failure x
  AbsProgettoPar.TypeOfIndexBinaryMinusSingle _ expr1 expr2 -> failure x
  AbsProgettoPar.TypeOfIndexBinaryProduct _ typeindex expr1 expr2 -> failure x
  AbsProgettoPar.TypeOfIndexBinaryProductSingle _ expr1 expr2 -> failure x
  AbsProgettoPar.TypeOfIndexBinaryDivision _ typeindex expr1 expr2 -> failure x
  AbsProgettoPar.TypeOfIndexBinaryDivisionSingle _ expr1 expr2 -> failure x
  AbsProgettoPar.TypeOfIndexBinaryModule _ typeindex expr1 expr2 -> failure x
  AbsProgettoPar.TypeOfIndexBinaryModuleSingle _ expr1 expr2 -> failure x
  AbsProgettoPar.TypeOfIndexBinaryPower _ typeindex expr1 expr2 -> failure x
  AbsProgettoPar.TypeOfIndexBinaryPowerSingle _ expr1 expr2 -> failure x
  AbsProgettoPar.TypeOfIndexExpressionCall _ typeindex id_ exps -> failure x
  AbsProgettoPar.TypeOfIndexExpressionCallSingle _ id_ exps -> failure x
  AbsProgettoPar.TypeOfIndexExpressionBracket _ typeindex exp -> failure x
  AbsProgettoPar.TypeOfIndexExpressionBracketSingle _  exp -> failure x
