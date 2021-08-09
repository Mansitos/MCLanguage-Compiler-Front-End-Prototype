-- Haskell data types for the abstract syntax.
-- Generated by the BNF converter.

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | The abstract syntax of language progetto3par.

module AbsProgettoPar where

import Prelude (Char, Double, Integer, String)
import qualified Prelude as C (Eq, Ord, Show, Read)
import qualified Data.String

data Boolean a
    = Boolean_true {contentBoolean::a}| Boolean_false {contentBoolean::a}
    | Boolean_True {contentBoolean::a}| Boolean_False {contentBoolean::a}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data S a = StartCode {s_content::a , s_statements::(STATEMENTS a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data STATEMENTS a
    = ListStatements {statements_content::a, statements_statement::(STATEMENT a) , statements_statements::(STATEMENTS a)} 
    | EmptyStatement {statements_content::a}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data B a = BlockStatement {b_content::a , b_statements::(STATEMENTS a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data STATEMENT a
    = Statement {statement_content::a, statement_b::(B a)}
    | ExpressionStatement {statement_content::a, statement_expressionstatement::(EXPRESSIONSTATEMENT a)}
    | AssignmentStatement {statement_content::a, statement_lvalueexpression::(LVALUEEXPRESSION a), statement_assignop::(ASSIGNOP a), statement_expression::(EXPRESSION a)}
    | ConditionalStatement {statement_content::a, statement_conditionalstate::(CONDITIONALSTATE a)}
    | WhileDoStatement {statement_content::a,  statement_whilestatement::(WHILESTATEMENT a)}
    | DoWhileStatement {statement_content::a,  statement_dostatement::(DOSTATEMENT a)}
    | ForStatement {statement_content::a,  statement_forstatement::(FORSTATEMENT a)}
    | BreakStatement {statement_content::a}
    | ContinueStatement {statement_content::a}
    | ReturnStatement {statement_content::a, statement_returnstatement::(RETURNSTATEMENT a)}
    | VariableDeclarationStatement {statement_content::a, statemenets_variabletype::(VARIABLETYPE a) , statemenets_vardeclist::(VARDECLIST a)}
    | ProcedureStatement {statement_content::a, statement_ident::(Ident a ), statement_parameters::(PARAMETERS a), statement_statements::(STATEMENTS a)}
    | FunctionStatement {statement_content::a, statement_ident::(Ident a ), statement_parameters::(PARAMETERS a), statement_typeexpressionfunc::(TYPEEXPRESSIONFUNC a), statement_statements::(STATEMENTS a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data PARAMETERS a
    = ParameterList {parameters_content::a, parameters_parameter::(PARAMETER a), parameters_parameters::(PARAMETERS a)} 
    | ParameterListSingle {parameters_content::a, parameters_parameter::(PARAMETER a)}
    | ParameterListEmpty{parameters_content::a}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data PARAMETER a = Parameter {parameter_content::a, parameter_ident::(Ident a), parameter_typeexpression::(TYPEEXPRESSIONFUNC a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data ASSIGNOP a
    = AssignOperationEq {assignop_content::a}
    | AssignOperationEqPlus {assignop_content::a}
    | AssignOperationEqMinus {assignop_content::a}
    | AssignOperationEqProd {assignop_content::a}
    | AssignOperationEqFract {assignop_content::a}
    | AssignOperationEqPercent {assignop_content::a}
    | AssignOperationEqPower {assignop_content::a}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data VARIABLETYPE a
    = VariableTypeParam {variabletype_content::a}
    | VariableTypeConst {variabletype_content::a}
    | VariableTypeVar {variabletype_content::a}
    | VariableTypeRef {variabletype_content::a}
    | VariableTypeConstRef {variabletype_content::a}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data VARDECLIST a = VariableDeclarationSingle {vardeclist_content::a, vardeclist_vardecid::(VARDECID a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data VARDECID a = VariableDeclaration {vardecid_content::a, vardecid_identlist::(IDENTLIST a), vardecid_typepart::(TYPEPART a), vardecid_initpart::(INITPART a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data IDENTLIST a
    = IdentifierList {identlist_content::a, identlist_ident::(Ident a ), identlist_identlist::(IDENTLIST a)}
    | IdentifierSingle {identlist_content::a, identlist_ident::(Ident a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data TYPEPART a = TypePart {type_part::a, typepart_typeexpression::(TYPEEXPRESSION a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data INITPART a
    = InitializzationPart {initpart_content::a, initpart_expression::(EXPRESSION a)}
    | InitializzationPartArray {initpart_content::a, initpart_listelementary::(ARRAYINIT a)}
    | InitializzationPartEmpty {initpart_content::a}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data ARRAYINIT a
    = ArrayInitSingle {arrayinit_content::a, arrayinit_arrayinit::(ARRAYINIT a)}
    | ArrayInit {arrayinit_content::a, arrayinit_arrayinit1::(ARRAYINIT a), arrayinit_arrayinit2::(ARRAYINIT a)}
    | ArrayInitSingleElems {arrayinit_content::a, arrayinit_listelementarray::(LISTELEMENTARRAY a) }
    | ArrayInitElems {arrayinit_content::a, arrayinit_listelementarray::(LISTELEMENTARRAY a), arrayinit_arrayinit::(ARRAYINIT a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data LISTELEMENTARRAY a
    = ListElementsOfArray {listelementarray_content::a, listelementarray_expression::(EXPRESSION a), listelementarray_listelementarray::(LISTELEMENTARRAY a)}
    | ListElementOfArray {listelementarray_content::a, listelementarray_expression::(EXPRESSION a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data TYPEEXPRESSIONFUNC a
    = TypeExpressionArrayOfPointer {typeexpressionfunc_content::a, typeexpressionfunc_typeexpressionfunc::(TYPEEXPRESSIONFUNC a)}
    | TypeExpressionFunction {typeexpressionfunc_content::a, typeexpressionfunc_typeexpression::(TYPEEXPRESSION a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data TYPEEXPRESSION a
    = TypeExpression {typeexpression_content::a, typeexpression_primitivetype::(PRIMITIVETYPE a)}
    | TypeExpressionArraySimple {typeexpression_content::a, typeexpression_rangeexp::(RANGEEXP a), typeexpression_typeexpressionfunc::(TYPEEXPRESSIONFUNC a)}
    | TypeExpressionArray {typeexpression_content::a, typeexpression_rangeexp::(RANGEEXP a), typeexpression_typeexpressionfunc::(TYPEEXPRESSIONFUNC a)}
    | TypeExpressionPointer {typeexpression_content::a, typeexpression_primitivetype::(PRIMITIVETYPE a), typexpression_pointer::(POINTER a)}
    | TypeExpressionPointerOfArray {typeexpression_content::a, typeexpression_typeexpressionfunc::(TYPEEXPRESSIONFUNC a), typexpression_pointer::(POINTER a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data POINTER a 
    = PointerSymbol {pointer_content::a, pointer_pointer::(POINTER a)} 
    | PointerSymbolSingle {pointer_content::a}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data RANGEEXP a
    = RangeExpression {rangeexp_content::a, rangeexp_expression1::(EXPRESSION a), rangeexp_expression2::(EXPRESSION a), rangeexp_rangeexp::(RANGEEXP a)}
    | RangeExpressionSingle {rangeexp_content::a, rangeexp_expression1::(EXPRESSION a), rangeexp_expression2::(EXPRESSION a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data PRIMITIVETYPE a
    = PrimitiveTypeVoid {primitivetype_content::a}
    | PrimitiveTypeBool {primitivetype_content::a}
    | PrimitiveTypeInt {primitivetype_content::a}
    | PrimitiveTypeReal {primitivetype_content::a}
    | PrimitiveTypeString {primitivetype_content::a}
    | PrimitiveTypeChar {primitivetype_content::a}
    | TypeArray {primitivetype_content::a, primitivetype_primitivetype::(PRIMITIVETYPE a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data CONDITIONALSTATE a
    = ConditionalStatementSimpleThen {conditionalstate_content::a, conditionalstate_expression::(EXPRESSION a), conditionalstate_statement::(STATEMENT a), conditionalstate_elsestatement::(ELSESTATEMENT a)}
    | ConditionalStatementSimpleWThen {conditionalstate_content::a, conditionalstate_expression::(EXPRESSION a), conditionalstate_b::(B a), conditionalstate_elsestatement::(ELSESTATEMENT a)}
    | ConditionalStatementCtrlThen {conditionalstate_content::a, conditionalstate_ctrldecstatement::(CTRLDECSTATEMENT a), conditionalstate_statement::(STATEMENT a), conditionalstate_elsestatement::(ELSESTATEMENT a)}
    | ConditionalStatementCtrlWThen {conditionalstate_content::a,conditionalstate_ctrldecstatement:: (CTRLDECSTATEMENT a), conditionalstate_b::(B a), conditionalstate_elsestatement::(ELSESTATEMENT a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data WHILESTATEMENT a
    = WhileStateSimpleDo {whilestatement_content::a , whilestatement_expression::(EXPRESSION a), whilestatement_statement::(STATEMENT a)}
    | WhileStateSimpleWDo {whilestatement_content::a , whilestatement_expression::(EXPRESSION a), whilestatement_b::(B a)}
    | WhileStateCtrlDo {whilestatement_content::a , whilestatement_sctrldecstatement::(CTRLDECSTATEMENT a), whilestatement_statement::(STATEMENT a)}
    | WhileStateCtrlWDo {whilestatement_content::a , whilestatement_sctrldecstatement::(CTRLDECSTATEMENT a), whilestatement_b::(B a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data DOSTATEMENT a =  DoWhileState {dostatement_content::a, dostatement_statement::(STATEMENT a), dostatement_expression::(EXPRESSION a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data FORSTATEMENT a
    = ForStateIndexDo {forstatement_content::a, forstatement_indexvardec::(INDEXVARDEC a), forstatement_rangexp::(RANGEEXP a), forstatement_statement::(STATEMENT a)}
    | ForStateIndexWDo {forstatement_content::a,forstatement_indexvardec::(INDEXVARDEC a), forstatement_rangexp::(RANGEEXP a), forstatement_b::(B a)}
    | ForStateExprDo {forstatement_content::a, forstatement_rangexp::(RANGEEXP a), forstatement_statement::(STATEMENT a)}
    | ForStateExprWDo {forstatement_content::a, forstatement_rangexp::(RANGEEXP a), forstatement_b::(B a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data INDEXVARDEC a = IndexVarDeclaration {indexvardec_content::a, indexvardec_ident::(Ident a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data ELSESTATEMENT a = ElseStateEmpty {elsestatement_content::a}
    |ElseState {elsestatement_content::a, elsestatement_statement::(STATEMENT a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data RETURNSTATEMENT a 
  = ReturnState {returnstatement_content::a , returnstatament_expression::(EXPRESSION a)} 
  | ReturnStateEmpty {returnstatement_content::a}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data CTRLDECSTATEMENT a
    = CtrlDecStateVar {ctrldecstatement_content::a, ctrldecstatement_ident::(Ident a), ctrldecstatement_typepart::(TYPEPART a), ctrldecstatement_expression::(EXPRESSION a)}
    | CtrlDecStateConst {ctrldecstatement_content::a, ctrldecstatement_ident::(Ident a),ctrldecstatement_typepart::(TYPEPART a), ctrldecstatement_expression::(EXPRESSION a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data EXPRESSIONSTATEMENT a
    = VariableExpression {expressionstatement_content::a, expressionstatement_ident::(Ident a )} 
    | CallExpression {expressionstatement_content::a, expressionstatement_callexpression::(CALLEXPRESSION a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data CALLEXPRESSION a
    = CallExpressionParentheses {callexpression_content::a, callexpression_ident::(Ident a), callexpression_namedexpressionlist::(NAMEDEXPRESSIONLIST a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data NAMEDEXPRESSIONLIST a
    = NamedExpressionList {namedexpressionlist_content::a, namedexpressionlist_namedexpression::(NAMEDEXPRESSION a)}
    | NamedExpressionListEmpty {namedexpressionlist_content::a}
    | NamedExpressionLists {namedexpressionlist_content::a, namedexpressionlist_namedexpression::(NAMEDEXPRESSION a), namedexpressionlist_namedexpressionlist::(NAMEDEXPRESSIONLIST a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data NAMEDEXPRESSION a = NamedExpression {namedexpression_content::a, namedexpression_expression::(EXPRESSION a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data EXPRESSIONS a
    =  Expressions {expressions_content::a, expressions_expression::(EXPRESSION a), expressions_expressions::(EXPRESSIONS a)}
    |  Expression {expressions_content::a,expressions_expression::(EXPRESSION a)}
    |  ExpressionEmpty {expressions_content::a}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data EXPRESSION a
    = ExpressionIdent {expression_content::a, expression_ident::(Ident a), expression_arrayindexelement::(ARRAYINDEXELEMENT a)}
    | ExpressionInteger {expression_content::a, expression_integer::(AbsProgettoPar.Integer a)}
    | ExpressionReal {expression_content::a, expression_real::(Real a)}
    | ExpressionString {expression_content::a, expression_string::(AbsProgettoPar.String a)}
    | ExpressionChar {expression_content::a, expression_char::(AbsProgettoPar.Char a)}
    | ExpressionBoolean {expression_content::a, expression_bool::(Boolean a)}
    | ExpressionBinaryPlus {expression_content::a, expression_expressionf::(EXPRESSION a), expression_expressionse::(EXPRESSION a)}
    | ExpressionBinaryMinus {expression_content::a, expression_expressionf::(EXPRESSION a), expression_expressionse::(EXPRESSION a)}
    | ExpressionBinaryProduct {expression_content::a, expression_expressionf::(EXPRESSION a), expression_expressionse::(EXPRESSION a)}
    | ExpressionBinaryDivision {expression_content::a, expression_expressionf::(EXPRESSION a), expression_expressionse::(EXPRESSION a)}
    | ExpressionBinaryModule {expression_content::a, expression_expressionf::(EXPRESSION a), expression_expressionse::(EXPRESSION a)}
    | ExpressionBinaryPower {expression_content::a, expression_expressionf::(EXPRESSION a), expression_expressionse::(EXPRESSION a)}
    | ExpressionBinaryAnd {expression_content::a, expression_expressionf::(EXPRESSION a), expression_expressionse::(EXPRESSION a)}
    | ExpressionBinaryOr {expression_content::a, expression_expressionf::(EXPRESSION a), expression_expressionse::(EXPRESSION a)}
    | ExpressionBinaryEq {expression_content::a, expression_expressionf::(EXPRESSION a), expression_expressionse::(EXPRESSION a)}
    | ExpressionBinaryNotEq {expression_content::a, expression_expressionf::(EXPRESSION a), expression_expressionse::(EXPRESSION a)}
    | ExpressionBinaryGratherEq {expression_content::a, expression_expressionf::(EXPRESSION a), expression_expressionse::(EXPRESSION a)}
    | ExpressionBinaryGrather {expression_content::a, expression_expressionf::(EXPRESSION a), expression_expressionse::(EXPRESSION a)}
    | ExpressionBinaryLessEq {expression_content::a, expression_expressionf::(EXPRESSION a), expression_expressionse::(EXPRESSION a)}
    | ExpressionBinaryLess {expression_content::a, expression_expressionf::(EXPRESSION a), expression_expressionse::(EXPRESSION a)}
    | ExpressionUnary {expression_content::a, expression_unaryop::(UNARYOP a), expression_default::(DEFAULT a)}
    | ExpressionCast {expression_content::a, expression_default::(DEFAULT a), expression_primitivetype::(PRIMITIVETYPE a)}
    | ExpressionBracket {expression_content::a, expression_expression::(EXPRESSION a)}
    | ExpressionCall {expression_content::a, expression_ident::(Ident a), expression_expressions::(EXPRESSIONS a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data DEFAULT a
    = ExpressionIdentD {default_content::a, default_ident::(Ident a), default_arrayindexelement::(ARRAYINDEXELEMENT a)}
    | ExpressionIntegerD {default_content::a, default_integer::(AbsProgettoPar.Integer a)}
    | ExpressionRealD {default_content::a, default_real::(Real a)}
    | ExpressionStringD {default_content::a, default_string::(AbsProgettoPar.String a)}
    | ExpressionCharD {default_content::a, default_char::(AbsProgettoPar.Char a)}
    | ExpressionBooleanD {default_content::a, default_bool::(Boolean a)}
    | ExpressionBracketD {default_content::a, default_expression::(EXPRESSION a)}
    | ExpressionCallD {default_content::a, default_ident::(Ident a), default_expressions::(EXPRESSIONS a)}
    | ExpressionCastD {default_content::a, default_default::(DEFAULT a), default_primitivetype::(PRIMITIVETYPE a)}
    | ExpressionUnaryD {default_content::a, default_unaryop::(UNARYOP a), default_default::(DEFAULT a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data UNARYOP a
    = UnaryOperationPositive {unaryop_content::a}
    | UnaryOperationNegative {unaryop_content::a}
    | UnaryOperationNot {unaryop_content::a}
    | UnaryOperationPointer {unaryop_content::a}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data BINARYOP a
    = BinaryOperationPlus {binaryop_content::a}
    | BinaryOperationMinus {binaryop_content::a}
    | BinaryOperationProduct {binaryop_content::a}
    | BinaryOperationDivision {binaryop_content::a}
    | BinaryOperationModule {binaryop_content::a}
    | BinaryOperationPower {binaryop_content::a}
    | BinaryOperationAnd {binaryop_content::a}
    | BinaryOperationOr {binaryop_content::a}
    | BinaryOperationEq {binaryop_content::a}
    | BinaryOperationNotEq {binaryop_content::a}
    | BinaryOperationGratherEq {binaryop_content::a}
    | BinaryOperationGrather {binaryop_content::a}
    | BinaryOperationLessEq {binaryop_content::a}
    | BinaryOperationLess {binaryop_content::a}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data LVALUEEXPRESSION a
    = LvalueExpressions {lvalueexpression_content::a, lvalueexpression_ident::(Ident a), lvalueexpression_arrayindexelement::(ARRAYINDEXELEMENT a), lvalueexpression_lvaluexpression::(LVALUEEXPRESSION a)}
    | LvalueExpression  {lvalueexpression_content::a, lvalueexpression_ident::(Ident a), lvalueexpression_arrayindexelement::(ARRAYINDEXELEMENT a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data ARRAYINDEXELEMENT a
    = ArrayIndexElement {arrayindexelement_content::a, arrayindexelement_typeindex::(TYPEINDEX a)}
    | ArrayIndexElements {arrayindexelement_content::a, arrayindexelement_typeindex::(TYPEINDEX a), arrayindexelement_arrayindexelements::(ARRAYINDEXELEMENTS a)}
    | ArrayIndexElementEmpty {arrayindexelement_content::a}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data ARRAYINDEXELEMENTS a
  = ArrayIndexElementsSingle {arrayindexelements_content::a, arrayindexelements_typeindex::(TYPEINDEX a)}
  | ArrayIndexElementsMultiple {arrayindexelements_content::a, arrayindexelements_typeindex::(TYPEINDEX a), arrayindexelements_arrayindexelements::(ARRAYINDEXELEMENTS a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data TYPEINDEX a
    = TypeOfIndexInt {typeindex_content::a, typeindex_typeindex::(TYPEINDEX a), typeindex_integer::(AbsProgettoPar.Integer a)}
    | TypeOfIndexIntSingle {typeindex_content::a, typeindex_integer::(AbsProgettoPar.Integer a)}
    | TypeOfIndexVar {typeindex_content::a, typeindex_typeindex::(TYPEINDEX a), typeindex_ident::(Ident a), typeindex_arrayindexelement::(ARRAYINDEXELEMENT a)}
    | TypeOfIndexVarSingle {typeindex_content::a, typeindex_ident::(Ident a), typeindex_arrayindexelement::(ARRAYINDEXELEMENT a)}
    | TypeOfIndexPointer {typeindex_content::a, typeindex_typeindex::(TYPEINDEX a), typeindex_unaryop::(UNARYOP a), typeindex_default::(DEFAULT a)}
    | TypeOfIndexPointerSingle {typeindex_content::a, typeindex_unaryop::(UNARYOP a), typeindex_default::(DEFAULT a)}
    | TypeOfIndexBinaryPlus {typeindex_content::a, typeindex_typeindex::(TYPEINDEX a), typeindex_expressionf::(EXPRESSION a), typeindex_expressionse::(EXPRESSION a)}
    | TypeOfIndexBinaryPlusSingle {typeindex_content::a, typeindex_expressionf::(EXPRESSION a),typeindex_expressionse::(EXPRESSION a)}
    | TypeOfIndexBinaryMinus {typeindex_content::a, typeindex_typeindex::(TYPEINDEX a), typeindex_expressionf::(EXPRESSION a), typeindex_expressionse::(EXPRESSION a)}
    | TypeOfIndexBinaryMinusSingle {typeindex_content::a, typeindex_expressionf::(EXPRESSION a),typeindex_expressionse::(EXPRESSION a)}
    | TypeOfIndexBinaryProduct {typeindex_content::a, typeindex_typeindex::(TYPEINDEX a), typeindex_expressionf::(EXPRESSION a), typeindex_expressionse::(EXPRESSION a)}
    | TypeOfIndexBinaryProductSingle {typeindex_content::a, typeindex_expressionf::(EXPRESSION a),typeindex_expressionse::(EXPRESSION a)}
    | TypeOfIndexBinaryDivision {typeindex_content::a, typeindex_typeindex::(TYPEINDEX a), typeindex_expressionf::(EXPRESSION a), typeindex_expressionse::(EXPRESSION a)}
    | TypeOfIndexBinaryDivisionSingle {typeindex_content::a, typeindex_expressionf::(EXPRESSION a),typeindex_expressionse::(EXPRESSION a)}
    | TypeOfIndexBinaryModule {typeindex_content::a, typeindex_typeindex::(TYPEINDEX a), typeindex_expressionf::(EXPRESSION a), typeindex_expressionse::(EXPRESSION a)}
    | TypeOfIndexBinaryModuleSingle {typeindex_content::a, typeindex_expressionf::(EXPRESSION a),typeindex_expressionse::(EXPRESSION a)}
    | TypeOfIndexBinaryPower {typeindex_content::a, typeindex_typeindex::(TYPEINDEX a), typeindex_expressionf::(EXPRESSION a), typeindex_expressionse::(EXPRESSION a)}
    | TypeOfIndexBinaryPowerSingle {typeindex_content::a, typeindex_expressionf::(EXPRESSION a),typeindex_expressionse::(EXPRESSION a)}
    | TypeOfIndexExpressionCall {typeindex_content::a, typeindex_typeindex::(TYPEINDEX a), typeindex_ident::(Ident a), typeindex_expressions::(EXPRESSIONS a)}
    | TypeOfIndexExpressionCallSingle {typeindex_content::a, typeindex_ident::(Ident a), typeindex_expressions::(EXPRESSIONS a)}
    | TypeOfIndexExpressionBracket {typeindex_content::a, typeindex_typeindex::(TYPEINDEX a), typeindex_expression::(EXPRESSION a)}
    | TypeOfIndexExpressionBracketSingle {typeindex_content::a, typeindex_expression::(EXPRESSION a)}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Ident a = Ident {valueId::Prelude.String, contentId::a}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Integer a = Integer {valueInt::Prelude.Integer, contentInt::a}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Real a = Real {valueReal::Prelude.Double , contentReal::a}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Char a = Char {valueChar::Prelude.Char, contentChar::a}
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data String a = String {valueString::Prelude.String, contentString::a}
  deriving (C.Eq, C.Ord, C.Show, C.Read)
