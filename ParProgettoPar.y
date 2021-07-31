-- This Happy file was machine-generated by the BNF converter
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module ParProgettoPar
  ( happyError
  , myLexer
  , pS
  ) where

import Prelude

import qualified AbsProgettoPar as Abs
import LexProgettoPar

}

%name pS S
-- no lexer declaration
%monad { Err } { (>>=) } { return }
%tokentype {Token}
%token
  '!' { PT _ (TS _ 1) }
  '!=' { PT _ (TS _ 2) }
  '%' { PT _ (TS _ 3) }
  '%=' { PT _ (TS _ 4) }
  '&&' { PT _ (TS _ 6) }
  '(' { PT _ (TS _ 7) }
  ')' { PT _ (TS _ 8) }
  '*' { PT _ (TS _ 9) }
  '**' { PT _ (TS _ 10) }
  '**=' { PT _ (TS _ 11) }
  '*=' { PT _ (TS _ 12) }
  '+' { PT _ (TS _ 13) }
  '+=' { PT _ (TS _ 14) }
  ',' { PT _ (TS _ 15) }
  '-' { PT _ (TS _ 16) }
  '-=' { PT _ (TS _ 17) }
  '..' { PT _ (TS _ 18) }
  '/' { PT _ (TS _ 19) }
  '/=' { PT _ (TS _ 20) }
  ':' { PT _ (TS _ 21) }
  ';' { PT _ (TS _ 22) }
  '<' { PT _ (TS _ 23) }
  '<=' { PT _ (TS _ 24) }
  '=' { PT _ (TS _ 25) }
  '==' { PT _ (TS _ 26) }
  '>' { PT _ (TS _ 27) }
  '>=' { PT _ (TS _ 28) }
  'False' { PT _ (TS _ 29) }
  'True' { PT _ (TS _ 30) }
  '[' { PT _ (TS _ 31) }
  ']' { PT _ (TS _ 32) }
  'bool' { PT _ (TS _ 33) }
  'break' { PT _ (TS _ 34) }
  'char' { PT _ (TS _ 35) }
  'const' { PT _ (TS _ 36) }
  'continue' { PT _ (TS _ 37) }
  'do' { PT _ (TS _ 38) }
  'else' { PT _ (TS _ 39) }
  'false' { PT _ (TS _ 40) }
  'for' { PT _ (TS _ 41) }
  'function' { PT _ (TS _ 43) }
  'if' { PT _ (TS _ 44) }
  'in' { PT _ (TS _ 45) }
  'int' { PT _ (TS _ 46) }
  'param' { PT _ (TS _ 47) }
  'proc' { PT _ (TS _ 48) }
  'real' { PT _ (TS _ 49) }
  'ref' { PT _ (TS _ 50) }
  'return' { PT _ (TS _ 51) }
  'string' { PT _ (TS _ 52) }
  'then' { PT _ (TS _ 53) }
  'true' { PT _ (TS _ 54) }
  'var' { PT _ (TS _ 55) }
  'void' { PT _ (TS _ 56) }
  'while' { PT _ (TS _ 57) }
  '{' { PT _ (TS _ 58) }
  '||' { PT _ (TS _ 59) }
  '}' { PT _ (TS _ 60) }
  L_Ident  { PT _ (TV _) }
  L_charac { PT _ (TC _) }
  L_doubl  { PT _ (TD _) }
  L_integ  { PT _ (TI _) }
  L_quoted { PT _ (TL _) }

%%

Ident :: { Abs.Ident Posn }
Ident  : L_Ident { Abs.Ident (getTokenContent $1) (tokenPosn $1) }

Char    :: { Abs.Char Posn }
Char     : L_charac { Abs.Char ((read (getTokenContent $1)) :: Prelude.Char  ) (tokenPosn $1) }

Double  :: { Abs.Real Posn }
Double   : L_doubl  { Abs.Real ((read (getTokenContent $1)) :: Prelude.Double  ) (tokenPosn $1) }

Integer :: { Abs.Integer Posn }
Integer  : L_integ  { Abs.Integer ((read (getTokenContent $1)) :: Prelude.Integer ) (tokenPosn $1) }

String  :: { Abs.String  Posn }
String   : L_quoted { Abs.String (getTokenContent $1) (tokenPosn $1) }

Boolean :: { Abs.Boolean Posn }
Boolean : 'true' { Abs.Boolean_true (tokenPosn $1) }
        | 'false' { Abs.Boolean_false (tokenPosn $1) }
        | 'True' { Abs.Boolean_True (tokenPosn $1) }
        | 'False' { Abs.Boolean_False (tokenPosn $1) }

S :: { Abs.S Posn }
S : STATEMENTS { Abs.StartCode (Abs.statements_content $1) $1 }

STATEMENTS :: { Abs.STATEMENTS Posn }
STATEMENTS : STATEMENT STATEMENTS { Abs.ListStatements (Abs.statement_content $1) $1 $2 }
           | {- empty -} { Abs.EmptyStatement (Pn 0 0 0)}

B :: { Abs.B Posn }
B : '{' STATEMENTS '}' { Abs.BlockStatement (Abs.statements_content $2) $2 }

STATEMENT :: { Abs.STATEMENT Posn }
STATEMENT : B { Abs.Statement (Abs.b_content $1) $1 }
          | EXPRESSIONSTATEMENT ';' { Abs.ExpressionStatement (Abs.expressionstatement_content $1) $1 }
          | LVALUEEXPRESSION ASSIGNOP EXPRESSION ';' { Abs.AssignmentStatement (Abs.lvalueexpression_content $1) $1 $2 $3 }
          | CONDITIONALSTATE { Abs.ConditionalStatement (Abs.conditionalstate_content $1) $1 }
          | WHILESTATEMENT { Abs.WhileDoStatement (Abs.whilestatement_content $1) $1 }
          | DOSTATEMENT { Abs.DoWhileStatement (Abs.dostatement_content $1) $1 }
          | FORSTATEMENT { Abs.ForStatement (Abs.forstatement_content $1) $1 }
          | 'break' ';' { Abs.BreakStatement (tokenPosn $1)}
          | 'continue' ';' { Abs.ContinueStatement (tokenPosn $1)}
          | RETURNSTATEMENT ';' { Abs.ReturnStatement  (Abs.returnstatement_content $1) $1 }
          | VARIABLETYPE VARDECLIST ';' { Abs.VariableDeclarationStatement (Abs.variabletype_content $1) $1 $2 }
          | 'proc' Ident '(' PARAMETERS ')' ':' 'void' '{' STATEMENTS '}' { Abs.ProcedureStatement (tokenPosn $1) $2 $4 $9 }
          | 'function' Ident '(' PARAMETERS ')' ':' TYPEEXPRESSION '{' STATEMENTS '}' { Abs.FunctionStatement (tokenPosn $1) $2 $4 $7 $9 }

PARAMETERS :: { Abs.PARAMETERS Posn }
PARAMETERS : PARAMETER ',' PARAMETERS { Abs.ParameterList (Abs.parameter_content $1) $1 $3 }
           | PARAMETER  { Abs.ParameterListSingle (Abs.parameter_content $1) $1 }
           | {- empty -} { Abs.ParameterListEmpty (Pn 0 0 0)}

PARAMETER :: { Abs.PARAMETER Posn }
PARAMETER : Ident ':' PRIMITIVETYPE { Abs.Parameter (Abs.contentId $1) $1 $3 }
PARAMETER : Ident ':' PRIMITIVETYPE POINTER { Abs.ParameterPointer (Abs.contentId $1) $1 $3 $4 }

ASSIGNOP :: { Abs.ASSIGNOP Posn }
ASSIGNOP : '=' { Abs.AssignOperationEq (tokenPosn $1)}
         | '+=' { Abs.AssignOperationEqPlus (tokenPosn $1)}
         | '-=' { Abs.AssignOperationEqMinus (tokenPosn $1)}
         | '*=' { Abs.AssignOperationEqProd (tokenPosn $1)}
         | '/=' { Abs.AssignOperationEqFract (tokenPosn $1)}
         | '%=' { Abs.AssignOperationEqPercent (tokenPosn $1)}
         | '**=' { Abs.AssignOperationEqPower (tokenPosn $1)}

VARIABLETYPE :: { Abs.VARIABLETYPE Posn }
VARIABLETYPE : 'param' { Abs.VariableTypeParam (tokenPosn $1)}
             | 'const' { Abs.VariableTypeConst (tokenPosn $1)}
             | 'var' { Abs.VariableTypeVar (tokenPosn $1)}
             | 'ref' { Abs.VariableTypeRef (tokenPosn $1)}
             | 'const' 'ref' { Abs.VariableTypeConstRef (tokenPosn $1)}

VARDECLIST :: { Abs.VARDECLIST Posn }
VARDECLIST : VARDECID { Abs.VariableDeclarationSingle (Abs.vardecid_content $1) $1 }

VARDECID :: { Abs.VARDECID Posn }
VARDECID : IDENTLIST TYPEPART INITPART { Abs.VariableDeclaration (Abs.identlist_content $1) $1 $2 $3 }

IDENTLIST :: { Abs.IDENTLIST Posn }
IDENTLIST : Ident ',' IDENTLIST { Abs.IdentifierList (Abs.contentId $1) $1 $3 }
          | Ident { Abs.IdentifierSingle (Abs.contentId $1) $1 }

TYPEPART :: { Abs.TYPEPART Posn }
TYPEPART : ':' TYPEEXPRESSION { Abs.TypePart (tokenPosn $1) $2 }

INITPART :: { Abs.INITPART Posn }
INITPART : '=' EXPRESSION { Abs.InitializzationPart (tokenPosn $1) $2 }
         | '=' ARRAYINIT { Abs.InitializzationPartArray (tokenPosn $1) $2 }
         | {- empty -} { Abs.InitializzationPartEmpty (Pn 0 0 0)}

ARRAYINIT :: { Abs.ARRAYINIT Posn}
          : '[' ARRAYINIT ']' {Abs.ArrayInitSingle (tokenPosn $1) $2 }
          | '[' ARRAYINIT ',' ARRAYINIT ']' {Abs.ArrayInit (tokenPosn $1) $2 $4}
          | '['LISTELEMENTARRAY ']' {Abs.ArrayInitSingleElems (tokenPosn $1) $2 }
          | '['LISTELEMENTARRAY ']' ',' ARRAYINIT {Abs.ArrayInitElems (tokenPosn $1) $2 $5}
     
LISTELEMENTARRAY :: { Abs.LISTELEMENTARRAY Posn }
LISTELEMENTARRAY : EXPRESSION ',' LISTELEMENTARRAY { Abs.ListElementsOfArray (Abs.expression_content $1) $1 $3 }
                 | EXPRESSION { Abs.ListElementOfArray (Abs.expression_content $1) $1 }

TYPEEXPRESSION :: { Abs.TYPEEXPRESSION Posn }
TYPEEXPRESSION : PRIMITIVETYPE { Abs.TypeExpression (Abs.primitivetype_content $1) $1 }
               | '[' RANGEEXP ']' TYPEEXPRESSION { Abs.TypeExpressionArraySimple (tokenPosn $1) $2 $4 }
               | '[' '{' RANGEEXP '}' ']' TYPEEXPRESSION { Abs.TypeExpressionArray (tokenPosn $1) $3 $6 }
               | PRIMITIVETYPE POINTER { Abs.TypeExpressionPointer (Abs.primitivetype_content $1) $1 $2 }
               | '*' '[' ']' TYPEEXPRESSION { Abs.TypeExpressionArrayOfPointer (tokenPosn $1) $4 }
               | '(' TYPEEXPRESSION ')' POINTER { Abs.TypeExpressionPointerOfArray (tokenPosn $1) $2 $4 }

POINTER :: { Abs.POINTER Posn }
POINTER : POINTER '*' { Abs.PointerSymbol (Abs.pointer_content $1) $1 }
        | '*' { Abs.PointerSymbolSingle (tokenPosn $1)}

RANGEEXP :: { Abs.RANGEEXP Posn }
RANGEEXP : EXPRESSION '..' EXPRESSION ',' RANGEEXP { Abs.RangeExpression (Abs.expression_content $1) $1 $3 $5 }
         | EXPRESSION '..' EXPRESSION { Abs.RangeExpressionSingle (Abs.expression_content $1) $1 $3 }

PRIMITIVETYPE :: { Abs.PRIMITIVETYPE Posn } 
PRIMITIVETYPE : 'void' { Abs.PrimitiveTypeVoid (tokenPosn $1)}
              | 'bool' { Abs.PrimitiveTypeBool (tokenPosn $1)}
              | 'int' { Abs.PrimitiveTypeInt (tokenPosn $1)}
              | 'real' { Abs.PrimitiveTypeReal (tokenPosn $1)}
              | 'string' { Abs.PrimitiveTypeString (tokenPosn $1)}
              | 'char' { Abs.PrimitiveTypeChar (tokenPosn $1)}
              | '[' ']' PRIMITIVETYPE { Abs.TypeArray (tokenPosn $1) $3}
              
CONDITIONALSTATE :: { Abs.CONDITIONALSTATE Posn }
CONDITIONALSTATE : 'if' EXPRESSION 'then' STATEMENT ELSESTATEMENT { Abs.ConditionalStatementSimpleThen (tokenPosn $1) $2 $4 $5 }
                 | 'if' EXPRESSION B ELSESTATEMENT { Abs.ConditionalStatementSimpleWThen (tokenPosn $1) $2 $3 $4 }
                 | 'if' CTRLDECSTATEMENT 'then' STATEMENT ELSESTATEMENT { Abs.ConditionalStatementCtrlThen (tokenPosn $1) $2 $4 $5 }
                 | 'if' CTRLDECSTATEMENT B ELSESTATEMENT { Abs.ConditionalStatementCtrlWThen (tokenPosn $1) $2 $3 $4 }

WHILESTATEMENT :: { Abs.WHILESTATEMENT Posn }
WHILESTATEMENT : 'while' EXPRESSION 'do' STATEMENT { Abs.WhileStateSimpleDo (tokenPosn $1) $2 $4 }
               | 'while' EXPRESSION B { Abs.WhileStateSimpleWDo (tokenPosn $1) $2 $3 }
               | 'while' CTRLDECSTATEMENT 'do' STATEMENT { Abs.WhileStateCtrlDo (tokenPosn $1) $2 $4 }
               | 'while' CTRLDECSTATEMENT B { Abs.WhileStateCtrlWDo (tokenPosn $1) $2 $3 }

DOSTATEMENT :: { Abs.DOSTATEMENT Posn }
DOSTATEMENT : 'do' STATEMENT 'while' EXPRESSION ';' { Abs.DoWhileState (tokenPosn $1) $2 $4 }

FORSTATEMENT :: { Abs.FORSTATEMENT Posn }
FORSTATEMENT : 'for' INDEXVARDEC 'in' RANGEEXP 'do' STATEMENT { Abs.ForStateIndexDo (tokenPosn $1) $2 $4 $6 }
             | 'for' INDEXVARDEC 'in' RANGEEXP B { Abs.ForStateIndexWDo (tokenPosn $1) $2 $4 $5 }
             | 'for' RANGEEXP 'do' STATEMENT { Abs.ForStateExprDo (tokenPosn $1) $2 $4 }
             | 'for' RANGEEXP B { Abs.ForStateExprWDo (tokenPosn $1) $2 $3 }

INDEXVARDEC :: { Abs.INDEXVARDEC Posn }
INDEXVARDEC : Ident { Abs.IndexVarDeclaration (Abs.contentId $1) $1 }

ELSESTATEMENT :: { Abs.ELSESTATEMENT Posn }
ELSESTATEMENT : {- empty -} { Abs.ElseStateEmpty (Pn 0 0 0)}
              | 'else' STATEMENT { Abs.ElseState (tokenPosn $1) $2 }

RETURNSTATEMENT :: { Abs.RETURNSTATEMENT Posn }
RETURNSTATEMENT : 'return' EXPRESSION { Abs.ReturnState (tokenPosn $1) $2 }
                | 'return' { Abs.ReturnStateEmpty (tokenPosn $1)}

CTRLDECSTATEMENT :: { Abs.CTRLDECSTATEMENT Posn }
CTRLDECSTATEMENT : 'var' Ident TYPEPART '=' EXPRESSION { Abs.CtrlDecStateVar (tokenPosn $1) $2 $3 $5 }
                 | 'const' Ident TYPEPART'=' EXPRESSION { Abs.CtrlDecStateConst (tokenPosn $1) $2 $3 $5 }

EXPRESSIONSTATEMENT :: { Abs.EXPRESSIONSTATEMENT Posn }
EXPRESSIONSTATEMENT : Ident { Abs.VariableExpression (Abs.contentId $1) $1 }
                    | CALLEXPRESSION { Abs.CallExpression (Abs.callexpression_content $1) $1 }
                    
CALLEXPRESSION :: { Abs.CALLEXPRESSION Posn }
CALLEXPRESSION : Ident '(' NAMEDEXPRESSIONLIST ')' { Abs.CallExpressionParentheses (Abs.contentId $1) $1 $3 }

NAMEDEXPRESSIONLIST :: { Abs.NAMEDEXPRESSIONLIST Posn }
NAMEDEXPRESSIONLIST : NAMEDEXPRESSION { Abs.NamedExpressionList (Abs.namedexpression_content $1) $1 }
                    | {- empty -} { Abs.NamedExpressionListEmpty (Pn 0 0 0) }
                    | NAMEDEXPRESSION ',' NAMEDEXPRESSIONLIST { Abs.NamedExpressionLists (Abs.namedexpression_content $1) $1 $3 }

NAMEDEXPRESSION :: { Abs.NAMEDEXPRESSION Posn }
NAMEDEXPRESSION : EXPRESSION { Abs.NamedExpression (Abs.expression_content $1) $1 }

EXPRESSIONS :: {Abs.EXPRESSIONS Posn}
EXPRESSIONS : EXPRESSION ',' EXPRESSIONS { Abs.Expressions (Abs.expression_content $1) $1 $3 }
            | EXPRESSION  { Abs.Expression (Abs.expression_content $1) $1 }
            | {- empty -} {Abs.ExpressionEmpty (Pn 0 0 0) }

EXPRESSION :: { Abs.EXPRESSION Posn }
EXPRESSION : Ident ARRAYINDEXELEMENT { Abs.ExpressionIdent (Abs.contentId $1) $1 $2 }
           | Integer { Abs.ExpressionInteger (Abs.contentInt $1) $1 }
           | Double { Abs.ExpressionReal (Abs.contentReal $1) $1 }
           | String { Abs.ExpressionString (Abs.contentString $1) $1 }
           | Char { Abs.ExpressionChar (Abs.contentChar $1) $1}
           | Boolean { Abs.ExpressionBoolean (Abs.contentBoolean $1) $1 }
           | DEFAULT BINARYOP EXPRESSION { Abs.ExpressionBinary (Abs.default_content $1) $1 $2 $3 }
           | UNARYOP DEFAULT { Abs.ExpressionUnary (Abs.unaryop_content $1) $1 $2 }
           | DEFAULT ':' PRIMITIVETYPE { Abs.ExpressionCast (Abs.default_content $1) $1 $3 }
           | '(' EXPRESSION ')' { Abs.ExpressionBracket (tokenPosn $1) $2 }
           | Ident '(' EXPRESSIONS ')' { Abs.ExpressionCall (Abs.contentId $1) $1 $3 }
           
DEFAULT :: { Abs.DEFAULT Posn }
DEFAULT : Ident ARRAYINDEXELEMENT { Abs.ExpressionIdentD (Abs.contentId $1) $1 $2 }
        | Integer { Abs.ExpressionIntegerD (Abs.contentInt $1) $1 }
        | Double { Abs.ExpressionRealD (Abs.contentReal $1) $1 }
        | String { Abs.ExpressionStringD (Abs.contentString $1) $1 }
        | Char { Abs.ExpressionCharD (Abs.contentChar $1) $1 }
        | Boolean { Abs.ExpressionBooleanD (Abs.contentBoolean $1) $1 }
        | '(' EXPRESSION ')' { Abs.ExpressionBracketD (tokenPosn $1) $2 }
        | Ident '(' EXPRESSIONS ')' { Abs.ExpressionCallD (Abs.contentId $1) $1 $3 }
        | DEFAULT ':' PRIMITIVETYPE { Abs.ExpressionCastD (Abs.default_content $1) $1 $3 }
        | UNARYOP DEFAULT { Abs.ExpressionUnaryD (Abs.unaryop_content $1) $1 $2 }

UNARYOP :: { Abs.UNARYOP Posn }
UNARYOP : '+' { Abs.UnaryOperationPositive (tokenPosn $1)}
        | '-' { Abs.UnaryOperationNegative (tokenPosn $1)}
        | '!' { Abs.UnaryOperationNot (tokenPosn $1)}
        | '*' { Abs.UnaryOperationPointer (tokenPosn $1)}

BINARYOP :: { Abs.BINARYOP Posn}
BINARYOP : '+' { Abs.BinaryOperationPlus (tokenPosn $1)}
         | '-' { Abs.BinaryOperationMinus (tokenPosn $1)}
         | '*' { Abs.BinaryOperationProduct (tokenPosn $1)}
         | '/' { Abs.BinaryOperationDivision (tokenPosn $1)}
         | '%' { Abs.BinaryOperationModule (tokenPosn $1)}
         | '**' { Abs.BinaryOperationPower (tokenPosn $1)}
         | '&&' { Abs.BinaryOperationAnd (tokenPosn $1)}
         | '||' { Abs.BinaryOperationOr (tokenPosn $1)}
         | '==' { Abs.BinaryOperationEq (tokenPosn $1)}
         | '!=' { Abs.BinaryOperationNotEq (tokenPosn $1)}
         | '>=' { Abs.BinaryOperationGratherEq (tokenPosn $1)}
         | '>' { Abs.BinaryOperationGrather (tokenPosn $1)}
         | '<=' { Abs.BinaryOperationLessEq (tokenPosn $1)}
         | '<' { Abs.BinaryOperationLess (tokenPosn $1)}

LVALUEEXPRESSION :: { Abs.LVALUEEXPRESSION Posn }
LVALUEEXPRESSION : Ident ARRAYINDEXELEMENT ',' LVALUEEXPRESSION { Abs.LvalueExpressions (Abs.contentId $1) $1 $2 $4 }
                 | Ident ARRAYINDEXELEMENT { Abs.LvalueExpression (Abs.contentId $1) $1 $2 }

ARRAYINDEXELEMENT :: { Abs.ARRAYINDEXELEMENT Posn }
ARRAYINDEXELEMENT : '[' TYPEINDEX ']' { Abs.ArrayIndexElement (tokenPosn $1) $2 }
                  | '[' TYPEINDEX ']' ARRAYINDEXELEMENTS {Abs.ArrayIndexElements (tokenPosn $1) $2 $4}
                  | {- empty -} { Abs.ArrayIndexElementEmpty (Pn 0 0 0)}

ARRAYINDEXELEMENTS :: { Abs.ARRAYINDEXELEMENTS Posn }
ARRAYINDEXELEMENTS : '[' TYPEINDEX ']' { Abs.ArrayIndexElementsSingle (tokenPosn $1) $2 }
                   | '[' TYPEINDEX ']'ARRAYINDEXELEMENTS { Abs.ArrayIndexElementsMultiple (tokenPosn $1) $2 $4}


TYPEINDEX :: { Abs.TYPEINDEX Posn }
TYPEINDEX : TYPEINDEX ',' Integer { Abs.TypeOfIndexInt (Abs.typeindex_content $1) $1 $3 }
          | Integer { Abs.TypeOfIndexIntSingle (Abs.contentInt $1) $1 }
          | TYPEINDEX ',' Ident ARRAYINDEXELEMENT { Abs.TypeOfIndexVar (Abs.typeindex_content $1) $1 $3 $4 }
          | Ident ARRAYINDEXELEMENT { Abs.TypeOfIndexVarSingle (Abs.contentId $1) $1 $2 }
          | TYPEINDEX ',' UNARYOP DEFAULT {Abs.TypeOfIndexPointer (Abs.typeindex_content $1) $1 $3 $4}
          | UNARYOP DEFAULT {Abs.TypeOfIndexPointerSingle (Abs.unaryop_content $1) $1 $2}
          | TYPEINDEX ',' DEFAULT BINARYOP EXPRESSION {Abs.TypeOfIndexBinary (Abs.typeindex_content $1) $1 $3 $4 $5}
          | DEFAULT BINARYOP EXPRESSION {Abs.TypeOfIndexBinarySingle (Abs.default_content $1) $1 $2 $3}
          | TYPEINDEX ',' Ident '(' EXPRESSIONS ')' {Abs.TypeOfIndexExpressionCall (Abs.typeindex_content $1) $1 $3 $5}
          | Ident '(' EXPRESSIONS ')' {Abs.TypeOfIndexExpressionCallSingle (Abs.contentId $1) $1 $3}
          | TYPEINDEX ',' '(' EXPRESSION ')' {Abs.TypeOfIndexExpressionBracket (Abs.typeindex_content $1) $1 $4}
          | '(' EXPRESSION ')' {Abs.TypeOfIndexExpressionBracketSingle (tokenPosn $1) $2}
          
{

type Err = Either String

happyError :: [Token] -> Err a
happyError ts = Left $
  "syntax error at " ++ tokenPos ts ++
  case ts of
    []      -> []
    [Err _] -> " due to lexer error"
    t:_     -> " before `" ++ (prToken t) ++ "'"

myLexer :: String -> [Token]
myLexer = tokens

getTokenContent (PT _ (TV s)) = s
getTokenContent (PT _ (TI s)) = s
getTokenContent (PT _ (TC s)) = s
getTokenContent (PT _ (TL s)) = s
getTokenContent (PT _ (TD s)) = s

}

