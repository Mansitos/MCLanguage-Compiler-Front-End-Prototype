{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module TypeChecker where

import Type
import LexProgettoPar (Posn(..))
import AbsProgettoPar as Abs
import Data.Map
import Prelude

type Env = Map Prelude.String [EnvEntry]
            -- chiave, valore

data EnvEntry
    = Variable {varType::Type, varPosition::LexProgettoPar.Posn, varConstat::Bool}
    | Function {funType::Type, funPosition::LexProgettoPar.Posn, funParameters::[Parameter]}
    deriving (Show)

data Parameter
    = Parameter {paramType::Type, paramPosition::LexProgettoPar.Posn}
    deriving(Eq, Ord, Show)

data TCheckResult
    = TResult {environment::Env, t_type::Type, t_position::LexProgettoPar.Posn}
    | TError {errors::[Prelude.String]}
    deriving (Show)

getTypeEnvEntry :: [EnvEntry] -> Type
getTypeEnvEntry [] = B_type Type_Void
getTypeEnvEntry (x:xs) = case x of 
                            (Variable t pos const) -> t
                            (Function t pos parameters) -> t
                            _ -> B_type Type_Void

first :: (Env,[Prelude.String]) -> Env
first (f,s) = f

second :: (Env,[Prelude.String]) -> [Prelude.String]
second (f,s) = s

updateEnv :: (Abs.STATEMENTS Posn) -> Env -> [Prelude.String] -> (Env,[Prelude.String])
updateEnv node@(Abs.ListStatements pos stat stats) env err = case stat of
                                                                Abs.ReturnStatement pos ret-> (insertWith (++) "return" [Variable (B_type Type_Void) (Pn 0 1 1) False] env,err ++ checkErr env stat)
                                                                Abs.ExpressionStatement pos exp -> case exp of
                                                                                                    Abs.VariableExpression pos (Abs.Ident id posId) -> (insertWith (++) id [Variable (B_type Type_Real) (Pn 0 1 1) False] env,err ++ checkErr env stat)
                                                                                                    _ -> (env,err)
                                                                _ -> (env,err)
updateEnv node@(Abs.EmptyStatement  pos) env err = (env,err)

checkErr :: Env -> Abs.STATEMENT Posn -> [Prelude.String]
checkErr env stat = []                    

--------------------------------------
-- MAIN FUNCTIONS FOR TYPE CHECKING --
--------------------------------------

-- Funzioni da implementare:

-- a subtype di b? -> bool
-- a compatibile con b -> bool

-- Input: The entire Abstree + starting env
-- Output: Type-checking result of the program
executeTypeChecking :: Abs.S Posn -> Env -> Abs.S TCheckResult
executeTypeChecking node@(Abs.StartCode _ statements) start_env = Abs.StartCode (checkTypeStatements node start_env) (executeStatements statements start_env)

executeStatements :: Abs.STATEMENTS Posn -> Env -> Abs.STATEMENTS TCheckResult                     
executeStatements node@(Abs.ListStatements _ stat stats) env = let newEnv = updateEnv node env [] in 
                                                                Abs.ListStatements (checkTypeStatement stat env) (executeStatement stat env) (executeStatements stats (first newEnv))
executeStatements node@(Abs.EmptyStatement _) env = Abs.EmptyStatement (checkEmptyStatement node env)

executeStatement :: Abs.STATEMENT Posn -> Env -> Abs.STATEMENT TCheckResult
executeStatement node@(Abs.BreakStatement _) env = Abs.BreakStatement (checkTypeBreakStatement node env)
executeStatement node@(Abs.ContinueStatement _) env = Abs.ContinueStatement (checkTypeContinueStatement node env)
executeStatement node@(Abs.ReturnStatement _ ret) env = Abs.ReturnStatement (checkTypeReturnStatement node env) (executeReturnStatement ret env)
executeStatement node@(Abs.Statement _ b) env = Abs.Statement (checkTypeStatement node env) (executeB b env)
executeStatement node@(Abs.ExpressionStatement _ exp) env = Abs.ExpressionStatement (checkTypeStatement node env) (executeExpressionStatement exp env)
executeStatement node@(Abs.AssignmentStatement pos lval assignOp exp) env = Abs.AssignmentStatement (checkTypeStatement node env) (executeLValue lval env) (executeAssignOp assignOp env) (executeExpression exp env)
executeStatement node@(Abs.VariableDeclarationStatement pos tipo vardec) env = Abs.VariableDeclarationStatement (checkTypeStatement node env) (executeType tipo env) (executeVarDec vardec env)

executeType :: Abs.VARIABLETYPE Posn -> Env -> Abs.VARIABLETYPE TCheckResult
executeType node@(Abs.VariableTypeParam pos) env = Abs.VariableTypeParam (checkTypeType node env)
executeType node@(Abs.VariableTypeConst pos) env = Abs.VariableTypeConst (checkTypeType node env)
executeType node@(Abs.VariableTypeVar pos) env = Abs.VariableTypeVar (checkTypeType node env)
executeType node@(Abs.VariableTypeRef pos) env = Abs.VariableTypeRef (checkTypeType node env)
executeType node@(Abs.VariableTypeConstRef pos) env = Abs.VariableTypeConstRef (checkTypeType node env)

executeVarDec :: Abs.VARDECLIST Posn -> Env -> Abs.VARDECLIST TCheckResult
executeVarDec node@(Abs.VariableDeclarationSingle pos vardec) env = Abs.VariableDeclarationSingle (checkTypeVardec node env) (executeVardecID vardec env)

executeVardecID :: Abs.VARDECID Posn -> Env -> Abs.VARDECID TCheckResult
executeVardecID node@(Abs.VariableDeclaration pos idlist tipo init) env = Abs.VariableDeclaration (checkTypeVariableDec node env) (executeIDList idlist env) (executeTipoDec tipo env) (executeInit init env)

executeIDList :: Abs.IDENTLIST Posn -> Env -> Abs.IDENTLIST TCheckResult
executeIDList node@(Abs.IdentifierList pos id next) env = Abs.IdentifierList (checkIdentifierList node env) (executeIdent id env) (executeIDList next env)

executeTipoDec :: Abs.TYPEPART Posn -> Env -> Abs.TYPEPART TCheckResult
executeTipoDec node@(Abs.TypePart pos tipo) env = Abs.TypePart (checkTypeTypePart node env) (executeTipoPart tipo env)

executeInit :: Abs.INITPART Posn -> Env -> Abs.INITPART TCheckResult
executeInit node@(Abs.InitializzationPart pos initExp) env = Abs.InitializzationPart (checkTypeInitializzationPart node env) (executeExpression initExp env) --aggiungere array ed empty

--executeTipoPart :: Abs.

executeB :: Abs.B Posn -> Env -> Abs.B TCheckResult
executeB node@(Abs.BlockStatement pos statements) env = let newEnv = updateEnv statements env [] in 
                                                                 Abs.BlockStatement (checkTypeB node env) (executeStatements statements (first newEnv))

executeReturnStatement :: Abs.RETURNSTATEMENT Posn -> Env -> Abs.RETURNSTATEMENT TCheckResult
executeReturnStatement node@(Abs.ReturnState _ retExp) env = Abs.ReturnState (checkTypeReturnState node env) (executeExpression retExp env)
executeReturnStatement node@(Abs.ReturnStateEmpty _ ) env = Abs.ReturnStateEmpty (checkTypeReturnState node env)

executeExpressionStatement :: Abs.EXPRESSIONSTATEMENT Posn -> Env -> Abs.EXPRESSIONSTATEMENT TCheckResult
executeExpressionStatement node@(Abs.VariableExpression _ id) env = Abs.VariableExpression (checkTypeExpressionStatement node env) (executeIdent id env)

executeExpression :: Abs.EXPRESSION Posn -> Env -> Abs.EXPRESSION TCheckResult
executeExpression node@(Abs.ExpressionInteger pos value) env = Abs.ExpressionInteger (checkTypeExpresion node env) (executeInteger value env)
executeExpression node@(Abs.ExpressionBoolean pos value) env = Abs.ExpressionBoolean (checkTypeExpresion node env) (executeBoolean value env)
executeExpression node@(Abs.ExpressionChar pos value) env = Abs.ExpressionChar (checkTypeExpresion node env) (executeChar value env)
executeExpression node@(Abs.ExpressionString pos value) env = Abs.ExpressionString (checkTypeExpresion node env) (executeString value env)
executeExpression node@(Abs.ExpressionReal pos value) env = Abs.ExpressionReal (checkTypeExpresion node env) (executeReal value env)
executeExpression node@(Abs.ExpressionIdent pos id index) env = case index of
                                                                Abs.ArrayIndexElementEmpty posIdx -> Abs.ExpressionIdent (checkTypeIdent id env) (executeIdent id env) (executeArrayIndexElement (Abs.ArrayIndexElementEmpty posIdx) env)
                                                                Abs.ArrayIndexElement posIdx tipo -> Abs.ExpressionIdent (checkTypeIdent id env) (executeIdent id env) (Abs.ArrayIndexElementEmpty (TError ["index si"]))

executeLValue :: Abs.LVALUEEXPRESSION Posn -> Env -> Abs.LVALUEEXPRESSION TCheckResult
executeLValue node@(Abs.LvalueExpression pos id ident) env = case ident of
                                                            Abs.ArrayIndexElementEmpty posIdx -> Abs.LvalueExpression (checkTypeLvalueExpression node env) (executeIdent id env) (executeArrayIndexElement (Abs.ArrayIndexElementEmpty posIdx) env)
                                                            Abs.ArrayIndexElement posIdx tipo -> Abs.LvalueExpression (checkTypeLvalueExpression node env) (executeIdent id env) (Abs.ArrayIndexElementEmpty (TError ["index si"]))
executeLValue node@(Abs.LvalueExpressions pos id ident next) env = case ident of
                                                            Abs.ArrayIndexElementEmpty posIdx -> Abs.LvalueExpressions (checkTypeLvalueExpression node env) (executeIdent id env) (executeArrayIndexElement (Abs.ArrayIndexElementEmpty posIdx) env) (executeLValue next env)--aggiungere let newEnv
                                                            Abs.ArrayIndexElement posIdx tipo -> Abs.LvalueExpressions (checkTypeLvalueExpression node env) (executeIdent id env) (Abs.ArrayIndexElementEmpty (TError ["index si"]))  (executeLValue next env)                --aggiungere let newEnv
                                                                                                
executeAssignOp :: Abs.ASSIGNOP Posn -> Env -> Abs.ASSIGNOP TCheckResult
executeAssignOp node@(Abs.AssignOperationEq pos) env = Abs.AssignOperationEq (TResult env (B_type Type_Void) pos)
executeAssignOp node@(Abs.AssignOperationEqPlus pos) env = Abs.AssignOperationEqPlus (TResult env (B_type Type_Void) pos)
executeAssignOp node@(Abs.AssignOperationEqMinus pos) env = Abs.AssignOperationEqMinus (TResult env (B_type Type_Void) pos)
executeAssignOp node@(Abs.AssignOperationEqProd pos) env = Abs.AssignOperationEqProd (TResult env (B_type Type_Void) pos)
executeAssignOp node@(Abs.AssignOperationEqPercent pos) env = Abs.AssignOperationEqPercent (TResult env (B_type Type_Void) pos)
executeAssignOp node@(Abs.AssignOperationEqPower pos) env = Abs.AssignOperationEqPower (TResult env (B_type Type_Void) pos)

executeArrayIndexElement :: Abs.ARRAYINDEXELEMENT Posn -> Env -> Abs.ARRAYINDEXELEMENT TCheckResult
executeArrayIndexElement node@(Abs.ArrayIndexElementEmpty pos) env = Abs.ArrayIndexElementEmpty (checkArrayIndexElementEmpty node env)

executeIdent :: Abs.Ident Posn -> Env -> Abs.Ident TCheckResult
executeIdent node@(Abs.Ident id pos) env = Abs.Ident id (checkTypeIdent node env)

executeInteger :: Abs.Integer Posn -> Env -> Abs.Integer TCheckResult
executeInteger node@(Abs.Integer value pos) env = Abs.Integer value (TResult env (B_type Type_Integer ) pos)

executeChar :: Abs.Char Posn -> Env -> Abs.Char TCheckResult
executeChar node@(Abs.Char value pos) env = Abs.Char value (TResult env (B_type Type_Char ) pos)

executeString :: Abs.String Posn -> Env -> Abs.String TCheckResult
executeString node@(Abs.String value pos) env = Abs.String value (TResult env (B_type Type_String ) pos)

executeReal :: Abs.Real Posn -> Env -> Abs.Real TCheckResult
executeReal node@(Abs.Real value pos) env = Abs.Real value (TResult env (B_type Type_Real ) pos)

executeBoolean :: Abs.Boolean Posn -> Env -> Abs.Boolean TCheckResult
executeBoolean node@(Abs.Boolean_true pos) env = Abs.Boolean_true (TResult env (B_type Type_Boolean ) pos)
executeBoolean node@(Abs.Boolean_True pos) env = Abs.Boolean_True (TResult env (B_type Type_Boolean ) pos)
executeBoolean node@(Abs.Boolean_false pos) env = Abs.Boolean_false (TResult env (B_type Type_Boolean ) pos)
executeBoolean node@(Abs.Boolean_False pos) env = Abs.Boolean_False (TResult env (B_type Type_Boolean ) pos)

checkTypeStatements:: Abs.S Posn -> Env -> TCheckResult
checkTypeStatements (Abs.StartCode _ statements) start_env = case statements of
                                                                (Abs.EmptyStatement pos) -> checkEmptyStatement (Abs.EmptyStatement pos) start_env
                                                                (Abs.ListStatements pos stat stats) -> checkTypeStatement stat start_env

checkEmptyStatement :: Abs.STATEMENTS Posn -> Env -> TCheckResult
checkEmptyStatement (Abs.EmptyStatement pos) env = TResult env (B_type Type_Void) pos

checkTypeLvalueExpression :: Abs.LVALUEEXPRESSION Posn -> Env -> TCheckResult
checkTypeLvalueExpression node@(Abs.LvalueExpression pos id index) env = checkTypeIdent id env --da rivedere e modificare
checkTypeLvalueExpression node@(Abs.LvalueExpressions pos id index next) env = checkTypeIdent id env --da rivedere e modificare e gestire next

checkArrayIndexElementEmpty :: Abs.ARRAYINDEXELEMENT Posn -> Env -> TCheckResult
checkArrayIndexElementEmpty node@(Abs.ArrayIndexElementEmpty pos) env = TResult env (B_type Type_Void) pos --da rivedere

checkTypeStatement :: Abs.STATEMENT Posn -> Env -> TCheckResult
checkTypeStatement node@(Abs.BreakStatement pos) env = checkTypeBreakStatement node env
checkTypeStatement node@(Abs.ContinueStatement pos) env = checkTypeContinueStatement node env
checkTypeStatement node@(Abs.ReturnStatement pos ret) env = checkTypeReturnStatement node env
checkTypeStatement node@(Abs.Statement pos b) env = checkTypeB b env
checkTypeStatement node@(Abs.ExpressionStatement pos exp) env = checkTypeExpressionStatement exp env
checkTypeStatement node@(Abs.AssignmentStatement pos lval assignOp exp) env = checkTypeExpresion exp env --aggiungere controllo compatibilità lval con exp
checkTypeStatement node@(Abs.VariableDeclarationStatement pos tipo vardec) env = checkTypeType tipo env

checkTypeType :: Abs.VARIABLETYPE Posn -> Env -> TCheckResult
checkTypeType node@(Abs.VariableTypeParam pos) env = TResult env (B_type Type_Void) pos
checkTypeType node@(Abs.VariableTypeConst pos) env = TResult env (B_type Type_Void) pos
checkTypeType node@(Abs.VariableTypeVar pos) env = TResult env (B_type Type_Void) pos
checkTypeType node@(Abs.VariableTypeRef pos) env = TResult env (B_type Type_Void) pos
checkTypeType node@(Abs.VariableTypeConstRef pos) env = TResult env (B_type Type_Void) pos

checkTypeB :: Abs.B Posn -> Env -> TCheckResult
checkTypeB node@(Abs.BlockStatement pos statements) env = case statements of
                                                    (Abs.EmptyStatement pos) -> checkEmptyStatement (Abs.EmptyStatement pos) env
                                                    (Abs.ListStatements pos stat stats) -> checkTypeStatement stat env

checkTypeBreakStatement :: Abs.STATEMENT Posn -> Env -> TCheckResult
checkTypeBreakStatement (Abs.BreakStatement pos) env = case Data.Map.lookup "while" env of
    Just result -> TResult env (B_type Type_Void) pos
    Nothing -> TError ["Unexpected break statement at " ++ (show pos)]

checkTypeContinueStatement :: Abs.STATEMENT Posn -> Env -> TCheckResult
checkTypeContinueStatement (Abs.ContinueStatement pos) env = case Data.Map.lookup "while" env of
    Just result -> TResult env (B_type Type_Void) pos
    Nothing -> TError ["Unexpected continue statement at " ++ (show pos)]

checkTypeReturnStatement :: Abs.STATEMENT Posn -> Env -> TCheckResult
checkTypeReturnStatement node@(Abs.ReturnStatement pos ret) env = checkTypeReturnState ret env

checkTypeReturnState :: Abs.RETURNSTATEMENT Posn -> Env -> TCheckResult
checkTypeReturnState node@(Abs.ReturnState pos retExp) env = case Data.Map.lookup "return" env of
    Just result -> checkTypeExpresion retExp env
    Nothing -> TError ["Unexpected return at " ++ (show pos)]
checkTypeReturnState node@(Abs.ReturnStateEmpty pos ) env = case Data.Map.lookup "return" env of
    Just result -> TResult env (B_type Type_Void) pos
    Nothing -> TError ["Unexpected return at " ++ (show pos)]

checkTypeExpressionStatement :: Abs.EXPRESSIONSTATEMENT Posn -> Env -> TCheckResult
checkTypeExpressionStatement node@(Abs.VariableExpression pos id) env = checkTypeIdent id env

checkTypeExpresion :: Abs.EXPRESSION Posn -> Env -> TCheckResult
checkTypeExpresion node@(Abs.ExpressionInteger pos value) env = checkTypeInteger value env
checkTypeExpresion node@(Abs.ExpressionBoolean pos value) env = checkTypeBoolean value env
checkTypeExpresion node@(Abs.ExpressionChar pos value) env = checkTypeChar value env
checkTypeExpresion node@(Abs.ExpressionString pos value) env = checkTypeString value env
checkTypeExpresion node@(Abs.ExpressionReal pos value) env = checkTypeReal value env
checkTypeExpresion node@(Abs.ExpressionIdent pos value index) env = checkTypeIdent value env --gestire index

checkTypeIdent :: Abs.Ident Posn -> Env -> TCheckResult
checkTypeIdent node@(Abs.Ident id pos) env = case Data.Map.lookup id env of
    Just ident -> TResult env (getTypeEnvEntry ident) pos
    Nothing -> TError ["Unexpected ident at " ++ (show pos)]
    
checkTypeInteger :: Abs.Integer Posn -> Env -> TCheckResult
checkTypeInteger node@(Abs.Integer value pos) env = TResult env (B_type Type_Integer ) pos

checkTypeChar :: Abs.Char Posn -> Env -> TCheckResult
checkTypeChar node@(Abs.Char value pos) env = TResult env (B_type Type_Char ) pos

checkTypeString :: Abs.String Posn -> Env -> TCheckResult
checkTypeString node@(Abs.String value pos) env = TResult env (B_type Type_String ) pos

checkTypeReal :: Abs.Real Posn -> Env -> TCheckResult
checkTypeReal node@(Abs.Real value pos) env = TResult env (B_type Type_Real ) pos

checkTypeBoolean :: Abs.Boolean Posn -> Env -> TCheckResult
checkTypeBoolean node@(Abs.Boolean_true pos) env = TResult env (B_type Type_Boolean ) pos
checkTypeBoolean node@(Abs.Boolean_True pos) env = TResult env (B_type Type_Boolean ) pos
checkTypeBoolean node@(Abs.Boolean_false pos) env = TResult env (B_type Type_Boolean ) pos
checkTypeBoolean node@(Abs.Boolean_False pos) env = TResult env (B_type Type_Boolean ) pos