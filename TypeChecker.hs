{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module TypeChecker where

import Type
import LexProgettoPar (Posn(..))
import AbsProgettoPar as Abs
import Data.Map
import Prelude

------------------------------
--- ENVIRONMENT DATA TYPES ---
------------------------------

type Env = Map Prelude.String [EnvEntry]
            -- chiave, valore

data EnvEntry
    = Variable {varType::Type, varPosition::LexProgettoPar.Posn, varMode::Prelude.String}
    | Function {funType::Type, funPosition::LexProgettoPar.Posn, funParameters::[Parameter]}

data Parameter
    = Parameter {paramType::Type, paramPosition::LexProgettoPar.Posn}
    deriving(Eq, Ord)

data TCheckResult
    = TResult {environment::Env, t_type::Type, t_position::LexProgettoPar.Posn}
    | TError {errors::[Prelude.String]}

----------------------------------------
--- SHOW ISTANCES FOR ENV DATA TYPES ---
----------------------------------------

instance Show EnvEntry where
    show entry = case entry of
        TypeChecker.Variable ty pos varMode -> "EnvEntry: [" ++ "var:" ++ show ty ++ "|" ++ show pos ++ "|mode:" ++ show varMode ++"]"
        TypeChecker.Function ty pos params    -> "EnvEntry: [" ++ "fun:" ++ show ty ++ "|" ++ show pos ++ "|params:" ++ show params ++ "]"

instance Show Parameter where
    show param = case param of    
        TypeChecker.Parameter ty pos    -> "(param:" ++ show ty ++ "|" ++ show pos ++ ")"

instance Show TCheckResult where
    show tres = case tres of
        TypeChecker.TResult env ty pos  -> show env ++ "|" ++ show ty ++ "|" ++ show pos
        TypeChecker.TError errs         -> "Errors: " ++ show errs


--------------------------------
--- ENV DATA TYPES FUNCTIONS ---
--------------------------------

getTypeEnvEntry :: [EnvEntry] -> Type
getTypeEnvEntry [] = B_type Type_Void
getTypeEnvEntry (x:xs) = case x of 
                            (Variable t pos mode) -> t
                            (Function t pos parameters) -> t
                            _ -> B_type Type_Void

first :: (Env,[Prelude.String]) -> Env
first (f,s) = f

second :: (Env,[Prelude.String]) -> [Prelude.String]
second (f,s) = s

updateEnv :: (Abs.STATEMENTS Posn) -> Env -> [Prelude.String] -> (Env,[Prelude.String])
updateEnv node@(Abs.ListStatements pos stat stats) env err = case stat of
                                                                Abs.VariableDeclarationStatement pos varType vardec -> let ty = getVarType vardec in -- getting variable type (int etc.)
                                                                                                                         (let varMode = getVarMode varType in -- getting variable mode (const etc.)
                                                                                                                            (let ids = (getVariableDeclStatNames vardec) in -- getting id or ids of declared variables
                                                                                                                                (updateEnvFromList ids env pos varMode ty,err ++ checkErr env stat))) -- updating env for each declared var.

                                                                -- Abs.ReturnStatement pos ret-> (insertWith (++) "return" [Variable (B_type Type_Void) (Pn 0 1 1) False] env,err ++ checkErr env stat)
                                                                -- Abs.ExpressionStatement pos exp -> case exp of
                                                                --                                    Abs.VariableExpression pos (Abs.Ident id posId) -> (insertWith (++) id [Variable (B_type Type_Real) (Pn 0 1 1) False] env,err ++ checkErr env stat)
                                                                --                                    _ -> (env,err)
                                                                _ -> (env,err)
updateEnv node@(Abs.EmptyStatement  pos) env err = (env,err)

updateEnvFromList :: [Prelude.String] -> Env -> Posn -> Prelude.String -> Type -> Env
updateEnvFromList [] env pos varMode ty = env
updateEnvFromList (x:xs) env pos varMode ty = updateEnvFromList xs (insertWith (++) x [Variable ty pos varMode] env) pos varMode ty

----------------------------------------------------------------------
--- FUNCTIONS FOR GETTING INFOS FROM VAR-DECLARATIONS FOR ENV ENTRY --
----------------------------------------------------------------------

getVarMode :: Abs.VARIABLETYPE Posn -> Prelude.String
getVarMode (Abs.VariableTypeParam _) = "param"
getVarMode (Abs.VariableTypeConst _) = "const"
getVarMode (Abs.VariableTypeVar _) = "var"
getVarMode (Abs.VariableTypeRef _) = "ref"
getVarMode (Abs.VariableTypeConstRef _) = "constRef"

getVarType :: Abs.VARDECLIST Posn -> Type
getVarType (Abs.VariableDeclarationSingle _ (Abs.VariableDeclaration _ _ ty _)) = getTypePart ty

getTypePart :: Abs.TYPEPART Posn -> Type
getTypePart (Abs.TypePart _ typeExpr) = getTypeExpr typeExpr

getTypeExpr :: Abs.TYPEEXPRESSION Posn -> Type
getTypeExpr (Abs.TypeExpression _ primitive) = getTypeFromPrimitive primitive
getTypeExpr (Abs.TypeExpressionArraySimple _ _ _) = (B_type Type_Void) -- TODO
getTypeExpr (Abs.TypeExpressionArray _ _ _) = (B_type Type_Void) -- TODO
getTypeExpr (Abs.TypeExpressionPointer _ _ _) = (B_type Type_Void) -- TODO

getTypeFromPrimitive :: Abs.PRIMITIVETYPE Posn -> Type
getTypeFromPrimitive (Abs.PrimitiveTypeVoid _) = (B_type Type_Void)
getTypeFromPrimitive (Abs.PrimitiveTypeBool _) = (B_type Type_Boolean)
getTypeFromPrimitive (Abs.PrimitiveTypeInt _) = (B_type Type_Integer)
getTypeFromPrimitive (Abs.PrimitiveTypeReal _) = (B_type Type_Real)
getTypeFromPrimitive (Abs.PrimitiveTypeString _) = (B_type Type_String)
getTypeFromPrimitive (Abs.PrimitiveTypeChar _) = (B_type Type_Char)
getTypeFromPrimitive (Abs.TypeArray _ prim) =  (Type.Array (getTypeFromPrimitive prim))

getVariableDeclStatNames :: Abs.VARDECLIST Posn -> [Prelude.String]
getVariableDeclStatNames (Abs.VariableDeclarationSingle _ (Abs.VariableDeclaration _ id _ _)) = getIdList id

getIdList :: Abs.IDENTLIST Posn -> [Prelude.String]
getIdList (Abs.IdentifierList _ (Abs.Ident s _) identlist) = [s] ++ getIdList identlist
getIdList (Abs.IdentifierSingle _ (Abs.Ident s _)) = [s] 

checkErr :: Env -> Abs.STATEMENT Posn -> [Prelude.String]
checkErr env stat = []                    

-------------------------
-- EXECUTION FUNCTIONS --
-------------------------

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
executeStatement node@(Abs.VariableDeclarationStatement pos tipo vardec) env = Abs.VariableDeclarationStatement (checkTypeStatement node env) (executeVarType tipo env) (executeVarDecList vardec env)

executeVarType :: Abs.VARIABLETYPE Posn -> Env -> Abs.VARIABLETYPE TCheckResult
executeVarType node@(Abs.VariableTypeParam pos) env = Abs.VariableTypeParam (checkTypeType node env)
executeVarType node@(Abs.VariableTypeConst pos) env = Abs.VariableTypeConst (checkTypeType node env)
executeVarType node@(Abs.VariableTypeVar pos) env = Abs.VariableTypeVar (checkTypeType node env)
executeVarType node@(Abs.VariableTypeRef pos) env = Abs.VariableTypeRef (checkTypeType node env)
executeVarType node@(Abs.VariableTypeConstRef pos) env = Abs.VariableTypeConstRef (checkTypeType node env)

executeVarDecList :: Abs.VARDECLIST Posn -> Env -> Abs.VARDECLIST TCheckResult
executeVarDecList node@(Abs.VariableDeclarationSingle pos vardec) env = Abs.VariableDeclarationSingle (checkTypeVardec node env) (executeVardecID vardec env)

executeVardecID :: Abs.VARDECID Posn -> Env -> Abs.VARDECID TCheckResult
executeVardecID node@(Abs.VariableDeclaration pos idlist tipo init) env = Abs.VariableDeclaration (checkTypeVariableDec node env) (executeIDList idlist env) (executeTypePart tipo env) (executeInitPart init env)

executeIDList :: Abs.IDENTLIST Posn -> Env -> Abs.IDENTLIST TCheckResult
executeIDList node@(Abs.IdentifierList pos id next) env = Abs.IdentifierList (checkIdentifierList node env) (executeIdent id env) (executeIDList next env)
executeIDList node@(Abs.IdentifierSingle pos id) env = Abs.IdentifierSingle (checkIdentifierList node env) (executeIdent id env)

executeTypePart :: Abs.TYPEPART Posn -> Env -> Abs.TYPEPART TCheckResult
executeTypePart node@(Abs.TypePart pos tipo) env = Abs.TypePart (checkTypeTypePart node env) (executeTypeExpression tipo env)

executeInitPart :: Abs.INITPART Posn -> Env -> Abs.INITPART TCheckResult
executeInitPart node@(Abs.InitializzationPart pos initExp) env = Abs.InitializzationPart (checkTypeInitializzationPart node env) (executeExpression initExp env)
executeInitPart node@(Abs.InitializzationPartArray pos listelementarray) env = Abs.InitializzationPartArray (checkTypeInitializzationPart node env) (executeListElementArray listelementarray env)
executeInitPart node@(Abs.InitializzationPartEmpty pos) env = Abs.InitializzationPartEmpty (TResult env (B_type Type_Void) pos)

executeListElementArray :: Abs.LISTELEMENTARRAY Posn -> Env -> Abs.LISTELEMENTARRAY TCheckResult
executeListElementArray node@(Abs.ListElementsOfArray pos expr elementlist) env = Abs.ListElementsOfArray (checkListElementsOfArray node env) (executeExpression expr env) (executeListElementArray elementlist env)
executeListElementArray node@(Abs.ListElementOfArray pos expr) env = Abs.ListElementOfArray (checkListElementsOfArray node env) (executeExpression expr env)

executeTypeExpression :: Abs.TYPEEXPRESSION Posn -> Env -> Abs.TYPEEXPRESSION TCheckResult
executeTypeExpression node@(Abs.TypeExpression pos primitivetype) env = Abs.TypeExpression (checkTypeTypeExpression node env) (executePrimitiveType primitivetype env)
executeTypeExpression node@(Abs.TypeExpressionArraySimple pos rangeexp primitivetype) env = Abs.TypeExpressionArraySimple (checkTypeTypeExpression node env) (executeRangeExp rangeexp env) (executePrimitiveType primitivetype env)
executeTypeExpression node@(Abs.TypeExpressionArray pos rangeexp primitivetype) env = Abs.TypeExpressionArray (checkTypeTypeExpression node env) (executeRangeExp rangeexp env) (executePrimitiveType primitivetype env)
executeTypeExpression node@(Abs.TypeExpressionPointer pos primitivetype pointer) env = Abs.TypeExpressionPointer (checkTypeTypeExpression node env) (executePrimitiveType primitivetype env) (executeTypeExpressionPointer pointer env)

executeTypeExpressionPointer :: Abs.POINTER Posn -> Env -> Abs.POINTER TCheckResult
executeTypeExpressionPointer node@(Abs.PointerSymbol pos pointer) env = Abs.PointerSymbol (checkTypeExpressionpointer node env) (executeTypeExpressionPointer pointer env)
executeTypeExpressionPointer node@(Abs.PointerSymbolSingle pos) env = Abs.PointerSymbolSingle (checkTypeExpressionpointer node env)

executeRangeExp :: Abs.RANGEEXP Posn -> Env -> Abs.RANGEEXP TCheckResult
executeRangeExp node@(Abs.RangeExpression pos expr1 expr2 rangexp) env = Abs.RangeExpression (checkRangeExpType node env) (executeExpression expr1 env)  (executeExpression expr2 env) (executeRangeExp rangexp env)
executeRangeExp node@(Abs.RangeExpressionSingle pos expr1 expr2) env = Abs.RangeExpressionSingle (checkRangeExpType node env)  (executeExpression expr1 env)  (executeExpression expr2 env)

executePrimitiveType :: Abs.PRIMITIVETYPE Posn -> Env -> Abs.PRIMITIVETYPE TCheckResult
executePrimitiveType node@(Abs.PrimitiveTypeVoid pos) env = Abs.PrimitiveTypeVoid (TResult env (B_type Type_Void) pos)
executePrimitiveType node@(Abs.PrimitiveTypeBool pos) env = Abs.PrimitiveTypeBool (TResult env (B_type Type_Boolean ) pos)
executePrimitiveType node@(Abs.PrimitiveTypeInt pos) env = Abs.PrimitiveTypeInt (TResult env (B_type Type_Integer) pos)
executePrimitiveType node@(Abs.PrimitiveTypeReal pos) env = Abs.PrimitiveTypeReal (TResult env (B_type Type_Real) pos)
executePrimitiveType node@(Abs.PrimitiveTypeString pos) env = Abs.PrimitiveTypeString (TResult env (B_type Type_String) pos)
executePrimitiveType node@(Abs.PrimitiveTypeChar pos) env = Abs.PrimitiveTypeChar (TResult env (B_type Type_Char) pos)
executePrimitiveType node@(Abs.TypeArray pos primitivetype) env = Abs.TypeArray (checkPrimitiveType node env) (executePrimitiveType primitivetype env)

executeB :: Abs.B Posn -> Env -> Abs.B TCheckResult
executeB node@(Abs.BlockStatement pos statements) env = let newEnv = updateEnv statements env [] in 
                                                                 Abs.BlockStatement (checkTypeB node env) (executeStatements statements (first newEnv))

executeReturnStatement :: Abs.RETURNSTATEMENT Posn -> Env -> Abs.RETURNSTATEMENT TCheckResult
executeReturnStatement node@(Abs.ReturnState _ retExp) env = Abs.ReturnState (checkTypeReturnState node env) (executeExpression retExp env)
executeReturnStatement node@(Abs.ReturnStateEmpty _ ) env = Abs.ReturnStateEmpty (checkTypeReturnState node env)

executeExpressionStatement :: Abs.EXPRESSIONSTATEMENT Posn -> Env -> Abs.EXPRESSIONSTATEMENT TCheckResult
executeExpressionStatement node@(Abs.VariableExpression _ id) env = Abs.VariableExpression (checkTypeExpressionStatement node env) (executeIdent id env)
-- add for call

executeExpression :: Abs.EXPRESSION Posn -> Env -> Abs.EXPRESSION TCheckResult
executeExpression node@(Abs.ExpressionInteger pos value) env = Abs.ExpressionInteger (checkTypeExpression node env) (executeInteger value env)
executeExpression node@(Abs.ExpressionBoolean pos value) env = Abs.ExpressionBoolean (checkTypeExpression node env) (executeBoolean value env)
executeExpression node@(Abs.ExpressionChar pos value) env = Abs.ExpressionChar (checkTypeExpression node env) (executeChar value env)
executeExpression node@(Abs.ExpressionString pos value) env = Abs.ExpressionString (checkTypeExpression node env) (executeString value env)
executeExpression node@(Abs.ExpressionReal pos value) env = Abs.ExpressionReal (checkTypeExpression node env) (executeReal value env)
executeExpression node@(Abs.ExpressionIdent pos id index) env = case index of
                                                                Abs.ArrayIndexElementEmpty posIdx -> Abs.ExpressionIdent (checkTypeIdent id env) (executeIdent id env) (executeArrayIndexElement (Abs.ArrayIndexElementEmpty posIdx) env)
                                                                Abs.ArrayIndexElement posIdx tipo -> Abs.ExpressionIdent (checkTypeIdent id env) (executeIdent id env) (Abs.ArrayIndexElementEmpty (TError ["index si"]))
-- cast unary e bracket binary


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
executeAssignOp node@(Abs.AssignOperationEqFract pos) env = Abs.AssignOperationEqFract (TResult env (B_type Type_Void) pos)
executeAssignOp node@(Abs.AssignOperationEqPercent pos) env = Abs.AssignOperationEqPercent (TResult env (B_type Type_Void) pos)
executeAssignOp node@(Abs.AssignOperationEqPower pos) env = Abs.AssignOperationEqPower (TResult env (B_type Type_Void) pos)

executeArrayIndexElement :: Abs.ARRAYINDEXELEMENT Posn -> Env -> Abs.ARRAYINDEXELEMENT TCheckResult
executeArrayIndexElement node@(Abs.ArrayIndexElement pos index) env = Abs.ArrayIndexElement (checkArrayIndexElement node env) (executeTypeTypeIndex index env)
executeArrayIndexElement node@(Abs.ArrayIndexElementEmpty pos) env = Abs.ArrayIndexElementEmpty (checkArrayIndexElement node env)

checkArrayIndexElement :: Abs.ARRAYINDEXELEMENT Posn -> Env -> TCheckResult
checkArrayIndexElement node@(Abs.ArrayIndexElement pos index) env = checkTypeTypeIndex index env
checkArrayIndexElement node@(Abs.ArrayIndexElementEmpty pos) env = (TResult env (B_type Type_Void ) pos)

executeTypeTypeIndex :: Abs.TYPEINDEX Posn -> Env -> Abs.TYPEINDEX TCheckResult
executeTypeTypeIndex node@(Abs.TypeOfIndexInt pos typeindex integer) env = Abs.TypeOfIndexInt (checkTypeTypeIndex node env) (executeTypeTypeIndex typeindex env) (executeInteger integer env)
executeTypeTypeIndex node@(Abs.TypeOfIndexIntSingle pos integer) env = Abs.TypeOfIndexIntSingle (checkTypeTypeIndex node env) (executeInteger integer env)
executeTypeTypeIndex node@(Abs.TypeOfIndexVar pos typeindex id) env = Abs.TypeOfIndexVar (checkTypeTypeIndex node env) (executeTypeTypeIndex typeindex env) (executeIdent id env)
executeTypeTypeIndex node@(Abs.TypeOfIndexVarSingle pos id) env = Abs.TypeOfIndexVarSingle (checkTypeTypeIndex node env) (executeIdent id env)

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

---------------------------
-- TYPE CHECKS FUNCTIONS --
---------------------------

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
checkTypeStatement node@(Abs.AssignmentStatement pos lval assignOp exp) env = checkTypeExpression exp env --aggiungere controllo compatibilità lval con exp
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
    Just result -> checkTypeExpression retExp env
    Nothing -> TError ["Unexpected return at " ++ (show pos)]
checkTypeReturnState node@(Abs.ReturnStateEmpty pos ) env = case Data.Map.lookup "return" env of
    Just result -> TResult env (B_type Type_Void) pos
    Nothing -> TError ["Unexpected return at " ++ (show pos)]

checkTypeExpressionStatement :: Abs.EXPRESSIONSTATEMENT Posn -> Env -> TCheckResult
checkTypeExpressionStatement node@(Abs.VariableExpression pos id) env = checkTypeIdent id env

checkTypeExpression :: Abs.EXPRESSION Posn -> Env -> TCheckResult
checkTypeExpression node@(Abs.ExpressionInteger pos value) env = checkTypeInteger value env
checkTypeExpression node@(Abs.ExpressionBoolean pos value) env = checkTypeBoolean value env
checkTypeExpression node@(Abs.ExpressionChar pos value) env = checkTypeChar value env
checkTypeExpression node@(Abs.ExpressionString pos value) env = checkTypeString value env
checkTypeExpression node@(Abs.ExpressionReal pos value) env = checkTypeReal value env
checkTypeExpression node@(Abs.ExpressionIdent pos value index) env = checkTypeIdent value env --gestire index

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

checkTypeVardec :: Abs.VARDECLIST Posn -> Env -> TCheckResult
checkTypeVardec node@(Abs.VariableDeclarationSingle pos vardecid) env = TError ["vardecidlistsingle todo"]

checkTypeVariableDec :: Abs.VARDECID Posn -> Env -> TCheckResult
checkTypeVariableDec node@(Abs.VariableDeclaration pos identlist typeart initpart) env = TError [" vardecid TODO"]

checkIdentifierList :: Abs.IDENTLIST Posn -> Env -> TCheckResult
checkIdentifierList node@(Abs.IdentifierList pos ident identlist) env = TError ["identlist todo"]
checkIdentifierList node@(Abs.IdentifierSingle pos ident) env = TError ["SINGLEEEEEEEEEE"]
-- single todo?

checkTypeTypePart :: Abs.TYPEPART Posn -> Env -> TCheckResult
checkTypeTypePart node@(Abs.TypePart pos typexpr) env = TError ["typeaprt todo"]

checkTypeInitializzationPart ::  Abs.INITPART Posn -> Env -> TCheckResult
checkTypeInitializzationPart node@(Abs.InitializzationPart pos expr) env = TError ["todo :)"]
checkTypeInitializzationPart node@(Abs.InitializzationPartArray pos listelementarray) env = TError ["todo :)"]
checkTypeInitializzationPart node@(Abs.InitializzationPartEmpty pos ) env = TError ["TODO"]

checkTypeExpressionpointer :: Abs.POINTER Posn -> Env -> TCheckResult
checkTypeExpressionpointer node@(Abs.PointerSymbol pos pointer) env = TError ["che tipo gli assegno? quello del primitive type... è un padre, serve un let! su executeTypeExpr?"]
checkTypeExpressionpointer node@(Abs.PointerSymbolSingle pos) env = TError ["single pointer"]

checkPrimitiveType :: Abs.PRIMITIVETYPE Posn -> Env -> TCheckResult
checkPrimitiveType node@(Abs.PrimitiveTypeVoid pos) env = TResult env (B_type Type_Void) pos
checkPrimitiveType node@(Abs.PrimitiveTypeBool pos) env = TResult env (B_type Type_Boolean) pos
checkPrimitiveType node@(Abs.PrimitiveTypeInt pos) env = TResult env (B_type Type_Integer) pos
checkPrimitiveType node@(Abs.PrimitiveTypeReal pos) env = TResult env (B_type Type_Real) pos
checkPrimitiveType node@(Abs.PrimitiveTypeString pos) env = TResult env (B_type Type_String) pos
checkPrimitiveType node@(Abs.PrimitiveTypeChar pos) env = TResult env (B_type Type_Char) pos
checkPrimitiveType node@(Abs.TypeArray pos primitivetype) env = TError["Todo......?bo"]

checkTypeTypeExpression :: Abs.TYPEEXPRESSION Posn -> Env -> TCheckResult
checkTypeTypeExpression node@(Abs.TypeExpression pos primitiveType) env = TError ["mhh?"]
checkTypeTypeExpression node@(Abs.TypeExpressionArraySimple pos rangeexp primitivetype) env = TError ["mhh?"]
checkTypeTypeExpression node@(Abs.TypeExpressionArray pos rangeexp primitivetype) env= TError ["mhh?"]
checkTypeTypeExpression node@(Abs.TypeExpressionPointer pos primitivetype pointer) env = TError ["controllo pointer-primitive che coincida con l'expr? type? ..."]

checkListElementsOfArray :: Abs.LISTELEMENTARRAY Posn -> Env -> TCheckResult
checkListElementsOfArray node@(Abs.ListElementsOfArray pos expr elementlist) env = TError ["CONTROLLA LA LISTA"]
checkListElementsOfArray node@(Abs.ListElementOfArray pos expr) env = TError ["Ok? 1 elemento? ritorno il tipo?"]

checkRangeExpType :: Abs.RANGEEXP Posn -> Env -> TCheckResult
checkRangeExpType node@(Abs.RangeExpression pos expr1 expr2 rangexp) env = TError ["Controlla rangexp"]
checkRangeExpType node@(Abs.RangeExpressionSingle pos expr1 expr2) env = TError ["Controlla rangexp"]

checkTypeTypeIndex :: Abs.TYPEINDEX Posn -> Env -> TCheckResult
checkTypeTypeIndex node@(Abs.TypeOfIndexInt pos typeindex integer) env = TError ["todo"]
checkTypeTypeIndex node@(Abs.TypeOfIndexIntSingle pos integer) env = TResult env (B_type Type_Integer) pos
checkTypeTypeIndex node@(Abs.TypeOfIndexVar pos typeindex id) env = TError ["todo"]
checkTypeTypeIndex node@(Abs.TypeOfIndexVarSingle _ (Abs.Ident id pos)) env = case Data.Map.lookup id env of
                                    Just ident -> TResult env (getTypeEnvEntry ident) pos
                                    Nothing -> TError [" ?? var not def. Unexpected ident at " ++ (show pos)]