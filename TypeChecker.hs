-- Progetto LC 2021 -- Mansi/Cagnoni UNIUD --

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module TypeChecker where

import Type
import LexProgettoPar (Posn(..))
import AbsProgettoPar as Abs
import Data.Map
import Prelude

-------------------------------------------------------------------------------------
--- ENVIRONMENT DATA TYPES ----------------------------------------------------------
-------------------------------------------------------------------------------------

type Env = Map Prelude.String [EnvEntry]
            -- chiave, valore

data EnvEntry
    = Variable {varType::Type, varPosition::LexProgettoPar.Posn, varMode::Prelude.String}
    | Function {funType::Type, funPosition::LexProgettoPar.Posn, funParameters::[Parameter]}

data Parameter
    = Parameter {paramType::Type, paramPosition::LexProgettoPar.Posn, paramMode::Prelude.String, identifier::Prelude.String}
    deriving(Eq, Ord)

data TCheckResult
    = TResult {environment::Env, t_type::Type, t_position::LexProgettoPar.Posn}
    | TError {errors::[Prelude.String]}

--searchFunction [] (Pn abs row col) [Function t (Pn absf rowf colf) mode] =
--searchFunction [] (Pn abs row col) [] = 
--searchFunction ((x1,x2):xs) (Pn abs row col) zs= case x2 of
--                                                    Variable t pos mode -> searchFunction xs (Pn abs row col) zs
--                                                    Function t pos mode -> searchFunction xs (Pn abs row col) [Function t pos mode]

-------------------------------------------------------------------------------------------------
--- SHOW ISTANCES FOR ENV DATA TYPES ------------------------------------------------------------
-------------------------------------------------------------------------------------------------

instance Show EnvEntry where
    show entry = case entry of
        TypeChecker.Variable ty pos varMode -> "EnvEntry: [" ++ "var:" ++ show ty ++ "|" ++ show pos ++ "|mode:" ++ show varMode ++"]"
        TypeChecker.Function ty pos params  -> "EnvEntry: [" ++ "fun:" ++ show ty ++ "|" ++ show pos ++ "|params:" ++ show params ++ "]"

instance Show Parameter where
    show param = case param of    
        TypeChecker.Parameter ty pos mode id   -> "(" ++ show id ++ ":" ++ show ty ++ "|" ++ show pos ++ "|mode:" ++ show mode ++ ")"

instance Show TCheckResult where
    show tres = case tres of
        TypeChecker.TResult env ty pos  -> show env ++ "|" ++ show ty ++ "|" ++ show pos
        TypeChecker.TError errs         -> "Errors: " ++ show errs

--------------------------------------------------------------------------------------------------
--- GENERIC FUNCTIONS FOR TYPE-CHECKING  ---------------------------------------------------------
--------------------------------------------------------------------------------------------------

-- Checks if type A is compatible with type B
-- Semantic: can A be where type B is required?
--      Examples: int int -> true
--                int real -> true (because 1 can be seen as 1.0)
--                real int -> false
checkCompatibility :: TCheckResult -> TCheckResult -> Bool
checkCompatibility (TError _) _ = False
checkCompatibility _ (TError _) = False
checkCompatibility (TResult env t pos) (TResult envC tC posC) = case t of
                                                                    B_type Type_Void -> case tC of
                                                                                          B_type Type_Void -> True
                                                                                          _ -> False 
                                                                    B_type Type_Integer -> case tC of
                                                                                          B_type Type_Integer -> True   
                                                                                          B_type Type_Real -> True   -- int can be put where real is required
                                                                                          _ -> False 
                                                                    B_type Type_Real -> case tC of
                                                                                          B_type Type_Real -> True
                                                                                          _ -> False 
                                                                    B_type Type_Boolean  -> case tC of
                                                                                          B_type Type_Boolean  -> True
                                                                                          _ -> False 
                                                                    B_type Type_Char  -> case tC of
                                                                                          B_type Type_Char  -> True
                                                                                          _ -> False 
                                                                    B_type Type_String  -> case tC of
                                                                                          B_type Type_String  -> True
                                                                                          _ -> False
                                                                    _ -> False 

returnSuperType  :: TCheckResult -> TCheckResult -> TCheckResult
returnSuperType (TError errs) _ = (TError errs)
returnSuperType _ (TError errs) = (TError errs)
returnSuperType (TResult env t pos) (TResult envC tC posC) = case t of
                                                                    B_type Type_Void -> case tC of
                                                                                          B_type Type_Void -> (TResult env t pos)
                                                                    B_type Type_Integer -> case tC of
                                                                                          B_type Type_Integer -> (TResult env t pos)   
                                                                                          B_type Type_Real -> (TResult envC tC posC)   -- real > int
                                                                    B_type Type_Real -> case tC of
                                                                                          B_type Type_Real -> (TResult env t pos)
                                                                                          B_type Type_Integer -> (TResult env t pos) -- real > int
                                                                    B_type Type_Boolean  -> case tC of
                                                                                          B_type Type_Boolean  -> (TResult env t pos)
                                                                    B_type Type_Char  -> case tC of
                                                                                          B_type Type_Char  -> (TResult env t pos)
                                                                    B_type Type_String  -> case tC of
                                                                                          B_type Type_String  -> (TResult env t pos)
---------------------------------------------------------------------------------------------------
--- ENV DATA TYPES FUNCTIONS ----------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- Returns the type of a EnvEntry of the Environment -> Variable or Function entry
getTypeEnvEntry :: [EnvEntry] -> Type
getTypeEnvEntry [] = B_type Type_Void
getTypeEnvEntry (x:xs) = case x of 
                            (Variable t pos mode) -> t
                            (Function t pos parameters) -> t
                            _ -> B_type Type_Void

-- Returns the Env from a Map (Env,Errors) entry
first :: (Env,[Prelude.String]) -> Env
first (f,s) = f

-- Returns type checker Errors from a Map (Env,Errors) entry
second :: (Env,[Prelude.String]) -> [Prelude.String]
second (f,s) = s

-- Called when an environment update is needed.
-- It creates the right new env-entry when called with different types of statements
-- Example: if called with a "Abs node of type funciton statements" it creates a new env-entry for that function,
--          this is done by calling the required functions for getting the required infos for the entry: id, type, etc.
updateEnv :: (Abs.STATEMENTS Posn) -> Env -> [Prelude.String] -> (Env,[Prelude.String])
updateEnv node@(Abs.ListStatements pos stat stats) env err = case stat of
                                                                -- Variables
                                                                Abs.VariableDeclarationStatement pos varType vardec -> let ty = getVarType vardec in -- getting variable type (int etc.)
                                                                                                                         (let varMode = getVarMode varType in -- getting variable mode (const etc.)
                                                                                                                            (let ids = (getVariableDeclStatNames vardec) in -- getting id or ids of declared variables
                                                                                                                                (updateEnvFromList ids env pos varMode ty,err ++ checkErr env stat))) -- updating env for each declared var.
                                                                -- Functions and Procedures
                                                                Abs.ProcedureStatement pos id params stats -> let parameters = getParamList params in
                                                                                                                let fid = getIdFromIdent id in
                                                                                                                    ((insertWith (++) fid [Function (B_type Type_Void) pos parameters] env,err ++ checkErr env stat))
                                                                
                                                                Abs.FunctionStatement pos id params ty stats -> let parameters = getParamList params in
                                                                                                                    let fty = getTypeFromPrimitive ty in
                                                                                                                        (let fid = getIdFromIdent id in 
                                                                                                                            (insertWith (++) fid [Function fty pos parameters] env,err ++ checkErr env stat))
                                                                -- generic case
                                                                _ -> (env,err) 
updateEnv node@(Abs.EmptyStatement  pos) env err = (env,err)

updateEnvFromList :: [Prelude.String] -> Env -> Posn -> Prelude.String -> Type -> Env
updateEnvFromList [] env pos varMode ty = env
updateEnvFromList (x:xs) env pos varMode ty = updateEnvFromList xs (insertWith (++) x [Variable ty pos varMode] env) pos varMode ty

checkErr :: Env -> Abs.STATEMENT Posn -> [Prelude.String]
checkErr env stat = []   

------------------------------------------------------------------------------------------------------
--- FUNCTIONS FOR GETTING INFOS FROM FUNCTIONS-DECLARATIONS FOR ENV ENTRY ----------------------------
------------------------------------------------------------------------------------------------------

-- Given an Ident node of the ABS, returns the string of the identifier
getIdFromIdent :: Abs.Ident Posn -> Prelude.String
getIdFromIdent (Abs.Ident s _) = s 

-- Given a Parameters node of the ABS, returns a list of Parameters (constructor for the ENV)
getParamList :: Abs.PARAMETERS Posn -> [Parameter]
getParamList (Abs.ParameterList pos param params) = let p = buildParam param in [p] ++ getParamList params
getParamList (Abs.ParameterListSingle pos param)  = let p = buildParam param in [p]
getParamList (Abs.ParameterListEmpty pos)         = []

-- Given a Parameter node of the ABS, return a single built Parameter data type (constructor for the ENV)
buildParam :: Abs.PARAMETER Posn -> Parameter
buildParam (Abs.Parameter pos id ty) = (TypeChecker.Parameter (getTypeFromPrimitive ty) pos "_mode_" (getIdFromIdent id)) 

-------------------------------------------------------------------------------------------------------
--- FUNCTIONS FOR GETTING INFOS FROM VAR-DECLARATIONS FOR ENV ENTRY -----------------------------------
-------------------------------------------------------------------------------------------------------

-- Given a VariableType node of the ABS, returns a string indicating the type of variable
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

-- Given a TypeExpression node of the abs, execute the right getType function for obtaining the Type
getTypeExpr :: Abs.TYPEEXPRESSION Posn -> Type
getTypeExpr (Abs.TypeExpression _ primitive) = getTypeFromPrimitive primitive
getTypeExpr (Abs.TypeExpressionArraySimple _ _ primitive) = getTypeFromPrimitive primitive
getTypeExpr (Abs.TypeExpressionArray _ _ primitive) = getTypeFromPrimitive primitive
getTypeExpr (Abs.TypeExpressionPointer _ primitive pointer) = Pointer (getTypeFromPrimitive primitive) (checkPointerDepth pointer)

-- Given a Pointer node of the ABS, it counts the depth (how much pointers '*' there are) of that pointer
-- Example: var x:int***** -> depth: 5
checkPointerDepth :: Abs.POINTER Posn -> Prelude.Integer
checkPointerDepth (Abs.PointerSymbol _ p) = 1 + checkPointerDepth p
checkPointerDepth (Abs.PointerSymbolSingle _) = 1

-- Get a PrimitiveType node of the ABS, returns the correct Type
getTypeFromPrimitive :: Abs.PRIMITIVETYPE Posn -> Type
getTypeFromPrimitive (Abs.PrimitiveTypeVoid _) = (B_type Type_Void)
getTypeFromPrimitive (Abs.PrimitiveTypeBool _) = (B_type Type_Boolean)
getTypeFromPrimitive (Abs.PrimitiveTypeInt _) = (B_type Type_Integer)
getTypeFromPrimitive (Abs.PrimitiveTypeReal _) = (B_type Type_Real)
getTypeFromPrimitive (Abs.PrimitiveTypeString _) = (B_type Type_String)
getTypeFromPrimitive (Abs.PrimitiveTypeChar _) = (B_type Type_Char)
getTypeFromPrimitive (Abs.TypeArray _ prim) =  (Type.Array (getTypeFromPrimitive prim))

-- Get a VarDecList (list of vars declarations) of the ABS, returns a list of strings, where each element is the id of the vars
getVariableDeclStatNames :: Abs.VARDECLIST Posn -> [Prelude.String]
getVariableDeclStatNames (Abs.VariableDeclarationSingle _ (Abs.VariableDeclaration _ id _ _)) = getIdList id

getIdList :: Abs.IDENTLIST Posn -> [Prelude.String]
getIdList (Abs.IdentifierList _ (Abs.Ident s _) identlist) = [s] ++ getIdList identlist
getIdList (Abs.IdentifierSingle _ (Abs.Ident s _)) = [s] 
             
---------------------------------------------------------------------------------------------------
--- EXECUTION FUNCTIONS ---------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

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
executeStatement node@(Abs.ConditionalStatement pos condition) env = Abs.ConditionalStatement (checkTypeStatement node env) (executeConditionalState condition env)
executeStatement node@(Abs.WhileDoStatement pos whileStaement) env = Abs.WhileDoStatement (checkTypeStatement node env) (executeWhileState whileStaement env)
executeStatement node@(Abs.DoWhileStatement pos doStatement) env = Abs.DoWhileStatement (checkTypeStatement node env) (executeDoState doStatement env)
executeStatement node@(Abs.ForStatement pos forStatement) env = Abs.ForStatement (checkTypeStatement node env) (executeForState forStatement env)
executeStatement node@(Abs.ForAllStatement pos forAllStatement) env = Abs.ForAllStatement (checkTypeStatement node env) (executeForAllState forAllStatement env)
executeStatement node@(Abs.ProcedureStatement pos id param states) env = let newEnv = updateEnv (Abs.ListStatements pos node (Abs.EmptyStatement pos)) env [] in 
                                                                        Abs.ProcedureStatement (checkTypeStatement node env) (executeIdent id env) (executeParam param env) (executeStatements states (first newEnv))
executeStatement node@(Abs.FunctionStatement pos id param tipo states) env = let newEnv = updateEnv (Abs.ListStatements pos node (Abs.EmptyStatement pos)) env [] in  
                                                                        Abs.FunctionStatement (checkTypeStatement node env) (executeIdent id env) (executeParam param env) (executePrimitiveType tipo env) (executeStatements states (first newEnv))

executeParam :: Abs.PARAMETERS Posn -> Env -> Abs.PARAMETERS TCheckResult
executeParam node@(Abs.ParameterList pos param params) env = Abs.ParameterList (checkTypeExecuteParameter node env) (executeParameter param env) (executeParam params env)
executeParam node@(Abs.ParameterListSingle pos param) env = Abs.ParameterListSingle (checkTypeExecuteParameter node env) (executeParameter param env)
executeParam node@(Abs.ParameterListEmpty pos) env = Abs.ParameterListEmpty (checkTypeExecuteParameter node env) 

executeParameter :: Abs.PARAMETER Posn -> Env -> Abs.PARAMETER TCheckResult
executeParameter node@(Abs.Parameter pos id ty) env = Abs.Parameter (checkTypeParameter node env) (executeIdent id env) (executePrimitiveType ty env)

checkTypeExecuteParameter :: Abs.PARAMETERS Posn -> Env -> TCheckResult
checkTypeExecuteParameter node@(Abs.ParameterList pos param params) env = TError ["todo"]
checkTypeExecuteParameter node@(Abs.ParameterListSingle pos param) env = TError ["todo"]
checkTypeExecuteParameter node@(Abs.ParameterListEmpty pos) env = TError ["todo"]

checkTypeParameter:: Abs.PARAMETER Posn -> Env -> TCheckResult
checkTypeParameter node@(Abs.Parameter pos id ty) env = TError ["todo"]

executeConditionalState :: Abs.CONDITIONALSTATE Posn -> Env -> Abs.CONDITIONALSTATE TCheckResult
executeConditionalState node@(Abs.ConditionalStatementSimpleThen pos exp state elseState) env = Abs.ConditionalStatementSimpleThen (checkTypeCondition node env) (executeExpression exp env) (executeStatement state env) (executeElseStatement elseState env)
executeConditionalState node@(Abs.ConditionalStatementSimpleWThen pos exp b elseState) env = Abs.ConditionalStatementSimpleWThen (checkTypeCondition node env) (executeExpression exp env) (executeB b env) (executeElseStatement elseState env)
executeConditionalState node@(Abs.ConditionalStatementCtrlThen pos ctrlState state elseState) env = Abs.ConditionalStatementCtrlThen (checkTypeCondition node env) (executeCtrlStatement ctrlState env) (executeStatement state env) (executeElseStatement elseState env)
executeConditionalState node@(Abs.ConditionalStatementCtrlWThen pos ctrlState b elseState) env = Abs.ConditionalStatementCtrlWThen (checkTypeCondition node env) (executeCtrlStatement ctrlState env) (executeB b env) (executeElseStatement elseState env)

executeElseStatement :: Abs.ELSESTATEMENT Posn -> Env -> Abs.ELSESTATEMENT TCheckResult
executeElseStatement node@(Abs.ElseStateEmpty pos) env= Abs.ElseStateEmpty (checkTypeElseState node env)
executeElseStatement node@(Abs.ElseState pos state) env= Abs.ElseState (checkTypeElseState node env) (executeStatement state env)

executeCtrlStatement :: Abs.CTRLDECSTATEMENT Posn -> Env -> Abs.CTRLDECSTATEMENT TCheckResult
executeCtrlStatement node@(Abs.CtrlDecStateVar pos id exp) env = Abs.CtrlDecStateVar (checkTypeCtrlState node env) (executeIdent id env) (executeExpression exp env)
executeCtrlStatement node@(Abs.CtrlDecStateConst pos id exp) env = Abs.CtrlDecStateConst (checkTypeCtrlState node env) (executeIdent id env) (executeExpression exp env)

executeWhileState :: Abs.WHILESTATEMENT Posn -> Env -> Abs.WHILESTATEMENT TCheckResult
executeWhileState node@(Abs.WhileStateSimpleDo pos exp state) env = Abs.WhileStateSimpleDo (checkTypeWhile node env) (executeExpression exp env) (executeStatement state env)
executeWhileState node@(Abs.WhileStateSimpleWDo pos exp b) env = Abs.WhileStateSimpleWDo (checkTypeWhile node env) (executeExpression exp env) (executeB b env)
executeWhileState node@(Abs.WhileStateCtrlDo pos ctrl state) env = Abs.WhileStateCtrlDo (checkTypeWhile node env) (executeCtrlStatement ctrl env) (executeStatement state env)
executeWhileState node@(Abs.WhileStateCtrlWDo pos ctrl b) env = Abs.WhileStateCtrlWDo (checkTypeWhile node env) (executeCtrlStatement ctrl env) (executeB b env)

executeDoState :: Abs.DOSTATEMENT Posn -> Env -> Abs.DOSTATEMENT TCheckResult
executeDoState node@(Abs.DoWhileState pos state exp) env = Abs.DoWhileState (checkTypeDo node env) (executeStatement state env) (executeExpression exp env)

executeForState :: Abs.FORSTATEMENT Posn -> Env -> Abs.FORSTATEMENT TCheckResult
executeForState node@(Abs.ForStateIndexDo pos index exp state) env = Abs.ForStateIndexDo (checkTypeForState node env) (executeIndex index env) (executeExpression exp env) (executeStatement state env)
executeForState node@(Abs.ForStateIndexWDo pos index exp b) env = Abs.ForStateIndexWDo (checkTypeForState node env) (executeIndex index env) (executeExpression exp env) (executeB b env)
executeForState node@(Abs.ForStateExprDo pos exp state) env = Abs.ForStateExprDo (checkTypeForState node env) (executeExpression exp env) (executeStatement state env)
executeForState node@(Abs.ForStateExprWDo pos exp b) env = Abs.ForStateExprWDo (checkTypeForState node env) (executeExpression exp env) (executeB b env)

executeIndex :: Abs.INDEXVARDEC Posn -> Env -> Abs.INDEXVARDEC TCheckResult
executeIndex node@(Abs.IndexVarDeclaration pos id) env = Abs.IndexVarDeclaration (checkTypeIndexVarDec node env) (executeIdent id env)

executeForAllState :: Abs.FORALLSTATEMENT Posn -> Env -> Abs.FORALLSTATEMENT TCheckResult
executeForAllState node@(Abs.ForAllStateIndexDo pos index exp state) env = Abs.ForAllStateIndexDo (checkTypeForAllState node env) (executeIndex index env) (executeExpression exp env) (executeStatement state env)
executeForAllState node@(Abs.ForAllStateIndexWDo pos index exp b) env = Abs.ForAllStateIndexWDo (checkTypeForAllState node env) (executeIndex index env) (executeExpression exp env) (executeB b env)
executeForAllState node@(Abs.ForAllStateExprDo pos exp state) env = Abs.ForAllStateExprDo (checkTypeForAllState node env) (executeExpression exp env) (executeStatement state env)
executeForAllState node@(Abs.ForAllStateExprWDo pos exp b) env = Abs.ForAllStateExprWDo (checkTypeForAllState node env) (executeExpression exp env) (executeB b env)

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
executeB node@(Abs.BlockStatement pos statements) env = Abs.BlockStatement (checkTypeB node env) (executeStatements statements env)

executeReturnStatement :: Abs.RETURNSTATEMENT Posn -> Env -> Abs.RETURNSTATEMENT TCheckResult
executeReturnStatement node@(Abs.ReturnState pos retExp) env = Abs.ReturnState (checkTypeReturnState node env) (executeExpression retExp env)
executeReturnStatement node@(Abs.ReturnStateEmpty pos ) env = Abs.ReturnStateEmpty (checkTypeReturnState node env)

executeExpressionStatement :: Abs.EXPRESSIONSTATEMENT Posn -> Env -> Abs.EXPRESSIONSTATEMENT TCheckResult
executeExpressionStatement node@(Abs.VariableExpression pos id) env = Abs.VariableExpression (checkTypeExpressionStatement node env) (executeIdent id env)
executeExpressionStatement node@(Abs.CallExpression pos callexpr) env = Abs.CallExpression (checkTypeExpressionStatement node env) (executeCallExpression callexpr env)

executeCallExpression :: Abs.CALLEXPRESSION Posn -> Env -> Abs.CALLEXPRESSION TCheckResult
executeCallExpression node@(Abs.CallExpressionParentheses pos id namedexpr) env = Abs.CallExpressionParentheses (checkTypeCallExpression node env) (executeIdent id env) (executeNamedExpressionList namedexpr env)
executeCallExpression node@(Abs.CallExpressionQuadre pos id namedexpr) env = Abs.CallExpressionQuadre (checkTypeCallExpression node env) (executeIdent id env) (executeNamedExpressionList namedexpr env)

executeNamedExpressionList :: Abs.NAMEDEXPRESSIONLIST Posn -> Env -> Abs.NAMEDEXPRESSIONLIST TCheckResult
executeNamedExpressionList node@(Abs.NamedExpressionList pos namedexpr) env = Abs.NamedExpressionList (checkTypeNamedExpressionList node env) (executeNamedExpression namedexpr env)
executeNamedExpressionList node@(Abs.NamedExpressionListEmpty pos) env = Abs.NamedExpressionListEmpty (TResult env (B_type Type_Void) pos)
executeNamedExpressionList node@(Abs.NamedExpressionLists pos namedexpr namedexprlist) env = Abs.NamedExpressionLists (checkTypeNamedExpressionList node env) (executeNamedExpression namedexpr env) (executeNamedExpressionList namedexprlist env)
executeNamedExpressionList node@(Abs.NamedExpressionAssigned pos id expr) env = Abs.NamedExpressionAssigned (checkTypeNamedExpressionList node env) (executeIdent id env) (executeExpression expr env)

executeNamedExpression :: Abs.NAMEDEXPRESSION Posn -> Env -> Abs.NAMEDEXPRESSION TCheckResult
executeNamedExpression node@(Abs.NamedExpression pos expr) env = Abs.NamedExpression (checkTypeNamedExpression node env) (executeExpression expr env)

executeExpressions :: Abs.EXPRESSIONS Posn -> Env -> Abs.EXPRESSIONS TCheckResult
executeExpressions node@(Abs.Expressions pos exp exps) env = Abs.Expressions (checkTypeExpressions node env) (executeExpression exp env) (executeExpressions exps env)
executeExpressions node@(Abs.Expression pos exp) env = Abs.Expression (checkTypeExpressions node env) (executeExpression exp env)
executeExpressions node@(Abs.ExpressionEmpty pos) env = Abs.ExpressionEmpty (checkTypeExpressions node env)

executeExpression :: Abs.EXPRESSION Posn -> Env -> Abs.EXPRESSION TCheckResult
executeExpression node@(Abs.ExpressionInteger pos value) env = Abs.ExpressionInteger (checkTypeExpression node env) (executeInteger value env)
executeExpression node@(Abs.ExpressionBoolean pos value) env = Abs.ExpressionBoolean (checkTypeExpression node env) (executeBoolean value env)
executeExpression node@(Abs.ExpressionChar pos value) env = Abs.ExpressionChar (checkTypeExpression node env) (executeChar value env)
executeExpression node@(Abs.ExpressionString pos value) env = Abs.ExpressionString (checkTypeExpression node env) (executeString value env)
executeExpression node@(Abs.ExpressionReal pos value) env = Abs.ExpressionReal (checkTypeExpression node env) (executeReal value env)
executeExpression node@(Abs.ExpressionBracket pos exp) env = Abs.ExpressionBracket (checkTypeExpression node env) (executeExpression exp env)
executeExpression node@(Abs.ExpressionCast pos def tipo) env = Abs.ExpressionCast (checkTypeExpression node env) (executeDefault def env) (executePrimitiveType tipo env)
executeExpression node@(Abs.ExpressionUnary pos unary exp) env = Abs.ExpressionUnary (checkTypeExpression node env) (executeUnaryOp unary env) (executeExpression exp env)
executeExpression node@(Abs.ExpressionBinary pos def binary exp) env = Abs.ExpressionBinary (checkTypeExpression node env) (executeDefault def env) (executeBinaryOp binary env) (executeExpression exp env)
executeExpression node@(Abs.ExpressionIdent pos id index) env = case index of
                                                                Abs.ArrayIndexElementEmpty posIdx -> Abs.ExpressionIdent (checkTypeIdent id env) (executeIdent id env) (executeArrayIndexElement (Abs.ArrayIndexElementEmpty posIdx) env)
                                                                Abs.ArrayIndexElement posIdx tipo -> Abs.ExpressionIdent (checkTypeIdent id env) (executeIdent id env) (Abs.ArrayIndexElementEmpty (TError ["index si"]))
executeExpression node@(Abs.ExpressionCall pos id exps) env = Abs.ExpressionCall (checkTypeExpression node env) (executeIdent id env) (executeExpressions exps env) 

executeUnaryOp :: Abs.UNARYOP Posn -> Env -> Abs.UNARYOP TCheckResult
executeUnaryOp node@(Abs.UnaryOperationPositive pos) env = Abs.UnaryOperationPositive (checkTypeUnaryOp node env)
executeUnaryOp node@(Abs.UnaryOperationNegative pos) env = Abs.UnaryOperationNegative (checkTypeUnaryOp node env)
executeUnaryOp node@(Abs.UnaryOperationNot pos) env = Abs.UnaryOperationNot (checkTypeUnaryOp node env)
executeUnaryOp node@(Abs.UnaryOperationPointer pos) env = Abs.UnaryOperationPointer (checkTypeUnaryOp node env)

executeBinaryOp :: Abs.BINARYOP Posn -> Env -> Abs.BINARYOP TCheckResult
executeBinaryOp node@(Abs.BinaryOperationPlus pos) env = Abs.BinaryOperationPlus (checkTypeBinaryOp node env)
executeBinaryOp node@(Abs.BinaryOperationMinus pos) env = Abs.BinaryOperationMinus (checkTypeBinaryOp node env)
executeBinaryOp node@(Abs.BinaryOperationProduct pos) env = Abs.BinaryOperationProduct (checkTypeBinaryOp node env)
executeBinaryOp node@(Abs.BinaryOperationDivision pos) env = Abs.BinaryOperationDivision (checkTypeBinaryOp node env)
executeBinaryOp node@(Abs.BinaryOperationModule pos) env = Abs.BinaryOperationModule (checkTypeBinaryOp node env)
executeBinaryOp node@(Abs.BinaryOperationPower pos) env = Abs.BinaryOperationPower (checkTypeBinaryOp node env)
executeBinaryOp node@(Abs.BinaryOperationAnd pos) env = Abs.BinaryOperationAnd (checkTypeBinaryOp node env)
executeBinaryOp node@(Abs.BinaryOperationOr pos) env = Abs.BinaryOperationOr (checkTypeBinaryOp node env)
executeBinaryOp node@(Abs.BinaryOperationEq pos) env = Abs.BinaryOperationEq (checkTypeBinaryOp node env)
executeBinaryOp node@(Abs.BinaryOperationNotEq pos) env = Abs.BinaryOperationNotEq (checkTypeBinaryOp node env)
executeBinaryOp node@(Abs.BinaryOperationGratherEq pos) env = Abs.BinaryOperationGratherEq (checkTypeBinaryOp node env)
executeBinaryOp node@(Abs.BinaryOperationGrather pos) env = Abs.BinaryOperationGrather (checkTypeBinaryOp node env)
executeBinaryOp node@(Abs.BinaryOperationLessEq pos) env = Abs.BinaryOperationLessEq (checkTypeBinaryOp node env)
executeBinaryOp node@(Abs.BinaryOperationLess pos) env = Abs.BinaryOperationLess (checkTypeBinaryOp node env)

executeDefault :: Abs.DEFAULT Posn -> Env -> Abs.DEFAULT TCheckResult
executeDefault node@(Abs.ExpressionIntegerD pos value) env = Abs.ExpressionIntegerD (checkTypeDefault node env) (executeInteger value env)
executeDefault node@(Abs.ExpressionBooleanD pos value) env = Abs.ExpressionBooleanD (checkTypeDefault node env) (executeBoolean value env)
executeDefault node@(Abs.ExpressionCharD pos value) env = Abs.ExpressionCharD (checkTypeDefault node env) (executeChar value env)
executeDefault node@(Abs.ExpressionStringD pos value) env = Abs.ExpressionStringD (checkTypeDefault node env) (executeString value env)
executeDefault node@(Abs.ExpressionRealD pos value) env = Abs.ExpressionRealD (checkTypeDefault node env) (executeReal value env)
executeDefault node@(Abs.ExpressionBracketD pos exp) env = Abs.ExpressionBracketD (checkTypeDefault node env) (executeExpression exp env)
executeDefault node@(Abs.ExpressionIdentD pos id index) env = case index of
                                                                Abs.ArrayIndexElementEmpty posIdx -> Abs.ExpressionIdentD (checkTypeIdent id env) (executeIdent id env) (executeArrayIndexElement (Abs.ArrayIndexElementEmpty posIdx) env)
                                                                Abs.ArrayIndexElement posIdx tipo -> Abs.ExpressionIdentD (checkTypeIdent id env) (executeIdent id env) (Abs.ArrayIndexElementEmpty (TError ["index si"]))


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

-------------------------------------------------------------------------------------------------------
-- TYPE CHECKS FUNCTIONS ------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------

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
checkTypeStatement node@(Abs.AssignmentStatement pos lval assignOp exp) env = let expTCheck = checkTypeExpression exp env in if(checkCompatibility expTCheck (checkTypeLvalueExpression lval env)) then expTCheck else TError ["incompatible type at "++show pos]
checkTypeStatement node@(Abs.VariableDeclarationStatement pos tipo vardec) env = checkTypeType tipo env
checkTypeStatement node@(Abs.ConditionalStatement pos condition) env = checkTypeCondition condition env
checkTypeStatement node@(Abs.WhileDoStatement pos whileState) env = checkTypeWhile whileState env
checkTypeStatement node@(Abs.DoWhileStatement pos doState) env = checkTypeDo doState env
checkTypeStatement node@(Abs.ForStatement pos forState) env = checkTypeForState forState env
checkTypeStatement node@(Abs.ForAllStatement pos forAllState) env = checkTypeForAllState forAllState env
checkTypeStatement node@(Abs.ProcedureStatement pos id param states) env = TError ["todo proc"]
checkTypeStatement node@(Abs.FunctionStatement pos id param tipo states) env = TError ["todo funz"]


checkTypeCondition :: Abs.CONDITIONALSTATE Posn -> Env -> TCheckResult
checkTypeCondition node@(Abs.ConditionalStatementSimpleThen pos exp state elseState) env = TError ["if con then"]
checkTypeCondition node@(Abs.ConditionalStatementSimpleWThen pos exp b elseState) env = TError ["if senza then"]
checkTypeCondition node@(Abs.ConditionalStatementCtrlThen pos ctrlState state elseState) env = TError ["if con then e ctrl"] 
checkTypeCondition node@(Abs.ConditionalStatementCtrlWThen pos ctrlState b elseState) env = TError ["if senza then e con ctrl"]

checkTypeElseState :: Abs.ELSESTATEMENT Posn -> Env -> TCheckResult
checkTypeElseState node@(Abs.ElseState pos state) env = TError ["else non empty"] --non sicuri se diretto o bisogna andare sul figlio
checkTypeElseState node@(Abs.ElseStateEmpty pos) env = TError ["else empty"]

checkTypeCtrlState :: Abs.CTRLDECSTATEMENT Posn -> Env -> TCheckResult
checkTypeCtrlState node@(Abs.CtrlDecStateConst pos id exp) env = TError ["ctrl const"] --da controllare come else
checkTypeCtrlState node@(Abs.CtrlDecStateVar pos id exp) env = TError ["ctrl var"] --da controllare come else

checkTypeWhile :: Abs.WHILESTATEMENT Posn -> Env -> TCheckResult
checkTypeWhile node@(Abs.WhileStateSimpleDo pos exp state) env = TError ["while do"] --da controllare come else
checkTypeWhile node@(Abs.WhileStateSimpleWDo pos exp b) env = TError ["while"] --da controllare come else
checkTypeWhile node@(Abs.WhileStateCtrlDo pos ctrl state) env = TError ["while do ctrl"] --da controllare come else
checkTypeWhile node@(Abs.WhileStateCtrlWDo pos ctrl b) env = TError ["while ctrl"] --da controllare come else

checkTypeDo :: Abs.DOSTATEMENT Posn -> Env -> TCheckResult
checkTypeDo node@(Abs.DoWhileState pos state exp) env = TError ["do "] --da controllare come else

checkTypeForState :: Abs.FORSTATEMENT Posn -> Env -> TCheckResult
checkTypeForState node@(Abs.ForStateIndexDo pos index exp state) env = TError ["for idx do"] --da controllare come else
checkTypeForState node@(Abs.ForStateIndexWDo pos index exp b) env = TError ["for idx "] --da controllare come else
checkTypeForState node@(Abs.ForStateExprDo pos exp state) env = TError ["for exp do"] --da controllare come else
checkTypeForState node@(Abs.ForStateExprWDo pos exp b) env = TError ["for exp"] --da controllare come else

checkTypeIndexVarDec :: Abs.INDEXVARDEC Posn -> Env -> TCheckResult
checkTypeIndexVarDec node@(Abs.IndexVarDeclaration pos id) env =  TError ["index var dec"] --da controllare come else

checkTypeForAllState :: Abs.FORALLSTATEMENT Posn -> Env -> TCheckResult
checkTypeForAllState node@(Abs.ForAllStateIndexDo pos index exp state) env = TError ["forall idx do"] --da controllare come else
checkTypeForAllState node@(Abs.ForAllStateIndexWDo pos index exp b) env = TError ["forall idx "] --da controllare come else
checkTypeForAllState node@(Abs.ForAllStateExprDo pos exp state) env = TError ["forall exp do"] --da controllare come else
checkTypeForAllState node@(Abs.ForAllStateExprWDo pos exp b) env = TError ["forall exp"] --da controllare come else


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
checkTypeReturnState node@(Abs.ReturnStateEmpty pos ) env = case Data.Map.lookup "return" env of--(searchFunction (Data.Map.toList env) pos []) of
    Just result -> TResult env (B_type Type_Void) pos
    Nothing -> TError ["Unexpected return at " ++ (show pos)]

checkTypeExpressionStatement :: Abs.EXPRESSIONSTATEMENT Posn -> Env -> TCheckResult
checkTypeExpressionStatement node@(Abs.VariableExpression pos id) env = checkTypeIdent id env
checkTypeExpressionStatement node@(Abs.CallExpression pos callexpr) env = checkTypeCallExpression callexpr env

checkTypeExpressions :: Abs.EXPRESSIONS Posn -> Env -> TCheckResult
checkTypeExpressions node@(Abs.Expressions pos exp exps) env = TError ["exps"]
checkTypeExpressions node@(Abs.Expression pos exp) env = TError ["exp"]
checkTypeExpressions node@(Abs.ExpressionEmpty pos) env = TError ["empty"]

checkTypeExpression :: Abs.EXPRESSION Posn -> Env -> TCheckResult
checkTypeExpression node@(Abs.ExpressionInteger pos value) env = checkTypeInteger value env
checkTypeExpression node@(Abs.ExpressionBoolean pos value) env = checkTypeBoolean value env
checkTypeExpression node@(Abs.ExpressionChar pos value) env = checkTypeChar value env
checkTypeExpression node@(Abs.ExpressionString pos value) env = checkTypeString value env
checkTypeExpression node@(Abs.ExpressionReal pos value) env = checkTypeReal value env
checkTypeExpression node@(Abs.ExpressionBracket pos exp) env = checkTypeExpression exp env
checkTypeExpression node@(Abs.ExpressionCast pos def tipo) env = let tipoTCheck = checkPrimitiveType tipo env in if(checkCompatibility (checkTypeDefault def env) tipoTCheck) then tipoTCheck else TError ["Incompatibility type for casting at "++show pos]
checkTypeExpression node@(Abs.ExpressionUnary pos unary exp) env = let unaryTCheck = checkTypeUnaryOp unary env in if(checkCompatibility (checkTypeExpression exp env) unaryTCheck) then (checkTypeExpression exp env) else TError ["Incompatibility type for unary operator at "++show pos]
checkTypeExpression node@(Abs.ExpressionBinary pos def binary exp) env = let expCheck = checkTypeExpression exp env in
                                                                            (let defCheck = checkTypeDefault def env in 
                                                                                (let binaryTCheck = checkTypeBinaryOp binary env in if (checkCompatibility defCheck expCheck || checkCompatibility expCheck defCheck)
                                                                                    then let ty = returnSuperType expCheck defCheck in case binaryTCheck of
                                                                                        TResult _ (B_type Type_Real) _ -> if (checkCompatibility ty binaryTCheck) then ty else TError ["Incompatibility type for binary operator at "++show pos]
                                                                                        TResult _ (B_type Type_Boolean) _ -> case binary of
                                                                                            (Abs.BinaryOperationOr pos) -> if (checkCompatibility ty binaryTCheck) then ty else TError ["Incompatibility type for binary operator at "++show pos]
                                                                                            (Abs.BinaryOperationAnd pos) -> if (checkCompatibility ty binaryTCheck) then ty else TError ["Incompatibility type for binary operator at "++show pos]
                                                                                            (Abs.BinaryOperationEq pos) -> ty
                                                                                            (Abs.BinaryOperationNotEq pos) -> ty
                                                                                            _ -> if (checkCompatibility ty (TResult env (B_type Type_Real) pos)) || (checkCompatibility ty (TResult env (B_type Type_String) pos)) || (checkCompatibility ty (TResult env (B_type Type_Char) pos)) 
                                                                                                then ty 
                                                                                                else TError ["Incompatibility type for binary operator at "++show pos]
                                                                                    else TError ["a and b incomp types? "++show pos]
                                                                                    ))
checkTypeExpression node@(Abs.ExpressionIdent pos value index) env = checkTypeIdent value env --gestire index
checkTypeExpression node@(Abs.ExpressionCall pos id exps) env = checkTypeExpressions exps env --gestire compatibilità exps con id

checkTypeUnaryOp :: Abs.UNARYOP Posn -> Env -> TCheckResult
checkTypeUnaryOp node@(Abs.UnaryOperationPositive pos) env = TResult env (B_type Type_Real) pos
checkTypeUnaryOp node@(Abs.UnaryOperationNegative pos) env = TResult env (B_type Type_Real) pos
checkTypeUnaryOp node@(Abs.UnaryOperationNot pos) env = TResult env (B_type Type_Boolean) pos
checkTypeUnaryOp node@(Abs.UnaryOperationPointer pos) env = TError ["pointer"] --da rivedere

checkTypeBinaryOp :: Abs.BINARYOP Posn -> Env -> TCheckResult
checkTypeBinaryOp node@(Abs.BinaryOperationPlus pos) env = TResult env (B_type Type_Real) pos
checkTypeBinaryOp node@(Abs.BinaryOperationMinus pos) env = TResult env (B_type Type_Real) pos
checkTypeBinaryOp node@(Abs.BinaryOperationProduct pos) env = TResult env (B_type Type_Real) pos
checkTypeBinaryOp node@(Abs.BinaryOperationDivision pos) env = TResult env (B_type Type_Real) pos
checkTypeBinaryOp node@(Abs.BinaryOperationModule pos) env = TResult env (B_type Type_Real) pos
checkTypeBinaryOp node@(Abs.BinaryOperationPower pos) env = TResult env (B_type Type_Real) pos
checkTypeBinaryOp node@(Abs.BinaryOperationAnd pos) env = TResult env (B_type Type_Boolean) pos
checkTypeBinaryOp node@(Abs.BinaryOperationOr pos) env = TResult env (B_type Type_Boolean) pos
checkTypeBinaryOp node@(Abs.BinaryOperationEq pos) env = TResult env (B_type Type_Boolean) pos
checkTypeBinaryOp node@(Abs.BinaryOperationNotEq pos) env = TResult env (B_type Type_Boolean) pos
checkTypeBinaryOp node@(Abs.BinaryOperationGratherEq pos) env = TResult env (B_type Type_Boolean) pos
checkTypeBinaryOp node@(Abs.BinaryOperationGrather pos) env = TResult env (B_type Type_Boolean) pos
checkTypeBinaryOp node@(Abs.BinaryOperationLessEq pos) env = TResult env (B_type Type_Boolean) pos
checkTypeBinaryOp node@(Abs.BinaryOperationLess pos) env = TResult env (B_type Type_Boolean) pos

checkTypeDefault :: Abs.DEFAULT Posn -> Env -> TCheckResult
checkTypeDefault node@(Abs.ExpressionIntegerD pos value) env = checkTypeInteger value env
checkTypeDefault node@(Abs.ExpressionBooleanD pos value) env = checkTypeBoolean value env
checkTypeDefault node@(Abs.ExpressionCharD pos value) env = checkTypeChar value env
checkTypeDefault node@(Abs.ExpressionStringD pos value) env = checkTypeString value env
checkTypeDefault node@(Abs.ExpressionRealD pos value) env = checkTypeReal value env
checkTypeDefault node@(Abs.ExpressionBracketD pos exp) env = checkTypeExpression exp env
checkTypeDefault node@(Abs.ExpressionIdentD pos value index) env = checkTypeIdent value env --gestire index

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


checkTypeCallExpression :: Abs.CALLEXPRESSION Posn -> Env -> TCheckResult
checkTypeCallExpression node@(Abs.CallExpressionParentheses pos id namedexpr) env = TError ["mhh?"]
checkTypeCallExpression node@(Abs.CallExpressionQuadre pos id namedexpr) env = TError ["mhh?"]

checkTypeNamedExpressionList :: Abs.NAMEDEXPRESSIONLIST Posn -> Env -> TCheckResult
checkTypeNamedExpressionList node@(Abs.NamedExpressionList pos namedexprlist) env = TError ["mhh?"]
checkTypeNamedExpressionList node@(Abs.NamedExpressionListEmpty pos) env = TError ["mhh?"]
checkTypeNamedExpressionList node@(Abs.NamedExpressionLists pos namedexpr namedexprlist) env = TError ["mhh?"]
checkTypeNamedExpressionList node@(Abs.NamedExpressionAssigned pos id expr) env = TError ["mhh?"]

checkTypeNamedExpression :: Abs.NAMEDEXPRESSION Posn -> Env -> TCheckResult
checkTypeNamedExpression node@(Abs.NamedExpression pos expr) env = TError ["mhh?"]
                                    