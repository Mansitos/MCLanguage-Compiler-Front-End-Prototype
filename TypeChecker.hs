-- Progetto LC 2021 -- Mansi/Cagnoni UNIUD --

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module TypeChecker where

import Type
import LexProgettoPar (Posn(..))
import AbsProgettoPar as Abs
import Data.Map
import Prelude
import Data.List

-------------------------------------------------------------------------------------
--- ENVIRONMENT DATA TYPES ----------------------------------------------------------
-------------------------------------------------------------------------------------

type Env = Map Prelude.String [EnvEntry]
            -- chiave, valore

data EnvEntry
    = Variable {varType::Type, varPosition::LexProgettoPar.Posn, varMode::Prelude.String, canOverride::Prelude.Bool}
    | Function {funType::Type, funPosition::LexProgettoPar.Posn, funParameters::[Parameter]}

data Parameter
    = Parameter {paramType::Type, paramPosition::LexProgettoPar.Posn, paramMode::Prelude.String, identifier::Prelude.String}
    deriving(Eq, Ord)

data TCheckResult
    = TResult {environment::Env, t_type::Type, t_position::LexProgettoPar.Posn}
    | TError {errors::[Prelude.String]}

-------------------------------------------------------------------------------------------------
--- SHOW ISTANCES FOR ENV DATA TYPES ------------------------------------------------------------
-------------------------------------------------------------------------------------------------

instance Show EnvEntry where
    show entry = case entry of
        TypeChecker.Variable ty pos varMode canOverride -> "EnvEntry: [" ++ "var:" ++ show ty ++ "|" ++ show pos ++ "|mode:" ++ show varMode ++ "|canOverride:" ++ show canOverride ++ "]"
        TypeChecker.Function ty pos params              -> "EnvEntry: [" ++ "fun:" ++ show ty ++ "|" ++ show pos ++ "|params:" ++ show params ++ "]"

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
                                                                    Pointer t depth -> case tC of
                                                                                        Pointer ts depths -> case t of
                                                                                                            B_type Type_Integer -> if (ts==(B_type Type_Real) || ts==(B_type Type_Integer)) && depth==depths then True else False
                                                                                                            _ -> if t==ts && depth==depths then True else False
                                                                                        _ -> False
                                                                    Array t dim -> case tC of
                                                                                        Array ts dims -> case t of
                                                                                                            B_type Type_Integer -> if (ts==(B_type Type_Real) || ts==(B_type Type_Integer)) then True else False
                                                                                                            _ -> if t==ts then True else False
                                                                                        _ -> False
                                                                    _ -> False 

-- Given Type A and B (from TCheckResults) it returns the one which is more generic.
-- Semantic: Which type is more generic; a or b?
--      Examples: int int -> int
--                int real -> real 
--                real int -> real
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
                            (Variable t pos mode canOverride) -> t
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
                                                                                                                                if (checkIfCanOverride ids env) -- check if vars can be overrided (yes if inside a new block)
                                                                                                                                then (updateEnvFromListOfVarIds ids env pos varMode ty,err ++ checkErr env stat) -- updating env for each declared var.
                                                                                                                                else (env, err ++ ["Cannot redefine var ... mettere info"])))
                                                                -- Functions and Procedures
                                                                Abs.ProcedureStatement pos id params stats -> let parameters = getParamList params in
                                                                                                                let fid = getIdFromIdent id in
                                                                                                                    ((insertWith (++) fid [Function (B_type Type_Void) pos parameters] env, err ++ checkErr env stat))
                                                                
                                                                Abs.FunctionStatement pos id params ty stats -> let parameters = getParamList params in
                                                                                                                    let fty = getTypeFromPrimitive ty in
                                                                                                                        let fid = getIdFromIdent id in 
                                                                                                                            (insertWith (++) fid [Function fty pos parameters] env, err ++ checkErr env stat) 
                                                                -- generic case
                                                                _ -> (env,err) 
updateEnv node@(Abs.EmptyStatement pos) env err = (env,err)

-- Update the env for Conditional if-then-else statement
updateEnvCondStat :: (Abs.CONDITIONALSTATE Posn) -> Env -> [Prelude.String] -> (Env,[Prelude.String])
updateEnvCondStat (Abs.ConditionalStatementCtrlThen pos ctrlState state elseState) env err = case ctrlState of
                    Abs.CtrlDecStateVar pos id typepart exp -> (insertWith (++) (getIdFromIdent id) [Variable (getTypePart typepart) pos "var" False] env, err ++ checkErr env state)
                    Abs.CtrlDecStateConst pos id typepart exp -> (insertWith (++) (getIdFromIdent id) [Variable (getTypePart typepart) pos "const" False] env, err ++ checkErr env state)
updateEnvCondStat (Abs.ConditionalStatementCtrlWThen pos ctrlState b elseState) env err = case ctrlState of
                    Abs.CtrlDecStateVar pos id typepart exp -> (insertWith (++) (getIdFromIdent id) [Variable (getTypePart typepart) pos "var" False] env, err)
                    Abs.CtrlDecStateConst pos id typepart exp -> (insertWith (++) (getIdFromIdent id) [Variable (getTypePart typepart) pos "const" False] env, err)
updateEnvCondStat _ env err = (env,err)

-- Update the env for while statement
updateEnvWhileStat :: (Abs.WHILESTATEMENT Posn) -> Env -> [Prelude.String] -> (Env,[Prelude.String])
updateEnvWhileStat (Abs.WhileStateCtrlDo pos ctrl state) env err = case ctrl of
                    Abs.CtrlDecStateVar pos id typepart exp -> let newEnv = (insertWith (++) (getIdFromIdent id) [Variable (getTypePart typepart) pos "var" False] env, err ++ checkErr env state) in (insertWith (++) "while" [] (first newEnv), err ++ checkErr (first newEnv) state)
                    Abs.CtrlDecStateConst pos id typepart exp -> let newEnv = (insertWith (++) (getIdFromIdent id) [Variable (getTypePart typepart) pos "const" False] env, err ++ checkErr env state) in (insertWith (++) "while" [] (first newEnv), err ++ checkErr (first newEnv) state)
updateEnvWhileStat (Abs.WhileStateCtrlWDo pos ctrl b) env err = case ctrl of
                    Abs.CtrlDecStateVar pos id typepart exp -> let newEnv = (insertWith (++) (getIdFromIdent id) [Variable (getTypePart typepart) pos "var" False] env, err) in (insertWith (++) "while" [] (first newEnv), err)
                    Abs.CtrlDecStateConst pos id typepart exp -> let newEnv = (insertWith (++) (getIdFromIdent id) [Variable (getTypePart typepart) pos "const" False] env, err) in (insertWith (++) "while" [] (first newEnv), err)
updateEnvWhileStat (Abs.WhileStateSimpleDo pos expr state) env err = (insertWith (++) "while" [] env, err ++ checkErr env state)
updateEnvWhileStat (Abs.WhileStateSimpleWDo pos expr b) env err = (insertWith (++) "while" [] env, err)

-- Given a list of Params, it creates an envEntry of type param for each of them
createEnvEntryForParams :: [TypeChecker.Parameter] -> Env -> Env
createEnvEntryForParams ((TypeChecker.Parameter ty pos mode id):xs) env = createEnvEntryForParams xs (insertWith (++) id [Variable ty pos mode False] env)
createEnvEntryForParams [] env = env

-- Given a list of var IDS and an Env, it update that env adding the variable enventries for each var id.
updateEnvFromListOfVarIds :: [Prelude.String] -> Env -> Posn -> Prelude.String -> Type -> Env
updateEnvFromListOfVarIds [] env pos varMode ty = env
updateEnvFromListOfVarIds (x:xs) env pos varMode ty = updateEnvFromListOfVarIds xs (insertWith (++) x [Variable ty pos varMode False] env) pos varMode ty

-- Given an Env set to TRUE in CanOverride for each variable!
-- Used at the beginning of a new bloc (for example, after declaring a function, inside it is possible to override previous variable declaration (those outside))
updateIfCanOverride :: Env -> Env
updateIfCanOverride env = Data.Map.fromList (updateIfCanOverride_ (Data.Map.toList env))

-- Implementation of the previous function
updateIfCanOverride_ :: [(Prelude.String, [EnvEntry])] -> [(Prelude.String, [EnvEntry])]
updateIfCanOverride_ ((str,entry:entries):xs) = case entry of
                    Variable ty pos varMode canOverride ->  [(str,(Variable ty pos varMode True):entries)] ++ updateIfCanOverride_ xs
                    _ -> [(str,entry:(updateIfCanOverrideEntries_ entries))] ++ updateIfCanOverride_ xs
updateIfCanOverride_ ((str,[]):xs) = ((str,[]):xs)
updateIfCanOverride_ [] = []

-- "while" []

-- Sub-Function of updateIfCanOverride_
updateIfCanOverrideEntries_ :: [EnvEntry] -> [EnvEntry]
updateIfCanOverrideEntries_ (x:xs) = case x of
                                        Variable ty pos varMode canOverride -> (Variable ty pos varMode True):xs
                                        _ -> [x] ++ updateIfCanOverrideEntries_ xs
updateIfCanOverrideEntries_ []     = [] 

-- TODO
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

-- Given a list of parameters (from a func env entry) returns the list of types of each parameter
getTypeListFromFuncParams :: [Parameter] -> [Type]
getTypeListFromFuncParams ((TypeChecker.Parameter ty _ _ _):xs) = [ty] ++ getTypeListFromFuncParams xs
getTypeListFromFuncParams [] = []

-- Given a list of variable ids, returns true if they can be overrided (false if at least one of them CANNOT be overrided)
checkIfCanOverride :: [Prelude.String] -> Env -> Bool
checkIfCanOverride (x:xs) env = case Data.Map.lookup x env of
    Just (entry:entries) -> case entry of
        Variable ty pos varMode canOverride -> canOverride && (checkIfCanOverride xs env)
        _ -> True && (checkIfCanOverride xs env)
    Nothing -> True && (checkIfCanOverride xs env)
checkIfCanOverride [] env = True

-- Given a parameter list, return the list of ids
getListOfIdsFromParamList :: [TypeChecker.Parameter] -> [Prelude.String]
getListOfIdsFromParamList ((TypeChecker.Parameter ty pos mode id):xs) = [id] ++ getListOfIdsFromParamList xs
getListOfIdsFromParamList [] = []

-- Return true if there is a dups in the list (of parameters ids)
checkDuplicatedParametersInFunDecl :: [Prelude.String] -> Prelude.Bool
checkDuplicatedParametersInFunDecl (x:xs) = isInList x xs || checkDuplicatedParametersInFunDecl xs
checkDuplicatedParametersInFunDecl [] = False

-- Return true if the given string is in the given string list
isInList :: Prelude.String -> [Prelude.String] -> Prelude.Bool
isInList id (x:xs) = id == x || isInList id xs
isInList id [] = False

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
getTypeExpr (Abs.TypeExpressionArraySimple _ rangeexp primitive) = Array (getTypeFromPrimitive primitive) (getArrayDim rangeexp)
getTypeExpr (Abs.TypeExpressionArray _ rangeexp primitive) = Array (getTypeFromPrimitive primitive) (getArrayDim rangeexp)
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
getTypeFromPrimitive (Abs.TypeArray _ prim) =  (Type.Array (getTypeFromPrimitive prim) (getArrayDimFunc prim))

getArrayDimFunc :: Abs.PRIMITIVETYPE Posn -> Prelude.Integer
getArrayDimFunc (Abs.TypeArray _ ty) = 1 + getArrayDimFunc ty
getArrayDimFunc _ = 1

getArrayDim :: Abs.RANGEEXP Posn -> Prelude.Integer
getArrayDim (Abs.RangeExpression pos exp1 exp2 rangeexp) = 1 + getArrayDim rangeexp
getArrayDim _ = 1

-- Get a PrimitiveType node of an array abs node, it returns the primitive type
-- Example: var x:[][][]int -> int
getArrayPrimitiveType :: Abs.PRIMITIVETYPE Posn -> Type
getArrayPrimitiveType (Abs.PrimitiveTypeVoid _) = (B_type Type_Void)
getArrayPrimitiveType (Abs.PrimitiveTypeBool _) = (B_type Type_Boolean)
getArrayPrimitiveType (Abs.PrimitiveTypeInt _) = (B_type Type_Integer)
getArrayPrimitiveType (Abs.PrimitiveTypeReal _) = (B_type Type_Real)
getArrayPrimitiveType (Abs.PrimitiveTypeString _) = (B_type Type_String)
getArrayPrimitiveType (Abs.PrimitiveTypeChar _) = (B_type Type_Char)
getArrayPrimitiveType (Abs.TypeArray _ prim) =  getArrayPrimitiveType prim

-- Get a VarDecList (list of vars declarations) of the ABS, returns a list of strings, where each element is the id of the vars
getVariableDeclStatNames :: Abs.VARDECLIST Posn -> [Prelude.String]
getVariableDeclStatNames (Abs.VariableDeclarationSingle _ (Abs.VariableDeclaration _ id _ _)) = getIdList id

-- Given an IdentList node, return a list of string containing all the ids
getIdList :: Abs.IDENTLIST Posn -> [Prelude.String]
getIdList (Abs.IdentifierList _ (Abs.Ident s _) identlist) = [s] ++ getIdList identlist
getIdList (Abs.IdentifierSingle _ (Abs.Ident s _)) = [s] 
             
---------------------------------------------------------------------------------------------------
--- EXECUTION FUNCTIONS ---------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

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
executeStatement node@(Abs.Statement _ b) env = let newEnv = updateIfCanOverride env in Abs.Statement (checkTypeStatement node env) (executeB b newEnv)
executeStatement node@(Abs.ExpressionStatement _ exp) env = Abs.ExpressionStatement (checkTypeStatement node env) (executeExpressionStatement exp env)
executeStatement node@(Abs.AssignmentStatement pos lval assignOp exp) env = Abs.AssignmentStatement (checkTypeStatement node env) (executeLValue lval env) (executeAssignOp assignOp env) (executeExpression exp env)
executeStatement node@(Abs.VariableDeclarationStatement pos tipo vardec) env = Abs.VariableDeclarationStatement (checkTypeStatement node env) (executeVarType tipo env) (executeVarDecList vardec env)
executeStatement node@(Abs.ConditionalStatement pos condition) env = let newEnv = updateEnvCondStat condition (updateIfCanOverride env) [] in Abs.ConditionalStatement (checkTypeStatement node env) (executeConditionalState condition (first newEnv))
executeStatement node@(Abs.WhileDoStatement pos whileStaement) env = let newEnv = updateEnvWhileStat whileStaement (updateIfCanOverride env) [] in Abs.WhileDoStatement (checkTypeStatement node env) (executeWhileState whileStaement (first newEnv))
executeStatement node@(Abs.DoWhileStatement pos doStatement) env = Abs.DoWhileStatement (checkTypeStatement node env) (executeDoState doStatement env)
executeStatement node@(Abs.ForStatement pos forStatement) env = Abs.ForStatement (checkTypeStatement node env) (executeForState forStatement env)
executeStatement node@(Abs.ForAllStatement pos forAllStatement) env = Abs.ForAllStatement (checkTypeStatement node env) (executeForAllState forAllStatement env)
executeStatement node@(Abs.ProcedureStatement pos id param states) env = let newEnv = createEnvEntryForParams (getParamList param) (updateIfCanOverride (first (updateEnv (Abs.ListStatements pos node (Abs.EmptyStatement pos)) env []))) in
                                                                            let newEnv2 = Data.Map.delete "while" (first (insertWith (++) "return" [] newEnv, [])) in  
                                                                                Abs.ProcedureStatement (checkTypeStatement node env) (executeIdentFunc id env) (executeParam param env) (executeStatements states newEnv2)
executeStatement node@(Abs.FunctionStatement pos id param tipo states) env = let newEnv = createEnvEntryForParams (getParamList param) (updateIfCanOverride (first (updateEnv (Abs.ListStatements pos node (Abs.EmptyStatement pos)) env []))) in
                                                                                let newEnv2 = Data.Map.delete "while" (first (insertWith (++) "return" [] newEnv, [])) in  
                                                                                    Abs.FunctionStatement (checkTypeStatement node env) (executeIdentFunc id env) (executeParam param env) (executePrimitiveType tipo env) (executeStatements states newEnv2)

executeParam :: Abs.PARAMETERS Posn -> Env -> Abs.PARAMETERS TCheckResult
executeParam node@(Abs.ParameterList pos param params) env = Abs.ParameterList (checkTypeExecuteParameter node env) (executeParameter param env) (executeParam params env)
executeParam node@(Abs.ParameterListSingle pos param) env = Abs.ParameterListSingle (checkTypeExecuteParameter node env) (executeParameter param env)
executeParam node@(Abs.ParameterListEmpty pos) env = Abs.ParameterListEmpty (checkTypeExecuteParameter node env) 

executeParameter :: Abs.PARAMETER Posn -> Env -> Abs.PARAMETER TCheckResult
executeParameter node@(Abs.Parameter pos id ty) env = Abs.Parameter (checkTypeParameter node env) (executeIdentVar id env) (executePrimitiveType ty env)

executeConditionalState :: Abs.CONDITIONALSTATE Posn -> Env -> Abs.CONDITIONALSTATE TCheckResult
executeConditionalState node@(Abs.ConditionalStatementSimpleThen pos exp state elseState) env = Abs.ConditionalStatementSimpleThen (checkTypeCondition node env) (executeExpression exp env) (executeStatement state env) (executeElseStatement elseState env)
executeConditionalState node@(Abs.ConditionalStatementSimpleWThen pos exp b elseState) env = Abs.ConditionalStatementSimpleWThen (checkTypeCondition node env) (executeExpression exp env) (executeB b env) (executeElseStatement elseState env)
executeConditionalState node@(Abs.ConditionalStatementCtrlThen pos ctrlState state elseState) env = Abs.ConditionalStatementCtrlThen (checkTypeCondition node env) (executeCtrlStatement ctrlState env) (executeStatement state env) (executeElseStatement elseState env)
executeConditionalState node@(Abs.ConditionalStatementCtrlWThen pos ctrlState b elseState) env = Abs.ConditionalStatementCtrlWThen (checkTypeCondition node env) (executeCtrlStatement ctrlState env) (executeB b env) (executeElseStatement elseState env)

executeElseStatement :: Abs.ELSESTATEMENT Posn -> Env -> Abs.ELSESTATEMENT TCheckResult
executeElseStatement node@(Abs.ElseStateEmpty pos) env= Abs.ElseStateEmpty (checkTypeElseState node env)
executeElseStatement node@(Abs.ElseState pos state) env= Abs.ElseState (checkTypeElseState node env) (executeStatement state env)

executeCtrlStatement :: Abs.CTRLDECSTATEMENT Posn -> Env -> Abs.CTRLDECSTATEMENT TCheckResult
executeCtrlStatement node@(Abs.CtrlDecStateVar pos id typepart exp) env = Abs.CtrlDecStateVar (checkTypeCtrlState node env) (executeIdentVar id env) (executeTypePart typepart env) (executeExpression exp env)
executeCtrlStatement node@(Abs.CtrlDecStateConst pos id typepart exp) env = Abs.CtrlDecStateConst (checkTypeCtrlState node env) (executeIdentVar id env) (executeTypePart typepart env) (executeExpression exp env)

executeWhileState :: Abs.WHILESTATEMENT Posn -> Env -> Abs.WHILESTATEMENT TCheckResult
executeWhileState node@(Abs.WhileStateSimpleDo pos exp state) env = Abs.WhileStateSimpleDo (checkTypeWhile node env) (executeExpression exp env) (executeStatement state env)
executeWhileState node@(Abs.WhileStateSimpleWDo pos exp b) env = Abs.WhileStateSimpleWDo (checkTypeWhile node env) (executeExpression exp env) (executeB b env)
executeWhileState node@(Abs.WhileStateCtrlDo pos ctrl state) env = Abs.WhileStateCtrlDo (checkTypeWhile node env) (executeCtrlStatement ctrl env) (executeStatement state env)
executeWhileState node@(Abs.WhileStateCtrlWDo pos ctrl b) env = Abs.WhileStateCtrlWDo (checkTypeWhile node env) (executeCtrlStatement ctrl env) (executeB b env)

executeDoState :: Abs.DOSTATEMENT Posn -> Env -> Abs.DOSTATEMENT TCheckResult
executeDoState node@(Abs.DoWhileState pos state exp) env = Abs.DoWhileState (checkTypeDo node env) (executeStatement state env) (executeExpression exp env)

executeForState :: Abs.FORSTATEMENT Posn -> Env -> Abs.FORSTATEMENT TCheckResult
executeForState node@(Abs.ForStateIndexDo pos index rangexp state) env = Abs.ForStateIndexDo (checkTypeForState node env) (executeIndex index env) (executeRangeExp rangexp env) (executeStatement state env)
executeForState node@(Abs.ForStateIndexWDo pos index rangexp b) env = Abs.ForStateIndexWDo (checkTypeForState node env) (executeIndex index env) (executeRangeExp rangexp env) (executeB b env)
executeForState node@(Abs.ForStateExprDo pos rangexp state) env = Abs.ForStateExprDo (checkTypeForState node env) (executeRangeExp rangexp env) (executeStatement state env)
executeForState node@(Abs.ForStateExprWDo pos rangexp b) env = Abs.ForStateExprWDo (checkTypeForState node env) (executeRangeExp rangexp env) (executeB b env)

executeIndex :: Abs.INDEXVARDEC Posn -> Env -> Abs.INDEXVARDEC TCheckResult
executeIndex node@(Abs.IndexVarDeclaration pos id) env = Abs.IndexVarDeclaration (checkTypeIndexVarDec node env) (executeIdentVar id env)

executeForAllState :: Abs.FORALLSTATEMENT Posn -> Env -> Abs.FORALLSTATEMENT TCheckResult
executeForAllState node@(Abs.ForAllStateIndexDo pos index rangexp state) env = Abs.ForAllStateIndexDo (checkTypeForAllState node env) (executeIndex index env) (executeRangeExp rangexp env) (executeStatement state env)
executeForAllState node@(Abs.ForAllStateIndexWDo pos index rangexp b) env = Abs.ForAllStateIndexWDo (checkTypeForAllState node env) (executeIndex index env) (executeRangeExp rangexp env) (executeB b env)
executeForAllState node@(Abs.ForAllStateExprDo pos rangexp state) env = Abs.ForAllStateExprDo (checkTypeForAllState node env) (executeRangeExp rangexp env) (executeStatement state env)
executeForAllState node@(Abs.ForAllStateExprWDo pos rangexp b) env = Abs.ForAllStateExprWDo (checkTypeForAllState node env) (executeRangeExp rangexp env) (executeB b env)

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
executeIDList node@(Abs.IdentifierList pos id next) env = Abs.IdentifierList (checkIdentifierList node env) (executeIdentVar id env) (executeIDList next env)
executeIDList node@(Abs.IdentifierSingle pos id) env = Abs.IdentifierSingle (checkIdentifierList node env) (executeIdentVar id env)

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
executeExpressionStatement node@(Abs.VariableExpression pos id) env = Abs.VariableExpression (checkTypeExpressionStatement node env) (executeIdentVar id env)
executeExpressionStatement node@(Abs.CallExpression pos callexpr) env = Abs.CallExpression (checkTypeExpressionStatement node env) (executeCallExpression callexpr env)

executeCallExpression :: Abs.CALLEXPRESSION Posn -> Env -> Abs.CALLEXPRESSION TCheckResult
executeCallExpression node@(Abs.CallExpressionParentheses pos id namedexpr) env = Abs.CallExpressionParentheses (checkTypeCallExpression node env) (executeIdentFunc id env) (executeNamedExpressionList namedexpr env)
executeCallExpression node@(Abs.CallExpressionQuadre pos id namedexpr) env = Abs.CallExpressionQuadre (checkTypeCallExpression node env) (executeIdentFunc id env) (executeNamedExpressionList namedexpr env)
-- quadre -> array?

executeNamedExpressionList :: Abs.NAMEDEXPRESSIONLIST Posn -> Env -> Abs.NAMEDEXPRESSIONLIST TCheckResult
executeNamedExpressionList node@(Abs.NamedExpressionList pos namedexpr) env = Abs.NamedExpressionList (checkTypeNamedExpressionList node env) (executeNamedExpression namedexpr env)
executeNamedExpressionList node@(Abs.NamedExpressionListEmpty pos) env = Abs.NamedExpressionListEmpty (TResult env (B_type Type_Void) pos)
executeNamedExpressionList node@(Abs.NamedExpressionLists pos namedexpr namedexprlist) env = Abs.NamedExpressionLists (checkTypeNamedExpressionList node env) (executeNamedExpression namedexpr env) (executeNamedExpressionList namedexprlist env)
executeNamedExpressionList node@(Abs.NamedExpressionAssigned pos id expr) env = Abs.NamedExpressionAssigned (checkTypeNamedExpressionList node env) (executeIdentVar id env) (executeExpression expr env)

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
executeExpression node@(Abs.ExpressionUnary pos unary exp) env = case unary of
                                                                Abs.UnaryOperationPointer pos -> if (checkDepthIsCorrect node env 0) then Abs.ExpressionUnary (checkTypeExpression node env) (executeUnaryOp unary env) (executeExpression exp env) else Abs.ExpressionUnary (TError ["number of pointer symbol is different at "++show pos]) (executeUnaryOp unary env) (executeExpression exp env)
                                                                _ -> Abs.ExpressionUnary (checkTypeExpression node env) (executeUnaryOp unary env) (executeExpression exp env)
executeExpression node@(Abs.ExpressionBinary pos def binary exp) env = Abs.ExpressionBinary (checkTypeExpression node env) (executeDefault def env) (executeBinaryOp binary env) (executeExpression exp env)
executeExpression node@(Abs.ExpressionIdent pos id index) env = case index of
                                                                Abs.ArrayIndexElementEmpty posIdx -> Abs.ExpressionIdent (checkTypeIdentVar id env) (executeIdentVar id env) (executeArrayIndexElement (Abs.ArrayIndexElementEmpty posIdx) env)
                                                                Abs.ArrayIndexElement posIdx tipo -> Abs.ExpressionIdent (checkTypeIdentVar id env) (executeIdentVar id env) (Abs.ArrayIndexElementEmpty (TError ["index si"]))
executeExpression node@(Abs.ExpressionCall pos id exps) env = Abs.ExpressionCall (checkTypeExpression node env) (executeIdentFunc id env) (executeExpressions exps env) 

checkDepthIsCorrect :: Abs.EXPRESSION Posn -> Env -> Prelude.Integer -> Prelude.Bool
checkDepthIsCorrect node@(Abs.ExpressionUnary pos unary exp) env d = case unary of
                                                                    Abs.UnaryOperationPointer pos -> checkDepthIsCorrect exp env (d+1)
                                                                    _ -> False
checkDepthIsCorrect node@(Abs.ExpressionIdent pos id index) env d = case index of
                                                                    Abs.ArrayIndexElementEmpty posIdx -> if (depthIsEqual (checkTypeIdentVar id env) d) then True else False
                                                                    Abs.ArrayIndexElement posIdx tipo -> False
checkDepthIsCorrect _ env d = False                                                                    

depthIsEqual :: TCheckResult -> Prelude.Integer -> Bool
depthIsEqual (TResult env (Pointer t d) pos) depth = if d==depth then True else False
depthIsEqual _ depth = False

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
                                                                Abs.ArrayIndexElementEmpty posIdx -> Abs.ExpressionIdentD (checkTypeIdentVar id env) (executeIdentVar id env) (executeArrayIndexElement (Abs.ArrayIndexElementEmpty posIdx) env)
                                                                Abs.ArrayIndexElement posIdx tipo -> Abs.ExpressionIdentD (checkTypeIdentVar id env) (executeIdentVar id env) (executeArrayIndexElement index env)


executeLValue :: Abs.LVALUEEXPRESSION Posn -> Env -> Abs.LVALUEEXPRESSION TCheckResult
executeLValue node@(Abs.LvalueExpression pos id ident) env = case ident of
                                                            Abs.ArrayIndexElementEmpty posIdx -> Abs.LvalueExpression (checkTypeLvalueExpression node env) (executeIdentVar id env) (executeArrayIndexElement (Abs.ArrayIndexElementEmpty posIdx) env)
                                                            Abs.ArrayIndexElement posIdx tipo -> Abs.LvalueExpression (checkTypeLvalueExpression node env) (executeIdentVar id env) (executeArrayIndexElement (Abs.ArrayIndexElement posIdx tipo ) env)
executeLValue node@(Abs.LvalueExpressions pos id ident next) env = case ident of
                                                            Abs.ArrayIndexElementEmpty posIdx -> Abs.LvalueExpressions (checkTypeLvalueExpression node env) (executeIdentVar id env) (executeArrayIndexElement (Abs.ArrayIndexElementEmpty posIdx) env) (executeLValue next env)
                                                            Abs.ArrayIndexElement posIdx tipo -> Abs.LvalueExpressions (checkTypeLvalueExpression node env) (executeIdentVar id env) (executeArrayIndexElement (Abs.ArrayIndexElement posIdx tipo ) env)  (executeLValue next env)                
                                                                                                
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
executeTypeTypeIndex node@(Abs.TypeOfIndexVar pos typeindex id) env = Abs.TypeOfIndexVar (checkTypeTypeIndex node env) (executeTypeTypeIndex typeindex env) (executeIdentVar id env)
executeTypeTypeIndex node@(Abs.TypeOfIndexVarSingle pos id) env = Abs.TypeOfIndexVarSingle (checkTypeTypeIndex node env) (executeIdentVar id env)

executeIdentFunc :: Abs.Ident Posn -> Env -> Abs.Ident TCheckResult
executeIdentFunc node@(Abs.Ident id pos) env = Abs.Ident id (checkTypeIdentFunc node env)

executeIdentVar :: Abs.Ident Posn -> Env -> Abs.Ident TCheckResult
executeIdentVar node@(Abs.Ident id pos) env = Abs.Ident id (checkTypeIdentVar node env)

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
checkTypeLvalueExpression node@(Abs.LvalueExpression pos ident@(Abs.Ident id posI) index) env = case Data.Map.lookup id env of
                                                                        Just [Variable (Array t dim) pos mode override] -> if dim == (countIndex index) then checkTypeIdentVar ident env else TError ["number of index different at "++show pos] 
                                                                        Just _ -> checkTypeIdentVar ident env
                                                                        Nothing -> TError ["ident not find at "++show pos]
checkTypeLvalueExpression node@(Abs.LvalueExpressions pos ident@(Abs.Ident id posI) index next) env = case Data.Map.lookup id env of
                                                                        Just [Variable (Array t dim) pos mode override] -> if dim == (countIndex index) 
                                                                            then if (checkCompatibility (getRealType (checkTypeIdentVar ident env)) (checkTypeLvalueExpression next env)) then checkTypeIdentVar ident env else TError ["not all ident have same type at "++show pos]
                                                                            else TError ["number of index different at "++show pos] 
                                                                        Just _ -> if (checkCompatibility (getRealType (checkTypeIdentVar ident env)) (checkTypeLvalueExpression next env)) then checkTypeIdentVar ident env else TError ["not all ident have same type at "++show pos]
                                                                        Nothing -> TError ["ident not find at "++show pos]

countIndex :: Abs.ARRAYINDEXELEMENT Posn -> Prelude.Integer 
countIndex (Abs.ArrayIndexElement pos ti) = countIndex_ ti
countIndex (Abs.ArrayIndexElementEmpty pos) = 0

countIndex_ :: Abs.TYPEINDEX Posn -> Prelude.Integer 
countIndex_ (Abs.TypeOfIndexInt pos ti val) = 1 + countIndex_ ti
countIndex_ (Abs.TypeOfIndexIntSingle pos val) = 1 
countIndex_ (Abs.TypeOfIndexVar pos ti val) = 1 + countIndex_ ti
countIndex_ (Abs.TypeOfIndexVarSingle pos val) = 1 

getRealType :: TCheckResult -> TCheckResult
getRealType tcheck = case tcheck of
                    TResult env (Pointer t depth) pos -> TResult env t pos
                    TResult env (Array t dim) pos -> TResult env t pos
                    _ -> tcheck

checkArrayIndexElementEmpty :: Abs.ARRAYINDEXELEMENT Posn -> Env -> TCheckResult
checkArrayIndexElementEmpty node@(Abs.ArrayIndexElementEmpty pos) env = TResult env (B_type Type_Void) pos --da rivedere

checkTypeStatement :: Abs.STATEMENT Posn -> Env -> TCheckResult
checkTypeStatement node@(Abs.BreakStatement pos) env = checkTypeBreakStatement node env
checkTypeStatement node@(Abs.ContinueStatement pos) env = checkTypeContinueStatement node env
checkTypeStatement node@(Abs.ReturnStatement pos ret) env = checkTypeReturnStatement node env
checkTypeStatement node@(Abs.Statement pos b) env = checkTypeB b env
checkTypeStatement node@(Abs.ExpressionStatement pos exp) env = checkTypeExpressionStatement exp env
checkTypeStatement node@(Abs.AssignmentStatement pos lval assignOp exp) env = let expTCheck = (getRealType (checkTypeExpression exp env)) in if(checkCompatibility expTCheck (getRealType (checkTypeLvalueExpression lval env))) then expTCheck else TError ["incompatible type at "++show pos]
checkTypeStatement node@(Abs.VariableDeclarationStatement pos tipo vardec) env = checkTypeVardec vardec env
checkTypeStatement node@(Abs.ConditionalStatement pos condition) env = checkTypeCondition condition env
checkTypeStatement node@(Abs.WhileDoStatement pos whileState) env = checkTypeWhile whileState env
checkTypeStatement node@(Abs.DoWhileStatement pos doState) env = checkTypeDo doState env
checkTypeStatement node@(Abs.ForStatement pos forState) env = checkTypeForState forState env
checkTypeStatement node@(Abs.ForAllStatement pos forAllState) env = checkTypeForAllState forAllState env
checkTypeStatement node@(Abs.ProcedureStatement pos id param states) env = checkTypeExecuteParameter param env     -- non deve esserci return diverso da void
checkTypeStatement node@(Abs.FunctionStatement pos id param tipo states) env = checkTypeExecuteParameter param env -- se c'è return (deve esserci) deve combaciare il tipo

checkTypeCondition :: Abs.CONDITIONALSTATE Posn -> Env -> TCheckResult
checkTypeCondition node@(Abs.ConditionalStatementSimpleThen pos exp state elseState) env = if (checkCompatibility (TResult env (B_type Type_Boolean) pos) (checkTypeExpression exp env)) then TResult env (B_type Type_Void) pos else TError ["expression for condition not is bool at "++show pos]
checkTypeCondition node@(Abs.ConditionalStatementSimpleWThen pos exp b elseState) env = if (checkCompatibility (TResult env (B_type Type_Boolean) pos) (checkTypeExpression exp env)) then TResult env (B_type Type_Void) pos else TError ["expression for condition not is bool at "++show pos]
checkTypeCondition node@(Abs.ConditionalStatementCtrlThen pos ctrlState state elseState) env = checkTypeCtrlState ctrlState env
checkTypeCondition node@(Abs.ConditionalStatementCtrlWThen pos ctrlState b elseState) env = checkTypeCtrlState ctrlState env

checkTypeElseState :: Abs.ELSESTATEMENT Posn -> Env -> TCheckResult
checkTypeElseState node@(Abs.ElseState pos state) env = TResult env (B_type Type_Void) pos
checkTypeElseState node@(Abs.ElseStateEmpty pos) env = TResult env (B_type Type_Void) pos

checkTypeCtrlState :: Abs.CTRLDECSTATEMENT Posn -> Env -> TCheckResult
checkTypeCtrlState node@(Abs.CtrlDecStateConst pos id typepart exp) env = if (checkCompatibility (checkTypeExpression exp env) (checkTypeTypePart typepart env)) then TResult env (B_type Type_Void) pos else TError ["expression for ctrl declaration constant is null at "++show pos]
checkTypeCtrlState node@(Abs.CtrlDecStateVar pos id typepart exp) env = if (checkCompatibility (checkTypeExpression exp env) (checkTypeTypePart typepart env)) then TResult env (B_type Type_Void) pos else TError ["expression for ctrl declaration variable is null at "++show pos]

checkTypeWhile :: Abs.WHILESTATEMENT Posn -> Env -> TCheckResult
checkTypeWhile node@(Abs.WhileStateSimpleDo pos exp state) env = if (checkCompatibility (TResult env (B_type Type_Boolean) pos) (checkTypeExpression exp env)) then TResult env (B_type Type_Void) pos else TError ["expression for while guard not is bool at "++show pos]
checkTypeWhile node@(Abs.WhileStateSimpleWDo pos exp b) env = if (checkCompatibility (TResult env (B_type Type_Boolean) pos) (checkTypeExpression exp env)) then TResult env (B_type Type_Void) pos else TError ["expression for while guard not is bool at "++show pos]
checkTypeWhile node@(Abs.WhileStateCtrlDo pos ctrl state) env = checkTypeCtrlState ctrl env
checkTypeWhile node@(Abs.WhileStateCtrlWDo pos ctrl b) env = checkTypeCtrlState ctrl env

checkTypeDo :: Abs.DOSTATEMENT Posn -> Env -> TCheckResult
checkTypeDo node@(Abs.DoWhileState pos state exp) env = if (checkCompatibility (TResult env (B_type Type_Boolean) pos) (checkTypeExpression exp env)) then TResult env (B_type Type_Void) pos else TError ["expression for do while guard not is bool at "++show pos]

checkTypeForState :: Abs.FORSTATEMENT Posn -> Env -> TCheckResult
checkTypeForState node@(Abs.ForStateIndexDo pos index rangexp state) env = if(checkCompatibility (checkRangeExpType rangexp env) (checkTypeIndexVarDec index env) ) then TResult env (B_type Type_Void) pos else TError ["ident in for guard incompatible with range at "++show pos]
checkTypeForState node@(Abs.ForStateIndexWDo pos index rangexp b) env = if(checkCompatibility (checkRangeExpType rangexp env) (checkTypeIndexVarDec index env) ) then TResult env (B_type Type_Void) pos else TError ["ident in for guard incompatible with range at "++show pos]
checkTypeForState node@(Abs.ForStateExprDo pos rangexp state) env = TResult env (B_type Type_Void) pos
checkTypeForState node@(Abs.ForStateExprWDo pos rangexp b) env = TResult env (B_type Type_Void) pos

checkTypeIndexVarDec :: Abs.INDEXVARDEC Posn -> Env -> TCheckResult
checkTypeIndexVarDec node@(Abs.IndexVarDeclaration pos id) env =  checkTypeIdentVar id env

checkTypeForAllState :: Abs.FORALLSTATEMENT Posn -> Env -> TCheckResult
checkTypeForAllState node@(Abs.ForAllStateIndexDo pos index rangexp state) env = if(checkCompatibility (checkRangeExpType rangexp env) (checkTypeIndexVarDec index env)) then TResult env (B_type Type_Void) pos else TError ["ident in for guard incompatible with range at "++show pos]
checkTypeForAllState node@(Abs.ForAllStateIndexWDo pos index rangexp b) env = if(checkCompatibility (checkRangeExpType rangexp env) (checkTypeIndexVarDec index env)) then TResult env (B_type Type_Void) pos else TError ["ident in for guard incompatible with range at "++show pos]
checkTypeForAllState node@(Abs.ForAllStateExprDo pos rangexp state) env = TResult env (B_type Type_Void) pos
checkTypeForAllState node@(Abs.ForAllStateExprWDo pos rangexp b) env = TResult env (B_type Type_Void) pos

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
checkTypeBreakStatement (Abs.BreakStatement pos) env = case Data.Map.lookup "while" env of -- check if inside a while block
    Just result -> TResult env (B_type Type_Void) pos
    Nothing -> TError ["Unexpected break statement at " ++ (show pos)]

checkTypeContinueStatement :: Abs.STATEMENT Posn -> Env -> TCheckResult
checkTypeContinueStatement (Abs.ContinueStatement pos) env = case Data.Map.lookup "while" env of -- check if inside a while block
    Just result -> TResult env (B_type Type_Void) pos
    Nothing -> TError ["Unexpected continue statement at " ++ (show pos)]

checkTypeReturnStatement :: Abs.STATEMENT Posn -> Env -> TCheckResult
checkTypeReturnStatement node@(Abs.ReturnStatement pos ret) env = checkTypeReturnState ret env

checkTypeReturnState :: Abs.RETURNSTATEMENT Posn -> Env -> TCheckResult
checkTypeReturnState node@(Abs.ReturnState pos retExp) env = case Data.Map.lookup "return" env of
    Just result -> checkTypeExpression retExp env
    Nothing -> TError ["Unexpected return at " ++ (show pos)]
checkTypeReturnState node@(Abs.ReturnStateEmpty pos ) env = case Data.Map.lookup "return" env of --(searchFunction (Data.Map.toList env) pos []) of
    Just result -> TResult env (B_type Type_Void) pos
    Nothing -> TError ["Unexpected return at " ++ (show pos)]

checkTypeExpressionStatement :: Abs.EXPRESSIONSTATEMENT Posn -> Env -> TCheckResult
checkTypeExpressionStatement node@(Abs.VariableExpression pos id) env = checkTypeIdentVar id env
checkTypeExpressionStatement node@(Abs.CallExpression pos callexpr) env = checkTypeCallExpression callexpr env

checkTypeExpressions :: Abs.EXPRESSIONS Posn -> Env -> TCheckResult
checkTypeExpressions node@(Abs.Expressions pos exp exps) env = TResult env (B_type Type_Void) pos
checkTypeExpressions node@(Abs.Expression pos exp) env = TResult env (B_type Type_Void) pos
checkTypeExpressions node@(Abs.ExpressionEmpty pos) env = TResult env (B_type Type_Void) pos

checkTypeExpression :: Abs.EXPRESSION Posn -> Env -> TCheckResult
checkTypeExpression node@(Abs.ExpressionInteger pos value) env = checkTypeInteger value env
checkTypeExpression node@(Abs.ExpressionBoolean pos value) env = checkTypeBoolean value env
checkTypeExpression node@(Abs.ExpressionChar pos value) env = checkTypeChar value env
checkTypeExpression node@(Abs.ExpressionString pos value) env = checkTypeString value env
checkTypeExpression node@(Abs.ExpressionReal pos value) env = checkTypeReal value env
checkTypeExpression node@(Abs.ExpressionBracket pos exp) env = checkTypeExpression exp env
checkTypeExpression node@(Abs.ExpressionCast pos def tipo) env = let tipoTCheck = checkPrimitiveType tipo env in if(checkCompatibility (checkTypeDefault def env) tipoTCheck) then tipoTCheck else TError ["Incompatibility type for casting at "++show pos]
checkTypeExpression node@(Abs.ExpressionUnary pos unary exp) env = case unary of
                                                                    Abs.UnaryOperationPointer pos -> case exp of
                                                                                                    Abs.ExpressionUnary _ _ _ -> checkTypeExpression exp env
                                                                                                    Abs.ExpressionIdent pos id index -> case index of 
                                                                                                                                        Abs.ArrayIndexElementEmpty pos -> let pointer = checkTypeIdentVar id env in case pointer of
                                                                                                                                                                                                                    res@(TResult env (Pointer t depth) pos) -> res
                                                                                                                                                                                                                    _ -> TError ["not a pointer at "++show pos]
                                                                                                                                        Abs.ArrayIndexElement pos t -> TError ["not is a pointer at "++show pos]
                                                                                                    _ -> TError ["not is a pointer at "++show pos]
                                                                    _ -> let unaryTCheck = checkTypeUnaryOp unary env in if(checkCompatibility (checkTypeExpression exp env) unaryTCheck) then (checkTypeExpression exp env) else TError ["Incompatibility type for unary operator at "++show pos]
checkTypeExpression node@(Abs.ExpressionBinary pos def binary exp) env = let expCheck = checkTypeExpression exp env in
                                                                            (let defCheck = checkTypeDefault def env in 
                                                                                (let binaryTCheck = checkTypeBinaryOp binary env in if (checkCompatibility defCheck expCheck || checkCompatibility expCheck defCheck)
                                                                                    then let ty = returnSuperType expCheck defCheck in case binaryTCheck of
                                                                                        TResult _ (B_type Type_Real) _ -> if (checkCompatibility ty binaryTCheck) then ty else TError ["Incompatibility type for binary operator at "++show pos]
                                                                                        TResult _ (B_type Type_Boolean) _ -> case binary of
                                                                                            (Abs.BinaryOperationOr pos) -> if (checkCompatibility ty binaryTCheck) then binaryTCheck else TError ["Incompatibility type for binary operator at "++show pos]
                                                                                            (Abs.BinaryOperationAnd pos) -> if (checkCompatibility ty binaryTCheck) then binaryTCheck else TError ["Incompatibility type for binary operator at "++show pos]
                                                                                            (Abs.BinaryOperationEq pos) -> binaryTCheck
                                                                                            (Abs.BinaryOperationNotEq pos) -> binaryTCheck
                                                                                            _ -> if (checkCompatibility ty (TResult env (B_type Type_Real) pos)) || (checkCompatibility ty (TResult env (B_type Type_String) pos)) || (checkCompatibility ty (TResult env (B_type Type_Char) pos)) 
                                                                                                then binaryTCheck
                                                                                                else TError ["Incompatibility type for binary operator at "++show pos]
                                                                                    else TError ["a and b incomp types? "++show pos]
                                                                                    ))
checkTypeExpression node@(Abs.ExpressionIdent pos value@(Abs.Ident id posI) index) env =  case Data.Map.lookup id env of
                                                                        Just [Variable (Array t dim) pos mode override] -> if dim == (countIndex index) then checkTypeIdentVar value env else TError ["number of index different at "++show pos] 
                                                                        Just _ -> checkTypeIdentVar value env
                                                                        Nothing -> TError ["ident not find at "++show pos]
checkTypeExpression node@(Abs.ExpressionCall pos (Abs.Ident id posid) exps) env = case Data.Map.lookup id env of
                                                                Just [Function t posf param] -> checkTypeExpressionCall_ node env [Function t posf param]
                                                                Just [Variable _ _ _ _] -> TError [" ?? function not def.at " ++ (show pos)]
                                                                Just (x:xs) -> case findEntryOfType (x:xs) "func" of -- controllare se c'è una entry di tipo func
                                                                        [] -> TError [" ?? function not def.at " ++ (show pos)]
                                                                        [Function t posf param] -> checkTypeExpressionCall_ node env [Function t posf param]
                                                                Nothing -> TError [" ?? function not def. Unexpected ident at " ++ (show pos)]

-- sub-function of the previous one
checkTypeExpressionCall_ :: Abs.EXPRESSION Posn -> Env -> [EnvEntry] -> TCheckResult
checkTypeExpressionCall_ (Abs.ExpressionCall pos (Abs.Ident id posid) exps) env [Function t posf param] = case exps of
    (Abs.Expression pos exp) -> if Prelude.length (param) == 1 -- The call was with 1 param, does the definition requires only 1 param?
                                               then if (let expType = checkTypeExpression exp env -- Check if the type is compatibile with the one required in the definition
                                                        in checkCompatibility expType (TResult env (Prelude.head (getTypeListFromFuncParams param)) pos)) then TResult env t pos 
                                                    else TError ["tipo nella chiamata non coincide (ma il numero era ok)"]
                                               else TError ["call with 1 param but missing others params"]
    (Abs.ExpressionEmpty pos) -> if param == [] then TResult env t pos else TError ["chiamata senza paramertri"] -- The call was with no params, check if the definition requires no param too
    (Abs.Expressions pos exp expss) -> if Prelude.length (param) == 1 + (countNumberOfExps expss) -- The call has n params, does the definition requires n params?
                                                              then if (checkCompatibilityOfExpsList exps param env) then TResult env t pos 
                                                                   else TError ["number of param ok but compatibility of types NOT OK"]
                                                              else TError ["number of param not equal in the call"]

countNumberOfExps :: Abs.EXPRESSIONS Posn -> Prelude.Int
countNumberOfExps (Abs.Expressions _ _ exps) = 1 + countNumberOfExps exps
countNumberOfExps (Abs.Expression _ _) = 1
countNumberOfExps (Abs.ExpressionEmpty _) = 1

checkCompatibilityOfExpsList :: Abs.EXPRESSIONS Posn -> [TypeChecker.Parameter] -> Env-> Prelude.Bool
checkCompatibilityOfExpsList  (Abs.Expressions pos exp exps) ((TypeChecker.Parameter ty _ _ _):zs) env = let expType = checkTypeExpression exp env in if checkCompatibility expType (TResult env ty pos) 
                                                                                                                                                         then True && (checkCompatibilityOfExpsList exps zs env) else False
checkCompatibilityOfExpsList  (Abs.Expression pos exp) ((TypeChecker.Parameter ty _ _ _):zs) env = let expType = checkTypeExpression exp env in if checkCompatibility expType (TResult env ty pos) 
                                                                                                                                                     then True else False
checkCompatibilityOfExpsList  (Abs.ExpressionEmpty pos) [] env = True                                                                                                                                                 

checkTypeUnaryOp :: Abs.UNARYOP Posn -> Env -> TCheckResult
checkTypeUnaryOp node@(Abs.UnaryOperationPositive pos) env = TResult env (B_type Type_Real) pos
checkTypeUnaryOp node@(Abs.UnaryOperationNegative pos) env = TResult env (B_type Type_Real) pos
checkTypeUnaryOp node@(Abs.UnaryOperationNot pos) env = TResult env (B_type Type_Boolean) pos
checkTypeUnaryOp node@(Abs.UnaryOperationPointer pos) env = TResult env (B_type Type_Void) pos

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
checkTypeDefault node@(Abs.ExpressionIdentD pos value index) env = checkTypeIdentVar value env --gestire index

checkTypeIdentVar :: Abs.Ident Posn -> Env -> TCheckResult
checkTypeIdentVar node@(Abs.Ident id pos) env = case Data.Map.lookup id env of
    Just [Variable t pos mode override] -> TResult env t pos -- check if var TODO
    Just (x:xs) -> case findEntryOfType (x:xs) "var" of
                    [] -> TError ["Unexpected varident at " ++ (show pos)]
                    [y] -> TResult env (getTypeEnvEntry [y]) pos
    Nothing -> TError ["Unexpected var ident at " ++ (show pos)]

checkTypeIdentFunc :: Abs.Ident Posn -> Env -> TCheckResult
checkTypeIdentFunc node@(Abs.Ident id pos) env = case Data.Map.lookup id env of
    Just [Function t pos param] -> TResult env t pos -- check if var TODO
    Just (x:xs) -> case findEntryOfType (x:xs) "func" of
                    [] -> TError ["Unexpected func ident at " ++ (show pos)]
                    [y] -> TResult env (getTypeEnvEntry [y]) pos
    Nothing -> TError ["Unexpected func ident at " ++ (show pos)]

-- Given a list of envEntry, returns the first occurence of the given type (var or func env entry)
findEntryOfType :: [EnvEntry] -> Prelude.String -> [EnvEntry]
findEntryOfType (x:xs) str = case str of 
                                "var" -> case x of -- searching for var entry 
                                        Variable t pos mode override -> [x]
                                        _ -> findEntryOfType xs str
                                "func"-> case x of -- searching for func entry 
                                        Function t pos param -> [x]
                                        _ -> findEntryOfType xs str
findEntryOfType [] str = []
    
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
checkTypeVardec node@(Abs.VariableDeclarationSingle pos vardecid) env = checkTypeVariableDec vardecid env

checkTypeVariableDec :: Abs.VARDECID Posn -> Env -> TCheckResult
checkTypeVariableDec node@(Abs.VariableDeclaration pos identlist typepart initpart) env = case initpart of
                                                                                        Abs.InitializzationPartEmpty _ -> checkTypeTypePart typepart env
                                                                                        _ -> let typeCheck = checkTypeTypePart typepart env in
                                                                                                let initCheck = checkTypeInitializzationPart initpart env in
                                                                                                    case typeCheck of
                                                                                                        TResult env (Pointer t depth) pos -> case initCheck of
                                                                                                            TResult env (Pointer tI depthI) pos -> if (checkCompatibility (TResult env (Pointer tI ((depthI+1)-(checkDef initpart))) pos) (TResult env (Pointer t depth) pos)) then typeCheck else TError ["Pointer initializzation incompatible type at "++show pos]
                                                                                                            _ -> if (checkCompatibility initCheck (TResult env t pos)) then typeCheck else TError ["initializzation incompatible type at "++show pos]
                                                                                                        TResult env (Array t dim) pos -> case initCheck of
                                                                                                            TResult env (Array ts dims) pos -> if checkCompatibility (TResult env ts pos) (TResult env t pos) then typeCheck else TError ["Array|| initializzation incompatible type at "++show pos]
                                                                                                            _ -> TError ["Array initializzation incompatible type at "++show pos]
                                                                                                        _ -> case initCheck of
                                                                                                            TResult env (Pointer tI depthI) pos -> if (checkCompatibility (TResult env tI pos) typeCheck && (depthI-(checkDef initpart))==0) then typeCheck else TError ["initializzation incompatible type at "++show pos]
                                                                                                            TResult env (Array t dim) pos -> if (checkCompatibility (getRealType initCheck) typeCheck) then typeCheck else TError ["initializzation incompatible type at "++show pos]
                                                                                                            _ -> if (checkCompatibility initCheck typeCheck) then typeCheck else TError ["initializzation incompatible type at "++show pos]

checkDef :: Abs.INITPART Posn -> Prelude.Integer
checkDef (Abs.InitializzationPart pos exp) = checkDef_ exp
checkDef _ = 0

checkDef_ :: Abs.EXPRESSION Posn -> Prelude.Integer
checkDef_ (Abs.ExpressionUnary pos unary exp) = case unary of
                                                Abs.UnaryOperationPointer pos -> 1 + checkDef_ exp
                                                _ -> 0
checkDef_ _ = 0

checkIdentifierList :: Abs.IDENTLIST Posn -> Env -> TCheckResult
checkIdentifierList node@(Abs.IdentifierList pos ident identlist) env = TResult env (B_type Type_Void) pos
checkIdentifierList node@(Abs.IdentifierSingle pos ident) env = TResult env (B_type Type_Void) pos

checkTypeTypePart :: Abs.TYPEPART Posn -> Env -> TCheckResult
checkTypeTypePart node@(Abs.TypePart pos typexpr) env = checkTypeTypeExpression typexpr env

checkTypeInitializzationPart ::  Abs.INITPART Posn -> Env -> TCheckResult
checkTypeInitializzationPart node@(Abs.InitializzationPart pos expr) env = checkTypeExpression expr env
checkTypeInitializzationPart node@(Abs.InitializzationPartArray pos listelementarray) env = checkListElementsOfArray listelementarray env
checkTypeInitializzationPart node@(Abs.InitializzationPartEmpty pos ) env = TResult env (B_type Type_Void) pos

checkTypeExpressionpointer :: Abs.POINTER Posn -> Env -> TCheckResult
checkTypeExpressionpointer node@(Abs.PointerSymbol pos pointer) env = TResult env (B_type Type_Void) pos
checkTypeExpressionpointer node@(Abs.PointerSymbolSingle pos) env = TResult env (B_type Type_Void) pos

checkPrimitiveType :: Abs.PRIMITIVETYPE Posn -> Env -> TCheckResult
checkPrimitiveType node@(Abs.PrimitiveTypeVoid pos) env = TResult env (B_type Type_Void) pos
checkPrimitiveType node@(Abs.PrimitiveTypeBool pos) env = TResult env (B_type Type_Boolean) pos
checkPrimitiveType node@(Abs.PrimitiveTypeInt pos) env = TResult env (B_type Type_Integer) pos
checkPrimitiveType node@(Abs.PrimitiveTypeReal pos) env = TResult env (B_type Type_Real) pos
checkPrimitiveType node@(Abs.PrimitiveTypeString pos) env = TResult env (B_type Type_String) pos
checkPrimitiveType node@(Abs.PrimitiveTypeChar pos) env = TResult env (B_type Type_Char) pos
checkPrimitiveType node@(Abs.TypeArray pos primitivetype) env =  TResult env (Array (getArrayPrimitiveType primitivetype) (getArrayDimFunc primitivetype)) pos -- check if ok?

checkTypeTypeExpression :: Abs.TYPEEXPRESSION Posn -> Env -> TCheckResult
checkTypeTypeExpression node@(Abs.TypeExpression pos primitiveType) env = let checkArray = checkPrimitiveType primitiveType env in case checkArray of
                                                                                                                                    TResult env (Array _ _) pos -> TError ["array inizializzato senza aver specificato la dimensione at "++show pos]
                                                                                                                                    _ -> checkArray
checkTypeTypeExpression node@(Abs.TypeExpressionArraySimple pos rangeexp primitivetype) env =  TResult env (Array (getTypeFromPrimitive primitivetype) (getArrayDim rangeexp)) pos
checkTypeTypeExpression node@(Abs.TypeExpressionArray pos rangeexp primitivetype) env =  TResult env (getTypeFromPrimitive primitivetype) pos -- check compatibilità rangeexp e array?
                                                                                                                                          -- tra ty e la range?
checkTypeTypeExpression node@(Abs.TypeExpressionPointer pos primitivetype pointer) env = TResult env (getTypeExpr node) pos


checkListElementsOfArray :: Abs.LISTELEMENTARRAY Posn -> Env -> TCheckResult
checkListElementsOfArray node@(Abs.ListElementsOfArray pos expr elementlist) env = let exprTCheck = checkTypeExpression expr env in if (checkCompatibility exprTCheck (getRealType (checkListElementsOfArray elementlist env))) then TResult env (Array (getType exprTCheck) 0) pos else TError ["lista di elementi di tipi incompatibili at "++show pos]
checkListElementsOfArray node@(Abs.ListElementOfArray pos expr) env = let exprTCheck = checkTypeExpression expr env in TResult env (Array (getType exprTCheck) 0) pos

getType :: TCheckResult -> Type
getType (TResult env t pos) = t

checkRangeExpType :: Abs.RANGEEXP Posn -> Env -> TCheckResult
checkRangeExpType node@(Abs.RangeExpression pos expr1 expr2 rangexp) env = if ((checkCompatibility (checkTypeExpression expr1 env) (checkTypeExpression expr2 env) || checkCompatibility (checkTypeExpression expr2 env) (checkTypeExpression expr1 env)) && (checkOrder expr1 expr2) ) then --TODO distinguere due errori con altro if per order
                                                                                                                                                            if (checkCompatibility (returnSuperType (checkTypeExpression expr1 env) (checkTypeExpression expr2 env)) (checkRangeExpType rangexp env))
                                                                                                                                                                then checkSuperTypeRangeExp(returnSuperType (checkTypeExpression expr1 env) (checkTypeExpression expr2 env))
                                                                                                                                                                else TError ["type of expressions of the range is incompatible"]
                                                                                                                                                             else TError ["type of expressions of the range is incompatible"]
checkRangeExpType node@(Abs.RangeExpressionSingle pos expr1 expr2) env = if ((checkCompatibility (checkTypeExpression expr1 env) (checkTypeExpression expr2 env) || checkCompatibility (checkTypeExpression expr2 env) (checkTypeExpression expr1 env)) && (checkOrder expr1 expr2) ) then checkSuperTypeRangeExp(returnSuperType (checkTypeExpression expr1 env) (checkTypeExpression expr2 env)) else TError ["type of expressions of the range is incompatible"]

checkOrder :: Abs.EXPRESSION Posn -> Abs.EXPRESSION Posn -> Bool
checkOrder (Abs.ExpressionInteger pos (Abs.Integer val posI)) (Abs.ExpressionInteger poss (Abs.Integer vals posIs)) = val<=vals
checkOrder (Abs.ExpressionReal pos (Abs.Real val posR)) (Abs.ExpressionReal poss (Abs.Real vals posRs)) = val<=vals
checkOrder (Abs.ExpressionInteger pos (Abs.Integer val posI)) (Abs.ExpressionReal poss (Abs.Real vals posRs)) = (Prelude.fromInteger val)<=vals
checkOrder (Abs.ExpressionReal pos (Abs.Real val posR)) (Abs.ExpressionInteger poss (Abs.Integer vals posIs)) = val<=(Prelude.fromInteger vals)
checkOrder (Abs.ExpressionChar pos (Abs.Char val posC)) (Abs.ExpressionChar poss (Abs.Char vals posCs)) = val<=vals
checkOrder (Abs.ExpressionString pos (Abs.String val posS)) (Abs.ExpressionString poss (Abs.String vals posSs)) = val<=vals
checkOrder _ _ = False

-- Check the superType in a given RangeExp
checkSuperTypeRangeExp :: TCheckResult -> TCheckResult
checkSuperTypeRangeExp (TResult env tipo pos) = case tipo of
                                                B_type Type_Integer -> (TResult env tipo pos)
                                                B_type Type_Real -> (TResult env tipo pos)                                          
                                                B_type Type_Char -> (TResult env tipo pos)                                            
                                                B_type Type_String -> (TResult env tipo pos)
                                                _ -> TError ["incompatible type for range expression at "++show pos]

checkTypeTypeIndex :: Abs.TYPEINDEX Posn -> Env -> TCheckResult
checkTypeTypeIndex node@(Abs.TypeOfIndexInt pos typeindex integer) env = if checkCompatibility (TResult env (B_type Type_Integer) pos) (checkTypeTypeIndex typeindex env)
                                                                         then TResult env (B_type Type_Integer) pos
                                                                         else TError ["Index types of array not all the same - int"]
checkTypeTypeIndex node@(Abs.TypeOfIndexIntSingle pos integer) env = TResult env (B_type Type_Integer) pos
checkTypeTypeIndex node@(Abs.TypeOfIndexVar pos typeindex id) env = if checkCompatibility (checkTypeIdentVar id env) (checkTypeTypeIndex typeindex env)
                                                                    then TResult env (B_type Type_Integer) pos
                                                                    else TError ["Index types of array not all the same"]
checkTypeTypeIndex node@(Abs.TypeOfIndexVarSingle _ (Abs.Ident id pos)) env = case Data.Map.lookup id env of
                                    Just ident -> TResult env (getTypeEnvEntry ident) pos
                                    Nothing -> TError [" ?? var not def. Unexpected ident at " ++ (show pos)]

checkTypeCallExpression :: Abs.CALLEXPRESSION Posn -> Env -> TCheckResult
checkTypeCallExpression node@(Abs.CallExpressionParentheses _ (Abs.Ident id pos) namedexpr) env = case Data.Map.lookup id env of
                                                    Just [Function t posf param] -> checkTypeCallExpression_ node env [Function t posf param]
                                                    Just [Variable _ _ _ _] -> TError [" ?? function not def.at " ++ (show pos)]
                                                    Just (x:xs) -> case findEntryOfType (x:xs) "func" of -- controllare se c'è una entry di tipo func
                                                        [] -> TError [" ?? function not def.at " ++ (show pos)]
                                                        [Function t posf param] -> checkTypeCallExpression_ node env [Function t posf param]
                                                    Nothing -> TError [" ?? function not def.at " ++ (show pos)]
checkTypeCallExpression node@(Abs.CallExpressionQuadre pos id namedexpr) env = TError ["mhh?"] -- array?

-- sub-function of the previous one
checkTypeCallExpression_ :: Abs.CALLEXPRESSION Posn -> Env -> [EnvEntry] -> TCheckResult
checkTypeCallExpression_ (Abs.CallExpressionParentheses _ (Abs.Ident id pos) namedexpr) env [Function t posf param] = case namedexpr of
    (Abs.NamedExpressionList res namedexpr) -> if Prelude.length (param) == 1 -- The call was with 1 param, does the definition requires only 1 param?
                                               then if (let namedType = checkTypeNamedExpression namedexpr env -- Check if the type is compatibile with the one required in the definition
                                                        in checkCompatibility namedType (TResult env (Prelude.head (getTypeListFromFuncParams param)) pos)) then TResult env t pos 
                                                    else TError ["tipo nella chiamata non coincide (ma il numero era ok)"]
                                               else TError ["call with 1 param but missing others params"]
    (Abs.NamedExpressionListEmpty res) -> if param == [] then TResult env t pos else TError ["chiamata senza paramertri"] -- The call was with no params, check if the definition requires no param too
    (Abs.NamedExpressionLists res _ namedexprlist) -> if Prelude.length (param) == 1 + (countNumberOfParam namedexprlist) -- The call has n params, does the definition requires n params?
                                                              then if (checkCompatibilityOfParamsList namedexpr param env) then TResult env t pos 
                                                                   else TError ["number of param ok but compatibility of types NOT OK"]
                                                              else TError ["number of param not equal in the call"]
    (Abs.NamedExpressionAssigned res id namedexpr) -> TError ["mhh?"] -- label per leggibilità codice ...

-- Given a List of named expression, counts them and return the result
countNumberOfParam :: Abs.NAMEDEXPRESSIONLIST Posn -> Prelude.Int
countNumberOfParam (Abs.NamedExpressionLists _ _ namedexprlist) = 1 + countNumberOfParam namedexprlist
countNumberOfParam (Abs.NamedExpressionList _ _) = 1

checkCompatibilityOfParamsList :: Abs.NAMEDEXPRESSIONLIST Posn -> [TypeChecker.Parameter] -> Env-> Prelude.Bool
checkCompatibilityOfParamsList  (Abs.NamedExpressionLists pos x xs) ((TypeChecker.Parameter ty _ _ _):zs) env = let namedType = checkTypeNamedExpression x env in if checkCompatibility namedType (TResult env ty pos) 
                                                                                                                                                         then True && (checkCompatibilityOfParamsList xs zs env) else False
checkCompatibilityOfParamsList  (Abs.NamedExpressionList pos x) ((TypeChecker.Parameter ty _ _ _):zs) env = let namedType = checkTypeNamedExpression x env in if checkCompatibility namedType (TResult env ty pos) 
                                                                                                                                                     then True else False

checkTypeNamedExpressionList :: Abs.NAMEDEXPRESSIONLIST Posn -> Env -> TCheckResult
checkTypeNamedExpressionList node@(Abs.NamedExpressionList pos namedexprlist) env = TResult env (B_type Type_Void) pos
checkTypeNamedExpressionList node@(Abs.NamedExpressionListEmpty pos) env = TResult env (B_type Type_Void) pos
checkTypeNamedExpressionList node@(Abs.NamedExpressionLists pos namedexpr namedexprlist) env = TResult env (B_type Type_Void) pos
checkTypeNamedExpressionList node@(Abs.NamedExpressionAssigned pos id expr) env = TResult env (B_type Type_Void) pos

checkTypeNamedExpression :: Abs.NAMEDEXPRESSION Posn -> Env -> TCheckResult
checkTypeNamedExpression node@(Abs.NamedExpression pos expr) env = checkTypeExpression expr env
                                    
checkTypeExecuteParameter :: Abs.PARAMETERS Posn -> Env -> TCheckResult
checkTypeExecuteParameter node@(Abs.ParameterList pos param params) env = let pamList = (getParamList node) in
                                                                                (if  checkDuplicatedParametersInFunDecl (getListOfIdsFromParamList pamList) -- check if params ids are not dups
                                                                                then TError ["duplicated ids params in func decl"] -- dups in params 
                                                                                else TResult env (B_type Type_Integer) pos) -- no dups: decl ok
checkTypeExecuteParameter node@(Abs.ParameterListSingle pos param) env = TResult env (B_type Type_Integer) pos -- single can't have dups in ids
checkTypeExecuteParameter node@(Abs.ParameterListEmpty pos) env = TResult env (B_type Type_Void) pos -- empty can't have dups in ids

checkTypeParameter:: Abs.PARAMETER Posn -> Env -> TCheckResult
checkTypeParameter node@(Abs.Parameter pos id ty) env = TResult env (B_type Type_Void) pos