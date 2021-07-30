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
    | Function {funType::Type, funPosition::LexProgettoPar.Posn, funParameters::[Parameter], canOverride::Prelude.Bool}

data Parameter
    = Parameter {paramType::Type, paramPosition::LexProgettoPar.Posn, paramMode::Prelude.String, identifier::Prelude.String}
    deriving(Eq, Ord)

data TCheckResult
    = TResult {environment::Env, t_type::Type, t_position::LexProgettoPar.Posn}
    | TError {errors::[Prelude.String]}

-------------------------------------------------------------------------------------------------
--- SHOW ISTANCES FOR ENV DATA TYPES ------------------------------------------------------------
-------------------------------------------------------------------------------------------------

-- Start env: it includes the pre-defined functiosn/procedures required
startEnv = fromList [("readChar",[Function {funType = (B_type Type_Char), funPosition = (Pn 0 0 0), funParameters = [], canOverride = False}]),("readInt",[Function {funType = (B_type Type_Integer), funPosition = (Pn 0 0 0), funParameters = [], canOverride = False}]),("readReal",[Function {funType = (B_type Type_Real), funPosition = (Pn 0 0 0), funParameters = [], canOverride = False}]),("readString",[Function {funType = (B_type Type_String), funPosition = (Pn 0 0 0), funParameters = [], canOverride = False}]),("writeChar",[Function {funType = (B_type Type_Void), funPosition = (Pn 0 0 0), funParameters = [TypeChecker.Parameter {paramType = (B_type Type_Integer), paramPosition = (Pn 0 0 0), paramMode = "_mode_", identifier = "input"}], canOverride = False}]),("writeInt",[Function {funType = (B_type Type_Void), funPosition = (Pn 0 0 0), funParameters = [TypeChecker.Parameter {paramType = (B_type Type_Integer), paramPosition = (Pn 0 0 0), paramMode = "_mode_", identifier = "input"}], canOverride = False}]),("writeReal",[Function {funType = (B_type Type_Void), funPosition = (Pn 0 0 0), funParameters = [TypeChecker.Parameter {paramType = (B_type Type_Integer), paramPosition = (Pn 0 0 0), paramMode = "_mode_", identifier = "input"}], canOverride = False}]),("writeString",[Function {funType = (B_type Type_Void), funPosition = (Pn 0 0 0), funParameters = [TypeChecker.Parameter {paramType = (B_type Type_Integer), paramPosition = (Pn 0 0 0), paramMode = "_mode_", identifier = "input"}], canOverride = False}])]

instance Show EnvEntry where
    show entry = case entry of
        TypeChecker.Variable ty pos varMode canOverride -> "EnvEntry: [" ++ "var:" ++ show ty ++ "|" ++ show pos ++ "|mode:" ++ show varMode ++ "|canOverride:" ++ show canOverride ++ "]"
        TypeChecker.Function ty pos params canOverride  -> "EnvEntry: [" ++ "fun:" ++ show ty ++ "|" ++ show pos ++ "|params:" ++ show params ++ "|canOverride:" ++ show canOverride ++ "]"

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
                                                                                          B_type Type_Integer -> (TResult env t pos)   -- real > int
                                                                    B_type Type_Boolean  -> case tC of
                                                                                          B_type Type_Boolean  -> (TResult env t pos)
                                                                    B_type Type_Char  -> case tC of
                                                                                          B_type Type_Char  -> (TResult env t pos)
                                                                    B_type Type_String  -> case tC of
                                                                                          B_type Type_String  -> (TResult env t pos)
                                                                    Pointer tp depth -> case tC of
                                                                                        Pointer ts depths -> (TResult env t pos)
                                                                                        _ -> TResult env tC pos

---------------------------------------------------------------------------------------------------
--- ENV DATA TYPES FUNCTIONS ----------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

-- Merge two given TErrors
mergeErrors :: TCheckResult -> TCheckResult -> TCheckResult
mergeErrors (TError e1) (TError e2) = TError (e1++e2)
mergeErrors (TError e1) _ = TError e1
mergeErrors _ (TError e2) = TError e2

-- Returns the type of a EnvEntry of the Environment -> Variable or Function entry
getTypeEnvEntry :: [EnvEntry] -> Type
getTypeEnvEntry [] = B_type Type_Void
getTypeEnvEntry (x:xs) = case x of 
                            (Variable t pos mode canOverride) -> t
                            (Function t pos parameters canOverride) -> t

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
                                                                                                                                if (checkIfCanOverride ids env "var") -- check if vars can be overrided (yes if inside a new block)
                                                                                                                                then (updateEnvFromListOfVarIds ids env pos varMode ty, err) -- updating env for each declared var.
                                                                                                                                else (updateEnvFromListOfVarIds ids env pos varMode ty, err)))
                                                                -- Functions and Procedures
                                                                Abs.ProcedureStatement pos id params stats -> let parameters = getParamList params in
                                                                                                                let fid = getIdFromIdent id in
                                                                                                                    if (checkIfCanOverride [fid] env "func") -- check if the func can be overrided (defined inside a new block)
                                                                                                                    then (insertWith (++) fid [Function (B_type Type_Void) pos parameters False] env, err)
                                                                                                                    else (env, err) -- it was already defined
                                                                Abs.FunctionStatement pos id params ty stats -> let parameters = getParamList params in
                                                                                                                    let fty = getTypeFromPrimitive ty in
                                                                                                                        let fid = getIdFromIdent id in 
                                                                                                                            if (checkIfCanOverride [fid] env "func") -- check if the func can be overrided (defined inside a new block)
                                                                                                                            then (insertWith (++) fid [Function fty pos parameters False] env, err)
                                                                                                                            else (env, err) -- it was already defined
                                                                -- generic case
                                                                _ -> (env,err) 
updateEnv node@(Abs.EmptyStatement pos) env err = (env,err)

-- Update the env for Conditional if-then-else statement
updateEnvCondStat :: (Abs.CONDITIONALSTATE Posn) -> Env -> [Prelude.String] -> (Env,[Prelude.String])
updateEnvCondStat (Abs.ConditionalStatementCtrlThen pos ctrlState state elseState) env err = case ctrlState of
                    Abs.CtrlDecStateVar pos id typepart exp -> (insertWith (++) (getIdFromIdent id) [Variable (getTypePart typepart) pos "var" False] env, err)
                    Abs.CtrlDecStateConst pos id typepart exp -> (insertWith (++) (getIdFromIdent id) [Variable (getTypePart typepart) pos "const" False] env, err)
updateEnvCondStat (Abs.ConditionalStatementCtrlWThen pos ctrlState b elseState) env err = case ctrlState of
                    Abs.CtrlDecStateVar pos id typepart exp -> (insertWith (++) (getIdFromIdent id) [Variable (getTypePart typepart) pos "var" False] env, err)
                    Abs.CtrlDecStateConst pos id typepart exp -> (insertWith (++) (getIdFromIdent id) [Variable (getTypePart typepart) pos "const" False] env, err)
updateEnvCondStat _ env err = (env,err)

-- Update the env for while statement
updateEnvWhileStat :: (Abs.WHILESTATEMENT Posn) -> Env -> [Prelude.String] -> (Env,[Prelude.String])
updateEnvWhileStat (Abs.WhileStateCtrlDo pos ctrl state) env err = case ctrl of
                    Abs.CtrlDecStateVar pos id typepart exp -> let newEnv = (insertWith (++) (getIdFromIdent id) [Variable (getTypePart typepart) pos "var" False] env, err) in (insertWith (++) "while" [] (first newEnv), err)
                    Abs.CtrlDecStateConst pos id typepart exp -> let newEnv = (insertWith (++) (getIdFromIdent id) [Variable (getTypePart typepart) pos "const" False] env, err) in (insertWith (++) "while" [] (first newEnv), err)
updateEnvWhileStat (Abs.WhileStateCtrlWDo pos ctrl b) env err = case ctrl of
                    Abs.CtrlDecStateVar pos id typepart exp -> let newEnv = (insertWith (++) (getIdFromIdent id) [Variable (getTypePart typepart) pos "var" False] env, err) in (insertWith (++) "while" [] (first newEnv), err)
                    Abs.CtrlDecStateConst pos id typepart exp -> let newEnv = (insertWith (++) (getIdFromIdent id) [Variable (getTypePart typepart) pos "const" False] env, err) in (insertWith (++) "while" [] (first newEnv), err)
updateEnvWhileStat (Abs.WhileStateSimpleDo pos expr state) env err = (insertWith (++) "while" [] env, err)
updateEnvWhileStat (Abs.WhileStateSimpleWDo pos expr b) env err = (insertWith (++) "while" [] env, err)

-- Given a list of Params, it creates an envEntry of type param for each of them
createEnvEntryForParams :: [TypeChecker.Parameter] -> Env -> Env
createEnvEntryForParams ((TypeChecker.Parameter ty pos mode id):xs) env = createEnvEntryForParams xs (insertWith (++) id [Variable ty pos mode False] env)
createEnvEntryForParams [] env = env

-- Given a list of var IDS and an Env, it update that env adding the variable enventries for each var id.
updateEnvFromListOfVarIds :: [Prelude.String] -> Env -> Posn -> Prelude.String -> Type -> Env
updateEnvFromListOfVarIds [] env pos varMode ty = env
updateEnvFromListOfVarIds (x:xs) env pos varMode ty = case Data.Map.lookup x env of
                                                       Just [Variable typ posv varMv override] -> if override 
                                                                                                    then updateEnvFromListOfVarIds xs (insertWith (++) x [Variable ty pos varMode False] env) pos varMode ty 
                                                                                                    else updateEnvFromListOfVarIds xs env pos varMode ty
                                                       Just ((Variable typ posv varMv override):xenv) -> if override 
                                                                                                    then updateEnvFromListOfVarIds xs (insertWith (++) x [Variable ty pos varMode False] env) pos varMode ty 
                                                                                                    else updateEnvFromListOfVarIds xs env pos varMode ty
                                                       Just _ -> updateEnvFromListOfVarIds xs env pos varMode ty                                                                              
                                                       Nothing -> updateEnvFromListOfVarIds xs (insertWith (++) x [Variable ty pos varMode False] env) pos varMode ty

-- Given an Env set to TRUE in CanOverride for each variable and func!
-- Used at the beginning of a new block (for example, after declaring a function, inside it is possible to override previous variable declaration (those outside))
updateIfCanOverride :: Env -> Env
updateIfCanOverride env = Data.Map.fromList (updateIfCanOverride_ (Data.Map.toList env))

-- Implementation of the previous function
updateIfCanOverride_ :: [(Prelude.String, [EnvEntry])] -> [(Prelude.String, [EnvEntry])]
updateIfCanOverride_ ((str,entry:entries):xs) = case entry of
                    Variable ty pos varMode canOverride ->  [(str,(Variable ty pos varMode True):entries)] ++ updateIfCanOverride_ xs
                    Function ty pos param canOverride -> [(str,(Function ty pos param True):entries)] ++ updateIfCanOverride_ xs
updateIfCanOverride_ ((str,[]):xs) = ((str,[]):xs)
updateIfCanOverride_ [] = []

-- Given a list of variable ids, returns true if they can be overrided (false if at least one of them CANNOT be overrided)
checkIfCanOverride :: [Prelude.String] -> Env -> Prelude.String -> Bool
checkIfCanOverride (x:xs) env "var" = case Data.Map.lookup x env of
    Just (entry:entries) -> case entry of
        Variable ty pos varMode canOverride -> canOverride && (checkIfCanOverride xs env "var")
        _ -> True && (checkIfCanOverride xs env "var")
    Nothing -> True && (checkIfCanOverride xs env "var")
checkIfCanOverride (x:xs) env "func" = case Data.Map.lookup x env of
    Just (entry:entries) -> case entry of
        Function ty pos param canOverride -> canOverride
        _ -> True
    Nothing -> True
checkIfCanOverride [] env _ = True

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
buildParam (Abs.ParameterPointer pos id ty po) = (TypeChecker.Parameter (buildPointerOfType (getTypeFromPrimitive ty) (countPointers po)) pos "_mode_" (getIdFromIdent id)) 

-- Given a list of parameters (from a func env entry) returns the list of types of each parameter
getTypeListFromFuncParams :: [Parameter] -> [Type]
getTypeListFromFuncParams ((TypeChecker.Parameter ty _ _ _):xs) = [ty] ++ getTypeListFromFuncParams xs
getTypeListFromFuncParams [] = []

-- Given a parameter list, return the list of ids
getListOfIdsFromParamList :: [TypeChecker.Parameter] -> [Prelude.String]
getListOfIdsFromParamList ((TypeChecker.Parameter ty pos mode id):xs) = [id] ++ getListOfIdsFromParamList xs
getListOfIdsFromParamList [] = []

-- Return true if there is a dups in the list (of parameters ids)
checkDuplicatedParametersInFunDecl :: [Prelude.String] -> Prelude.Bool
checkDuplicatedParametersInFunDecl (x:xs) = isInList x xs || checkDuplicatedParametersInFunDecl xs
checkDuplicatedParametersInFunDecl [] = False

-- Check if function can be overrided
checkFuncOverride :: Abs.Ident Posn -> Env -> TCheckResult
checkFuncOverride (Abs.Ident id pos) env = if (checkIfCanOverride [id] env "func")
                                           then TResult env (B_type Type_Void) pos 
                                           else TError ["Cannot redefine function " ++ id ++ "! Position: " ++ show pos]

------------------------------------------------------------------------------------------------------
--- FUNCTIONS FOR POINTERS  --------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------

-- Given a primitive type, builds a pointer of that type
buildPointerOfType :: Type -> Prelude.Integer -> Type
buildPointerOfType t n = Pointer t n

-- Given a pointer symbol, counts how many are them
-- Example: **** -> 4
countPointers :: Abs.POINTER Posn -> Prelude.Integer
countPointers (Abs.PointerSymbol pos po) = 1 + countPointers po
countPointers (Abs.PointerSymbolSingle pos) = 1

-- Return true if the given string is in the given string list
isInList :: Prelude.String -> [Prelude.String] -> Prelude.Bool
isInList id (x:xs) = id == x || isInList id xs
isInList id [] = False

-------------------------------------------------------------------------------------------------------
--- FUNCTIONS FOR GETTING INFOS FROM VAR-DECLARATIONS FOR ENV ENTRY -----------------------------------
-------------------------------------------------------------------------------------------------------

getRealType :: TCheckResult -> TCheckResult
getRealType tcheck = case tcheck of
                    TResult env (Pointer t depth) pos -> TResult env t pos
                    TResult env (Array t dim) pos -> TResult env t pos
                    _ -> tcheck

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
getTypeExpr (Abs.TypeExpressionArraySimple _ rangeexp typeexpression) = Array (getTypeFromTypeExp typeexpression) (getArrayLength rangeexp)
getTypeExpr (Abs.TypeExpressionArray _ rangeexp typeexpression) = Array (getTypeFromTypeExp typeexpression) (getArrayLength rangeexp)
getTypeExpr (Abs.TypeExpressionPointer _ primitive pointer) = Pointer (getTypeFromPrimitive primitive) (checkPointerDepth pointer)
getTypeExpr (Abs.TypeExpressionPointerOfArray pos typeexpression pointer) = Pointer (getTypeFromTypeExp typeexpression) (checkPointerDepth pointer)

-- Given a Pointer node of the ABS, it counts the depth (how much pointers '*' there are) of that pointer
-- Example: var x:int***** -> depth: 5
checkPointerDepth :: Abs.POINTER Posn -> Prelude.Integer
checkPointerDepth (Abs.PointerSymbol _ p) = 1 + checkPointerDepth p
checkPointerDepth (Abs.PointerSymbolSingle _) = 1

-- Given a typeexpression returns the type
getTypeFromTypeExp :: Abs.TYPEEXPRESSION Posn -> Type
getTypeFromTypeExp (Abs.TypeExpression _ primitive) = getTypeFromPrimitive primitive
getTypeFromTypeExp (Abs.TypeExpressionArraySimple _ rangeexp typeexpression) = Array (getTypeFromTypeExp typeexpression) (getArrayLength rangeexp)
getTypeFromTypeExp (Abs.TypeExpressionArray _ rangeexp typeexpression) = Array (getTypeFromTypeExp typeexpression) (getArrayLength rangeexp)
getTypeFromTypeExp (Abs.TypeExpressionPointer _ primitive pointer) = Pointer (getTypeFromPrimitive primitive) (checkPointerDepth pointer)
getTypeFromTypeExp (Abs.TypeExpressionPointerOfArray pos typeexpression pointer) = Pointer (getTypeFromTypeExp typeexpression) (checkPointerDepth pointer)

-- Get a PrimitiveType node of the ABS, returns the correct Type
getTypeFromPrimitive :: Abs.PRIMITIVETYPE Posn -> Type
getTypeFromPrimitive (Abs.PrimitiveTypeVoid _) = (B_type Type_Void)
getTypeFromPrimitive (Abs.PrimitiveTypeBool _) = (B_type Type_Boolean)
getTypeFromPrimitive (Abs.PrimitiveTypeInt _) = (B_type Type_Integer)
getTypeFromPrimitive (Abs.PrimitiveTypeReal _) = (B_type Type_Real)
getTypeFromPrimitive (Abs.PrimitiveTypeString _) = (B_type Type_String)
getTypeFromPrimitive (Abs.PrimitiveTypeChar _) = (B_type Type_Char)
getTypeFromPrimitive (Abs.TypeArray _ prim) =  (Type.Array (getTypeFromPrimitive prim) (getArrayDimFunc prim))

-- Returns array dimension
getArrayDimFunc :: Abs.PRIMITIVETYPE Posn -> Prelude.Integer
getArrayDimFunc (Abs.TypeArray _ ty) = 1 + getArrayDimFunc ty
getArrayDimFunc _ = 1

-- Counts array length from rangeexpression
getArrayLength :: Abs.RANGEEXP Posn -> Prelude.Integer
getArrayLength (Abs.RangeExpression pos exp1 exp2 rangeexp) = 1 + getArrayLength rangeexp
getArrayLength _ = 1

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

-- counts number of indexed dimension on a indexed array call
countIndex :: Abs.ARRAYINDEXELEMENT Posn -> Prelude.Integer 
countIndex (Abs.ArrayIndexElement pos ti) = countIndex_ ti
countIndex (Abs.ArrayIndexElementEmpty pos) = 0

-- implements the previous func
countIndex_ :: Abs.TYPEINDEX Posn -> Prelude.Integer 
countIndex_ (Abs.TypeOfIndexInt pos ti val) = 1 + countIndex_ ti
countIndex_ (Abs.TypeOfIndexIntSingle pos val) = 1 
countIndex_ (Abs.TypeOfIndexVar pos ti val index) = 1 + countIndex_ ti
countIndex_ (Abs.TypeOfIndexVarSingle pos val index) = 1 
countIndex_ node@(Abs.TypeOfIndexPointer pos typeindex unaryop def) = 1 + countIndex_ typeindex
countIndex_ node@(Abs.TypeOfIndexPointerSingle pos unaryop def) = 1
countIndex_ node@(Abs.TypeOfIndexBinary pos typeindex def binaryop exp) = 1 + countIndex_ typeindex
countIndex_ node@(Abs.TypeOfIndexBinarySingle pos def binaryop exp ) = 1
countIndex_ node@(Abs.TypeOfIndexExpressionCall pos typeindex id exps ) = 1 + countIndex_ typeindex
countIndex_ node@(Abs.TypeOfIndexExpressionCallSingle pos id exps ) = 1

-- Checks if array is being indexed
    -- if it is: return primitive type
    -- if it isn't: return array type
indexing :: TCheckResult -> Abs.ARRAYINDEXELEMENT Posn -> TCheckResult
indexing (TResult env (Array t dim) pos) index = case index of
                                                        Abs.ArrayIndexElementEmpty posIn -> TResult env (Array t dim) pos
                                                        _ -> TResult env t pos
indexing t index = t

-- Check if array has pointers inside
isTherePointer :: Type -> Bool
isTherePointer (Pointer _ _) = True
isTherePointer (Array t _) = isTherePointer t
isTherePointer _ = False
         
---------------------------------------------------------------------------------------------------
--- GENERIC FUNCTIONS used for RETURN KEYS CHECKS -------------------------------------------------
---------------------------------------------------------------------------------------------------

subString :: Prelude.String -> Prelude.String -> Prelude.String
subString (x:xs) zs = case x of
                    ' ' -> if (zs == "TypeArray") then "array" ++ researchType xs [] else zs
                    _ -> subString xs (zs++[x])

researchType :: Prelude.String -> Prelude.String -> Prelude.String
researchType (x:xs) zs = case x of
                        ' ' -> if (zs == "primitivetype_primitivetype") then researchType_ xs [] else researchType xs []
                        _ -> researchType xs (zs++[x])

researchType_ :: Prelude.String -> Prelude.String -> Prelude.String
researchType_ (x:xs) zs = case x of
                        ' ' -> if (zs == "=") then researchType_ xs [] else stringTypeConv zs
                        _ -> researchType_ xs (zs++[x])

stringTypeConv :: Prelude.String -> Prelude.String
stringTypeConv str = case str of
                    "PrimitiveTypeInt" -> "int"
                    "PrimitiveTypeReal" -> "real"
                    "PrimitiveTypeString" -> "string"
                    "PrimitiveTypeChar" -> "char"
                    "PrimitiveTypeBool" -> "bool"
                    "PrimitiveTypeVoid" -> "void"
                    _ -> str

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
executeStatements node@(Abs.EmptyStatement _) env = Abs.EmptyStatement (checkListStatement node env)

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
executeStatement node@(Abs.ProcedureStatement pos id param states) env = let newEnv = createEnvEntryForParams (getParamList param) (updateIfCanOverride (first (updateEnv (Abs.ListStatements pos node (Abs.EmptyStatement pos)) env []))) in
                                                                            let newEnv2 = Data.Map.delete "while" (first (insertWith (++) "return_void" [] newEnv, [])) in  
                                                                                Abs.ProcedureStatement (checkTypeStatement node env) (executeIdentFunc id env) (executeParam param env) (executeStatements states newEnv2)
executeStatement node@(Abs.FunctionStatement pos id param tipo states) env = let newEnv = createEnvEntryForParams (getParamList param) (updateIfCanOverride (first (updateEnv (Abs.ListStatements pos node (Abs.EmptyStatement pos)) env []))) in
                                                                                let newEnv2 = Data.Map.delete "while" (first (insertWith (++) ("return_"++stringTypeConv (subString (show tipo) [])) [] newEnv, [])) in  
                                                                                    Abs.FunctionStatement (checkTypeStatement node env) (executeIdentFunc id env) (executeParam param env) (executePrimitiveType tipo env) (executeStatements states newEnv2)

executeParam :: Abs.PARAMETERS Posn -> Env -> Abs.PARAMETERS TCheckResult
executeParam node@(Abs.ParameterList pos param params) env = Abs.ParameterList (checkTypeExecuteParameter node env) (executeParameter param env) (executeParam params env)
executeParam node@(Abs.ParameterListSingle pos param) env = Abs.ParameterListSingle (checkTypeExecuteParameter node env) (executeParameter param env)
executeParam node@(Abs.ParameterListEmpty pos) env = Abs.ParameterListEmpty (checkTypeExecuteParameter node env) 

executeParameter :: Abs.PARAMETER Posn -> Env -> Abs.PARAMETER TCheckResult
executeParameter node@(Abs.Parameter pos id ty) env = Abs.Parameter (checkTypeParameter node env) (executeIdentVar id env) (executePrimitiveType ty env)
executeParameter node@(Abs.ParameterPointer pos id ty po) env = Abs.ParameterPointer (checkTypeParameter node env) (executeIdentVar id env) (executePrimitiveType ty env) (executeTypeExpressionPointer po env)

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
executeInitPart node@(Abs.InitializzationPartArray pos arrayinit) env = Abs.InitializzationPartArray (checkTypeInitializzationPart node env) (executeArrayInit arrayinit env)
executeInitPart node@(Abs.InitializzationPartEmpty pos) env = Abs.InitializzationPartEmpty (TResult env (B_type Type_Void) pos)

executeArrayInit :: Abs.ARRAYINIT Posn -> Env -> Abs.ARRAYINIT TCheckResult
executeArrayInit node@(Abs.ArrayInitSingle pos arrayinit) env = Abs.ArrayInitSingle (checkTypeArrayInit node env) (executeArrayInit arrayinit env)
executeArrayInit node@(Abs.ArrayInit pos arrayinit1 arrayinit2) env = Abs.ArrayInit (checkTypeArrayInit node env) (executeArrayInit arrayinit1 env) (executeArrayInit arrayinit2 env)
executeArrayInit node@(Abs.ArrayInitSingleElems pos listelementarray) env = Abs.ArrayInitSingleElems (checkTypeArrayInit node env) (executeListElementArray listelementarray env)
executeArrayInit node@(Abs.ArrayInitElems pos listelementarray arrayinit) env = Abs.ArrayInitElems (checkTypeArrayInit node env) (executeListElementArray listelementarray env) (executeArrayInit arrayinit env)

executeListElementArray :: Abs.LISTELEMENTARRAY Posn -> Env -> Abs.LISTELEMENTARRAY TCheckResult
executeListElementArray node@(Abs.ListElementsOfArray pos expr elementlist) env = Abs.ListElementsOfArray (checkListElementsOfArray node env) (executeExpression expr env) (executeListElementArray elementlist env)
executeListElementArray node@(Abs.ListElementOfArray pos expr) env = Abs.ListElementOfArray (checkListElementsOfArray node env) (executeExpression expr env)

executeTypeExpression :: Abs.TYPEEXPRESSION Posn -> Env -> Abs.TYPEEXPRESSION TCheckResult
executeTypeExpression node@(Abs.TypeExpression pos primitivetype) env = Abs.TypeExpression (checkTypeTypeExpression node env) (executePrimitiveType primitivetype env)
executeTypeExpression node@(Abs.TypeExpressionArraySimple pos rangeexp typeexpression) env = Abs.TypeExpressionArraySimple (checkTypeTypeExpression node env) (executeRangeExp rangeexp env) (executeTypeExpression typeexpression env)
executeTypeExpression node@(Abs.TypeExpressionArray pos rangeexp typeexpression) env = Abs.TypeExpressionArray (checkTypeTypeExpression node env) (executeRangeExp rangeexp env) (executeTypeExpression typeexpression env)
executeTypeExpression node@(Abs.TypeExpressionPointer pos primitivetype pointer) env = Abs.TypeExpressionPointer (checkTypeTypeExpression node env) (executePrimitiveType primitivetype env) (executeTypeExpressionPointer pointer env)
executeTypeExpression node@(Abs.TypeExpressionPointerOfArray pos typeexpression pointer) env = Abs.TypeExpressionPointerOfArray (checkTypeTypeExpression node env) (executeTypeExpression typeexpression env) (executeTypeExpressionPointer pointer env)

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

executeNamedExpressionList :: Abs.NAMEDEXPRESSIONLIST Posn -> Env -> Abs.NAMEDEXPRESSIONLIST TCheckResult
executeNamedExpressionList node@(Abs.NamedExpressionList pos namedexpr) env = Abs.NamedExpressionList (checkTypeNamedExpressionList node env) (executeNamedExpression namedexpr env)
executeNamedExpressionList node@(Abs.NamedExpressionListEmpty pos) env = Abs.NamedExpressionListEmpty (TResult env (B_type Type_Void) pos)
executeNamedExpressionList node@(Abs.NamedExpressionLists pos namedexpr namedexprlist) env = Abs.NamedExpressionLists (checkTypeNamedExpressionList node env) (executeNamedExpression namedexpr env) (executeNamedExpressionList namedexprlist env)

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
executeExpression node@(Abs.ExpressionUnary pos unary def) env = Abs.ExpressionUnary (checkTypeExpression node env) (executeUnaryOp unary env) (executeDefault def env)
executeExpression node@(Abs.ExpressionBinary pos def binary exp) env = Abs.ExpressionBinary (checkTypeExpression node env) (executeDefault def env) (executeBinaryOp binary env) (executeExpression exp env)
executeExpression node@(Abs.ExpressionIdent pos id index) env = Abs.ExpressionIdent (checkTypeIdentVar id env) (executeIdentVar id env) (executeArrayIndexElement index env)
executeExpression node@(Abs.ExpressionCall pos id exps) env = Abs.ExpressionCall (checkTypeExpression node env) (executeIdentFunc id env) (executeExpressions exps env) 

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
executeDefault node@(Abs.ExpressionIntegerD pos value) env = Abs.ExpressionIntegerD (checkTypeDefault 0 node env) (executeInteger value env)
executeDefault node@(Abs.ExpressionBooleanD pos value) env = Abs.ExpressionBooleanD (checkTypeDefault 0 node env) (executeBoolean value env)
executeDefault node@(Abs.ExpressionCharD pos value) env = Abs.ExpressionCharD (checkTypeDefault 0 node env) (executeChar value env)
executeDefault node@(Abs.ExpressionStringD pos value) env = Abs.ExpressionStringD (checkTypeDefault 0 node env) (executeString value env)
executeDefault node@(Abs.ExpressionRealD pos value) env = Abs.ExpressionRealD (checkTypeDefault 0 node env) (executeReal value env)
executeDefault node@(Abs.ExpressionBracketD pos exp) env = Abs.ExpressionBracketD (checkTypeDefault 0 node env) (executeExpression exp env)
executeDefault node@(Abs.ExpressionCastD pos def ty) env = Abs.ExpressionCastD (checkTypeDefault 0 node env) (executeDefault def env) (executePrimitiveType ty env)
executeDefault node@(Abs.ExpressionUnaryD pos unary def) env = Abs.ExpressionUnaryD (checkTypeDefault 0 node env) (executeUnaryOp unary env) (executeDefault def env)
executeDefault node@(Abs.ExpressionIdentD pos id index) env = Abs.ExpressionIdentD (checkTypeIdentVar id env) (executeIdentVar id env) (executeArrayIndexElement index env)

executeLValue :: Abs.LVALUEEXPRESSION Posn -> Env -> Abs.LVALUEEXPRESSION TCheckResult
executeLValue node@(Abs.LvalueExpression pos id ident) env = Abs.LvalueExpression (checkTypeLvalueExpression node env) (executeIdentVar id env) (executeArrayIndexElement ident env)
executeLValue node@(Abs.LvalueExpressions pos id ident next) env = Abs.LvalueExpressions (checkTypeLvalueExpression node env) (executeIdentVar id env) (executeArrayIndexElement ident env) (executeLValue next env)                
                                                                                                
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

executeTypeTypeIndex :: Abs.TYPEINDEX Posn -> Env -> Abs.TYPEINDEX TCheckResult
executeTypeTypeIndex node@(Abs.TypeOfIndexInt pos typeindex integer) env = Abs.TypeOfIndexInt (checkTypeTypeIndex node env) (executeTypeTypeIndex typeindex env) (executeInteger integer env)
executeTypeTypeIndex node@(Abs.TypeOfIndexIntSingle pos integer) env = Abs.TypeOfIndexIntSingle (checkTypeTypeIndex node env) (executeInteger integer env)
executeTypeTypeIndex node@(Abs.TypeOfIndexVar pos typeindex id index) env = Abs.TypeOfIndexVar (checkTypeTypeIndex node env) (executeTypeTypeIndex typeindex env) (executeIdentVar id env) (executeArrayIndexElement index env)
executeTypeTypeIndex node@(Abs.TypeOfIndexVarSingle pos id index) env = Abs.TypeOfIndexVarSingle (checkTypeTypeIndex node env) (executeIdentVar id env) (executeArrayIndexElement index env)
executeTypeTypeIndex node@(Abs.TypeOfIndexPointer pos typeindex unaryop def) env = Abs.TypeOfIndexPointer (checkTypeTypeIndex node env) (executeTypeTypeIndex typeindex env) (executeUnaryOp unaryop env) (executeDefault def env)
executeTypeTypeIndex node@(Abs.TypeOfIndexPointerSingle pos unaryop def) env = Abs.TypeOfIndexPointerSingle (checkTypeTypeIndex node env) (executeUnaryOp unaryop env) (executeDefault def env)
executeTypeTypeIndex node@(Abs.TypeOfIndexBinary pos typeindex def binaryop exp) env = Abs.TypeOfIndexBinary (checkTypeTypeIndex node env) (executeTypeTypeIndex typeindex env) (executeDefault def env) (executeBinaryOp binaryop env) (executeExpression exp env)
executeTypeTypeIndex node@(Abs.TypeOfIndexBinarySingle pos def binaryop exp ) env = Abs.TypeOfIndexBinarySingle (checkTypeTypeIndex node env) (executeDefault def env) (executeBinaryOp binaryop env) (executeExpression exp env)
executeTypeTypeIndex node@(Abs.TypeOfIndexExpressionCall pos typeindex id exps ) env = Abs.TypeOfIndexExpressionCall (checkTypeTypeIndex node env) (executeTypeTypeIndex typeindex env) (executeIdentVar id env) (executeExpressions exps env)
executeTypeTypeIndex node@(Abs.TypeOfIndexExpressionCallSingle pos id exps ) env = Abs.TypeOfIndexExpressionCallSingle (checkTypeTypeIndex node env) (executeIdentVar id env) (executeExpressions exps env)

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
                                                                (Abs.EmptyStatement pos) -> checkListStatement (Abs.EmptyStatement pos) start_env
                                                                node@(Abs.ListStatements pos stat stats) -> checkListStatement node start_env

checkListStatement :: Abs.STATEMENTS Posn -> Env -> TCheckResult
checkListStatement (Abs.EmptyStatement pos) env = TResult env (B_type Type_Void) pos
checkListStatement (Abs.ListStatements pos stat stats) env = TResult env (B_type Type_Void) pos

checkTypeLvalueExpression :: Abs.LVALUEEXPRESSION Posn -> Env -> TCheckResult
checkTypeLvalueExpression node@(Abs.LvalueExpression pos ident@(Abs.Ident id posI) index) env = case Data.Map.lookup id env of
                                                                        -- 1 entry of type array
                                                                        Just [Variable (Array t dim) pos mode override] -> case index of 
                                                                                                                            Abs.ArrayIndexElementEmpty posIn -> if mode == "param"  -- if param.. error because it cannot be overwritten
                                                                                                                                                                then TError ["Variable " ++ id ++" is a param var. (const. at compile-time)! Cannot assign a value!"++ (show posI)] 
                                                                                                                                                                else TResult env (Array t dim) pos
                                                                                                                            _ ->if dim == (countIndex index) then if mode == "param"  -- if param.. error because it cannot be overwritten
                                                                                                                                                                    then TError ["Variable " ++ id ++" is a param var. (const. at compile-time)! Cannot assign a value!"++ (show posI)] 
                                                                                                                                                                    else TResult env t pos else TError ["Array indexing incorrect! number of indexed dimensions not matching the dim. of the array! "++ show pos] 
                                                                        -- multiple entries; first is of type array
                                                                        Just ((Variable (Array t dim) pos mode override):xs) -> case index of
                                                                                                                                Abs.ArrayIndexElementEmpty posIn -> if mode == "param"  -- if param.. error because it cannot be overwritten
                                                                                                                                                                    then TError ["Variable " ++ id ++" is a param var. (const. at compile-time)! Cannot assign a value!"++ (show posI)] 
                                                                                                                                                                    else TResult env (Array t dim) pos
                                                                                                                                _ ->if dim == (countIndex index) then if mode == "param"  -- if param.. error because it cannot be overwritten
                                                                                                                                                                    then TError ["Variable " ++ id ++" is a param var. (const. at compile-time)! Cannot assign a value!"++ (show posI)] 
                                                                                                                                                                    else TResult env t pos else TError ["Array indexing incorrect! number of indexed dimensions not matching the dim. of the array! "++ show pos] 
                                                                        -- 1 entry of type func
                                                                        Just [Function _ _ _ _] -> (TError ["Variable " ++ id ++ " undeclared! Position: " ++ (show posI)])
                                                                        -- multiple entries; first is of type func
                                                                        Just ((Function _ _ _ _):xs) -> let v =findEntryOfType xs "var" in
                                                                                                        case v of
                                                                                                            [] -> (TError ["Variable " ++ id ++ " undeclared! Position: " ++ (show posI)])
                                                                                                            ((Variable (Array t dim) pos mode override):ys) -> case index of
                                                                                                                                                                Abs.ArrayIndexElementEmpty posIn -> if mode == "param"  -- if param.. error because it cannot be overwritten
                                                                                                                                                                                                    then TError ["Variable " ++ id ++" is a param var. (const. at compile-time)! Cannot assign a value!" ++ (show posI)]
                                                                                                                                                                                                    else TResult env (Array t dim) pos
                                                                                                                                                                _ -> if dim == (countIndex index) then if mode == "param"  -- if param.. error because it cannot be overwritten
                                                                                                                                                                                                       then TError ["Variable " ++ id ++" is a param var. (const. at compile-time)! Cannot assign a value!" ++ (show posI)] 
                                                                                                                                                                                                       else TResult env t pos else TError ["Array indexing incorrect! number of indexed dimensions not matching the dim. of the array! " ++ show pos] 
                                                                                                            ((Variable t pos mode override):ys) -> if mode == "param" -- if param.. error because it cannot be overwritten
                                                                                                                                                   then TError ["Variable " ++ id ++" is a param var. (const. at compile-time)! Cannot assign a value!"++ (show posI)] 
                                                                                                                                                   else TResult env t pos
                                                                        -- 1 entry of type var
                                                                        Just [Variable t pos mode override] -> if mode == "param"  -- if param.. error because it cannot be overwritten
                                                                                                               then TError ["Variable " ++ id ++" is a param var. (const. at compile-time)! Cannot assign a value!"++ (show posI)] 
                                                                                                               else TResult env t pos
                                                                        -- multiple entries; first is of type var
                                                                        Just ((Variable t pos mode override):xs) -> if mode == "param"  -- if param.. error because it cannot be overwritten
                                                                                                               then TError ["Variable " ++ id ++" is a param var. (const. at compile-time)! Cannot assign a value!"++ (show posI)] 
                                                                                                               else TResult env t pos
                                                                        Nothing -> (TError ["Variable " ++ id ++ " undeclared! Position: " ++ (show posI)])

checkTypeLvalueExpression node@(Abs.LvalueExpressions pos ident@(Abs.Ident id posI) index next) env = case Data.Map.lookup id env of
                                                                        -- 1 entry of type array
                                                                        Just [Variable (Array t dim) pos mode override] -> case index of
                                                                                                                            Abs.ArrayIndexElementEmpty posIn -> if (checkCompatibility (TResult env (Array t dim) pos) (checkTypeLvalueExpression next env)) then if mode == "param" 
                                                                                                                                                                                                                                                                  then TError ["Variable " ++ id ++" is a param var. (const. at compile-time)! Cannot assign a value!"++ (show posI)] 
                                                                                                                                                                                                                                                                  else TResult env (Array t dim) pos else case (checkTypeLvalueExpression next env) of
                                                                                                                                                                                                                                                                    TError e -> TError e -- if there was an error, propagate... if it wasn't then the error is because of the incompatible types!
                                                                                                                                                                                                                                                                    _ -> TError ["Incompatible types on multiple assignment! Position: " ++ (show posI)]
                                                                                                                            _ ->if dim == (countIndex index) then if (checkCompatibility (TResult env t pos) (checkTypeLvalueExpression next env)) then if mode == "param" 
                                                                                                                                                                                                                                                        then TError ["Variable " ++ id ++" is a param var. (const. at compile-time)! Cannot assign a value!"++ (show posI)] 
                                                                                                                                                                                                                                                        else TResult env t pos else case (checkTypeLvalueExpression next env) of
                                                                                                                                                                                                                                                            TError e -> TError e -- if there was an error, propagate... if it wasn't then the error is because of the incompatible types!
                                                                                                                                                                                                                                                            _ -> TError ["Incompatible types on multiple assignment! Position: " ++ (show posI)]
                                                                                                                                else TError ["Array indexing incorrect! number of indexed dimensions not matching the dim. of the array! "++ show pos] 
                                                                        -- multiple entries; first is of type array
                                                                        Just ((Variable (Array t dim) pos mode override):xs) -> case index of
                                                                                                                            Abs.ArrayIndexElementEmpty posIn -> if (checkCompatibility (TResult env (Array t dim) pos) (checkTypeLvalueExpression next env)) then if mode == "param" 
                                                                                                                                                                                                                                                             then TError ["Variable " ++ id ++" is a param var. (const. at compile-time)! Cannot assign a value!"++ (show posI)] 
                                                                                                                                                                                                                                                             else TResult env (Array t dim) pos else case (checkTypeLvalueExpression next env) of
                                                                                                                                                                                                                                                                TError e -> TError e -- if there was an error, propagate... if it wasn't then the error is because of the incompatible types!
                                                                                                                                                                                                                                                                _ -> TError ["Incompatible types on multiple assignment! Position: " ++ (show posI)]
                                                                                                                            _ ->if dim == (countIndex index) then if (checkCompatibility (TResult env t pos) (checkTypeLvalueExpression next env)) then if mode == "param" 
                                                                                                                                                                                                                                                        then TError ["Variable " ++ id ++" is a param var. (const. at compile-time)! Cannot assign a value!"++ (show posI)] 
                                                                                                                                                                                                                                                        else TResult env t pos else case (checkTypeLvalueExpression next env) of
                                                                                                                                                                                                                                                            TError e -> TError e -- if there was an error, propagate... if it wasn't then the error is because of the incompatible types!
                                                                                                                                                                                                                                                            _ -> TError ["Incompatible types on multiple assignment! Position: " ++ (show posI)]
                                                                                                                                else TError ["Array indexing incorrect! number of indexed dimensions not matching the dim. of the array! "++ show pos] 
                                                                        -- 1 entry of type func
                                                                        Just [Function _ _ _ _] -> (TError ["Variable " ++ id ++ " undeclared! Position: " ++ (show posI)])
                                                                        -- multiple entries; first is of type func
                                                                        Just ((Function _ _ _ _):xs) -> let v =findEntryOfType xs "var" in
                                                                                                        case v of
                                                                                                            [] -> (TError ["Variable " ++ id ++ " undeclared! Position: " ++ (show posI)])
                                                                                                            ((Variable (Array t dim) pos mode override):ys) -> case index of
                                                                                                                            Abs.ArrayIndexElementEmpty posIn -> if (checkCompatibility (TResult env (Array t dim) pos) (checkTypeLvalueExpression next env)) then if mode == "param" 
                                                                                                                                                                                                                                                                  then TError ["Variable " ++ id ++" is a param var. (const. at compile-time)! Cannot assign a value!"++ (show posI)] 
                                                                                                                                                                                                                                                                  else TResult env (Array t dim) pos else case (checkTypeLvalueExpression next env) of
                                                                                                                                                                                                                                                                    TError e -> TError e
                                                                                                                                                                                                                                                                    _ -> TError ["Incompatible types on multiple assignment! Position: " ++ (show posI)]
                                                                                                                            _ ->if dim == (countIndex index) then if (checkCompatibility (TResult env t pos) (checkTypeLvalueExpression next env)) then if mode == "param" 
                                                                                                                                                                                                                                                        then TError ["Variable " ++ id ++" is a param var. (const. at compile-time)! Cannot assign a value!"++ (show posI)] 
                                                                                                                                                                                                                                                        else TResult env t pos else case (checkTypeLvalueExpression next env) of
                                                                                                                                                                                                                                                            TError e -> TError e -- if there was an error, propagate... if it wasn't then the error is because of the incompatible types!
                                                                                                                                                                                                                                                            _ -> TError ["Incompatible types on multiple assignment! Position: " ++ (show posI)]
                                                                                                                                else TError ["Array indexing incorrect! number of indexed dimensions not matching the dim. of the array! "++ show pos] 
                                                                                                            ((Variable t pos mode override):ys) -> if (checkCompatibility (TResult env t pos) (checkTypeLvalueExpression next env)) then if mode == "param" 
                                                                                                                                                                                                                                         then TError ["Variable " ++ id ++" is a param var. (const. at compile-time)! Cannot assign a value!"++ (show posI)] 
                                                                                                                                                                                                                                         else TResult env t pos else case (checkTypeLvalueExpression next env) of
                                                                                                                                                                                                                                            TError e -> TError e -- if there was an error, propagate... if it wasn't then the error is because of the incompatible types!
                                                                                                                                                                                                                                            _ -> TError ["Incompatible types on multiple assignment! Position: " ++ (show posI)]
                                                                        -- 1 entry of type var
                                                                        Just [Variable t pos mode override] -> if (checkCompatibility (TResult env t pos) (checkTypeLvalueExpression next env)) then if mode == "param" 
                                                                                                                                                                                                then TError ["Variable " ++ id ++" is a param var. (const. at compile-time)! Cannot assign a value!"++ (show posI)] 
                                                                                                                                                                                                else TResult env t pos else case (checkTypeLvalueExpression next env) of
                                                                                                                                                                                                    TError e -> TError e -- if there was an error, propagate... if it wasn't then the error is because of the incompatible types!
                                                                                                                                                                                                    _ -> TError ["Incompatible types on multiple assignment! Position: " ++ (show posI)]
                                                                        -- multiple entries; first is of type var
                                                                        Just ((Variable t pos mode override):xs) -> if (checkCompatibility (TResult env t pos) (checkTypeLvalueExpression next env)) then if mode == "param" 
                                                                                                                                                                                                          then TError ["Variable " ++ id ++" is a param var. (const. at compile-time)! Cannot assign a value!"++ (show posI)] 
                                                                                                                                                                                                          else TResult env t pos else case (checkTypeLvalueExpression next env) of
                                                                                                                                                                                                              TError e -> TError e -- if there was an error, propagate... if it wasn't then the error is because of the incompatible types!
                                                                                                                                                                                                              _ -> TError ["Incompatible types on multiple assignment! Position: " ++ (show posI)]
                                                                        Nothing -> (TError ["Variable " ++ id ++ " undeclared! Position: " ++ (show posI)])


checkArrayIndexElement :: Abs.ARRAYINDEXELEMENT Posn -> Env -> TCheckResult
checkArrayIndexElement node@(Abs.ArrayIndexElement pos index) env = let indexTCheck = checkTypeTypeIndex index env in
                                                                        case indexTCheck of
                                                                            TResult _ _ _ -> (TResult env (B_type Type_Void ) pos)
                                                                            TError e -> indexTCheck
checkArrayIndexElement node@(Abs.ArrayIndexElementEmpty pos) env = (TResult env (B_type Type_Void ) pos)

checkTypeStatement :: Abs.STATEMENT Posn -> Env -> TCheckResult
checkTypeStatement node@(Abs.BreakStatement pos) env = checkTypeBreakStatement node env
checkTypeStatement node@(Abs.ContinueStatement pos) env = checkTypeContinueStatement node env
checkTypeStatement node@(Abs.ReturnStatement pos ret) env = checkTypeReturnStatement node env
checkTypeStatement node@(Abs.Statement pos b) env = checkTypeB b env
checkTypeStatement node@(Abs.ExpressionStatement pos exp) env = checkTypeExpressionStatement exp env
checkTypeStatement node@(Abs.AssignmentStatement pos lval assignOp exp) env = let expTCheck = (checkTypeExpression exp env) in
                                                                                    let lvalTCheck = (checkTypeLvalueExpression lval env) in
                                                                                        case lvalTCheck of
                                                                                            TResult _ (Pointer t depth) _ -> case expTCheck of
                                                                                                                             TResult _ (Pointer te depthe) _ ->if depth==depthe+1 
                                                                                                                                                                then
                                                                                                                                                                    if t==te
                                                                                                                                                                        then
                                                                                                                                                                            expTCheck
                                                                                                                                                                        else
                                                                                                                                                                            TError ["Cannot assign pointer of type " ++ show (getType expTCheck) ++ " to pointer of type " ++ show (getType lvalTCheck) ++ "! Position: "++ show pos]
                                                                                                                                                                else TError ["Pointer of depth "++ show depth++" is incompatible with a pointer of depth "++ show depthe++"! Position: "++ show pos]
                                                                                                                             TResult _ (Array te dime) _ -> if depth==1 then
                                                                                                                                                                 if t == Array te dime
                                                                                                                                                                         then
                                                                                                                                                                             expTCheck
                                                                                                                                                                         else 
                                                                                                                                                                             TError ["Pointer of type "++ show t++" cannot point to value of type " ++ show (getType expTCheck) ++ "! Position: "++ show pos]
                                                                                                                                                else TError ["Expression is not a pointer! Position: "++ show pos]
                                                                                                                             TResult _ te _ -> if depth==1 then
                                                                                                                                                    if checkCompatibility (TResult env t pos) (TResult env te pos)
                                                                                                                                                        then
                                                                                                                                                            expTCheck
                                                                                                                                                        else 
                                                                                                                                                            TError ["Pointer of type "++ show t++" cannot point to value of type " ++ show (getType expTCheck) ++ "! Position: "++ show pos]
                                                                                                                                                else TError ["Expression is not a pointer! Position: "++ show pos]
                                                                                                                             TError e -> expTCheck
                                                                                            TResult _ (Array t dim) _ -> case expTCheck of
                                                                                                                             TResult _ _ _ -> TError ["Cannot assign values to variable of type " ++ show (getType lvalTCheck) ++ "! Position: "++ show pos]
                                                                                                                             TError e -> expTCheck
                                                                                            TResult _ t _ -> case expTCheck of --casi base
                                                                                                                TResult _ (Array te dime) _ -> TError ["Cannot assign value of type " ++ show (getType expTCheck) ++ " to variable of type " ++ show (getType lvalTCheck) ++ "! Position: "++ show pos]                                                                          
                                                                                                                TResult _ (Pointer te depthe) _ ->  TError ["Cannot assign value of type " ++ show (getType expTCheck) ++ " to variable of type " ++ show (getType lvalTCheck) ++ "! Position: "++ show pos]                                                                          
                                                                                                                TResult _ te _ -> if(checkCompatibility expTCheck lvalTCheck) then expTCheck else TError ["Cannot assign value of type " ++ show (getType expTCheck) ++ " to variable of type " ++ show (getType lvalTCheck) ++ "! Position: "++ show pos]
                                                                                                                TError e -> expTCheck
                                                                                            TError e -> case expTCheck of
                                                                                                                TResult _ _ _ -> lvalTCheck
                                                                                                                TError e -> mergeErrors lvalTCheck expTCheck 
checkTypeStatement node@(Abs.VariableDeclarationStatement pos tipo vardec) env = checkTypeVardec vardec env
checkTypeStatement node@(Abs.ConditionalStatement pos condition) env = checkTypeCondition condition env
checkTypeStatement node@(Abs.WhileDoStatement pos whileState) env = checkTypeWhile whileState env
checkTypeStatement node@(Abs.DoWhileStatement pos doState) env = checkTypeDo doState env
checkTypeStatement node@(Abs.ForStatement pos forState) env = checkTypeForState forState env
checkTypeStatement node@(Abs.ProcedureStatement pos id param states) env = checkErrors (checkFuncOverride id env) (checkTypeExecuteParameter param env)
checkTypeStatement node@(Abs.FunctionStatement pos id param tipo states) env = checkErrors (checkFuncOverride id env) (checkTypeExecuteParameter param env)

checkTypeCondition :: Abs.CONDITIONALSTATE Posn -> Env -> TCheckResult
checkTypeCondition node@(Abs.ConditionalStatementSimpleThen pos exp state elseState) env = let expTCheck = checkTypeExpression exp env in 
                                                                                            case expTCheck of 
                                                                                               TResult _ _ _ -> if (checkCompatibility (TResult env (B_type Type_Boolean) pos) expTCheck) then TResult env (B_type Type_Void) pos else TError ["Conditional expression for if-then-else is not boolean! Position: "++ show pos]
                                                                                               TError e -> expTCheck
checkTypeCondition node@(Abs.ConditionalStatementSimpleWThen pos exp b elseState) env = let expTCheck = checkTypeExpression exp env in
                                                                                        case expTCheck of 
                                                                                            TResult _ _ _ -> if (checkCompatibility (TResult env (B_type Type_Boolean) pos) expTCheck) then TResult env (B_type Type_Void) pos else TError ["Conditional expression for if-then-else is not boolean! Position: "++ show pos]
                                                                                            TError e -> expTCheck
checkTypeCondition node@(Abs.ConditionalStatementCtrlThen pos ctrlState state elseState) env = checkTypeCtrlState ctrlState env
checkTypeCondition node@(Abs.ConditionalStatementCtrlWThen pos ctrlState b elseState) env = checkTypeCtrlState ctrlState env

checkTypeElseState :: Abs.ELSESTATEMENT Posn -> Env -> TCheckResult
checkTypeElseState node@(Abs.ElseState pos state) env = TResult env (B_type Type_Void) pos
checkTypeElseState node@(Abs.ElseStateEmpty pos) env = TResult env (B_type Type_Void) pos

checkTypeCtrlState :: Abs.CTRLDECSTATEMENT Posn -> Env -> TCheckResult
checkTypeCtrlState node@(Abs.CtrlDecStateConst pos id typepart exp) env = TResult env (B_type Type_Void) pos 
checkTypeCtrlState node@(Abs.CtrlDecStateVar pos id typepart exp) env = TResult env (B_type Type_Void) pos

checkTypeWhile :: Abs.WHILESTATEMENT Posn -> Env -> TCheckResult
checkTypeWhile node@(Abs.WhileStateSimpleDo pos exp state) env = let expTCheck = checkTypeExpression exp env in 
                                                                    case expTCheck of
                                                                        TResult _ _ _ -> if (checkCompatibility (TResult env (B_type Type_Boolean) pos) expTCheck) then TResult env (B_type Type_Void) pos else TError ["Guard expression for while loop is not boolean! Position: "++ show pos]
                                                                        TError e -> expTCheck
checkTypeWhile node@(Abs.WhileStateSimpleWDo pos exp b) env = let expTCheck = checkTypeExpression exp env in 
                                                                    case expTCheck of 
                                                                        TResult _ _ _ -> if (checkCompatibility (TResult env (B_type Type_Boolean) pos) expTCheck) then TResult env (B_type Type_Void) pos else TError ["Guard expression for while loop is not boolean! Position: "++ show pos]
                                                                        TError e -> expTCheck 

checkTypeWhile node@(Abs.WhileStateCtrlDo pos ctrl state) env = checkTypeCtrlState ctrl env
checkTypeWhile node@(Abs.WhileStateCtrlWDo pos ctrl b) env = checkTypeCtrlState ctrl env

checkTypeDo :: Abs.DOSTATEMENT Posn -> Env -> TCheckResult
checkTypeDo node@(Abs.DoWhileState pos state exp) env = let expTCheck = checkTypeExpression exp env in 
                                                            case expTCheck of
                                                                TResult _ _ _ -> if (checkCompatibility (TResult env (B_type Type_Boolean) pos) expTCheck) then TResult env (B_type Type_Void) pos else TError ["Guard expression for do-while loop is not boolean! Position: "++ show pos]
                                                                TError e -> expTCheck

checkTypeForState :: Abs.FORSTATEMENT Posn -> Env -> TCheckResult
checkTypeForState node@(Abs.ForStateIndexDo pos index rangexp state) env = let rangeTCheck = checkRangeExpType rangexp env in
                                                                            let indexTCheck = checkTypeIndexVarDec index env in
                                                                                case rangeTCheck of
                                                                                    TResult _ _ _ -> case indexTCheck of
                                                                                                    TResult _ _ _ -> if(checkCompatibility rangeTCheck indexTCheck ) then TResult env (B_type Type_Void) pos else TError ["Index-var type and range-expression have Incompatible types! Position "++ show pos]
                                                                                                    _ -> indexTCheck
                                                                                    _ -> case indexTCheck of
                                                                                        TResult _ _ _ -> rangeTCheck
                                                                                        _ -> mergeErrors rangeTCheck indexTCheck
checkTypeForState node@(Abs.ForStateIndexWDo pos index rangexp b) env = let rangeTCheck = checkRangeExpType rangexp env in
                                                                            let indexTCheck = checkTypeIndexVarDec index env in
                                                                                case rangeTCheck of
                                                                                    TResult _ _ _ -> case indexTCheck of
                                                                                                    TResult _ _ _ -> if(checkCompatibility rangeTCheck indexTCheck ) then TResult env (B_type Type_Void) pos else TError ["Index-var type and range-expression have Incompatible types! Position "++ show pos]
                                                                                                    _ -> indexTCheck
                                                                                    _ -> case indexTCheck of
                                                                                        TResult _ _ _ -> rangeTCheck
                                                                                        _ -> mergeErrors rangeTCheck indexTCheck
checkTypeForState node@(Abs.ForStateExprDo pos rangexp state) env = let rangeTCheck = checkRangeExpType rangexp env in 
                                                                        case rangeTCheck of
                                                                            TResult _ _ _ -> TResult env (B_type Type_Void) pos
                                                                            _ -> rangeTCheck
checkTypeForState node@(Abs.ForStateExprWDo pos rangexp b) env = let rangeTCheck = checkRangeExpType rangexp env in 
                                                                        case rangeTCheck of
                                                                            TResult _ _ _ -> TResult env (B_type Type_Void) pos
                                                                            _ -> rangeTCheck
checkTypeIndexVarDec :: Abs.INDEXVARDEC Posn -> Env -> TCheckResult
checkTypeIndexVarDec node@(Abs.IndexVarDeclaration pos id) env =  checkTypeIdentVar id env

checkTypeType :: Abs.VARIABLETYPE Posn -> Env -> TCheckResult
checkTypeType node@(Abs.VariableTypeParam pos) env = TResult env (B_type Type_Void) pos
checkTypeType node@(Abs.VariableTypeConst pos) env = TResult env (B_type Type_Void) pos
checkTypeType node@(Abs.VariableTypeVar pos) env = TResult env (B_type Type_Void) pos
checkTypeType node@(Abs.VariableTypeRef pos) env = TResult env (B_type Type_Void) pos
checkTypeType node@(Abs.VariableTypeConstRef pos) env = TResult env (B_type Type_Void) pos

checkTypeB :: Abs.B Posn -> Env -> TCheckResult
checkTypeB node@(Abs.BlockStatement pos statements) env = case statements of
                                                    (Abs.EmptyStatement pos) -> checkListStatement (Abs.EmptyStatement pos) env
                                                    (Abs.ListStatements pos stat stats) -> TResult env (B_type Type_Void) pos

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

checkTypeReturnState :: Abs.RETURNSTATEMENT Posn -> Env -> TCheckResult --TODO Pointers return --
checkTypeReturnState node@(Abs.ReturnState pos retExp) env = let retExpTCheck = checkTypeExpression retExp env in
                                                                case retExpTCheck of
                                                                    TResult env (Array t dim) pos -> case Data.Map.lookup ("return"++"_array"++(show t)) env of
                                                                                            Just result -> retExpTCheck
                                                                                            Nothing -> TError ["Unexpected return statement at " ++ (show pos)]
                                                                    TResult env (Pointer t depth) pos -> case Data.Map.lookup ("return"++"_"++(show t)) env of
                                                                                            Just result -> if depth == checkDef_ retExp then retExpTCheck else TError ["Unexpected return statement at " ++ (show pos)]
                                                                                            Nothing -> TError ["Unexpected return statement at " ++ (show pos)]
                                                                    TResult env t pos -> case Data.Map.lookup ("return"++"_"++ show t) env of
                                                                                            Just result -> retExpTCheck
                                                                                            Nothing -> TError ["Unexpected return statement at " ++ (show pos)]
                                                                    _ -> TError ["Unexpected return statement at " ++ (show pos)]
checkTypeReturnState node@(Abs.ReturnStateEmpty pos ) env = case Data.Map.lookup "return_void" env of
    Just result -> TResult env (B_type Type_Void) pos
    Nothing -> TError ["Unexpected return statement at " ++ (show pos)]

checkTypeExpressionStatement :: Abs.EXPRESSIONSTATEMENT Posn -> Env -> TCheckResult
checkTypeExpressionStatement node@(Abs.VariableExpression pos id) env = checkTypeIdentVar id env
checkTypeExpressionStatement node@(Abs.CallExpression pos callexpr) env = checkTypeCallExpression callexpr env

checkTypeExpressions :: Abs.EXPRESSIONS Posn -> Env -> TCheckResult
checkTypeExpressions node@(Abs.Expressions pos exp exps) env = let expsTCheck = checkTypeExpression exp env in
                                                                let expssTCheck = checkTypeExpressions exps env in
                                                                    case expsTCheck of
                                                                        TResult _ _ _ -> case expssTCheck of
                                                                                        TResult _ _ _ -> TResult env (B_type Type_Void) pos
                                                                                        _ -> mergeErrors expsTCheck expssTCheck
                                                                        _ -> mergeErrors expsTCheck expssTCheck
checkTypeExpressions node@(Abs.Expression pos exp) env = let expsTCheck = checkTypeExpression exp env in
                                                                case expsTCheck of
                                                                    TResult _ _ _ -> TResult env (B_type Type_Void) pos
                                                                    _ -> expsTCheck
checkTypeExpressions node@(Abs.ExpressionEmpty pos) env = TResult env (B_type Type_Void) pos

checkTypeExpression :: Abs.EXPRESSION Posn -> Env -> TCheckResult
checkTypeExpression node@(Abs.ExpressionInteger pos value) env = checkTypeInteger value env
checkTypeExpression node@(Abs.ExpressionBoolean pos value) env = checkTypeBoolean value env
checkTypeExpression node@(Abs.ExpressionChar pos value) env = checkTypeChar value env
checkTypeExpression node@(Abs.ExpressionString pos value) env = checkTypeString value env
checkTypeExpression node@(Abs.ExpressionReal pos value) env = checkTypeReal value env
checkTypeExpression node@(Abs.ExpressionBracket pos exp) env = checkTypeExpression exp env
checkTypeExpression node@(Abs.ExpressionCast pos def tipo) env = let tipoTCheck = checkPrimitiveType tipo env in
                                                                    let defTCheck = checkTypeDefault 0 def env in
                                                                        let realdefTCheck = getRealTypeDef defTCheck def in
                                                                        case realdefTCheck of
                                                                            TResult _ _ _ -> case tipoTCheck of
                                                                                TResult _ _ _ -> if(checkCompatibility realdefTCheck tipoTCheck) then tipoTCheck else TError ["Incompatibility type for casting at "++ show pos]
                                                                                _ -> if(checkCompatibility realdefTCheck tipoTCheck) then checkErrors realdefTCheck tipoTCheck else mergeErrors (TError ["Incompatibility type for casting at "++ show pos]) tipoTCheck
                                                                            _ -> case tipoTCheck of
                                                                                TResult _ _ _ -> if(checkCompatibility realdefTCheck tipoTCheck) then checkErrors realdefTCheck tipoTCheck else mergeErrors (TError ["Incompatibility type for casting at "++ show pos]) realdefTCheck
                                                                                _ -> if(checkCompatibility realdefTCheck tipoTCheck) then checkErrors realdefTCheck tipoTCheck else mergeErrors (TError ["Incompatibility type for casting at "++ show pos]) (checkErrors realdefTCheck tipoTCheck)
checkTypeExpression node@(Abs.ExpressionUnary pos unary def) env = case unary of
                                                                    Abs.UnaryOperationPointer pos -> let numberDef= 1+checkDef__ def in
                                                                                                    (case def of
                                                                                                    Abs.ExpressionUnaryD _ _ _ -> checkTypeDefault 2 def env
                                                                                                    Abs.ExpressionIdentD pos id index -> case index of 
                                                                                                                                        Abs.ArrayIndexElementEmpty pos -> let pointer = checkTypeIdentVar id env in case pointer of
                                                                                                                                                                                                                    res@(TResult env (Pointer t depth) pos) -> if depth-numberDef==0 then TResult env t pos else TResult env (Pointer t (depth-numberDef)) pos
                                                                                                                                                                                                                    _ -> mergeErrors (TError ["Pointer expected at Position: " ++ show pos]) pointer
                                                                                                                                        Abs.ArrayIndexElement pos t -> let pointer = checkTypeIdentVar id env in case pointer of
                                                                                                                                                                                                                    res@(TResult env (Array t dim) pos) -> if isTherePointer t then computeDeferencing (TResult env t pos) numberDef else mergeErrors (TError ["Pointer expected at Position: " ++ show pos]) pointer
                                                                                                                                                                                                                    res@(TResult env (Pointer t depth) pos) ->  if depth-numberDef==0 then indexing (TResult env t pos) index else TResult env (Pointer t (depth-numberDef)) pos
                                                                                                                                                                                                                    _ -> mergeErrors (TError ["Pointer expected at Position: " ++ show pos]) pointer
                                                                                                    _ -> TError ["Pointer expected at Position: " ++ show pos])
                                                                    _ -> let unaryTCheck = checkTypeUnaryOp unary env in
                                                                            let defTCheck = checkTypeDefault 0 def env in
                                                                                if(checkCompatibility defTCheck unaryTCheck) then checkErrors  unaryTCheck defTCheck else mergeErrors (TError ["Incompatibility type for unary operator at "++ show pos]) defTCheck
checkTypeExpression node@(Abs.ExpressionBinary pos def binary exp) env = let expCheck = checkTypeExpression exp env in
                                                                            let realexpTCheck = getRealTypeExp expCheck exp in -- TODO forse remove
                                                                            (let defCheck = checkTypeDefault 0 def env in 
                                                                                let realdefTCheck = getRealTypeDef defCheck def in
                                                                                (let binaryTCheck = checkTypeBinaryOp binary env in if (checkCompatibility realdefTCheck realexpTCheck || checkCompatibility realexpTCheck realdefTCheck)
                                                                                    then let ty = returnSuperType realexpTCheck realdefTCheck in case binaryTCheck of
                                                                                        TResult _ (B_type Type_Real) _ -> if (checkCompatibility ty binaryTCheck) then checkErrors realexpTCheck (checkErrors realdefTCheck ty) else  mergeErrors (mergeErrors (TError ["Operator requires operands to be of type real but " ++ show (getType realdefTCheck) ++ " and " ++ show (getType realexpTCheck) ++ " are given! Position: "++ show pos]) realdefTCheck) realexpTCheck
                                                                                        TResult _ (B_type Type_Boolean) _ -> case binary of
                                                                                            (Abs.BinaryOperationOr pos) -> if (checkCompatibility ty binaryTCheck) then checkErrors realexpTCheck (checkErrors realdefTCheck binaryTCheck) else mergeErrors (mergeErrors (TError ["Operator OR cannot be applied to operands of types different from bool! Position: "++ show pos]) realdefTCheck) realexpTCheck
                                                                                            (Abs.BinaryOperationAnd pos) -> if (checkCompatibility ty binaryTCheck) then checkErrors realexpTCheck (checkErrors realdefTCheck binaryTCheck) else mergeErrors (mergeErrors (TError ["Operator AND cannot be applied to operands of types different from bool! Position: "++ show pos]) realdefTCheck) realexpTCheck
                                                                                            (Abs.BinaryOperationEq pos) -> checkErrors realexpTCheck (checkErrors realdefTCheck binaryTCheck)
                                                                                            (Abs.BinaryOperationNotEq pos) -> checkErrors realexpTCheck (checkErrors realdefTCheck binaryTCheck)
                                                                                            _ -> if (checkCompatibility ty (TResult env (B_type Type_Real) pos)) || (checkCompatibility ty (TResult env (B_type Type_String) pos)) || (checkCompatibility ty (TResult env (B_type Type_Char) pos)) 
                                                                                                then checkErrors realexpTCheck (checkErrors realdefTCheck binaryTCheck)
                                                                                                else mergeErrors (mergeErrors (TError ["Operator cannot be applied to operands of type " ++ show (getType ty) ++"! Position: "++ show pos]) realdefTCheck) realexpTCheck
                                                                                    else mergeErrors (mergeErrors (TError ["Operands of types " ++ show (getType realdefTCheck) ++ " and " ++ show (getType realexpTCheck)++" are incompatible! Position:" ++ show pos]) realdefTCheck) realexpTCheck
                                                                                    ))
checkTypeExpression node@(Abs.ExpressionIdent pos ident@(Abs.Ident id posI) index) env =  case Data.Map.lookup id env of
                                                                                            Just [Variable (Array t dim) pos mode override] -> case index of
                                                                                                                                                Abs.ArrayIndexElementEmpty posIn -> TResult env (Array t dim) pos
                                                                                                                                                _ ->if dim == (countIndex index) then TResult env t pos else TError ["Array indexing incorrect! number of indexed dimensions not matching the dim. of the array! "++ show pos] 
                                                                                            Just ((Variable (Array t dim) pos mode override):xs) -> case index of
                                                                                                                                                    Abs.ArrayIndexElementEmpty posIn -> TResult env (Array t dim) pos
                                                                                                                                                    _ ->if dim == (countIndex index) then TResult env t pos else TError ["Array indexing incorrect! number of indexed dimensions not matching the dim. of the array! "++ show pos] 
                                                                                            Just [Function _ _ _ _] -> (TError ["Variable " ++ id ++ " undeclared! Position: " ++ (show posI)])
                                                                                            Just ((Function _ _ _ _):xs) -> let v =findEntryOfType xs "var" in
                                                                                                                            case v of
                                                                                                                                [] -> (TError ["Variable " ++ id ++ " undeclared! Position: " ++ (show posI)])
                                                                                                                                ((Variable (Array t dim) pos mode override):ys) -> case index of
                                                                                                                                                                                    Abs.ArrayIndexElementEmpty posIn -> TResult env (Array t dim) pos
                                                                                                                                                                                    _ ->if dim == (countIndex index) then TResult env t pos else TError ["Array indexing incorrect! number of indexed dimensions not matching the dim. of the array! "++ show pos] 
                                                                                                                                ((Variable t pos mode override):ys) -> TResult env t pos
                                                                                            Just [Variable t pos mode override] -> TResult env t pos
                                                                                            Just ((Variable t pos mode override):xs) -> TResult env t pos
                                                                                            Nothing -> (TError ["Variable " ++ id ++ " undeclared! Position: " ++ (show posI)])
checkTypeExpression node@(Abs.ExpressionCall pos (Abs.Ident id posid) exps) env = case Data.Map.lookup id env of
                                                                Just [Function t posf param canOverride] -> checkTypeExpressionCall_ node env [Function t posf param canOverride]
                                                                Just [Variable _ _ _ _] -> mergeErrors (TError ["Function " ++ id ++ " undeclared! Position: " ++ (show posid)]) (checkTypeExpressions exps env)
                                                                Just (x:xs) -> case findEntryOfType (x:xs) "func" of
                                                                        [] -> mergeErrors (TError ["Function " ++ id ++ " undeclared! Position: " ++ (show posid)]) (checkTypeExpressions exps env)
                                                                        [Function t posf param canOverride] -> checkTypeExpressionCall_ node env [Function t posf param canOverride]
                                                                Nothing -> mergeErrors (TError ["Function " ++ id ++ " undeclared! Position: " ++ (show posid)]) (checkTypeExpressions exps env)                                 

getRealTypeExp :: TCheckResult -> Abs.EXPRESSION Posn -> TCheckResult
getRealTypeExp (TResult env (Pointer t depth) pos) exp = if depth==checkDef_ exp then getRealTypeExp (TResult env t pos) exp else TError ["depth different at "++ show pos] -- TODO forse non serv
getRealTypeExp (TResult env (Array t dim) pos) exp = if dim==checkDimIndex_ exp then getRealTypeExp (TResult env t pos) exp else TError ["dim different at "++ show pos] -- TODO forse non serv
getRealTypeExp t exp = t

getRealTypeDef :: TCheckResult -> Abs.DEFAULT Posn -> TCheckResult
getRealTypeDef (TResult env (Pointer t depth) pos) def = if depth==checkDef__ def then getRealTypeDef (TResult env t pos) def else TError ["depth different at "++ show pos] -- TODO forse non serv
getRealTypeDef (TResult env (Array t dim) pos) def = if dim==checkDimIndex__ def then getRealTypeDef (TResult env t pos) def else TError ["dim different at "++ show pos] -- TODO forse non serv
getRealTypeDef t exp = t

checkDimIndex_ ::Abs.EXPRESSION Posn -> Prelude.Integer
checkDimIndex_ (Abs.ExpressionIdent pos id index) = case index of
                                                      Abs.ArrayIndexElementEmpty posI -> 0
                                                      Abs.ArrayIndexElement posI ty -> case ty of
                                                                                        Abs.TypeOfIndexInt posv tyv idv -> 1 + checkDimIndex_ (Abs.ExpressionIdent pos id (Abs.ArrayIndexElement posI tyv))
                                                                                        Abs.TypeOfIndexIntSingle posv idv -> 1
                                                                                        Abs.TypeOfIndexVar posv tyv idv indexv-> 1 + checkDimIndex_ (Abs.ExpressionIdent pos id (Abs.ArrayIndexElement posI tyv))
                                                                                        Abs.TypeOfIndexVarSingle posv idv indexv-> 1
checkDimIndex_ (Abs.ExpressionBracket pos exp) = checkDimIndex_ exp
checkDimIndex_ (Abs.ExpressionUnary pos unary def ) = checkDimIndex__ def
checkDimIndex_ _ = 0

checkDimIndex__ ::Abs.DEFAULT Posn -> Prelude.Integer
checkDimIndex__ (Abs.ExpressionIdentD pos id index) = case index of
                                                      Abs.ArrayIndexElementEmpty posI -> 0
                                                      Abs.ArrayIndexElement posI ty -> case ty of
                                                                                        Abs.TypeOfIndexInt posv tyv idv -> 1 + checkDimIndex__ (Abs.ExpressionIdentD pos id (Abs.ArrayIndexElement posI tyv))
                                                                                        Abs.TypeOfIndexIntSingle posv idv -> 1
                                                                                        Abs.TypeOfIndexVar posv tyv idv indexv-> 1 + checkDimIndex__ (Abs.ExpressionIdentD pos id (Abs.ArrayIndexElement posI tyv))
                                                                                        Abs.TypeOfIndexVarSingle posv idv indexv-> 1
checkDimIndex__ (Abs.ExpressionBracketD pos exp) = checkDimIndex_ exp
checkDimIndex__ (Abs.ExpressionUnaryD pos unary def ) = checkDimIndex__ def
checkDimIndex__ _ = 0

-- sub-function of the previous one
checkTypeExpressionCall_ :: Abs.EXPRESSION Posn -> Env -> [EnvEntry] -> TCheckResult
checkTypeExpressionCall_ (Abs.ExpressionCall pos (Abs.Ident id posid) exps) env [Function t posf param canOverride] = case exps of
    (Abs.Expression pos exp) -> if Prelude.length (param) == 1 -- The call was with 1 param, does the definition requires only 1 param?
                                               then if (checkCompatibilityOfExpsList (Abs.Expressions pos exp (Abs.ExpressionEmpty pos)) param env) then TResult env t pos 
                                                    else TError ["Function " ++ id ++ "( ) requires a parameter of type " ++ show (Prelude.head (getTypeListFromFuncParams param)) ++ " but " ++  show (getType (checkTypeExpression exp env)) ++ " is given! Position:" ++ show pos]
                                               else TError ["Function " ++ id ++ "( ) called with too few arguments! Position: " ++ show pos]
    (Abs.ExpressionEmpty pos) -> if param == [] then TResult env t pos else TError ["Function " ++ id ++ " called without parameters! Position: " ++ show pos] -- The call was with no params, check if the definition requires no param too
    (Abs.Expressions pos exp expss) -> if Prelude.length (param) == 1 + (countNumberOfExps expss) -- The call has n params, does the definition requires n params?
                                                              then if (checkCompatibilityOfExpsList exps param env) then TResult env t pos 
                                                                   else TError ["Function " ++ id ++ "( ) called with parameters of the wrong type! Position: " ++ show pos]
                                                              else TError ["Function " ++ id ++ "( ) called with a different number of parameters than it's definition! Position: " ++ show pos]

countNumberOfExps :: Abs.EXPRESSIONS Posn -> Prelude.Int
countNumberOfExps (Abs.Expressions _ _ exps) = 1 + countNumberOfExps exps
countNumberOfExps (Abs.Expression _ _) = 1
countNumberOfExps (Abs.ExpressionEmpty _) = 1

checkCompatibilityOfExpsList :: Abs.EXPRESSIONS Posn -> [TypeChecker.Parameter] -> Env-> Prelude.Bool
checkCompatibilityOfExpsList  (Abs.Expressions pos exp exps) ((TypeChecker.Parameter ty _ _ _):zs) env = let expType = checkTypeExpression exp env in 
                                                                                                            if checkCompatibility expType (TResult env ty pos) 
                                                                                                                then True && (checkCompatibilityOfExpsList exps zs env) else False
checkCompatibilityOfExpsList  (Abs.Expression pos exp) ((TypeChecker.Parameter ty _ _ _):zs) env = let expType = checkTypeExpression exp env in 
                                                                                                        if checkCompatibility expType (TResult env ty pos) 
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

checkTypeDefault :: Prelude.Integer -> Abs.DEFAULT Posn -> Env -> TCheckResult
checkTypeDefault s node@(Abs.ExpressionIntegerD pos value) env = checkTypeInteger value env
checkTypeDefault s node@(Abs.ExpressionBooleanD pos value) env = checkTypeBoolean value env
checkTypeDefault s node@(Abs.ExpressionCharD pos value) env = checkTypeChar value env
checkTypeDefault s node@(Abs.ExpressionStringD pos value) env = checkTypeString value env
checkTypeDefault s node@(Abs.ExpressionRealD pos value) env = checkTypeReal value env
checkTypeDefault s node@(Abs.ExpressionBracketD pos exp) env = checkTypeExpression exp env
checkTypeDefault s node@(Abs.ExpressionIdentD pos ident@(Abs.Ident id posI) index) env = case Data.Map.lookup id env of
                                                                        Just [Variable (Array t dim) pos mode override] -> case index of
                                                                                                                            Abs.ArrayIndexElementEmpty posIn -> TResult env (Array t dim) pos
                                                                                                                            _ ->if dim == (countIndex index) then TResult env t pos else TError ["Array indexing incorrect! number of indexed dimensions not matching the dim. of the array! "++ show pos] 
                                                                        Just ((Variable (Array t dim) pos mode override):xs) -> case index of
                                                                                                                                Abs.ArrayIndexElementEmpty posIn -> TResult env (Array t dim) pos
                                                                                                                                _ ->if dim == (countIndex index) then TResult env t pos else TError ["Array indexing incorrect! number of indexed dimensions not matching the dim. of the array! "++ show pos] 
                                                                        Just [Function _ _ _ _] -> (TError ["Variable " ++ id ++ " undeclared! Position: " ++ (show posI)])
                                                                        Just ((Function _ _ _ _):xs) -> let v =findEntryOfType xs "var" in
                                                                                                        case v of
                                                                                                            [] -> (TError ["Variable " ++ id ++ " undeclared! Position: " ++ (show posI)])
                                                                                                            ((Variable (Array t dim) pos mode override):ys) -> case index of
                                                                                                                                                                Abs.ArrayIndexElementEmpty posIn -> TResult env (Array t dim) pos
                                                                                                                                                                _ ->if dim == (countIndex index) then TResult env t pos else TError ["Array indexing incorrect! number of indexed dimensions not matching the dim. of the array! "++ show pos] 
                                                                                                            ((Variable t pos mode override):ys) -> TResult env t pos
                                                                        Just [Variable t pos mode override] -> TResult env t pos
                                                                        Just ((Variable t pos mode override):xs) -> TResult env t pos
                                                                        Nothing -> (TError ["Variable " ++ id ++ " undeclared! Position: " ++ (show posI)])
checkTypeDefault s node@(Abs.ExpressionCastD pos def ty) env = let tipoTCheck = checkPrimitiveType ty env in
                                                                    let defTCheck = checkTypeDefault 1 def env in
                                                                        let realdefTCheck = getRealTypeDef defTCheck def in
                                                                        case realdefTCheck of
                                                                            TResult _ _ _ -> case tipoTCheck of
                                                                                TResult _ _ _ -> if(checkCompatibility realdefTCheck tipoTCheck) then tipoTCheck else TError ["Incompatibility type for casting at "++ show pos]
                                                                                _ -> if(checkCompatibility realdefTCheck tipoTCheck) then checkErrors realdefTCheck tipoTCheck else mergeErrors (TError ["Incompatibility type for casting at "++ show pos]) tipoTCheck
                                                                            _ -> case tipoTCheck of
                                                                                TResult _ _ _ -> if(checkCompatibility realdefTCheck tipoTCheck) then checkErrors realdefTCheck tipoTCheck else mergeErrors (TError ["Incompatibility type for casting at "++ show pos]) realdefTCheck
                                                                                _ -> if(checkCompatibility realdefTCheck tipoTCheck) then checkErrors realdefTCheck tipoTCheck else mergeErrors (TError ["Incompatibility type for casting at "++ show pos]) (checkErrors realdefTCheck tipoTCheck)
checkTypeDefault s node@(Abs.ExpressionCallD pos (Abs.Ident id posid) exps) env = case Data.Map.lookup id env of
                                                                                Just [Function t posf param canOverride] -> checkTypeExpressionCallD_ node env [Function t posf param canOverride]
                                                                                Just [Variable _ _ _ _] -> mergeErrors (TError ["Function " ++ id ++ " undeclared! Position: " ++ (show posid)]) (checkTypeExpressions exps env)
                                                                                Just (x:xs) -> case findEntryOfType (x:xs) "func" of
                                                                                        [] -> mergeErrors (TError ["Function " ++ id ++ " undeclared! Position: " ++ (show posid)]) (checkTypeExpressions exps env)
                                                                                        [Function t posf param canOverride] -> checkTypeExpressionCallD_ node env [Function t posf param canOverride]
                                                                                Nothing -> mergeErrors (TError ["Function " ++ id ++ " undeclared! Position: " ++ (show posid)]) (checkTypeExpressions exps env)
checkTypeDefault s node@(Abs.ExpressionUnaryD pos unary def) env = case unary of
                                                                    Abs.UnaryOperationPointer pos -> let numberDef= if s==2 then 2+checkDef__ def else 1+checkDef__ def in
                                                                                                    (case def of
                                                                                                    Abs.ExpressionUnaryD _ _ _ -> if s==0 then computeDeferencing (checkTypeDefault 1 def env) numberDef 
                                                                                                                                            else if s==2 then computeDeferencing (checkTypeDefault 1 def env) numberDef  else checkTypeDefault 1 def env
                                                                                                    Abs.ExpressionIdentD pos id index -> case index of 
                                                                                                                                        Abs.ArrayIndexElementEmpty pos -> let pointer = checkTypeIdentVar id env in case pointer of
                                                                                                                                                                                                                    res@(TResult env (Pointer t depth) pos) -> if depth-numberDef==0 then TResult env t pos else TResult env (Pointer t (depth-numberDef)) pos
                                                                                                                                                                                                                    _ -> mergeErrors (TError ["Pointer expected at position: "++ show pos]) pointer
                                                                                                                                        Abs.ArrayIndexElement pos t -> let pointer = checkTypeIdentVar id env in case pointer of
                                                                                                                                                                                                                    res@(TResult env (Array t dim) pos) -> if isTherePointer t then res else mergeErrors (TError ["Pointer expected at position: "++ show pos]) pointer
                                                                                                                                                                                                                    res@(TResult env (Pointer t depth) pos) -> if depth-numberDef==0 then TResult env t pos else TResult env (Pointer t (depth-numberDef)) pos
                                                                                                                                                                                                                    _ -> mergeErrors (TError ["Pointer expected at position: "++ show pos]) pointer
                                                                                                    _ -> TError ["Pointer expected at position: "++ show pos])
                                                                    _ -> let unaryTCheck = checkTypeUnaryOp unary env in
                                                                            let defTCheck = checkTypeDefault 1 def env in
                                                                                if(checkCompatibility defTCheck unaryTCheck) then checkErrors  unaryTCheck defTCheck else mergeErrors (TError ["Incompatibility type for unary operator at "++ show pos]) defTCheck

-- Given a deferenced var; return it's type if it has been deferenced the correct number of time
computeDeferencing :: TCheckResult -> Prelude.Integer -> TCheckResult
computeDeferencing (TResult env (Pointer t depth) pos) def = if depth-def==0 then TResult env t pos else TResult env (Pointer t (depth-def)) pos
computeDeferencing t def = t

checkTypeExpressionCallD_ :: Abs.DEFAULT Posn -> Env -> [EnvEntry] -> TCheckResult
checkTypeExpressionCallD_ (Abs.ExpressionCallD pos (Abs.Ident id posid) exps) env [Function t posf param canOverride] = case exps of
    (Abs.Expression pos exp) -> if Prelude.length (param) == 1 -- The call was with 1 param, does the definition requires only 1 param?
                                               then if (let expType = checkTypeExpression exp env -- Check if the type is compatibile with the one required in the definition
                                                        in checkCompatibility expType (TResult env (Prelude.head (getTypeListFromFuncParams param)) pos)) then TResult env t pos 
                                                    else TError ["Function " ++ id ++ "( ) requires a parameter of type " ++ show (Prelude.head (getTypeListFromFuncParams param)) ++ " but " ++  show (getType (checkTypeExpression exp env)) ++ " is given! Position:" ++ show pos]
                                               else TError ["Function " ++ id ++ "( ) called with too few arguments! Position: " ++ show pos]
    (Abs.ExpressionEmpty pos) -> if param == [] then TResult env t pos else TError ["Function " ++ id ++ " called without parameters! Position: " ++ show pos] -- The call was with no params, check if the definition requires no param too
    (Abs.Expressions pos exp expss) -> if Prelude.length (param) == 1 + (countNumberOfExps expss) -- The call has n params, does the definition requires n params?
                                                              then if (checkCompatibilityOfExpsList exps param env) then TResult env t pos 
                                                                   else TError ["Function " ++ id ++ "( ) called with parameters of the wrong type! Position: " ++ show pos]
                                                              else TError ["Function " ++ id ++ "( ) called with a different number of parameters than it's definition! Position: " ++ show pos]

checkTypeIdentVar :: Abs.Ident Posn -> Env -> TCheckResult
checkTypeIdentVar node@(Abs.Ident id pos) env = case Data.Map.lookup id env of
    Just [Variable t pos mode override] -> TResult env t pos
    Just (x:xs) -> case findEntryOfType (x:xs) "var" of
                    [] -> TError ["Variable " ++ id ++ " undeclared at position: " ++ (show pos)]
                    [y] -> TResult env (getTypeEnvEntry [y]) pos
    Nothing -> TError ["Variable " ++ id ++ " undeclared at position: " ++ (show pos)]

checkTypeIdentFunc :: Abs.Ident Posn -> Env -> TCheckResult
checkTypeIdentFunc node@(Abs.Ident id pos) env = case Data.Map.lookup id env of
    Just [Function t pos param canOverride] -> TResult env t pos
    Just (x:xs) -> case findEntryOfType (x:xs) "func" of
                    [] -> TError ["Function " ++ id ++ "( ) undeclared at position: " ++ (show pos)]
                    [y] -> TResult env (getTypeEnvEntry [y]) pos
    Nothing -> TError ["Function " ++ id ++ "( ) undeclared at position: " ++ (show pos)]

-- Given a list of envEntry, returns the first occurence of the given type (var or func env entry)
findEntryOfType :: [EnvEntry] -> Prelude.String -> [EnvEntry]
findEntryOfType (x:xs) str = case str of 
                                "var" -> case x of -- searching for var entry 
                                        Variable t pos mode override -> [x]
                                        _ -> findEntryOfType xs str
                                "func"-> case x of -- searching for func entry 
                                        Function t pos param canOverride -> [x]
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
checkTypeVariableDec node@(Abs.VariableDeclaration pos identlist typepart initpart) env = let identTCheck = checkIdentifierList identlist env in
                                                                                    (case initpart of
                                                                                        Abs.InitializzationPartEmpty _ -> checkErrors  identTCheck (checkTypeTypePart typepart env)
                                                                                        _ -> let typeCheck = checkTypeTypePart typepart env in
                                                                                                let initCheck = checkTypeInitializzationPart initpart env in
                                                                                                    case typeCheck of
                                                                                                        TResult env (Pointer t depth) pos -> case initCheck of
                                                                                                            TResult env (Pointer tI depthI) pos -> if (checkCompatibility (TResult env (Pointer tI ((depthI+1)-(checkDef initpart))) pos) (TResult env (Pointer t depth) pos)) then checkErrors initCheck (checkErrors identTCheck typeCheck) else mergeErrors initCheck (mergeErrors (TError ["Pointer initializzation incompatible type at "++ show (getPos initCheck)]) identTCheck)
                                                                                                            _ -> if (checkCompatibility initCheck (TResult env t pos) && depth==1) then checkErrors initCheck (checkErrors identTCheck typeCheck) else mergeErrors initCheck (mergeErrors (TError ["Pointer initializzation incompatible type at "++ show (getPos initCheck)]) identTCheck)
                                                                                                        TResult env (Array t dim) pos -> case initCheck of
                                                                                                            TResult env (Array ts dims) pos -> if checkCompatibility (TResult env ts pos) (TResult env t pos) then checkErrors initCheck (checkErrors identTCheck typeCheck) else mergeErrors initCheck (mergeErrors (TError ["Cannot initialize array of type " ++ show (getType typeCheck) ++ " with values of type "++ show (getType initCheck) ++ "! Position:" ++ show (getPos initCheck)]) identTCheck) -- TODO show better the primitive type!
                                                                                                            _ -> mergeErrors initCheck (mergeErrors (TError ["Array initializzation incompatible type at "++ show (getPos initCheck)]) identTCheck)
                                                                                                        _ -> if (checkCompatibility initCheck typeCheck) then checkErrors initCheck (checkErrors identTCheck typeCheck) else mergeErrors identTCheck (mergeErrors initCheck (TError ["Cannot initialize variable of type " ++ show (getType typeCheck) ++ " with values of type "++ show (getType initCheck) ++ "! Position:" ++ show (getPos initCheck)])))

checkErrors :: TCheckResult -> TCheckResult -> TCheckResult
checkErrors (TResult env ty pos) (TResult envs tys poss) = TResult envs tys poss
checkErrors (TResult env ty pos) (TError e) = TError e
checkErrors (TError e) (TResult env ty pos) = TError e
checkErrors (TError e) (TError er) = mergeErrors (TError e) (TError er)

getPos :: TCheckResult -> Posn 
getPos (TResult env t pos) = pos
getPos (TError e) = Pn 0 0 0

checkDef :: Abs.INITPART Posn -> Prelude.Integer
checkDef (Abs.InitializzationPart pos exp) = checkDef_ exp
checkDef _ = 0

checkDef_ :: Abs.EXPRESSION Posn -> Prelude.Integer
checkDef_ (Abs.ExpressionUnary pos unary def) = case unary of
                                                Abs.UnaryOperationPointer pos -> 1 + checkDef__ def
                                                _ -> 0 + checkDef__ def
checkDef_ (Abs.ExpressionBracket pos exp) = checkDef_ exp 
checkDef_ _ = 0

checkDef__ :: Abs.DEFAULT Posn -> Prelude.Integer
checkDef__ (Abs.ExpressionUnaryD pos unary def) = case unary of
                                                Abs.UnaryOperationPointer pos -> 1 + checkDef__ def
                                                _ -> 0 + checkDef__ def
checkDef__ (Abs.ExpressionBracketD pos exp) = checkDef_ exp 
checkDef__ _ = 0

checkIdentifierList :: Abs.IDENTLIST Posn -> Env -> TCheckResult
checkIdentifierList node@(Abs.IdentifierList pos ident@(Abs.Ident id posI) identlist) env = let identTCheck = checkIdentifierList (Abs.IdentifierSingle pos ident) env in
                                                                                                let identListTCheck = checkIdentifierList identlist env in
                                                                                                    case identTCheck of
                                                                                                        TResult _ _ _ -> case identListTCheck of
                                                                                                                        TResult _ _ _ -> TResult env (B_type Type_Void) pos
                                                                                                                        _ -> mergeErrors identTCheck identListTCheck
                                                                                                        _ -> case identListTCheck of
                                                                                                            TResult _ _ _ -> mergeErrors identTCheck identListTCheck
                                                                                                            _ -> mergeErrors identTCheck identListTCheck

checkIdentifierList node@(Abs.IdentifierSingle pos ident@(Abs.Ident id posI)) env = case Data.Map.lookup id env of
                                                                                    Just [Variable ty posv mode override] -> if override then TResult env (B_type Type_Void) pos else TError ["Variable "++ id ++" is already defined at "++ show posv]
                                                                                    Just (Variable ty posv mode override:xs) -> if override then TResult env (B_type Type_Void) pos else TError ["Variable "++ id ++" is already defined at "++ show posv]
                                                                                    Just [Function ty posv param canOverride] -> TResult env (B_type Type_Void) pos
                                                                                    Just (Function ty posv param canOverride:xs) -> case findEntryOfType xs "var" of
                                                                                                                                    [] -> TResult env (B_type Type_Void) pos
                                                                                                                                    (Variable ty posv mode override):xs -> if override then TResult env (B_type Type_Void) pos else TError ["Variable "++ id ++" is already defined at "++ show posv]
                                                                                    Nothing -> TResult env (B_type Type_Void) pos

checkTypeTypePart :: Abs.TYPEPART Posn -> Env -> TCheckResult
checkTypeTypePart node@(Abs.TypePart pos typexpr) env = checkTypeTypeExpression typexpr env

checkTypeInitializzationPart ::  Abs.INITPART Posn -> Env -> TCheckResult
checkTypeInitializzationPart node@(Abs.InitializzationPart pos expr) env = checkTypeExpression expr env
checkTypeInitializzationPart node@(Abs.InitializzationPartArray pos arrayinit) env = checkTypeArrayInit arrayinit env
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
checkPrimitiveType node@(Abs.TypeArray pos primitivetype) env =  TResult env (Array (getArrayPrimitiveType primitivetype) (getArrayDimFunc primitivetype)) pos

checkTypeTypeExpression :: Abs.TYPEEXPRESSION Posn -> Env -> TCheckResult
checkTypeTypeExpression node@(Abs.TypeExpression pos primitiveType) env = let checkArray = checkPrimitiveType primitiveType env in case checkArray of
                                                                                                                                    TResult env (Array _ _) pos -> TError ["Array declaration without size specification is not allowed! Position: "++ show pos]
                                                                                                                                    _ -> checkArray
checkTypeTypeExpression node@(Abs.TypeExpressionArraySimple pos rangeexp typeexpression) env = let rangeExpTCheck = checkRangeExpType rangeexp env in
                                                                                                case rangeExpTCheck of
                                                                                                    TResult env (B_type Type_Integer) pos -> TResult env (Array (getTypeFromTypeExp typeexpression) (getArrayLength rangeexp)) pos
                                                                                                    _ -> mergeErrors (TError ["Array declaration with wrong range is not allowed! Position: "++ show pos]) rangeExpTCheck
checkTypeTypeExpression node@(Abs.TypeExpressionArray pos rangeexp typeexpression) env =  let rangeExpTCheck = checkRangeExpType rangeexp env in
                                                                                                case rangeExpTCheck of
                                                                                                    TResult env (B_type Type_Integer) pos -> TResult env (Array (getTypeFromTypeExp typeexpression) (getArrayLength rangeexp)) pos
                                                                                                    _ -> mergeErrors (TError ["Array declaration with wrong range is not allowed! Position: "++ show pos]) rangeExpTCheck
checkTypeTypeExpression node@(Abs.TypeExpressionPointer pos primitivetype pointer) env = TResult env (getTypeExpr node) pos
checkTypeTypeExpression node@(Abs.TypeExpressionPointerOfArray pos typeexpression pointer) env = case typeexpression of
                                                                                                    Abs.TypeExpressionArray {} -> TError ["Type Expression not allowed here! Position: " ++ show pos]
                                                                                                    Abs.TypeExpressionArraySimple {} -> TError ["Type Expression not allowed here! Position: " ++ show pos]
                                                                                                    _ ->TResult env (getTypeExpr node) pos


checkListElementsOfArray :: Abs.LISTELEMENTARRAY Posn -> Env -> TCheckResult
checkListElementsOfArray node@(Abs.ListElementsOfArray pos expr elementlist) env = let exprTCheck = checkTypeExpression expr env in if (checkCompatibility exprTCheck (getRealType (checkListElementsOfArray elementlist env))) then TResult env (Array (getType exprTCheck) 0) pos else TError ["Types incompatibles in TODO Position: "++ show pos]
checkListElementsOfArray node@(Abs.ListElementOfArray pos expr) env = let exprTCheck = checkTypeExpression expr env in TResult env (Array (getType exprTCheck) 0) pos

getType :: TCheckResult -> Type
getType (TResult env t pos) = t
getType _ = B_type Type_Void

checkRangeExpType :: Abs.RANGEEXP Posn -> Env -> TCheckResult
checkRangeExpType node@(Abs.RangeExpression pos expr1 expr2 rangexp) env = if ((checkCompatibility (checkTypeExpression expr1 env) (checkTypeExpression expr2 env) || checkCompatibility (checkTypeExpression expr2 env) (checkTypeExpression expr1 env))) then 
                                                                                                                                                            if (checkOrder expr1 expr2 env) 
                                                                                                                                                                then if (checkCompatibility (returnSuperType (checkTypeExpression expr1 env) (checkTypeExpression expr2 env)) (checkRangeExpType rangexp env))
                                                                                                                                                                        then checkSuperTypeRangeExp(returnSuperType (checkTypeExpression expr1 env) (checkTypeExpression expr2 env))
                                                                                                                                                                        else mergeErrors (mergeErrors (mergeErrors (TError ["type of expressions of the range is incompatible"]) (checkTypeExpression expr1 env)) (checkTypeExpression expr2 env)) (checkRangeExpType rangexp env)
                                                                                                                                                                     else TError ["Wrong order of range expression elements! Position: "++ show pos]
                                                                                                                                                                else mergeErrors (mergeErrors (TError ["Incompatible type in range expression! Positon: " ++ show pos]) (checkTypeExpression expr1 env)) (checkTypeExpression expr2 env)
checkRangeExpType node@(Abs.RangeExpressionSingle pos expr1 expr2) env = if ((checkCompatibility (checkTypeExpression expr1 env) (checkTypeExpression expr2 env) || checkCompatibility (checkTypeExpression expr2 env) (checkTypeExpression expr1 env)))
                                                                                                                                then if (checkOrder expr1 expr2 env) 
                                                                                                                                    then checkSuperTypeRangeExp(returnSuperType (checkTypeExpression expr1 env) (checkTypeExpression expr2 env))
                                                                                                                                    else TError ["Wrong order of range expression elements! Position: "++ show pos]
                                                                                                                                else mergeErrors (mergeErrors (TError ["Incompatible type in range expression! Positon: " ++ show pos]) (checkTypeExpression expr1 env)) (checkTypeExpression expr2 env)

checkOrder :: Abs.EXPRESSION Posn -> Abs.EXPRESSION Posn -> Env -> Bool
checkOrder (Abs.ExpressionInteger pos (Abs.Integer val posI)) (Abs.ExpressionInteger poss (Abs.Integer vals posIs)) _ = val<=vals
checkOrder (Abs.ExpressionReal pos (Abs.Real val posR)) (Abs.ExpressionReal poss (Abs.Real vals posRs)) _ = val<=vals
checkOrder (Abs.ExpressionInteger pos (Abs.Integer val posI)) (Abs.ExpressionReal poss (Abs.Real vals posRs)) _ = (Prelude.fromInteger val)<=vals
checkOrder (Abs.ExpressionReal pos (Abs.Real val posR)) (Abs.ExpressionInteger poss (Abs.Integer vals posIs)) _ = val<=(Prelude.fromInteger vals)
checkOrder (Abs.ExpressionChar pos (Abs.Char val posC)) (Abs.ExpressionChar poss (Abs.Char vals posCs)) _ = val<=vals
checkOrder (Abs.ExpressionString pos (Abs.String val posS)) (Abs.ExpressionString poss (Abs.String vals posSs)) _ = val<=vals
checkOrder (Abs.ExpressionIdent pos id index) exp env = let idTCheck = (checkTypeExpression (Abs.ExpressionIdent pos id index) env) in
                                                            let expTCheck = (checkTypeExpression exp env) in
                                                                case idTCheck of
                                                                    TResult env (Pointer t depth) pos -> False
                                                                    TResult env (Array t dim) pos -> False
                                                                    _ -> if (checkCompatibility idTCheck expTCheck) then True else False
checkOrder exp (Abs.ExpressionIdent pos id index) env = let idTCheck = (checkTypeExpression (Abs.ExpressionIdent pos id index) env) in
                                                            let expTCheck = (checkTypeExpression exp env) in
                                                                case idTCheck of
                                                                    TResult env (Pointer t depth) pos -> False
                                                                    TResult env (Array t dim) pos -> False
                                                                    _ -> if (checkCompatibility idTCheck expTCheck) then True else False
checkOrder (Abs.ExpressionUnary pos unary def) (Abs.ExpressionUnary poss unarys defs) env = let exp1 = checkTypeExpression (Abs.ExpressionUnary pos unary def) env in
                                                                                                let exp2 = checkTypeExpression (Abs.ExpressionUnary pos unary def) env in
                                                                                                    case exp1 of
                                                                                                        TResult env (Pointer t depth) pos -> False
                                                                                                        TResult env (Array t dim) pos -> False
                                                                                                        TResult env t pos -> case exp2 of
                                                                                                                            TResult env (Pointer t depth) pos -> False
                                                                                                                            TResult env (Array t dim) pos -> False
                                                                                                                            TResult env t pos -> if checkCompatibility exp1 exp2 then True else False
                                                                                                                            _ -> False
                                                                                                        _ -> False
checkOrder (Abs.ExpressionUnary pos unary def) exp env = let exp1 = checkTypeExpression (Abs.ExpressionUnary pos unary def) env in
                                                                                                let exp2 = checkTypeExpression exp env in
                                                                                                    case exp1 of
                                                                                                        TResult env (Pointer t depth) pos -> False
                                                                                                        TResult env (Array t dim) pos -> False
                                                                                                        TResult env t pos -> case exp2 of
                                                                                                                            TResult env (Pointer t depth) pos -> False
                                                                                                                            TResult env (Array t dim) pos -> False
                                                                                                                            TResult env t pos -> if checkCompatibility exp1 exp2 then True else False
                                                                                                                            _ -> False
                                                                                                        _ -> False
checkOrder exp (Abs.ExpressionUnary pos unary def) env = let exp1 = checkTypeExpression (Abs.ExpressionUnary pos unary def) env in
                                                                                                let exp2 = checkTypeExpression exp env in
                                                                                                    case exp1 of
                                                                                                        TResult env (Pointer t depth) pos -> False
                                                                                                        TResult env (Array t dim) pos -> False
                                                                                                        TResult env t pos -> case exp2 of
                                                                                                                            TResult env (Pointer t depth) pos -> False
                                                                                                                            TResult env (Array t dim) pos -> False
                                                                                                                            TResult env t pos -> if checkCompatibility exp1 exp2 then True else False
                                                                                                                            _ -> False
                                                                                                        _ -> False 
checkOrder exp1 exp2 env = if (checkCompatibility (checkTypeExpression exp1 env) (checkTypeExpression exp2 env)) then True else False

-- Check the superType in a given RangeExp
checkSuperTypeRangeExp :: TCheckResult -> TCheckResult
checkSuperTypeRangeExp (TResult env tipo pos) = case tipo of
                                                B_type Type_Integer -> (TResult env tipo pos)
                                                B_type Type_Real -> (TResult env tipo pos)                                          
                                                B_type Type_Char -> (TResult env tipo pos)                                            
                                                B_type Type_String -> (TResult env tipo pos)
                                                _ -> TError ["Incompatible types for range expression at position: "++ show pos]

checkTypeTypeIndex :: Abs.TYPEINDEX Posn -> Env -> TCheckResult
checkTypeTypeIndex node@(Abs.TypeOfIndexInt pos typeindex integer) env = if checkCompatibility (TResult env (B_type Type_Integer) pos) (checkTypeTypeIndex typeindex env)
                                                                         then TResult env (B_type Type_Integer) pos
                                                                         else TError ["Index types of array not all the same - int"]
checkTypeTypeIndex node@(Abs.TypeOfIndexIntSingle pos integer) env = TResult env (B_type Type_Integer) pos
checkTypeTypeIndex node@(Abs.TypeOfIndexVar pos typeindex id@(Abs.Ident idi posi) index) env = case index of
                                                                                    Abs.ArrayIndexElementEmpty pos -> if checkCompatibility (checkTypeIdentVar id env) (checkTypeTypeIndex typeindex env) && checkCompatibility (checkTypeIdentVar id env) (TResult env (B_type Type_Integer) pos)
                                                                                                                        then TResult env (B_type Type_Integer) pos
                                                                                                                        else TError ["Index types of array not all the same"]
                                                                                    Abs.ArrayIndexElement pos tyindex -> case Data.Map.lookup idi env of
                                                                                                                        Just ident -> let idTCheck = getTypeEnvEntry ident in
                                                                                                                                    case idTCheck of
                                                                                                                                        Array t dim -> if t == B_type Type_Integer && dim==(countIndex_ tyindex) && checkCompatibility (TResult env t pos) (checkTypeTypeIndex typeindex env) then TResult env t pos else TError ["incompatible type for index at "++ show pos]
                                                                                                                                        _ -> if idTCheck == B_type Type_Integer && checkCompatibility (TResult env idTCheck pos) (checkTypeTypeIndex typeindex env) then TResult env idTCheck pos else TError ["incompatible type for index at "++ show pos]
                                                                                                                        Nothing -> TError [" ?? var not def. Unexpected ident at " ++ (show pos)]
checkTypeTypeIndex node@(Abs.TypeOfIndexVarSingle _ (Abs.Ident id pos) index) env = case index of
                                                                                    Abs.ArrayIndexElementEmpty pos -> case Data.Map.lookup id env of
                                                                                                                        Just ident -> if getTypeEnvEntry ident == B_type Type_Integer then TResult env (getTypeEnvEntry ident) pos else TError ["incompatible type for index at "++ show pos]
                                                                                                                        Nothing -> TError [" ?? var not def. Unexpected ident at " ++ (show pos)]
                                                                                    Abs.ArrayIndexElement pos tyindex -> case Data.Map.lookup id env of
                                                                                                                        Just ident -> let idTCheck = getTypeEnvEntry ident in
                                                                                                                                    case idTCheck of
                                                                                                                                        Array t dim -> if t == B_type Type_Integer && dim==(countIndex_ tyindex) then TResult env t pos else TError ["incompatible type for index at "++ show pos]
                                                                                                                                        _ -> if idTCheck == B_type Type_Integer then TResult env idTCheck pos else TError ["incompatible type for index at "++ show pos]
                                                                                                                        Nothing -> TError [" ?? var not def. Unexpected ident at " ++ (show pos)]
checkTypeTypeIndex node@(Abs.TypeOfIndexPointer pos typeindex unaryop def) env = let defTCheck = checkTypeDefault 0 def env in
                                                                                case defTCheck of
                                                                                    TResult env (Pointer t depth) pos -> if t==B_type Type_Integer && depth==(checkUnary unaryop)+(checkDef__ def) && checkCompatibility (TResult env t pos) (checkTypeTypeIndex typeindex env) then TResult env t pos else TError ["Type is not correct"]
                                                                                    _ -> TError ["Type is not correct"]
checkTypeTypeIndex node@(Abs.TypeOfIndexPointerSingle pos unaryop def) env = let defTCheck = checkTypeDefault 0 def env in
                                                                                case defTCheck of
                                                                                    TResult env (Pointer t depth) pos -> if t==B_type Type_Integer && depth==(checkUnary unaryop)+(checkDef__ def) then TResult env t pos else TError ["Type is not correct"]
                                                                                    _ -> TError ["Type is not correct"]
checkTypeTypeIndex node@(Abs.TypeOfIndexBinary pos typeindex def binaryop exp) env = let expTCheck = checkTypeExpression (Abs.ExpressionBinary pos def binaryop exp) env in
                                                                                    case expTCheck of
                                                                                        TResult env (B_type Type_Integer) pos -> if checkCompatibility expTCheck (checkTypeTypeIndex typeindex env) then expTCheck else TError ["Type is not correct"]
                                                                                        _ -> TError ["Type is not correct"]
checkTypeTypeIndex node@(Abs.TypeOfIndexBinarySingle pos def binaryop exp ) env = let expTCheck = checkTypeExpression (Abs.ExpressionBinary pos def binaryop exp) env in
                                                                                    case expTCheck of
                                                                                        TResult env (B_type Type_Integer) pos -> expTCheck
                                                                                        _ -> TError ["Type is not correct"]
checkTypeTypeIndex node@(Abs.TypeOfIndexExpressionCall pos typeindex (Abs.Ident id posi) exps ) env = case checkTypeExpression (Abs.ExpressionCall pos (Abs.Ident id posi) exps) env of
                                                                                                TResult _ _ _ ->
                                                                                                                    case Data.Map.lookup id env of
                                                                                                                        Just [Variable _ _ _ _] -> TError ["Function "++ id++ "( ) not defined! Position:" ++ (show pos)]
                                                                                                                        Just ((Variable _ _ _ _):xs) -> let f =findEntryOfType xs "func" in
                                                                                                                                                        case f of
                                                                                                                                                            [Function t _ _ _] -> if t==B_type Type_Integer && checkCompatibility (TResult env t pos) (checkTypeTypeIndex typeindex env) then TResult env t pos else TError ["Incompatible type"]
                                                                                                                                                            [] -> TError ["Function "++ id++ "( ) not defined! Position:" ++ (show pos)]
                                                                                                                        Just [Function t _ _ _] -> if t==B_type Type_Integer && checkCompatibility (TResult env t pos) (checkTypeTypeIndex typeindex env) then TResult env t pos else TError ["Incompatible type"]
                                                                                                                        Just ((Function t _ _ _):xs) -> if t==B_type Type_Integer && checkCompatibility (TResult env t pos) (checkTypeTypeIndex typeindex env) then TResult env t pos else TError ["Incompatible type"]
                                                                                                                        Nothing -> TError ["Function "++ id++ "( ) not defined! Position:" ++ (show pos)]
                                                                                                TError e -> TError e
checkTypeTypeIndex node@(Abs.TypeOfIndexExpressionCallSingle pos (Abs.Ident id posi) exps ) env = case checkTypeExpression (Abs.ExpressionCall pos (Abs.Ident id posi) exps) env of
                                                                                                TResult _ _ _ ->
                                                                                                                    case Data.Map.lookup id env of
                                                                                                                        Just [Variable _ _ _ _] -> TError ["Function "++ id++ "( ) not defined! Position:" ++ (show pos)]
                                                                                                                        Just ((Variable _ _ _ _):xs) -> let f =findEntryOfType xs "func" in
                                                                                                                                                        case f of
                                                                                                                                                            [Function t _ _ _] -> if t==B_type Type_Integer then TResult env t pos else TError ["Incompatible type"]
                                                                                                                                                            [] -> TError ["Function "++ id++ "( ) not defined! Position:" ++ (show pos)]
                                                                                                                        Just [Function t _ _ _] -> if t==B_type Type_Integer then TResult env t pos else TError ["Incompatible type"]
                                                                                                                        Just ((Function t _ _ _):xs) -> if t==B_type Type_Integer then TResult env t pos else TError ["Incompatible type"]
                                                                                                                        Nothing -> TError ["Function "++ id++ "( ) not defined! Position:" ++ (show pos)]
                                                                                                TError e -> TError e
checkTypeTypeIndex node@(Abs.TypeOfIndexExpressionBracket pos typeindex exp) env = let expTCheck = checkTypeExpression exp env in
                                                                                case expTCheck of
                                                                                    TResult env (Pointer t depth) pos -> if t==B_type Type_Integer && depth==checkDef_ exp && checkCompatibility expTCheck (checkTypeTypeIndex typeindex env) then TResult env t pos else TError ["Incompatible type"]
                                                                                    _ -> if checkCompatibility expTCheck (TResult env (B_type Type_Integer) pos) && checkCompatibility expTCheck (checkTypeTypeIndex typeindex env) then TResult env (B_type Type_Integer) pos else TError ["Incompatible type"]
checkTypeTypeIndex node@(Abs.TypeOfIndexExpressionBracketSingle pos exp) env = let expTCheck = checkTypeExpression exp env in
                                                                                case expTCheck of
                                                                                    TResult env (Pointer t depth) pos -> if t==B_type Type_Integer && depth==checkDef_ exp then TResult env t pos else TError ["Incompatible type"]
                                                                                    _ -> if checkCompatibility expTCheck (TResult env (B_type Type_Integer) pos) then TResult env (B_type Type_Integer) pos else TError ["Incompatible type"]

checkUnary :: Abs.UNARYOP Posn -> Prelude.Integer
checkUnary (Abs.UnaryOperationPointer pos) = 1
checkUnary _ = 0

checkTypeCallExpression :: Abs.CALLEXPRESSION Posn -> Env -> TCheckResult
checkTypeCallExpression node@(Abs.CallExpressionParentheses _ (Abs.Ident id pos) namedexpr) env = case Data.Map.lookup id env of
                                                    Just [Function t posf param canOverride] -> checkTypeCallExpression_ node env [Function t posf param canOverride]
                                                    Just [Variable _ _ _ _] -> mergeErrors (TError ["Function "++ id++ "( ) not defined! Position:" ++ (show pos)]) (checkTypeNamedExpressionList namedexpr env)
                                                    Just (x:xs) -> case findEntryOfType (x:xs) "func" of
                                                        [] -> mergeErrors (TError ["Function "++ id++ "( ) not defined! Position:" ++ (show pos)]) (checkTypeNamedExpressionList namedexpr env)
                                                        [Function t posf param canOverride] -> checkTypeCallExpression_ node env [Function t posf param canOverride]
                                                    Nothing -> mergeErrors (TError ["Function "++ id++ "( ) not defined! Position:" ++ (show pos)]) (checkTypeNamedExpressionList namedexpr env)
-- sub-function of the previous one
checkTypeCallExpression_ :: Abs.CALLEXPRESSION Posn -> Env -> [EnvEntry] -> TCheckResult
checkTypeCallExpression_ (Abs.CallExpressionParentheses _ (Abs.Ident id pos) namedexpr) env [Function t posf param canOverride] = case namedexpr of
    (Abs.NamedExpressionList res namedexprr) -> if Prelude.length (param) == 1 -- The call was with 1 param, does the definition requires only 1 param?
                                               then if (checkCompatibilityOfParamsList namedexpr param env) then TResult env t pos 
                                                    else TError ["Function " ++ id ++ "( ) requires a parameter of type " ++ show (Prelude.head (getTypeListFromFuncParams param)) ++ " but " ++  show (getType (checkTypeNamedExpression namedexprr env)) ++ " is given! Position:" ++ show pos]
                                               else TError ["Function " ++ id ++ "( ) called with too few arguments! Position: " ++ show pos]
    (Abs.NamedExpressionListEmpty res) -> if param == [] then TResult env t pos else TError ["Function " ++ id ++ " called without parameters! Position: " ++ show pos] -- The call was with no params, check if the definition requires no param too
    (Abs.NamedExpressionLists res _ namedexprlist) -> if Prelude.length (param) == 1 + (countNumberOfParam namedexprlist) -- The call has n params, does the definition requires n params?
                                                              then if (checkCompatibilityOfParamsList namedexpr param env) then TResult env t pos 
                                                                   else TError ["Function " ++ id ++ "( ) called with parameters of the wrong type! Position: " ++ show pos]
                                                              else TError ["Function " ++ id ++ "( ) called with a different number of parameters than it's definition! Position: " ++ show pos]

-- Given a List of named expression, counts them and return the result
countNumberOfParam :: Abs.NAMEDEXPRESSIONLIST Posn -> Prelude.Int
countNumberOfParam (Abs.NamedExpressionLists _ _ namedexprlist) = 1 + countNumberOfParam namedexprlist
countNumberOfParam (Abs.NamedExpressionList _ _) = 1

checkCompatibilityOfParamsList :: Abs.NAMEDEXPRESSIONLIST Posn -> [TypeChecker.Parameter] -> Env-> Prelude.Bool
checkCompatibilityOfParamsList  (Abs.NamedExpressionLists pos x@(Abs.NamedExpression posn exp) xs) ((TypeChecker.Parameter ty _ _ _):zs) env = let namedType = checkTypeNamedExpression x env in 
                                                                                                                                                if checkCompatibility namedType (TResult env ty pos) 
                                                                                                                                                    then True && (checkCompatibilityOfParamsList xs zs env) else False
checkCompatibilityOfParamsList  (Abs.NamedExpressionList pos x@(Abs.NamedExpression posn exp)) ((TypeChecker.Parameter ty _ _ _):zs) env = let namedType = checkTypeNamedExpression x env in 
                                                                                                                                            if checkCompatibility namedType (TResult env ty pos) 
                                                                                                                                                then True else False

checkTypeNamedExpressionList :: Abs.NAMEDEXPRESSIONLIST Posn -> Env -> TCheckResult
checkTypeNamedExpressionList node@(Abs.NamedExpressionList pos namedexprlist) env = let namedListTCheck = checkTypeNamedExpression namedexprlist env in
                                                                                        case namedListTCheck of
                                                                                            TResult _ _ _ -> TResult env (B_type Type_Void) pos
                                                                                            _ -> namedListTCheck
checkTypeNamedExpressionList node@(Abs.NamedExpressionListEmpty pos) env = TResult env (B_type Type_Void) pos
checkTypeNamedExpressionList node@(Abs.NamedExpressionLists pos namedexpr namedexprlist) env = let namedListTCheck = checkTypeNamedExpression namedexpr env in
                                                                                                    let namedListsTCheck = checkTypeNamedExpressionList namedexprlist env in
                                                                                                    case namedListTCheck of
                                                                                                        TResult _ _ _ -> case namedListsTCheck of
                                                                                                                            TResult _ _ _ -> TResult env (B_type Type_Void) pos
                                                                                                                            _ -> namedListsTCheck
                                                                                                        _ -> case namedListsTCheck of
                                                                                                            TResult _ _ _ -> namedListTCheck
                                                                                                            _ -> mergeErrors namedListTCheck namedListsTCheck

checkTypeNamedExpression :: Abs.NAMEDEXPRESSION Posn -> Env -> TCheckResult
checkTypeNamedExpression node@(Abs.NamedExpression pos expr) env = checkTypeExpression expr env
                                    
checkTypeExecuteParameter :: Abs.PARAMETERS Posn -> Env -> TCheckResult
checkTypeExecuteParameter node@(Abs.ParameterList pos param params) env = let pamList = (getParamList node) in
                                                                                (if  checkDuplicatedParametersInFunDecl (getListOfIdsFromParamList pamList) -- check if params ids are not dups
                                                                                then TError ["Duplicated parameter identifiers in function declaration! Position:" ++ show pos] -- dups in params 
                                                                                else TResult env (B_type Type_Integer) pos) -- no dups: decl ok
checkTypeExecuteParameter node@(Abs.ParameterListSingle pos param) env = TResult env (B_type Type_Integer) pos -- single can't have dups in ids
checkTypeExecuteParameter node@(Abs.ParameterListEmpty pos) env = TResult env (B_type Type_Void) pos -- empty can't have dups in ids

checkTypeParameter:: Abs.PARAMETER Posn -> Env -> TCheckResult
checkTypeParameter node@(Abs.Parameter pos id ty) env = TResult env (B_type Type_Void) pos
checkTypeParameter node@(Abs.ParameterPointer pos id primitivetype pointer) env = TResult env (B_type Type_Void) pos

checkTypeArrayInit :: Abs.ARRAYINIT Posn -> Env -> TCheckResult
checkTypeArrayInit _ _ = TError ["TODO ARRAYINIT"] -- TODO