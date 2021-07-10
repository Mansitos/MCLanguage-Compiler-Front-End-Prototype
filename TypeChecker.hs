module TypeChecker where

import Type
import LexProgettoPar (Posn)
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

checkTypeStatements:: Abs.S Posn -> Env -> TCheckResult
checkTypeStatements (Abs.StartCode _ statements) start_env = TError ["Coming soon :)"]

checkTypeStatement :: Abs.STATEMENT Posn -> Env -> TCheckResult
checkTypeStatement node@(Abs.BreakStatement pos) env = checkTypeBreakStatement node env

executeStatements :: Abs.STATEMENTS Posn -> Env -> Abs.STATEMENTS TCheckResult                      -- stat or node?
executeStatements node@(Abs.ListStatements _ stat stats) env = Abs.ListStatements (checkTypeStatement stat env) (executeStatement stat env) (executeStatements stats env)
executeStatements node@(Abs.EmptyStatement _) env = Abs.EmptyStatement (checkEmptyStatement node env)

executeStatement :: Abs.STATEMENT Posn -> Env -> Abs.STATEMENT TCheckResult
executeStatement node@(Abs.BreakStatement _) env = Abs.BreakStatement (checkTypeBreakStatement node env)

checkEmptyStatement :: Abs.STATEMENTS Posn -> Env -> TCheckResult
checkEmptyStatement (Abs.EmptyStatement pos) env = TResult env (B_type Type_Void) pos

checkTypeBreakStatement :: Abs.STATEMENT Posn -> Env -> TCheckResult
checkTypeBreakStatement (Abs.BreakStatement pos) env = case Data.Map.lookup "while" env of
    Just result -> TResult env (B_type Type_Void) pos
    Nothing -> TError ["Unexpected break statement at " ++ (show pos)]
