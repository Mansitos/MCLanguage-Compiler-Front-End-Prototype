-- Cagnoni/Mansi UNIUD Progetto LC3

-- Pragma for implementing touples
{-# LANGUAGE MultiParamTypeClasses #-} 
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}

module TacGen where

import AbsTac as Tac
import AbsProgettoPar as Abs
import LexProgettoPar (Posn(..))
import TypeChecker
import Type
import Data.Map
import Data.Tuple

-- Touples ------------------------------------------------------------------------------------
class Sel1 a b | a -> b where sel1 :: a -> b
instance Sel1 (a1,a2) a1 where sel1 (x,_) = x
instance Sel1 (a1,a2,a3) a1 where sel1 (x,_,_) = x
instance Sel1 (a1,a2,a3,a4) a1 where sel1 (x,_,_,_) = x
instance Sel1 (a1,a2,a3,a4,a5) a1 where sel1 (x,_,_,_,_) = x

class Sel2 a b | a -> b where sel2 :: a -> b
instance Sel2 (a1,a2) a2 where sel2 (_,x) = x
instance Sel2 (a1,a2,a3) a2 where sel2 (_,x,_) = x
instance Sel2 (a1,a2,a3,a4) a2 where sel2 (_,x,_,_) = x
instance Sel2 (a1,a2,a3,a4,a5) a2 where sel2 (_,x,_,_,_) = x

class Sel3 a b | a -> b where sel3 :: a -> b
instance Sel3 (a1,a2,a3) a3 where sel3 (_,_,x) = x
instance Sel3 (a1,a2,a3,a4) a3 where sel3 (_,_,x,_) = x
instance Sel3 (a1,a2,a3,a4,a5) a3 where sel3 (_,_,x,_,_) = x

class Sel4 a b | a -> b where sel4 :: a -> b
instance Sel4 (a1,a2,a3,a4) a4 where sel4 (_,_,_,x) = x
instance Sel4 (a1,a2,a3,a4,a5) a4 where sel4 (_,_,_,x,_) = x

class Sel5 a b | a -> b where sel5 :: a -> b
instance Sel5 (a1,a2,a3,a4,a5) a5 where sel5 (_,_,_,_,x) = x

------------------------------------------------------------------------------------------------
-- GENERIC FUNCTIONS ---------------------------------------------------------------------------
------------------------------------------------------------------------------------------------

-- Builds a new label given the (optional) string and the counter
newLabel :: Prelude.String -> Prelude.Integer -> Label 
newLabel "" n       = Label ("L"++show n)
newLabel "end" n    = Label ("end")
newLabel str n      = Label (str ++show n)

-- Builds a new variable address for a temporary variable; given a counter
newTemp :: Prelude.Integer -> Address
newTemp n = AddrAddress ("t"++show n)

-- Given an identifier and its positions; builds a variable address
buildIDAddr :: Posn -> Prelude.String -> Address
buildIDAddr posv@(Pn a r c) id = AddrAddress (id++"@"++show r++","++show c)

-- Given 2 TACs; merges them into 1 tacs
merge2Tacs :: TAC -> TAC -> TAC
merge2Tacs (TAC [][]) (TAC [][]) = TAC [][]
merge2Tacs (TAC x k) (TAC y f) = (TAC (x++y) (k++f))

-- Given a list of TACs, merges them into 1 TAC
mergeTacs :: [TAC] -> TAC
mergeTacs lst = (TAC (mergeTacFromList_ lst) (mergeTacFromList_f lst))

-- Implements the previous functions
mergeTacFromList_ :: [TAC] -> [TACEntry]
mergeTacFromList_ ((TAC entries fs):xs) = entries ++ mergeTacFromList_ xs
mergeTacFromList_ [] = []

-- Implements the previous functions
mergeTacFromList_f :: [TAC] -> [TACEntry]
mergeTacFromList_f ((TAC entries fs):xs) = fs ++ mergeTacFromList_f xs
mergeTacFromList_f [] = []

-- Given an Address, return the string of it's content. Used in printing.
showAddrContent :: Address -> Prelude.String 
showAddrContent (AddrString s) = "\"" ++ s ++ "\""
showAddrContent (AddrInt s) = show s    
showAddrContent (AddrBool s) = show s   
showAddrContent (AddrReal s) = show s   
showAddrContent (AddrChar s) = "\'" ++ show s ++ "\'"    
showAddrContent (AddrAddress s) = s
showAddrContent (AddrNULL) = "NULL"  

-- Given a list of variable addresses and the value (address) of RightInitialization builds the list of TAC codes for each init/decl.
-- Example: var x,y,z:int = 5
--      the list of address are the address for x,y,z
--      the address for rExpr is the address of 5
--      returns a list of 3 tac entries (one for each variable initialized at addr. of 5)
buildTacEntriesForVarsDecl :: [Address] -> Address -> Type -> [TACEntry]
buildTacEntriesForVarsDecl [x] rAddr ty = case rAddr of
    AddrNULL -> [TacAssignNullOp x (genDefaultInitAddr ty) ty]
    _ -> [TacAssignNullOp x rAddr ty]
buildTacEntriesForVarsDecl (x:xs) rAddr ty = case rAddr of 
    AddrNULL -> [TacAssignNullOp x (genDefaultInitAddr ty)  ty] ++ buildTacEntriesForVarsDecl xs rAddr ty 
    _ -> [TacAssignNullOp x rAddr ty] ++ buildTacEntriesForVarsDecl xs rAddr ty 

-- Generate a default address for default values
-- Example: declaring a variable of time int without initialization: the default init. value is 0; so a int address of val. 0 must be generated.
genDefaultInitAddr :: Type -> Address
genDefaultInitAddr ty = case ty of
    B_type Type_Integer  -> AddrInt 0
    B_type Type_Boolean  -> AddrBool False 
    B_type Type_Char     -> AddrChar ' '
    B_type Type_String   -> AddrString ""   
    B_type Type_Real     -> AddrReal  0.0

-- Given a EXPRESSION node, return it's type
getTypeFromExpr :: Abs.EXPRESSION TCheckResult -> Type
getTypeFromExpr (Abs.ExpressionInteger res@(TResult env t pos) value@(Abs.Integer val resi)) = t
getTypeFromExpr (Abs.ExpressionBoolean res@(TResult env t pos) value@(Abs.Boolean_true resi)) = t
getTypeFromExpr (Abs.ExpressionBoolean res@(TResult env t pos) value@(Abs.Boolean_false resi)) = t
getTypeFromExpr (Abs.ExpressionBoolean res@(TResult env t pos) value@(Abs.Boolean_True resi)) = t
getTypeFromExpr (Abs.ExpressionBoolean res@(TResult env t pos) value@(Abs.Boolean_False resi)) = t
getTypeFromExpr (Abs.ExpressionChar res@(TResult env t pos) value@(Abs.Char val resi)) = t      
getTypeFromExpr (Abs.ExpressionString res@(TResult env t pos) value@(Abs.String val resi)) = t  
getTypeFromExpr (Abs.ExpressionReal res@(TResult env t pos) value@(Abs.Real val resi)) = t      
getTypeFromExpr (Abs.ExpressionBracket res@(TResult env t pos) exp) = t                   
getTypeFromExpr (Abs.ExpressionCast res@(TResult env t pos) def tipo) = t
getTypeFromExpr (Abs.ExpressionUnary res@(TResult env t pos) unary def)  = t
getTypeFromExpr (Abs.ExpressionIdent res@(TResult env t pos) id index) = t
getTypeFromExpr (Abs.ExpressionCall res@(TResult env t pos) id exps) = t
getTypeFromExpr (Abs.ExpressionBinaryPlus res@(TResult env t pos) expr1 expr2) = t
getTypeFromExpr (Abs.ExpressionBinaryMinus res@(TResult env t pos) expr1 expr2) = t
getTypeFromExpr (Abs.ExpressionBinaryProduct res@(TResult env t pos) expr1 expr2) = t
getTypeFromExpr (Abs.ExpressionBinaryDivision res@(TResult env t pos) expr1 expr2) = t
getTypeFromExpr (Abs.ExpressionBinaryModule res@(TResult env t pos) expr1 expr2) = t
getTypeFromExpr (Abs.ExpressionBinaryPower res@(TResult env t pos) expr1 expr2) = t
getTypeFromExpr (Abs.ExpressionBinaryAnd res@(TResult env t pos) expr1 expr2) = t
getTypeFromExpr (Abs.ExpressionBinaryOr res@(TResult env t pos) expr1 expr2) = t
getTypeFromExpr (Abs.ExpressionBinaryEq res@(TResult env t pos) expr1 expr2) = t
getTypeFromExpr (Abs.ExpressionBinaryNotEq res@(TResult env t pos) expr1 expr2) = t
getTypeFromExpr (Abs.ExpressionBinaryGratherEq res@(TResult env t pos) expr1 expr2) = t
getTypeFromExpr (Abs.ExpressionBinaryGrather res@(TResult env t pos) expr1 expr2) = t
getTypeFromExpr (Abs.ExpressionBinaryLessEq res@(TResult env t pos) expr1 expr2) = t
getTypeFromExpr (Abs.ExpressionBinaryLess res@(TResult env t pos) expr1 expr2) = t

-- Given a type and a string (indicating the operator) builds the right operator
-- Example: INT, plus -> IntAdd operator is builded/returned
buildOp :: Type -> Prelude.String -> TacBinaryOp
buildOp t str = case str of
                    "plus" -> case t of
                                B_type Type_Integer -> IntAdd
                                B_type Type_Real -> RealAdd
                    "minus" -> case t of
                                B_type Type_Integer -> IntSub
                                B_type Type_Real -> RealSub
                    "product" -> case t of
                                B_type Type_Integer -> IntMul
                                B_type Type_Real -> RealMul
                    "division" -> case t of
                                B_type Type_Integer -> IntDiv
                                B_type Type_Real -> RealDiv
                    "module" -> case t of
                                B_type Type_Integer -> IntMod
                                B_type Type_Real -> RealMod
                    "power" -> case t of
                                B_type Type_Integer -> IntPow
                                B_type Type_Real -> RealPow

-- Given a type for left operand and a type for right operand and a string (indicating the relation operator) builds the right operator
-- Example: INT, REAL notqe -> NeqReal operator is builded/returned                               
buildROp :: Type -> Type -> Prelude.String -> TacRelOp
buildROp t1 t2 str = case str of
                        "and" -> And
                        "or" -> Or
                        "eq" ->case t1 of
                                B_type Type_Integer -> case t2 of
                                                        B_type Type_Integer -> EqInt
                                                        B_type Type_Real -> EqReal
                                B_type Type_Real -> EqReal
                                B_type Type_Char -> EqChar
                                B_type Type_String -> EqString
                                B_type Type_Boolean -> EqBool
                        "noteq" ->case t1 of
                                    B_type Type_Integer -> case t2 of
                                                            B_type Type_Integer -> NeqInt
                                                            B_type Type_Real -> NeqReal
                                    B_type Type_Real -> NeqReal
                                    B_type Type_Char -> NeqChar
                                    B_type Type_String -> NeqString
                                    B_type Type_Boolean -> NeqBool
                        "grathereq" ->case t1 of
                                        B_type Type_Integer -> case t2 of
                                                                B_type Type_Integer -> GeqInt
                                                                B_type Type_Real -> GeqReal
                                        B_type Type_Real -> GeqReal
                                        B_type Type_Char -> GeqChar
                                        B_type Type_String -> GeqString
                        "grather" ->case t1 of
                                        B_type Type_Integer -> case t2 of
                                                                B_type Type_Integer -> GtInt
                                                                B_type Type_Real -> GtReal
                                        B_type Type_Real -> GtReal
                                        B_type Type_Char -> GtChar
                                        B_type Type_String -> GtString
                        "lesseq" ->case t1 of
                                    B_type Type_Integer -> case t2 of
                                                            B_type Type_Integer -> LeqInt
                                                            B_type Type_Real -> LeqReal
                                    B_type Type_Real -> LeqReal
                                    B_type Type_Char -> LeqChar
                                    B_type Type_String -> LeqString
                        "less" ->case t1 of
                                    B_type Type_Integer -> case t2 of
                                                            B_type Type_Integer -> LtInt
                                                            B_type Type_Real -> LtReal
                                    B_type Type_Real -> LtReal
                                    B_type Type_Char -> LtChar
                                    B_type Type_String -> LtString

-- Given an assign operator node + 2 addresses + the type (of the assignement, from the tcheck result of the assignment operator)
-- builds the right TAC instruction.
buildAssignTac :: Abs.ASSIGNOP TCheckResult -> Address -> Address -> Type -> TACEntry
buildAssignTac assignOp leftAddr rightAddr t = case assignOp of
                                                (Abs.AssignOperationEq _ )         -> TacAssignNullOp   leftAddr rightAddr t
                                                (Abs.AssignOperationEqPlus _ )     -> TacAssignBinaryOp leftAddr (buildOp t "plus") leftAddr rightAddr t
                                                (Abs.AssignOperationEqMinus _ )    -> TacAssignBinaryOp leftAddr (buildOp t "minus") leftAddr rightAddr t
                                                (Abs.AssignOperationEqProd _ )     -> TacAssignBinaryOp leftAddr (buildOp t "product") leftAddr rightAddr t
                                                (Abs.AssignOperationEqFract _ )    -> TacAssignBinaryOp leftAddr (buildOp t "division") leftAddr rightAddr t
                                                (Abs.AssignOperationEqPercent _ )  -> TacAssignBinaryOp leftAddr (buildOp t "module") leftAddr rightAddr t
                                                (Abs.AssignOperationEqPower _ )    -> TacAssignBinaryOp leftAddr (buildOp t "power") leftAddr rightAddr t

------------------------------------------------------------------------------------------------
-- TAC GENERATION FUNCTIONS --------------------------------------------------------------------
------------------------------------------------------------------------------------------------

-- Given the start of a program (starting node Abs.S); starts the TAC generation process
genTAC :: Abs.S TCheckResult -> Abs.S TAC
genTAC (Abs.StartCode tres stats) = let endLab = newLabel "end" 0 in
                                        let statsTac = sel1 (genTacStatements stats 0 endLab 0 (endLab,endLab)) in
                                            let tacs = (statements_content statsTac) in
                                                (Abs.StartCode (TAC ((code tacs)++(TacLabel endLab):[ExitTac]) (funcs tacs)) statsTac)

genTacStatements :: Abs.STATEMENTS TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.STATEMENTS TAC,Prelude.Integer,Prelude.Integer)
genTacStatements (Abs.ListStatements tres stat stats) n l k (w,j) = case stats of
                                                                Abs.ListStatements tres _ _ -> let statTac = genTacStatement stat n l k (w,j) tres in
                                                                                                    let newC = sel2 statTac in
                                                                                                        let newL = newLabel "" (sel3 statTac) in
                                                                                                            let statsTac = genTacStatements stats newC newL (sel3 statTac) (w,j) in
                                                                                                                (Abs.ListStatements (merge2Tacs (statement_content (sel1 statTac)) (statements_content (sel1 statsTac))) (sel1 statTac) (sel1 statsTac),sel2 statsTac,sel3 statsTac)
                                                                Abs.EmptyStatement tres -> let statTac = genTacStatement stat n l k (w,j) tres in
                                                                                                let newC = sel2 statTac in
                                                                                                    let newL = newLabel "" (sel3 statTac) in
                                                                                                        (Abs.ListStatements (statement_content (sel1 statTac)) (sel1 statTac) (Abs.EmptyStatement (TAC [] [])),newC,sel3 statTac)
genTacStatements (Abs.EmptyStatement tres) n l k (w,j) = ((Abs.EmptyStatement (TAC [] [])),n,k)

genTacStatement :: Abs.STATEMENT TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> TCheckResult -> (Abs.STATEMENT TAC,Prelude.Integer,Prelude.Integer,Address)
genTacStatement (Abs.VariableDeclarationStatement res@(TResult _ ty _) tipo vardec) n l k (w,j) tres = let tipoTac = genTacVariableType tipo n l k (w,j) in
                                                                                                    let tipoContent = variabletype_content (sel1 tipoTac) in
                                                                                                        let vardecTac = genTacVarDecList vardec n l k (w,j) tres in
                                                                                                            let vardecContent = vardeclist_content (sel1 vardecTac) in
                                                                                                                let vardecAddrs = sel4 vardecTac in -- variable addresses # >1
                                                                                                                    let initAddr = sel5 vardecTac in
                                                                                                                        (Abs.VariableDeclarationStatement (merge2Tacs (merge2Tacs vardecContent (TAC (buildTacEntriesForVarsDecl vardecAddrs initAddr ty) []))
                                                                                                                                                             tipoContent) (sel1 tipoTac) (sel1 vardecTac) ,(sel2 vardecTac),(sel3 vardecTac),AddrNULL)
genTacStatement (Abs.BreakStatement res) n l k (w,j) tres    = ((Abs.BreakStatement (TAC [TacJump w,TacComment "break jump"] [])),n,k,AddrNULL)
genTacStatement (Abs.ContinueStatement res) n l k (w,j) tres = ((Abs.ContinueStatement (TAC [TacJump j,TacComment "continue jump"] [])),n,k,AddrNULL)
genTacStatement (Abs.ReturnStatement res ret) n l k (w,j) tres = case ret of 
    (Abs.ReturnStateEmpty _)  -> ((Abs.ReturnStatement (TAC [TacReturnVoid][]) (Abs.ReturnStateEmpty (TAC [][]))),n,k,AddrNULL)
    (Abs.ReturnState _ expr)  -> let expression = genTacExpression expr n l k (w,j) tres in
                                                                                    ((Abs.ReturnStatement (TAC ((code (expression_content (sel1 expression)))++
                                                                                                               [TacReturn (sel4 expression) (getTypeFromExpr expr)])
                                                                                                               []) (Abs.ReturnState (TAC [][]) (sel1 expression))),n,k,AddrNULL)
genTacStatement (Abs.Statement res block) n l k (w,j) tres = let newL = newLabel "" k in 
                                                                let newC = sel2 (genTacBlock block n newL k (w,j)) in
                                                                    let blockTac = (genTacBlock block n newL k (w,j)) in (Abs.Statement (b_content (sel1 blockTac)) (sel1 blockTac),newC,(sel3 blockTac),AddrNULL)
genTacStatement (Abs.ExpressionStatement res expstat) n l k (w,j) tres = let newL = newLabel "" k in
                                                                            let expressionstat = (genTacExpressionStatement expstat n newL k (w,j)) in
                                                                                let newC = sel2 expressionstat in
                                                                                    let exprAddr = sel4 expressionstat in
                                                                                        ((Abs.ExpressionStatement (expressionstatement_content (sel1 expressionstat)) (sel1 expressionstat)),newC,(sel3 expressionstat),exprAddr)
genTacStatement (Abs.AssignmentStatement resres@(TResult _ t _) lval assignOp exp) n l k (w,j) tres = let newL = newLabel "" k in
                                                                                    let leftVal = (genTacLeftVal lval n newL k (w,j)) in
                                                                                        let rightVal = (genTacExpression exp n newL k (w,j) tres) in
                                                                                            let newC = sel2 rightVal in
                                                                                                let exprAddr = sel4 rightVal in
                                                                                                    let leftValAddr = sel4 leftVal in
                                                                                                        let assignTac = (buildAssignTac assignOp leftValAddr exprAddr t) in
                                                                                                        ((Abs.AssignmentStatement (TAC (code (expression_content (sel1 rightVal)) ++ -- expression (rval) evaluation tac code
                                                                                                                                        [assignTac])                                 -- assign tac
                                                                                                                                        []) (sel1 leftVal) (genTacAssignOp assignOp) (sel1 rightVal)),newC,(sel3 rightVal),AddrNULL)
genTacStatement (Abs.ConditionalStatement res condition) n l k (w,j) tres = let newL = newLabel "else" k in 
                                                                                let condStatementTac = (genTacConditionalStatement condition n newL (k+1) (w,j)) in
                                                                                    let newC = sel2 condStatementTac in
                                                                                        ((Abs.ConditionalStatement (conditionalstate_content (sel1 condStatementTac)) (sel1 condStatementTac)),newC,(sel3 condStatementTac),AddrNULL)
genTacStatement (Abs.WhileDoStatement res while) n l k (w,j) tres = let newL = newLabel "body" k in 
                                                                        let whileStatement = (genTacWhileDoStatement while n newL (k+1) (w,j)) in
                                                                            let whileStatementTac = sel1 whileStatement in
                                                                                let newC = sel2 whileStatement in
                                                                                    let newK = sel3 whileStatement in
                                                                                        ((Abs.WhileDoStatement (whilestatement_content whileStatementTac) whileStatementTac),newC,newK,AddrNULL) -- null address? TODO
genTacStatement (Abs.DoWhileStatement res doStat) n l k (w,j) tres = let newL = newLabel "body" k in 
                                                                        let doStatement = (genTacDoWhileStatement doStat n newL (k+1) (w,j)) in
                                                                            let doStatementTac = sel1 doStatement in
                                                                                let newC = sel2 doStatement in
                                                                                    let newK = sel3 doStatement in
                                                                                        ((Abs.DoWhileStatement (dostatement_content doStatementTac) doStatementTac),newC,newK,AddrNULL) -- null address? TODO
genTacStatement (Abs.ForStatement res forStat) n l k (w,j) tres   = let newL = newLabel "body" k in
                                                                        let forStatement = (genTacForStatement forStat n newL (k+1) (w,j)) in
                                                                            let newC = sel2 forStatement in
                                                                                let newK = sel3 forStatement in
                                                                                    ((Abs.ForStatement (forstatement_content (sel1 forStatement)) (sel1 forStatement)),newC,newK,AddrNULL)
genTacStatement (Abs.ProcedureStatement res ident@(Abs.Ident id _) param states) n l k (w,j) tres = let newL = newLabel ("p_" ++ id) k in
                                                                                                        let endL = newLabel ("end_p_" ++ id) (k+1) in
                                                                                                            let statements = (genTacStatements states n newL (k+2) (w,j)) in
                                                                                                                let newC = sel2 statements in
                                                                                                                    let newK = sel3 statements in
                                                                                                                        ((Abs.ProcedureStatement (mergeTacs [(TAC [] [TacLabel newL]),  -- start func code label
                                                                                                                                                             (TAC [] (code (statements_content (sel1 statements)))), -- tac of statements inside the body (no funcs. decl. tacs.)
                                                                                                                                                             (TAC [] [TacLabel endL]),  -- end func code label   
                                                                                                                                                             (TAC [] (funcs (statements_content (sel1 statements)))) -- functions declared inside
                                                                                                                                                             ]) (Abs.Ident id (TAC [] [])) (Abs.ParameterListEmpty (TAC [] [])) (Abs.EmptyStatement (TAC [] []))),(sel2 statements),(sel3 statements),AddrNULL)                                           
genTacStatement (Abs.FunctionStatement res ident@(Abs.Ident id _) param tipo states) n l k (w,j) tres = ((Abs.FunctionStatement (TAC [] []) (Abs.Ident id (TAC [] [])) (Abs.ParameterListEmpty (TAC [] [])) (Abs.TypeExpressionFunction (TAC [] []) (Abs.TypeExpression (TAC [] []) (Abs.PrimitiveTypeVoid (TAC [] [])))) (Abs.EmptyStatement (TAC [] []))),n,k,AddrNULL)                                           

genTacAssignOp :: Abs.ASSIGNOP TCheckResult -> Abs.ASSIGNOP TAC
genTacAssignOp (Abs.AssignOperationEq _ )        = (Abs.AssignOperationEq (TAC [] []))       
genTacAssignOp (Abs.AssignOperationEqPlus _ )    = (Abs.AssignOperationEqPlus (TAC [] []))   
genTacAssignOp (Abs.AssignOperationEqMinus _ )    = (Abs.AssignOperationEqMinus(TAC [] []))   
genTacAssignOp (Abs.AssignOperationEqProd _ )    = (Abs.AssignOperationEqProd (TAC [] []))   
genTacAssignOp (Abs.AssignOperationEqFract _ )   = (Abs.AssignOperationEqFract (TAC [] [])) 
genTacAssignOp (Abs.AssignOperationEqPercent _ ) = (Abs.AssignOperationEqPercent (TAC [] []))
genTacAssignOp (Abs.AssignOperationEqPower _ )   = (Abs.AssignOperationEqPower (TAC [] []))  

genTacLeftVal :: Abs.LVALUEEXPRESSION  TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.LVALUEEXPRESSION  TAC, Prelude.Integer, Prelude.Integer, Address)
--genTAcLeftVal (Abs.LvalueExpressions res ident arrayindex lval) n l k (w,j) =
genTacLeftVal (Abs.LvalueExpression res@(TResult env _ _) ident@(Abs.Ident id resi) arrayindex     ) n l k (w,j) = case arrayindex of 
                                                                                                    (Abs.ArrayIndexElementEmpty _) -> case Data.Map.lookup id env of
                                                                                                        Just [Variable _ posv _ _] ->  let leftAddr = buildIDAddr posv id in -- gestire tutti icasi TODO
                                                                                                                                            ((Abs.LvalueExpression (TAC [] []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElementEmpty (TAC [] []))),n,k,leftAddr)
                                                                                                    -- _ -> -- is array

genTacExpressionStatement :: Abs.EXPRESSIONSTATEMENT TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.EXPRESSIONSTATEMENT TAC, Prelude.Integer, Prelude.Integer, Address)
genTacExpressionStatement (Abs.VariableExpression res@(TResult _ _ pos) ident@(Abs.Ident id resi)) n l k (w,j) = ((Abs.VariableExpression (TAC [] []) (Abs.Ident id (TAC [] []))),n,k,buildIDAddr pos id)
genTacExpressionStatement (Abs.CallExpression res@(TResult _ ty pos) call) n l k (w,j)   = let callexpression = (genTacCallExpression call n l k (w,j)) in
                                                                                             let funcAddr = sel4 callexpression in
                                                                                                 let callExprTac = sel1 callexpression in
                                                                                                     ((Abs.CallExpression (mergeTacs [(callexpression_content callExprTac), -- tac of callexpression
                                                                                                                                      case ty of
                                                                                                                                          B_type Type_Void -> (TAC [TacProcCall funcAddr] [])     -- tac of proc call
                                                                                                                                          _                -> (TAC [TacFuncCallLeft funcAddr] []) -- tac of func call 
                                                                                                                                          ]) (sel1 callexpression)),(sel2 callexpression),(sel3 callexpression),funcAddr)

genTacCallExpression :: Abs.CALLEXPRESSION TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.CALLEXPRESSION TAC, Prelude.Integer, Prelude.Integer,Address)
genTacCallExpression (Abs.CallExpressionParentheses res@(TResult _ _ pos) ident@(Abs.Ident id resi) namedExpr) n l k (w,j) = let namedExpression = genTacNamedExpression namedExpr n l k (w,j) in
                                                                                                                                let namedExprTac = sel1 namedExpression in
                                                                                                                                    let funcAddr = buildIDAddr pos id in
                                                                                                                                        ((Abs.CallExpressionParentheses (namedexpressionlist_content namedExprTac) (Abs.Ident id (TAC [] [])) namedExprTac),(sel2 namedExpression),(sel3 namedExpression),funcAddr)

genTacNamedExpression :: Abs.NAMEDEXPRESSIONLIST TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.NAMEDEXPRESSIONLIST TAC, Prelude.Integer, Prelude.Integer)
genTacNamedExpression (Abs.NamedExpressionList res namedexpr@(Abs.NamedExpression _ expr)) n l k (w,j) = let expression = genTacExpression expr n l k (w,j) res in
                                                                                                            let exprTac = (sel1 expression) in
                                                                                                                let exprAddr = (sel4 expression) in
                                                                                                                    let p_type = getTypeFromExpr expr in
                                                                                                                        ((Abs.NamedExpressionList (mergeTacs [(expression_content exprTac),         -- evaluation of the param
                                                                                                                                                              (TAC [TacParam exprAddr p_type] [])])    -- param tac
                                                                                                                                                              (Abs.NamedExpression (TAC [] []) exprTac)),(sel2 expression),(sel3 expression))
genTacNamedExpression (Abs.NamedExpressionLists res namedexpr@(Abs.NamedExpression _ expr) namedexprs) n l k (w,j) = let expression = genTacExpression expr n l k (w,j) res in
                                                                                                                        let namedExpressions = genTacNamedExpression namedexprs (sel2 expression) l (sel3 expression) (w,j) in
                                                                                                                            let namedExprsTac = sel1 namedExpressions in
                                                                                                                                let exprTac = (sel1 expression) in
                                                                                                                                    let exprAddr = (sel4 expression) in
                                                                                                                                        let p_type = getTypeFromExpr expr in
                                                                                                                                            ((Abs.NamedExpressionList (mergeTacs [(expression_content exprTac),         -- evaluation of the param
                                                                                                                                                                                  (TAC [TacParam exprAddr p_type] []),     -- param tac
                                                                                                                                                                                  (namedexpressionlist_content namedExprsTac) -- tac of other params (recursive call)
                                                                                                                                                                                  ])
                                                                                                                                                                                  (Abs.NamedExpression (TAC [] []) exprTac)),(sel2 namedExpressions),(sel3 namedExpressions))
genTacNamedExpression (Abs.NamedExpressionListEmpty res) n l k (w,j) = ((Abs.NamedExpressionListEmpty (TAC [] [])),n,k)

genTacForStatement :: Abs.FORSTATEMENT TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.FORSTATEMENT TAC, Prelude.Integer, Prelude.Integer)
genTacForStatement (Abs.ForStateIndexDo res index@(Abs.IndexVarDeclaration _ ident@(Abs.Ident id resi@(TResult _ _ pos))) rangexp stat) n l k (w,j) =
                                                                        let rangeExp = (genTacRangeExpr rangexp n l k (w,j)) in -- for range do stats
                                                                            let guardLabel = newLabel "guard" ((sel3 rangeExp)+1) in  -- wrong label for guard TODO
                                                                                let nextLabel = newLabel "next" ((sel3 rangeExp)+2) in
                                                                                    let statement = (genTacStatement stat (sel2 rangeExp) l ((sel3 rangeExp )+3) (nextLabel,guardLabel) res) in -- TODO +1 ?????
                                                                                        let statTac = sel1 statement in
                                                                                            let rangeExpTac = sel1 rangeExp in
                                                                                                case rangeExpTac of
                                                                                                    -- (Abs.RangeExpression res expr1 expr2 range) -> SHOULD NOT REACH !!!
                                                                                                    (Abs.RangeExpressionSingle tac expr1 expr2) -> let expr1Addr = sel4 rangeExp in
                                                                                                                                                    let expr2Addr = sel5 rangeExp in
                                                                                                                                                     let guardAddr = buildIDAddr pos id in  -- getting guard variable address
                                                                                                                                                        ((Abs.ForStateIndexDo (mergeTacs [(rangeexp_content rangeExpTac),                   -- rangeExpr TACS (evaluation of expr1 and expr2 code)
                                                                                                                                                                                        (TAC [TacAssignNullOp guardAddr expr1Addr (B_type Type_Integer)] []),  -- guard initialization to expr1 val
                                                                                                                                                                                        (TAC [TacJump guardLabel] []),                         -- jump to guard label
                                                                                                                                                                                        (TAC [TacLabel l] []),                                 -- body label              
                                                                                                                                                                                        (statement_content statTac),                        -- body TAC code
                                                                                                                                                                                        (TAC [TacAssignBinaryOp guardAddr IntAdd guardAddr (AddrInt 1) (B_type Type_Integer)] []), -- guard++
                                                                                                                                                                                        (TAC [TacLabel guardLabel] []),                        -- guard label
                                                                                                                                                                                        (TAC [TacRelConditionalJump l False LeqInt guardAddr expr2Addr] []),  -- check of guard <= end (relation jump)
                                                                                                                                                                                        (TAC [TacLabel nextLabel] [])])                        -- end of for
                                                                                                                                                                                        (Abs.IndexVarDeclaration (TAC [] []) (Abs.Ident id (TAC [] []))) rangeExpTac statTac),sel2 statement, sel3 statement)                                                                                      
genTacForStatement (Abs.ForStateIndexWDo res index@(Abs.IndexVarDeclaration _ ident@(Abs.Ident id resi@(TResult _ _ pos))) rangexp b@(Abs.BlockStatement _ stats)) n l k (w,j) =
                                                                            let rangeExp = (genTacRangeExpr rangexp n l k (w,j)) in -- for range do stats
                                                                                let guardLabel = newLabel "guard" (k+1) in  -- wrong label for guard TODO
                                                                                    let nextLabel = newLabel "next" (k+2) in
                                                                                        let statements = (genTacStatements stats (sel2 rangeExp) l ((sel3 rangeExp )+1) (nextLabel,guardLabel)) in -- TODO +1 ?????
                                                                                            let statsTac = sel1 statements in
                                                                                                let rangeExpTac = sel1 rangeExp in
                                                                                                    case rangeExpTac of
                                                                                                    -- (Abs.RangeExpression res expr1 expr2 range) -> SHOULD NOT REACH !!!
                                                                                                    (Abs.RangeExpressionSingle tac expr1 expr2) -> let expr1Addr = sel4 rangeExp in
                                                                                                                                                    let expr2Addr = sel5 rangeExp in
                                                                                                                                                        let guardAddr = buildIDAddr pos id in -- getting guard variable address
                                                                                                                                                        ((Abs.ForStateIndexWDo (mergeTacs [(rangeexp_content rangeExpTac),                   -- rangeExpr TACS (evaluation of expr1 and expr2 code)
                                                                                                                                                                                        (TAC [TacAssignNullOp guardAddr expr1Addr (B_type Type_Integer)] []),  -- guard initialization to expr1 val
                                                                                                                                                                                        (TAC [TacJump guardLabel] []),                          -- jump to guard label
                                                                                                                                                                                        (TAC [TacLabel l] []),                                  -- body label              
                                                                                                                                                                                        (statements_content statsTac),                       -- body TAC code
                                                                                                                                                                                        (TAC [TacAssignBinaryOp guardAddr IntAdd guardAddr (AddrInt 1) (B_type Type_Integer)] []), -- guard++
                                                                                                                                                                                        (TAC [TacLabel guardLabel] []),                         -- guard label
                                                                                                                                                                                        (TAC [TacRelConditionalJump l False LeqInt guardAddr expr2Addr] []), -- check of guard <= end (relation jump)
                                                                                                                                                                                        (TAC [TacLabel nextLabel] [])                          -- end of for 
                                                                                                                                                                                        ]) (Abs.IndexVarDeclaration (TAC [] []) (Abs.Ident id (TAC [] []))) rangeExpTac (Abs.BlockStatement (TAC [] []) statsTac)),sel2 statements, sel3 statements)                                                    
genTacForStatement (Abs.ForStateExprDo res rangexp stat)        n l k (w,j) = let rangeExp = (genTacRangeExpr rangexp n l k (w,j)) in -- for range do stats
                                                                                let guardLabel = newLabel "guard" (sel3 rangeExp) in  -- wrong label for guard TODO
                                                                                    let nextLabel = newLabel "next" ((sel3 rangeExp )+1) in
                                                                                        let statement = (genTacStatement stat ((sel2 rangeExp)+1) l ((sel3 rangeExp )+2) (nextLabel,guardLabel) res) in -- TODO +1 ?????    
                                                                                        let statTac = sel1 statement in
                                                                                            let rangeExpTac = sel1 rangeExp in
                                                                                                case rangeExpTac of
                                                                                                    -- (Abs.RangeExpression res expr1 expr2 range) -> SHOULD NOT REACH !!!
                                                                                                    (Abs.RangeExpressionSingle tac expr1 expr2) -> let expr1Addr = sel4 rangeExp in
                                                                                                                                                    let expr2Addr = sel5 rangeExp in
                                                                                                                                                     let guardTempAddr = (newTemp (sel2 rangeExp)) in -- generating temp variable for guard address
                                                                                                                                                        ((Abs.ForStateExprDo (mergeTacs [(rangeexp_content rangeExpTac),                    -- rangeExpr TACS (evaluation of expr1 and expr2 code)
                                                                                                                                                                                        (TAC [TacAssignNullOp guardTempAddr expr1Addr (B_type Type_Integer)] []),  -- guard temp initialization to expr1 val
                                                                                                                                                                                        (TAC [TacJump guardLabel] []),                         -- jump to guard label
                                                                                                                                                                                        (TAC [TacLabel l] []),                                 -- body label              
                                                                                                                                                                                        (statement_content statTac),                        -- body TAC code
                                                                                                                                                                                        (TAC [TacAssignBinaryOp guardTempAddr IntAdd guardTempAddr (AddrInt 1) (B_type Type_Integer)] []), -- guard++
                                                                                                                                                                                        (TAC [TacLabel guardLabel] []),                        -- guard label
                                                                                                                                                                                        (TAC [TacRelConditionalJump l False LeqInt guardTempAddr expr2Addr] []),  -- check of guard <= end (relation jump)
                                                                                                                                                                                        (TAC [TacLabel nextLabel] [])                          -- end of for
                                                                                                                                                                                        ]) rangeExpTac statTac),sel2 statement, sel3 statement)                                                                                      
genTacForStatement (Abs.ForStateExprWDo res rangexp b@(Abs.BlockStatement _ stats)) n l k (w,j) = let rangeExp = (genTacRangeExpr rangexp n l k (w,j)) in -- for range do stats
                                                                                                    let guardLabel = newLabel "guard" (k+1) in  -- wrong label for guard TODO
                                                                                                        let nextLabel = newLabel "next" (k+2) in
                                                                                                            let statements = (genTacStatements stats (sel2 rangeExp) l ((sel3 rangeExp )+1) (nextLabel,guardLabel)) in -- TODO +1 ?????    
                                                                                                            let statsTac = sel1 statements in
                                                                                                                let rangeExpTac = sel1 rangeExp in
                                                                                                                    case rangeExpTac of
                                                                                                                        -- (Abs.RangeExpression res expr1 expr2 range) -> SHOULD NOT REACH !!!
                                                                                                                        (Abs.RangeExpressionSingle tac expr1 expr2) -> let expr1Addr = sel4 rangeExp in
                                                                                                                                                                        let expr2Addr = sel5 rangeExp in
                                                                                                                                                                         let guardTempAddr = (newTemp (sel2 rangeExp)) in -- generating temp variable for guard address
                                                                                                                                                                            ((Abs.ForStateExprWDo (mergeTacs [(rangeexp_content rangeExpTac),                    -- rangeExpr TACS (evaluation of expr1 and expr2 code)
                                                                                                                                                                                                            (TAC [TacAssignNullOp guardTempAddr expr1Addr (B_type Type_Integer)] []),  -- guard temp initialization to expr1 val
                                                                                                                                                                                                            (TAC [TacJump guardLabel] []),                          -- jump to guard label
                                                                                                                                                                                                            (TAC [TacLabel l] []),                                  -- body label              
                                                                                                                                                                                                            (statements_content statsTac),                       -- body TAC code
                                                                                                                                                                                                            (TAC [TacAssignBinaryOp guardTempAddr IntAdd guardTempAddr (AddrInt 1) (B_type Type_Integer)] []), -- guard++
                                                                                                                                                                                                            (TAC [TacLabel guardLabel] []),                         -- guard label
                                                                                                                                                                                                            (TAC [TacRelConditionalJump l False LeqInt guardTempAddr expr2Addr] []),  -- check of guard <= end (relation jump)
                                                                                                                                                                                                            (TAC [TacLabel nextLabel] [])                           -- end of for
                                                                                                                                                                                                            ]) rangeExpTac (Abs.BlockStatement (TAC [] []) statsTac)),sel2 statements, sel3 statements)                                                    

genTacRangeExpr :: Abs.RANGEEXP TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.RANGEEXP TAC, Prelude.Integer, Prelude.Integer, Address, Address)
-- genTacRangeExpr (Abs.RangeExpression res expr1 expr2 range) n l k (w,j) = -- multiple range expression should be Used only in arrays? 1..2,1..2 ??? TODO
genTacRangeExpr (Abs.RangeExpressionSingle res expr1 expr2) n l k (w,j) = let exprLeft = (genTacExpression expr1 n l k (w,j) res) in
                                                                            let exprRight = (genTacExpression expr2 (sel2 exprLeft) l (sel3 exprLeft) (w,j) res) in
                                                                                let newC = sel2 exprRight in
                                                                                    let newK = sel3 exprRight in
                                                                                        let exprLeftTac = (sel1 exprLeft) in
                                                                                            let exprRightTac = (sel1 exprRight) in
                                                                                                ((Abs.RangeExpressionSingle (merge2Tacs (expression_content exprLeftTac) (expression_content exprRightTac)) exprLeftTac exprRightTac),newC,newK,sel4 exprLeft,sel4 exprRight)
                                                                            

genTacWhileDoStatement :: Abs.WHILESTATEMENT TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.WHILESTATEMENT TAC, Prelude.Integer, Prelude.Integer)
genTacWhileDoStatement (Abs.WhileStateSimpleDo res expr stat) n l k (w,j) = let guardExpr = (genTacExpression expr n l k (w,j) res) in 
                                                                                let exprTac = sel1 guardExpr in
                                                                                    let guardLab = newLabel "guard" (sel3 guardExpr) in
                                                                                        let nextLab = newLabel "next" ((sel3 guardExpr)+1) in
                                                                                            let statement = (genTacStatement stat (sel2 guardExpr) l ((sel3 guardExpr)+2) (nextLab,guardLab) res) in 
                                                                                                let statTac = sel1 statement in 
                                                                                                    let exprAddr = sel4 guardExpr in
                                                                                                        ((Abs.WhileStateSimpleDo (mergeTacs [(TAC [TacJump guardLab,TacLabel l] []),        -- jump to guard label + body label
                                                                                                                                             (statement_content statTac),                   -- body code tac
                                                                                                                                             (TAC [TacLabel guardLab] []),                  -- guard label
                                                                                                                                             (expression_content exprTac),                  -- code for guard expression eval.
                                                                                                                                             (TAC [TacConditionalJump l True exprAddr] []),    -- conditional jump on guard tac
                                                                                                                                             (TAC [TacLabel nextLab] [])])                     -- next (end of while block) label
                                                                                                                                             exprTac statTac), sel2 statement, sel3 statement)
genTacWhileDoStatement (Abs.WhileStateSimpleWDo res expr b@(Abs.BlockStatement _ statements)) n l k (w,j) = let guardExpr = (genTacExpression expr n l k (w,j) res) in 
                                                                                                                let exprTac = sel1 guardExpr in
                                                                                                                    let guardLab = newLabel "guard" (sel3 guardExpr) in
                                                                                                                        let nextLab = newLabel "next" ((sel3 guardExpr)+1) in
                                                                                                                            let stats = (genTacStatements statements (sel2 guardExpr) l ((sel3 guardExpr)+2) (nextLab,guardLab)) in 
                                                                                                                                let statsTac = sel1 stats in 
                                                                                                                                    let exprAddr = sel4 guardExpr in
                                                                                                                                        ((Abs.WhileStateSimpleWDo (mergeTacs [(TAC [TacJump guardLab,TacLabel l] []),     -- jump to guard label + body label   
                                                                                                                                                                              (statements_content statsTac),              -- body code tac
                                                                                                                                                                              (TAC [TacLabel guardLab] []),               -- guard label
                                                                                                                                                                              (expression_content exprTac),               -- code for guard expression eval.
                                                                                                                                                                              (TAC [TacConditionalJump l True exprAddr] []), -- conditional jump on guard tac       
                                                                                                                                                                              (TAC [TacLabel nextLab] [])])                  -- next (end of while block) label
                                                                                                                                                                              exprTac (Abs.BlockStatement (TAC [] []) statsTac)),sel2 stats, sel3 stats)
genTacWhileDoStatement (Abs.WhileStateCtrlDo res ctrlState state) n l k (w,j)  = let ctrlStatement = genTacControlStatement ctrlState n l k (w,j) in
                                                                                    let guardLab = l in -- continue will jump directly to code label because guard is not present (it's true or while is ignored (when ctrl decl is false no tac is generated))
                                                                                        let nextLab = newLabel "next" (sel3 ctrlStatement) in 
                                                                                            let statTac = genTacStatement state (sel2 ctrlStatement) l ((sel3 ctrlStatement)+1) (nextLab,guardLab) res in
                                                                                                let flagValue = checkControlDeclarationStatement ctrlState in -- parte di funzioni tac da propagare
                                                                                                    let tac = case flagValue of
                                                                                                                False -> (TAC [] [])
                                                                                                                True  -> (mergeTacs [(ctrldecstatement_content (sel1 ctrlStatement)),
                                                                                                                                     (TAC [TacComment "CtrlDeclStat was valid; guard is set to True (break statements are the only way to exit the loop!)",TacLabel l] []),  -- body label
                                                                                                                                     (statement_content (sel1 statTac)),   -- Tac of body code (if no break: DEADLOCK)
                                                                                                                                     (TAC [TacJump l,TacComment "Guard is set to True, there are no exit conditions to be evaluated!"] []), -- jump to code: loop
                                                                                                                                     (TAC [TacLabel nextLab] [])])          -- next lab (for break jumps)
                                                                                                                    in ((Abs.WhileStateCtrlDo tac (sel1 ctrlStatement) (sel1 statTac)),if flagValue then (sel2 statTac) else n, if flagValue then (sel3 statTac) else k) -- TODO COUNTERS TO CHECK
genTacWhileDoStatement (Abs.WhileStateCtrlWDo res ctrlState b@(Abs.BlockStatement _ statements)) n l k (w,j) = let ctrlStatement = genTacControlStatement ctrlState n l k (w,j) in
                                                                                                                let guardLab = l in -- continue will jump directly to code label because guard is not present (it's true or while is ignored (when ctrl decl is false no tac is generated))
                                                                                                                    let nextLab = newLabel "next" (sel3 ctrlStatement) in 
                                                                                                                        let statsTac = genTacStatements statements (sel2 ctrlStatement) l ((sel3 ctrlStatement)+1) (nextLab,guardLab) in
                                                                                                                            let flagValue = checkControlDeclarationStatement ctrlState in -- parte di funzioni tac da propagare
                                                                                                                                let tac = case flagValue of
                                                                                                                                            False -> (TAC [] [])
                                                                                                                                            True  -> (mergeTacs [(ctrldecstatement_content (sel1 ctrlStatement)),
                                                                                                                                                                 (TAC [TacComment "CtrlDeclStat was valid; guard is set to True (break statements are the only way to exit the loop!)",TacLabel l] []),  -- body label
                                                                                                                                                                 (statements_content (sel1 statsTac)),   -- Tac of body code (if no break: DEADLOCK)
                                                                                                                                                                 (TAC [TacJump l,TacComment "Guard is set to True, there are no exit conditions to be evaluated!"] []), -- jump to code: loop
                                                                                                                                                                 (TAC [TacLabel nextLab] [])])           -- next lab (for break jumps)
                                                                                                                                                in ((Abs.WhileStateCtrlWDo tac (sel1 ctrlStatement) (Abs.BlockStatement (TAC [] []) (sel1 statsTac))),if flagValue then (sel2 statsTac) else n, if flagValue then (sel3 statsTac) else k) -- TODO COUNTERS TO CHECK

genTacDoWhileStatement :: Abs.DOSTATEMENT TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.DOSTATEMENT TAC, Prelude.Integer, Prelude.Integer)
genTacDoWhileStatement (Abs.DoWhileState res stat expr) n l k (w,j) = let guardLab = newLabel "guard" k in
                                                                        let nextLab = newLabel "next" (k+1) in                              
                                                                            let statement = (genTacStatement stat n l (k+2) (nextLab,guardLab) res) in
                                                                                let guardExpr = (genTacExpression expr (sel2 statement) l (sel3 statement) (w,j) res) in 
                                                                                    let statTac = sel1 statement in 
                                                                                        let exprTac = sel1 guardExpr in
                                                                                            let exprAddr = sel4 guardExpr in
                                                                                                ((Abs.DoWhileState (mergeTacs [(TAC [TacLabel l] []),                       -- body label 
                                                                                                                               (statement_content statTac),                 -- body tac code (must be executed at least once in do-while blocks)
                                                                                                                               (expression_content exprTac),                -- code for guard expression eval.
                                                                                                                               (TAC [TacLabel guardLab] []),                   -- guard label
                                                                                                                               (TAC [TacConditionalJump l True exprAddr] []),  -- conditional jump on guard tac.
                                                                                                                               (TAC [TacLabel nextLab] [])])                   -- next (end of do-while block) label
                                                                                                                               statTac exprTac),sel2 guardExpr, sel3 guardExpr)

genTacBlock :: Abs.B TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.B TAC,Prelude.Integer,Prelude.Integer)
genTacBlock (Abs.BlockStatement res statements) n l k (w,j) = let statsTac = genTacStatements statements n l k (w,j) in ((Abs.BlockStatement (statements_content (sel1 statsTac)) (sel1 statsTac)),(sel2 statsTac),(sel3 statsTac))

genTacConditionalStatement :: Abs.CONDITIONALSTATE TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.CONDITIONALSTATE TAC,Prelude.Integer,Prelude.Integer)
genTacConditionalStatement (Abs.ConditionalStatementSimpleThen res exp state elseState) n l k (w,j) = let expTac = genTacExpression exp n l k (w,j) res in -- res è il giusto tcheck? TODO
                                                                                                        let statTac = genTacStatement state (sel2 expTac) l (sel3 expTac) (w,j) res in                
                                                                                                            let expAddr = sel4 expTac in
                                                                                                                let statAddr = sel4 statTac in -- SERVE? TODO
                                                                                                                    case elseState of 
                                                                                                                        -- if EXPR then CODE
                                                                                                                        (Abs.ElseStateEmpty _)  -> ((Abs.ConditionalStatementSimpleThen (mergeTacs [(expression_content (sel1 expTac)),             -- guard code eval. tac
                                                                                                                                                                                                    (TAC [TacConditionalJump l False expAddr] []),     -- conditional jump if-false on guard
                                                                                                                                                                                                    (statement_content (sel1 statTac)),             -- if_true code
                                                                                                                                                                                                    (TAC [TacLabel l] [])])                            -- if_false label jump (guard jump destination)
                                                                                                                                                                                                    (sel1 expTac) (sel1 statTac) (Abs.ElseStateEmpty (TAC [] []))),(sel2 statTac),(sel3 statTac)) 
                                                                                                                        -- if EXPR then CODE else CODE  
                                                                                                                        (Abs.ElseState _ elsestats) -> let elseStatesTac = genTacStatement elsestats (sel2 statTac) l (sel3 statTac) (w,j) res in
                                                                                                                                                            let nextLab = newLabel "next" (sel3 elseStatesTac) in
                                                                                                                                                                ((Abs.ConditionalStatementSimpleThen (mergeTacs [(expression_content (sel1 expTac)),            -- guard code eval. tac
                                                                                                                                                                                                                (TAC [TacConditionalJump l False expAddr] []),     -- conditional jump if-false on guard
                                                                                                                                                                                                                (statement_content (sel1 statTac)),             -- if_true code
                                                                                                                                                                                                                (TAC [TacJump nextLab] []),                        -- jump to end of if label (next label)
                                                                                                                                                                                                                (TAC [TacLabel l] []),                             -- if_false label jump (guard jump destination)
                                                                                                                                                                                                                (statement_content (sel1 elseStatesTac)),       -- else code tac
                                                                                                                                                                                                                (TAC [TacLabel nextLab] [])])                      -- next (end of if) label
                                                                                                                                                                                                                (sel1 expTac) (sel1 statTac) (Abs.ElseState (TAC [] []) (sel1 elseStatesTac)),(sel2 elseStatesTac),(sel3 elseStatesTac)+1)) -- if expr then ... else ...
genTacConditionalStatement (Abs.ConditionalStatementSimpleWThen res exp b@(Abs.BlockStatement _ statements) elseState) n l k (w,j)  = let expTac = genTacExpression exp n l k (w,j) res in -- res è il giusto tcheck? TODO
                                                                                                                                        let statTacs = genTacStatements statements (sel2 expTac) l (sel3 expTac) (w,j) in
                                                                                                                                            let expAddr = sel4 expTac in 
                                                                                                                                                case elseState of
                                                                                                                                                    (Abs.ElseStateEmpty _)      -> ((Abs.ConditionalStatementSimpleWThen (mergeTacs [(expression_content (sel1 expTac)), -- same as previous cases, but syntax has blocks!
                                                                                                                                                                                                                                     (TAC [TacConditionalJump l False expAddr] []),
                                                                                                                                                                                                                                     (statements_content (sel1 statTacs)),
                                                                                                                                                                                                                                     (TAC [TacLabel l] [])])
                                                                                                                                                                                                                                     (sel1 expTac) (Abs.BlockStatement (TAC [] []) (sel1 statTacs)) (Abs.ElseStateEmpty (TAC [] []))),(sel2 statTacs),(sel3 statTacs))   -- if expr then ...
                                                                                                                                                    (Abs.ElseState _ elsestats) -> let elseStatesTac = genTacStatement elsestats (sel2 statTacs) l (sel3 statTacs) (w,j) res in
                                                                                                                                                                                            let nextLab = newLabel "next" (sel3 elseStatesTac) in
                                                                                                                                                                                                ((Abs.ConditionalStatementSimpleWThen (mergeTacs [(expression_content (sel1 expTac)), -- same as previous cases, but syntax has blocks!
                                                                                                                                                                                                                                                  (TAC [TacConditionalJump l False expAddr] []),
                                                                                                                                                                                                                                                  (statements_content (sel1 statTacs)),
                                                                                                                                                                                                                                                  (TAC [TacJump nextLab] []),
                                                                                                                                                                                                                                                  (TAC [TacLabel l] []), (statement_content (sel1 elseStatesTac)),
                                                                                                                                                                                                                                                  (TAC [TacLabel nextLab] [])])
                                                                                                                                                                                                                                                  (sel1 expTac) (Abs.BlockStatement (TAC [] []) (sel1 statTacs)) (Abs.ElseState (TAC [] []) (sel1 elseStatesTac)),(sel2 elseStatesTac),(sel3 elseStatesTac)+1)) -- if expr then ... else ...
genTacConditionalStatement (Abs.ConditionalStatementCtrlThen res ctrlState state elseState) n l k (w,j) =   let ctrlStatement = genTacControlStatement ctrlState n l (k-1) (w,j) in
                                                                                                                let statTac = genTacStatement state (sel2 ctrlStatement) l (sel3 ctrlStatement) (w,j) res in
                                                                                                                    let flagValue = checkControlDeclarationStatement ctrlState in   -- get the result of the control declaration statement! valid declaration = true; invalid declaration = false flag!
                                                                                                                        case elseState of                                           -- We already know at COMPILE-TIME which code block (then or else) will be executed; there's no need of jumps
                                                                                                                            -- if CTRLDECL FLAG then CODE                           -- We ignore else code if the ctrl declaration was valid, and the opposite!
                                                                                                                            (Abs.ElseStateEmpty _)  -> let tac = case flagValue of
                                                                                                                                                                    True  -> TAC ((code (ctrldecstatement_content (sel1 ctrlStatement))) ++ [TacComment "CtrlDeclStat was valid; else code is ignored."] ++ (code (statement_content (sel1 statTac)))) [] -- we know then_code must be executed, tac = ctrldecl tac + tac of then block
                                                                                                                                                                    False -> TAC [] [] -- we know that else_code must be executed but else is empty! tac = empty
                                                                                                                                                                        in ((Abs.ConditionalStatementCtrlThen tac (sel1 ctrlStatement) (sel1 statTac) (Abs.ElseStateEmpty (TAC [] []))),if flagValue then (sel2 statTac) else (sel2 ctrlStatement),if flagValue then (sel3 statTac) else (sel3 ctrlStatement)) -- if ... then ...
                                                                                                                            -- if CTRLDECL FLAG then CODE else CODE  
                                                                                                                            (Abs.ElseState _ elsestats) -> let elseStatesTac = genTacStatement elsestats (if flagValue then (sel2 statTac) else (sel2 ctrlStatement)) l (if flagValue then (sel3 statTac) else (sel3 ctrlStatement)) (w,j) res in
                                                                                                                                                                let nextLab = newLabel "next" (sel3 elseStatesTac) in
                                                                                                                                                                    let tac = case flagValue of
                                                                                                                                                                                True  -> TAC ((code (ctrldecstatement_content (sel1 ctrlStatement))) ++ [TacComment "CtrlDeclStat was valid; else code is ignored."] ++ (code (statement_content (sel1 statTac)))) [] -- we know then_code  must be executed, tac = ctrldecl tac + tac of then block
                                                                                                                                                                                False -> TAC ((code (ctrldecstatement_content (sel1 ctrlStatement))) ++ [TacComment "CtrlDeclStat was invalid; then code is ignored."] ++ (code (statement_content (sel1 elseStatesTac)))) [] -- we know else_code must be executed, tac = ctrldecl tac + tac of else block
                                                                                                                                                                                            in ((Abs.ConditionalStatementCtrlThen tac (sel1 ctrlStatement) (sel1 statTac) (Abs.ElseState (TAC [] []) (sel1 elseStatesTac)),if flagValue then (sel2 statTac) else (sel2 elseStatesTac),if flagValue then (sel3 statTac) else (sel3 elseStatesTac)+1)) -- if expr then ... else ...        
genTacConditionalStatement (Abs.ConditionalStatementCtrlWThen res ctrlState b@(Abs.BlockStatement _ states) elseState) n l k (w,j)    = let ctrlStatement = genTacControlStatement ctrlState n l (k-1) (w,j) in
                                                                                                                                            let statsTac = genTacStatements states (sel2 ctrlStatement) l (sel3 ctrlStatement) (w,j) in
                                                                                                                                                let flagValue = checkControlDeclarationStatement ctrlState in   -- get the result of the control declaration statement! valid declaration = true; invalid declaration = false flag!
                                                                                                                                                    case elseState of                                           -- We already know at COMPILE-TIME which code block (then or else) will be executed; there's no need of jumps
                                                                                                                                                        -- if CTRLDECL FLAG then CODE                           -- We ignore else code if the ctrl declaration was valid, and the opposite!
                                                                                                                                                        (Abs.ElseStateEmpty _)  -> let tac = case flagValue of
                                                                                                                                                                                                True  -> TAC ((code (ctrldecstatement_content (sel1 ctrlStatement))) ++ [TacComment "CtrlDeclStat was valid; else code is ignored."] ++ (code (statements_content (sel1 statsTac)))) [] -- we know then_code must be executed, tac = ctrldecl tac + tac of then block
                                                                                                                                                                                                False -> TAC [] [] -- we know that else_code must be executed but else is empty! tac = empty
                                                                                                                                                                                                    in ((Abs.ConditionalStatementCtrlWThen tac (sel1 ctrlStatement) (Abs.BlockStatement (TAC [] []) (sel1 statsTac)) (Abs.ElseStateEmpty (TAC [] []))),if flagValue then (sel2 statsTac) else (sel2 ctrlStatement),if flagValue then (sel3 statsTac) else (sel3 ctrlStatement)) -- if ... then ...
                                                                                                                                                        -- if CTRLDECL FLAG then CODE else CODE  
                                                                                                                                                        (Abs.ElseState _ elsestats) -> let elseStatesTac = genTacStatement elsestats (if flagValue then (sel2 statsTac) else (sel2 ctrlStatement)) l (if flagValue then (sel3 statsTac) else (sel3 ctrlStatement)) (w,j) res in
                                                                                                                                                                                            let nextLab = newLabel "next" (sel3 elseStatesTac) in
                                                                                                                                                                                                let tac = case flagValue of
                                                                                                                                                                                                            True  -> TAC ((code (ctrldecstatement_content (sel1 ctrlStatement))) ++ [TacComment "CtrlDeclStat was valid; else code is ignored."]  ++ (code (statements_content (sel1 statsTac)))) [] -- we know then_code  must be executed, tac = ctrldecl tac + tac of then block
                                                                                                                                                                                                            False -> TAC ((code (ctrldecstatement_content (sel1 ctrlStatement))) ++ [TacComment "CtrlDeclStat was invalid; then code is ignored."] ++ (code (statement_content (sel1 elseStatesTac)))) [] -- we know else_code must be executed, tac = ctrldecl tac + tac of else block
                                                                                                                                                                                                                        in ((Abs.ConditionalStatementCtrlWThen tac (sel1 ctrlStatement) (Abs.BlockStatement (TAC [] []) (sel1 statsTac)) (Abs.ElseState (TAC [] []) (sel1 elseStatesTac)),if flagValue then (sel2 statsTac) else (sel2 elseStatesTac),if flagValue then (sel3 statsTac) else (sel3 elseStatesTac)+1)) -- if expr then ... else ...        

genTacControlStatement :: Abs.CTRLDECSTATEMENT TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) ->  (Abs.CTRLDECSTATEMENT TAC,Prelude.Integer,Prelude.Integer)
genTacControlStatement (Abs.CtrlDecStateVar res@(TResult _ ty _) ident@(Abs.Ident id resi@(TResult _ _ pos)) typepart@(Abs.TypePart (TResult _ typePart _) _) expr) n l k (w,j) = case ty of 
                                                                                                                                            B_type Type_Void -> let expression = genTacExpression expr n l k (w,j) res in 
                                                                                                                                                                    ((Abs.CtrlDecStateVar (TAC [TacAssignNullOp (buildIDAddr pos id) (genDefaultInitAddr typePart) typePart]    -- the ctrl decl statement was invalid; so ctrl var is initialized with default value
                                                                                                                                                                                                []) (Abs.Ident id (TAC [] [])) (Abs.TypePart (TAC [] []) (Abs.TypeExpression (TAC [] []) (Abs.PrimitiveTypeVoid (TAC [] [])))) (sel1 expression)),(sel2 expression),(sel3 expression))  -- it wasn't a correct ctrldecl assignment! so initialize at def. value!
                                                                                                                                            _                -> let expression = genTacExpression expr n l k (w,j) res in
                                                                                                                                                                    let exprAddr = sel4 expression in
                                                                                                                                                                        ((Abs.CtrlDecStateVar (TAC (code (expression_content (sel1 expression)) ++              -- tac code of rval expr evaluation
                                                                                                                                                                                                   [TacAssignNullOp (buildIDAddr pos id) exprAddr ty])         -- the ctrl decl statement was valid; so ctrl var is initialized with the initialization expr. value
                                                                                                                                                                                                   []) (Abs.Ident id (TAC [] [])) (Abs.TypePart (TAC [] []) (Abs.TypeExpression (TAC [] []) (Abs.PrimitiveTypeVoid (TAC [] [])))) (sel1 expression)),(sel2 expression),(sel3 expression))  -- it was a correct ctrldecl assignment
                                                                                                                                                                                                   
                                                                                                                                                                                                   
genTacControlStatement (Abs.CtrlDecStateConst res@(TResult _ ty _) ident@(Abs.Ident id resi@(TResult _ _ pos)) typepart@(Abs.TypePart (TResult _ typePart _) _) expr) n l k (w,j) = case ty of
                                                                                                                                            B_type Type_Void -> let expression = genTacExpression expr n l k (w,j) res in 
                                                                                                                                                                ((Abs.CtrlDecStateConst (TAC [TacAssignNullOp (buildIDAddr pos id) (genDefaultInitAddr typePart) typePart]    -- the ctrl decl statement was invalid; so ctrl var is initialized with default value
                                                                                                                                                                                            []) (Abs.Ident id (TAC [] [])) (Abs.TypePart (TAC [] []) (Abs.TypeExpression (TAC [] []) (Abs.PrimitiveTypeVoid (TAC [] [])))) (sel1 expression)),(sel2 expression),(sel3 expression))  -- it wasn't a correct ctrldecl assignment! so initialize at def. value!
                                                                                                                                            _                -> let expression = genTacExpression expr n l k (w,j) res in
                                                                                                                                                                    let exprAddr = sel4 expression in
                                                                                                                                                                        ((Abs.CtrlDecStateConst (TAC (code (expression_content (sel1 expression)) ++              -- tac code of rval expr evaluation
                                                                                                                                                                                                   [TacAssignNullOp (buildIDAddr pos id) exprAddr ty])         -- the ctrl decl statement was valid; so ctrl var is initialized with the initialization expr. value
                                                                                                                                                                                                   []) (Abs.Ident id (TAC [] [])) (Abs.TypePart (TAC [] []) (Abs.TypeExpression (TAC [] []) (Abs.PrimitiveTypeVoid (TAC [] [])))) (sel1 expression)),(sel2 expression),(sel3 expression))  -- it was a correct ctrldecl assignment                                                                    

checkControlDeclarationStatement :: Abs.CTRLDECSTATEMENT TCheckResult -> Prelude.Bool
checkControlDeclarationStatement (Abs.CtrlDecStateVar res@(TResult _ ty _) _ _ _) = case ty of 
                                                                                    B_type Type_Void -> False   -- if it wasn't a correct assignement (var x:int = "string") then void is returned, so the flag is false
                                                                                    _ -> True    -- it was a valid assignment, so true is the flag value
checkControlDeclarationStatement (Abs.CtrlDecStateConst res@(TResult _ ty _) _ _ _) = case ty of
                                                                                    B_type Type_Void -> False  -- if it wasn't a correct assignement (var x:int = "string") then void is returned, so the flag is false
                                                                                    _ -> True    -- it was a valid assignment, so true is the flag value

genTacVariableType :: Abs.VARIABLETYPE TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) ->  (Abs.VARIABLETYPE TAC,Prelude.Integer,Prelude.Integer,Address)
genTacVariableType (Abs.VariableTypeParam res) n l k (w,j)      = (Abs.VariableTypeParam    (TAC [] []),n,k,AddrNULL)
genTacVariableType (Abs.VariableTypeConst res) n l k (w,j)      = (Abs.VariableTypeConst    (TAC [] []),n,k,AddrNULL)
genTacVariableType (Abs.VariableTypeVar res) n l k (w,j)        = (Abs.VariableTypeVar      (TAC [] []),n,k,AddrNULL)
genTacVariableType (Abs.VariableTypeRef res) n l k (w,j)        = (Abs.VariableTypeRef      (TAC [] []),n,k,AddrNULL)
genTacVariableType (Abs.VariableTypeConstRef res) n l k (w,j)   = (Abs.VariableTypeConstRef (TAC [] []),n,k,AddrNULL)

genTacVarDecList :: Abs.VARDECLIST TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> TCheckResult -> (Abs.VARDECLIST TAC,Prelude.Integer,Prelude.Integer,[Address],Address)
genTacVarDecList (Abs.VariableDeclarationSingle res vardecId) n l k (w,j) tres = let vardecIdTac = genTacVarDecId vardecId n l k (w,j) tres in
                                                                            let vardecIdAddr = sel4 vardecIdTac in
                                                                                let initAddr = sel5 vardecIdTac in
                                                                                (Abs.VariableDeclarationSingle (vardecid_content (sel1 vardecIdTac)) (sel1 vardecIdTac),(sel2 vardecIdTac),(sel3 vardecIdTac),vardecIdAddr,initAddr)

genTacVarDecId :: Abs.VARDECID TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> TCheckResult -> (Abs.VARDECID TAC,Prelude.Integer,Prelude.Integer,[Address],Address)
genTacVarDecId (Abs.VariableDeclaration res@(TResult _ ty _) idlist typepart initpart) n l k (w,j) tres = case initpart of
                                                                            Abs.InitializzationPartEmpty resi -> let idlistTac = genTacIdentifierList idlist n l k (w,j) tres in
                                                                                                                    let tacId = identlist_content (sel1 idlistTac) in
                                                                                                                        let addrIdList = sel4 idlistTac in
                                                                                                                            let initAddr = AddrNULL in
                                                                                                                                (Abs.VariableDeclaration tacId (sel1 idlistTac) (Abs.TypePart (TAC [] []) (TypeExpression (TAC [] []) (Abs.PrimitiveTypeInt (TAC [] [])))) (Abs.InitializzationPartEmpty (TAC [] [])),(sel2 idlistTac),(sel3 idlistTac),addrIdList,initAddr)
                                                                            Abs.InitializzationPart resi expr -> let idlistTac = genTacIdentifierList idlist n l k (w,j) tres in
                                                                                                                    let tacId = identlist_content (sel1 idlistTac) in
                                                                                                                        let addrIdList = sel4 idlistTac in
                                                                                                                            let exprTac = (genTacExpression expr (sel2 idlistTac) l (sel3 idlistTac) (w,j) tres) in
                                                                                                                                let initTac = (Abs.InitializzationPart (expression_content (sel1 exprTac)) (sel1 exprTac)) in
                                                                                                                                    let initAddr = sel4 exprTac in
                                                                                                                                        (Abs.VariableDeclaration (expression_content (sel1 exprTac)) (sel1 idlistTac) (Abs.TypePart (TAC [] []) (TypeExpression (TAC [] []) (Abs.PrimitiveTypeInt (TAC [] [])))) initTac ,(sel2 exprTac),(sel3 exprTac),addrIdList,initAddr)
                                                                                --InitializzationPartArray resi array -> 

genTacExpression :: Abs.EXPRESSION TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> TCheckResult -> (Abs.EXPRESSION TAC,Prelude.Integer,Prelude.Integer,Address)
genTacExpression (Abs.ExpressionInteger res value@(Abs.Integer val resi))       n l k (w,j) tres = (Abs.ExpressionInteger (TAC [] []) (Abs.Integer val (TAC [] []))  ,n,k, AddrInt val)
genTacExpression (Abs.ExpressionBoolean res value@(Abs.Boolean_true resi))      n l k (w,j) tres = (Abs.ExpressionBoolean (TAC [] []) (Abs.Boolean_true (TAC [] [])) ,n,k, AddrBool True)
genTacExpression (Abs.ExpressionBoolean res value@(Abs.Boolean_false resi))     n l k (w,j) tres = (Abs.ExpressionBoolean (TAC [] []) (Abs.Boolean_false (TAC [] [])),n,k, AddrBool False)
genTacExpression (Abs.ExpressionBoolean res value@(Abs.Boolean_True resi))      n l k (w,j) tres = (Abs.ExpressionBoolean (TAC [] []) (Abs.Boolean_True (TAC [] [])) ,n,k, AddrBool True)
genTacExpression (Abs.ExpressionBoolean res value@(Abs.Boolean_False resi))     n l k (w,j) tres = (Abs.ExpressionBoolean (TAC [] []) (Abs.Boolean_False (TAC [] [])),n,k, AddrBool False)
genTacExpression (Abs.ExpressionChar res value@(Abs.Char val resi))             n l k (w,j) tres = (Abs.ExpressionChar    (TAC [] []) (Abs.Char val (TAC [] []))     ,n,k, AddrChar val)
genTacExpression (Abs.ExpressionString res value@(Abs.String val resi))         n l k (w,j) tres = (Abs.ExpressionString  (TAC [] []) (Abs.String val (TAC [] []))   ,n,k, AddrString val)
genTacExpression (Abs.ExpressionReal res value@(Abs.Real val resi))             n l k (w,j) tres = (Abs.ExpressionReal    (TAC [] []) (Abs.Real val (TAC [] []))     ,n,k, AddrReal val)
genTacExpression (Abs.ExpressionBracket res exp)                                n l k (w,j) tres = let exprTac = genTacExpression exp n l k (w,j) tres in (Abs.ExpressionBracket (expression_content (sel1 exprTac)) (sel1 exprTac),(sel2 exprTac),(sel3 exprTac),(sel4 exprTac))
{-genTacExpression (Abs.ExpressionCast res def tipo)  =-}   
genTacExpression (Abs.ExpressionUnary res@(TResult env ty pos) unary def)       n l k (w,j) tres = let defTac = genTacDefault def (n+1) l k (w,j) tres in 
                                                                                                let defAddr = sel4 defTac in
                                                                                                    let temp = newTemp n in
                                                                                                        case unary of 
                                                                                                            UnaryOperationPositive _ -> (Abs.ExpressionUnary (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Pos defAddr ty] [])  ) (Abs.UnaryOperationPositive (TAC [] [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp) 
                                                                                                            UnaryOperationNegative _ -> (Abs.ExpressionUnary (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Neg defAddr ty] [])  ) (Abs.UnaryOperationNegative (TAC [] [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp) 
                                                                                                            UnaryOperationNot      _ -> (Abs.ExpressionUnary (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Not defAddr ty] [])  ) (Abs.UnaryOperationNot (TAC [] [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp) 
                                                                                                            UnaryOperationPointer  _ -> (Abs.ExpressionUnary (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Point defAddr ty] [])) (Abs.UnaryOperationPointer (TAC [] [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp)
genTacExpression (Abs.ExpressionBinaryPlus res@(TResult env t pos) expr1 expr2) n l k (w,j) tres = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryPlus (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "plus") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryMinus res@(TResult env t pos) expr1 expr2) n l k (w,j) tres = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryMinus (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "minus") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryProduct res@(TResult env t pos) expr1 expr2) n l k (w,j) tres = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryProduct (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "product") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryDivision res@(TResult env t pos) expr1 expr2) n l k (w,j) tres = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryDivision (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "division") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryModule res@(TResult env t pos) expr1 expr2) n l k (w,j) tres = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryModule (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "module") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryPower res@(TResult env t pos) expr1 expr2) n l k (w,j) tres = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryPower (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "power") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryAnd res@(TResult env t pos) expr1 expr2) n l k (w,j) tres = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryAnd (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "and") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryOr res@(TResult env t pos) expr1 expr2) n l k (w,j) tres = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryOr (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "or") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryEq res@(TResult env t pos) expr1 expr2) n l k (w,j) tres = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryEq (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "eq") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)                                                                                                    
genTacExpression (Abs.ExpressionBinaryNotEq res@(TResult env t pos) expr1 expr2) n l k (w,j) tres = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryNotEq (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "noteq") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)                                                                                                    
genTacExpression (Abs.ExpressionBinaryGratherEq res@(TResult env t pos) expr1 expr2) n l k (w,j) tres = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryGratherEq (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "grathereq") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)                                                                                                    
genTacExpression (Abs.ExpressionBinaryGrather res@(TResult env t pos) expr1 expr2) n l k (w,j) tres = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryGrather (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "grather") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)                                                                                                    
genTacExpression (Abs.ExpressionBinaryLessEq res@(TResult env t pos) expr1 expr2) n l k (w,j) tres = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryLessEq (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "lesseq") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)                                                                                                    
genTacExpression (Abs.ExpressionBinaryLess res@(TResult env t pos) expr1 expr2) n l k (w,j) tres = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryLess (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "less") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)                                                                                                    

genTacExpression (Abs.ExpressionIdent res ident@(Abs.Ident id resi@(TResult env t pos)) index) n l k (w,j) tres = case Data.Map.lookup id env of
                                                                                                                  Just [Variable _ posv _ _] -> case index of -- gestire tutti icasi TODO 
                                                                                                                                                (Abs.ArrayIndexElementEmpty _) -> ((Abs.ExpressionIdent (TAC [] []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElementEmpty (TAC [] []))),n,k,buildIDAddr posv id)
                                                                                                                                                -- _ -> it is array
--genTacExpression (Abs.ExpressionCall res id exps) = ident@(Abs.Ident id resi)) n l k (w,j) tres       = 

genTacDefault :: Abs.DEFAULT TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> TCheckResult -> (Abs.DEFAULT TAC,Prelude.Integer,Prelude.Integer,Address)
genTacDefault (Abs.ExpressionIntegerD res value@(Abs.Integer val resi))       n l k (w,j) tres = (Abs.ExpressionIntegerD (TAC [] []) (Abs.Integer val (TAC [] [])),n,k, AddrInt val)
genTacDefault (Abs.ExpressionBooleanD res value@(Abs.Boolean_true resi))      n l k (w,j) tres = (Abs.ExpressionBooleanD (TAC [] []) (Abs.Boolean_true (TAC [] [])),n,k, AddrBool True)
genTacDefault (Abs.ExpressionBooleanD res value@(Abs.Boolean_false resi))     n l k (w,j) tres = (Abs.ExpressionBooleanD (TAC [] []) (Abs.Boolean_false (TAC [] [])),n,k, AddrBool False)
genTacDefault (Abs.ExpressionBooleanD res value@(Abs.Boolean_True resi))      n l k (w,j) tres = (Abs.ExpressionBooleanD (TAC [] []) (Abs.Boolean_True (TAC [] [])),n,k, AddrBool True)
genTacDefault (Abs.ExpressionBooleanD res value@(Abs.Boolean_False resi))     n l k (w,j) tres = (Abs.ExpressionBooleanD (TAC [] []) (Abs.Boolean_False (TAC [] [])),n,k, AddrBool False)
genTacDefault (Abs.ExpressionCharD res value@(Abs.Char val resi))             n l k (w,j) tres = (Abs.ExpressionCharD (TAC [] []) (Abs.Char val (TAC [] [])),n,k, AddrChar val)
genTacDefault (Abs.ExpressionStringD res value@(Abs.String val resi))         n l k (w,j) tres = (Abs.ExpressionStringD (TAC [] []) (Abs.String val (TAC [] [])),n,k, AddrString val)
genTacDefault (Abs.ExpressionRealD res value@(Abs.Real val resi))             n l k (w,j) tres = (Abs.ExpressionRealD (TAC [] []) (Abs.Real val (TAC [] [])),n,k, AddrReal val)
genTacDefault (Abs.ExpressionBracketD res exp)                                n l k (w,j) tres = let exprTac = genTacExpression exp n l k (w,j) tres in (Abs.ExpressionBracketD (expression_content (sel1 exprTac)) (sel1 exprTac),(sel2 exprTac),(sel3 exprTac), (sel4 exprTac))
{-genTacDefault (Abs.ExpressionCastD res def tipo)  = -}  
genTacDefault (Abs.ExpressionUnaryD res@(TResult env ty pos) unary def)       n l k (w,j) tres = let defTac = genTacDefault def (n+1) l k (w,j) tres in 
                                                                                            let temp = newTemp n in
                                                                                                case def of
                                                                                                    --Abs.ExpressionCastD res def tipo   
                                                                                                    --Abs.ExpressionUnaryD res@(TResult env ty pos) unary def
                                                                                                    --Abs.ExpressionIdentD res id index
                                                                                                    --Abs.ExpressionCallD res id exps
                                                                                                    _ -> case unary of 
                                                                                                            UnaryOperationPositive _ -> (Abs.ExpressionUnaryD (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Pos (sel4 defTac) ty] [])) (Abs.UnaryOperationPositive (TAC [] [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp) 
                                                                                                            UnaryOperationNegative _ -> (Abs.ExpressionUnaryD (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Neg (sel4 defTac) ty] [])) (Abs.UnaryOperationNegative (TAC [] [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp) 
                                                                                                            UnaryOperationNot      _ -> (Abs.ExpressionUnaryD (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Not (sel4 defTac) ty] [])) (Abs.UnaryOperationNot (TAC [] [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp) 
                                                                                                            UnaryOperationPointer  _ -> (Abs.ExpressionUnaryD (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Point (sel4 defTac) ty] [])) (Abs.UnaryOperationPointer (TAC [] [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp)
{-genTacDefault (Abs.ExpressionIdentD res id index) =
genTacDefault (Abs.ExpressionCallD res id exps) = -}


genTacIdentifierList :: Abs.IDENTLIST TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> TCheckResult -> (Abs.IDENTLIST TAC,Prelude.Integer,Prelude.Integer,[Address])
genTacIdentifierList (Abs.IdentifierSingle res@(TResult _ _ pos) ident@(Abs.Ident id resi)) n l k (w,j) tres       = (Abs.IdentifierSingle (TAC [] []) (Abs.Ident id (TAC [] [])),n,k,[buildIDAddr pos id])
genTacIdentifierList (Abs.IdentifierList res@(TResult _ _ pos) ident@(Abs.Ident id resi) idlist) n l k (w,j) tres  = let idlistTac = (genTacIdentifierList idlist n l k (w,j) tres) in
                                                                                                                    let idlistAddr = sel4 idlistTac in
                                                                                                                        (Abs.IdentifierList (TAC [] []) (Abs.Ident id (TAC [] [])) (sel1 idlistTac),(sel2 idlistTac),(sel3 idlistTac),[buildIDAddr pos id] ++ idlistAddr)
