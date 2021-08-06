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

-- Touples ------------------------------------------------------------
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
------------------------------------------------------------------------

newLabel :: Prelude.String -> Prelude.Integer -> Label 
newLabel "" n       = Label ("L"++show n)
newLabel "end" n    = Label ("\nend")
newLabel str n      = Label (str ++show n)

newTemp :: Prelude.Integer -> Address
newTemp n = AddrAddress ("t"++show n)

buildIDAddr :: Posn -> Prelude.String -> Address
buildIDAddr posv@(Pn a r c) id = AddrAddress (id++"@"++show r++","++show c)

merge2Tacs :: TAC -> TAC -> TAC
merge2Tacs (TAC []) (TAC []) = TAC []
merge2Tacs (TAC x) (TAC y) = TAC (x++y)

mergeTacs :: [TAC] -> TAC
mergeTacs lst = (TAC (mergeTacFromList_ lst))

mergeTacFromList_ :: [TAC] -> [TACEntry]
mergeTacFromList_ ((TAC entries):xs) = entries ++ mergeTacFromList_ xs
mergeTacFromList_ [] = []

showAddrContent :: Address -> Prelude.String 
showAddrContent (AddrString s) = "\"" ++ s ++ "\""
showAddrContent (AddrInt s) = show s    
showAddrContent (AddrBool s) = show s   
showAddrContent (AddrReal s) = show s   
showAddrContent (AddrChar s) = "\'" ++ show s ++ "\'"    
showAddrContent (AddrAddress s) = s
showAddrContent (AddrNULL) = "NULL"  

getTacEntry :: TAC -> [TACEntry]
getTacEntry (TAC e) = e

removePos :: Prelude.String -> Prelude.String
removePos (x:xs) = if (x=='_') then xs else removePos xs

getListId :: Prelude.String -> Prelude.String -> [Prelude.String] -> [Prelude.String]
getListId [] zs res = [zs]++res
getListId (x:xs) zs res = if (x==',') then getListId xs [] ([zs]++res) else getListId xs (zs++[x]) res

getPos :: Prelude.String  -> Prelude.String -> Prelude.String
getPos (x:xs) zs = if (x=='_') then zs else TacGen.getPos xs ([x]++zs)

buildTacEntriesForVarsDecl :: [Address] -> Address -> Type -> [TACEntry]
buildTacEntriesForVarsDecl [x] rAddr ty = case rAddr of
    AddrNULL -> [TacAssignNullOp x (genDefaultInitAddr ty) ty]
    _ -> [TacAssignNullOp x rAddr ty]
buildTacEntriesForVarsDecl (x:xs) rAddr ty = case rAddr of 
    AddrNULL -> [TacAssignNullOp x (genDefaultInitAddr ty)  ty] ++ buildTacEntriesForVarsDecl xs rAddr ty 
    _ -> [TacAssignNullOp x rAddr ty] ++ buildTacEntriesForVarsDecl xs rAddr ty 

-- 
genDefaultInitAddr :: Type -> Address
genDefaultInitAddr ty = case ty of
    B_type Type_Integer  -> AddrInt 0
    B_type Type_Boolean  -> AddrBool False 
    B_type Type_Char     -> AddrChar ' '
    B_type Type_String   -> AddrString ""   
    B_type Type_Real     -> AddrReal  0.0

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


-- Given the start of a program (starting node Abs.S); starts the TAC generation process
genTAC :: Abs.S TCheckResult -> Abs.S TAC
genTAC (Abs.StartCode tres stats) = let endLab = newLabel "end" 0 in
                                        let statsTac = sel1 (genTacStatements stats 0 endLab 0 endLab) in
                                            let tacs = (statements_content statsTac) in
                                                (Abs.StartCode (TAC ((content tacs)++(TacLabel endLab):[ExitTac])) statsTac)

genTacStatements :: Abs.STATEMENTS TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> Label -> (Abs.STATEMENTS TAC,Prelude.Integer,Prelude.Integer)
genTacStatements (Abs.ListStatements tres stat stats) n l k w = case stats of
                                                                Abs.ListStatements tres _ _ -> let statTac = genTacStatement stat n l k w tres in
                                                                                                    let newC = sel2 statTac in
                                                                                                        let newL = newLabel "" (sel3 statTac) in
                                                                                                            let statsTac = genTacStatements stats newC newL (sel3 statTac) w in
                                                                                                                (Abs.ListStatements (merge2Tacs (statement_content (sel1 statTac)) (statements_content (sel1 statsTac))) (sel1 statTac) (sel1 statsTac),newC,sel3 statTac)
                                                                Abs.EmptyStatement tres -> let statTac = genTacStatement stat n l k w tres in
                                                                                                let newC = sel2 statTac in
                                                                                                    let newL = newLabel "" (sel3 statTac) in
                                                                                                        (Abs.ListStatements (statement_content (sel1 statTac)) (sel1 statTac) (Abs.EmptyStatement (TAC [])),newC,sel3 statTac)
genTacStatements (Abs.EmptyStatement tres) n l k w = ((Abs.EmptyStatement (TAC [])),n,k)

genTacStatement :: Abs.STATEMENT TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> Label -> TCheckResult -> (Abs.STATEMENT TAC,Prelude.Integer,Prelude.Integer,Address)
genTacStatement (Abs.VariableDeclarationStatement res@(TResult _ ty _) tipo vardec) n l k w tres = let tipoTac = genTacVariableType tipo n l k w in
                                                                                                    let tipoContent = variabletype_content (sel1 tipoTac) in
                                                                                                        let vardecTac = genTacVarDecList vardec n l k w tres in
                                                                                                            let vardecContent = vardeclist_content (sel1 vardecTac) in
                                                                                                                let vardecAddrs = sel4 vardecTac in -- variable addresses # >1
                                                                                                                    let initAddr = sel5 vardecTac in
                                                                                                                        (Abs.VariableDeclarationStatement (merge2Tacs (merge2Tacs vardecContent (TAC (buildTacEntriesForVarsDecl vardecAddrs initAddr ty)))
                                                                                                                                                             tipoContent) (sel1 tipoTac) (sel1 vardecTac) ,(sel2 vardecTac),(sel3 vardecTac),AddrNULL)
genTacStatement (Abs.BreakStatement res) n l k w tres               = ((Abs.BreakStatement (TAC [TacJump w,TacComment "break jump"])),n,k,AddrNULL)
{-genTacStatement (Abs.ContinueStatement res)                      = 
genTacStatement (Abs.ReturnStatement res ret)                      =
-} 
genTacStatement (Abs.Statement res block) n l k w tres                 = let newL = newLabel "" (k+1) in 
                                                                            let newC = sel2 (genTacBlock block n newL (k+1) w) in
                                                                                let blockTac = (genTacBlock block n newL (k+1) w) in (Abs.Statement (b_content (sel1 blockTac)) (sel1 blockTac),newC,(sel3 blockTac),AddrNULL) -- Statement {statement_content::a, statement_b::(B a)}
{-
genTacStatement (Abs.ExpressionStatement res exp)                  =
genTacStatement (Abs.AssignmentStatement res lval assignOp exp)    =
genTacStatement (Abs.VariableDeclarationStatement res tipo vardec) = (Abs.VariableDeclarationStatement (TAC []) (genTacVariableDeclarationStatement vardec))-}
genTacStatement (Abs.ConditionalStatement res condition) n l k w tres = let newL = newLabel "else" (k+1) in 
                                                                        let condStatementTac = (genTacConditionalStatement condition n newL (k+1) w) in
                                                                            let newC = sel2 condStatementTac in
                                                                                ((Abs.ConditionalStatement (conditionalstate_content (sel1 condStatementTac)) (sel1 condStatementTac)),newC,(sel3 condStatementTac),AddrNULL)
genTacStatement (Abs.WhileDoStatement res while) n l k w tres         = let newL = newLabel "body" (k+1) in 
                                                                        let whileStatement = (genTacWhileDoStatement while n newL (k+1) w) in
                                                                            let whileStatementTac = sel1 whileStatement in
                                                                                let newC = sel2 whileStatement in
                                                                                    let newK = sel3 whileStatement in
                                                                                        ((Abs.WhileDoStatement (whilestatement_content whileStatementTac) whileStatementTac),newC,newK,AddrNULL) -- null address? TODO
genTacStatement (Abs.DoWhileStatement res doStat) n l k w tres        = let newL = newLabel "body" (k+1) in 
                                                                        let doStatement = (genTacDoWhileStatement doStat n newL (k+1) w) in
                                                                            let doStatementTac = sel1 doStatement in
                                                                                let newC = sel2 doStatement in
                                                                                    let newK = sel3 doStatement in
                                                                                        ((Abs.DoWhileStatement (dostatement_content doStatementTac) doStatementTac),newC,newK,AddrNULL) -- null address? TODO
genTacStatement (Abs.ForStatement res forStat) n l k w tres           = let newL = newLabel "body" (k+1) in
                                                                        let forStatement = (genTacForStatement forStat n newL (k+1) w) in
                                                                            let newC = sel2 forStatement in
                                                                                let newK = sel3 forStatement in
                                                                                    ((Abs.ForStatement (forstatement_content (sel1 forStatement)) (sel1 forStatement)),newC,newK,AddrNULL)
{-genTacStatement (Abs.ProcedureStatement res id param states) n l k w tres      =                                              
genTacStatement (Abs.FunctionStatement res id param tipo states) n l k w tres  =-}

genTacForStatement :: Abs.FORSTATEMENT TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> Label -> (Abs.FORSTATEMENT TAC, Prelude.Integer, Prelude.Integer)
genTacForStatement (Abs.ForStateIndexDo res index@(Abs.IndexVarDeclaration _ ident@(Abs.Ident id resi@(TResult _ _ pos))) rangexp stat) n l k w =
                                                                        let rangeExp = (genTacRangeExpr rangexp n l k w) in -- for range do stats
                                                                            let statement = (genTacStatement stat (sel2 rangeExp) l ((sel3 rangeExp )+1) w res) in -- TODO +1 ?????
                                                                                let statTac = sel1 statement in
                                                                                    let rangeExpTac = sel1 rangeExp in
                                                                                        let guardLabel = newLabel "guard" (k+1) in  -- wrong label for guard TODO
                                                                                            case rangeExpTac of
                                                                                                -- (Abs.RangeExpression res expr1 expr2 range) -> SHOULD NOT REACH !!!
                                                                                                (Abs.RangeExpressionSingle tac expr1 expr2) -> let expr1Addr = sel4 rangeExp in
                                                                                                                                                let expr2Addr = sel5 rangeExp in
                                                                                                                                                 let guardAddr = buildIDAddr pos id in
                                                                                                                                                    ((Abs.ForStateIndexDo (mergeTacs [(rangeexp_content rangeExpTac),                    -- rangeExpr TACS (evaluation of expr1 and expr2 code)
                                                                                                                                                                                    (TAC [TacAssignNullOp guardAddr expr1Addr (B_type Type_Integer)]),  -- guard initialization to expr1 val
                                                                                                                                                                                    (TAC [TacJump guardLabel]),                         -- jump to guard label
                                                                                                                                                                                    (TAC [TacLabel l]),                                 -- body label              
                                                                                                                                                                                    (statement_content statTac),                        -- body TAC code
                                                                                                                                                                                    (TAC [TacAssignBinaryOp guardAddr IntAdd guardAddr (AddrInt 1) (B_type Type_Integer)]), -- guard++
                                                                                                                                                                                    (TAC [TacLabel guardLabel]),                        -- guard label
                                                                                                                                                                                    (TAC [TacRelConditionalJump l False LeqInt guardAddr expr2Addr])  -- check of guard <= end (relation jump)
                                                                                                                                                                                    ]) (Abs.IndexVarDeclaration (TAC []) (Abs.Ident id (TAC []))) rangeExpTac statTac),sel2 statement, sel3 statement)                                                                                      
genTacForStatement (Abs.ForStateIndexWDo res index@(Abs.IndexVarDeclaration _ ident@(Abs.Ident id resi@(TResult _ _ pos))) rangexp b@(Abs.BlockStatement _ stats)) n l k w =
                                                                            let rangeExp = (genTacRangeExpr rangexp n l k w) in -- for range do stats
                                                                                let statements = (genTacStatements stats (sel2 rangeExp) l ((sel3 rangeExp )+1) w) in -- TODO +1 ?????
                                                                                    let statsTac = sel1 statements in
                                                                                        let rangeExpTac = sel1 rangeExp in
                                                                                            let guardLabel = newLabel "guard" (k+1) in  -- wrong label for guard TODO
                                                                                                case rangeExpTac of
                                                                                                    -- (Abs.RangeExpression res expr1 expr2 range) -> SHOULD NOT REACH !!!
                                                                                                    (Abs.RangeExpressionSingle tac expr1 expr2) -> let expr1Addr = sel4 rangeExp in
                                                                                                                                                    let expr2Addr = sel5 rangeExp in
                                                                                                                                                        let guardAddr = buildIDAddr pos id in
                                                                                                                                                        ((Abs.ForStateIndexWDo (mergeTacs [(rangeexp_content rangeExpTac),                    -- rangeExpr TACS (evaluation of expr1 and expr2 code)
                                                                                                                                                                                        (TAC [TacAssignNullOp guardAddr expr1Addr (B_type Type_Integer)]),  -- guard initialization to expr1 val
                                                                                                                                                                                        (TAC [TacJump guardLabel]),                          -- jump to guard label
                                                                                                                                                                                        (TAC [TacLabel l]),                                  -- body label              
                                                                                                                                                                                        (statements_content statsTac),                       -- body TAC code
                                                                                                                                                                                        (TAC [TacAssignBinaryOp guardAddr IntAdd guardAddr (AddrInt 1) (B_type Type_Integer)]), -- guard++
                                                                                                                                                                                        (TAC [TacLabel guardLabel]),                         -- guard label
                                                                                                                                                                                        (TAC [TacRelConditionalJump l False LeqInt guardAddr expr2Addr])  -- check of guard <= end (relation jump)
                                                                                                                                                                                        ]) (Abs.IndexVarDeclaration (TAC []) (Abs.Ident id (TAC []))) rangeExpTac (Abs.BlockStatement (TAC []) statsTac)),sel2 statements, sel3 statements)                                                    
genTacForStatement (Abs.ForStateExprDo res rangexp stat)        n l k w = let rangeExp = (genTacRangeExpr rangexp n l k w) in -- for range do stats
                                                                            let statement = (genTacStatement stat (sel2 rangeExp) l ((sel3 rangeExp )+1) w res) in -- TODO +1 ?????
                                                                                let statTac = sel1 statement in
                                                                                    let rangeExpTac = sel1 rangeExp in
                                                                                        let guardLabel = newLabel "guard" (k+1) in  -- wrong label for guard TODO
                                                                                            case rangeExpTac of
                                                                                                -- (Abs.RangeExpression res expr1 expr2 range) -> SHOULD NOT REACH !!!
                                                                                                (Abs.RangeExpressionSingle tac expr1 expr2) -> let expr1Addr = sel4 rangeExp in
                                                                                                                                                let expr2Addr = sel5 rangeExp in
                                                                                                                                                 let guardTempAddr = (newTemp (sel2 rangeExp)) in
                                                                                                                                                    ((Abs.ForStateExprDo (mergeTacs [(rangeexp_content rangeExpTac),                    -- rangeExpr TACS (evaluation of expr1 and expr2 code)
                                                                                                                                                                                    (TAC [TacAssignNullOp guardTempAddr expr1Addr (B_type Type_Integer)]),  -- guard temp initialization to expr1 val
                                                                                                                                                                                    (TAC [TacJump guardLabel]),                         -- jump to guard label
                                                                                                                                                                                    (TAC [TacLabel l]),                                 -- body label              
                                                                                                                                                                                    (statement_content statTac),                        -- body TAC code
                                                                                                                                                                                    (TAC [TacAssignBinaryOp guardTempAddr IntAdd guardTempAddr (AddrInt 1) (B_type Type_Integer)]), -- guard++
                                                                                                                                                                                    (TAC [TacLabel guardLabel]),                        -- guard label
                                                                                                                                                                                    (TAC [TacRelConditionalJump l False LeqInt guardTempAddr expr2Addr])  -- check of guard <= end (relation jump)
                                                                                                                                                                                    ]) rangeExpTac statTac),sel2 statement, sel3 statement)                                                                                      
genTacForStatement (Abs.ForStateExprWDo res rangexp b@(Abs.BlockStatement _ stats)) n l k w = let rangeExp = (genTacRangeExpr rangexp n l k w) in -- for range do stats
                                                                                                let statements = (genTacStatements stats (sel2 rangeExp) l ((sel3 rangeExp )+1) w) in -- TODO +1 ?????
                                                                                                    let statsTac = sel1 statements in
                                                                                                        let rangeExpTac = sel1 rangeExp in
                                                                                                            let guardLabel = newLabel "guard" (k+1) in  -- wrong label for guard TODO
                                                                                                                case rangeExpTac of
                                                                                                                    -- (Abs.RangeExpression res expr1 expr2 range) -> SHOULD NOT REACH !!!
                                                                                                                    (Abs.RangeExpressionSingle tac expr1 expr2) -> let expr1Addr = sel4 rangeExp in
                                                                                                                                                                    let expr2Addr = sel5 rangeExp in
                                                                                                                                                                     let guardTempAddr = (newTemp (sel2 rangeExp)) in
                                                                                                                                                                        ((Abs.ForStateExprWDo (mergeTacs [(rangeexp_content rangeExpTac),                    -- rangeExpr TACS (evaluation of expr1 and expr2 code)
                                                                                                                                                                                                        (TAC [TacAssignNullOp guardTempAddr expr1Addr (B_type Type_Integer)]),  -- guard temp initialization to expr1 val
                                                                                                                                                                                                        (TAC [TacJump guardLabel]),                          -- jump to guard label
                                                                                                                                                                                                        (TAC [TacLabel l]),                                  -- body label              
                                                                                                                                                                                                        (statements_content statsTac),                       -- body TAC code
                                                                                                                                                                                                        (TAC [TacAssignBinaryOp guardTempAddr IntAdd guardTempAddr (AddrInt 1) (B_type Type_Integer)]), -- guard++
                                                                                                                                                                                                        (TAC [TacLabel guardLabel]),                         -- guard label
                                                                                                                                                                                                        (TAC [TacRelConditionalJump l False LeqInt guardTempAddr expr2Addr])  -- check of guard <= end (relation jump)
                                                                                                                                                                                                        ]) rangeExpTac (Abs.BlockStatement (TAC []) statsTac)),sel2 statements, sel3 statements)                                                    

genTacRangeExpr :: Abs.RANGEEXP TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> Label -> (Abs.RANGEEXP TAC, Prelude.Integer, Prelude.Integer, Address, Address)
-- genTacRangeExpr (Abs.RangeExpression res expr1 expr2 range) n l k w = -- Used in arrays? 1..2,1..2 ???
genTacRangeExpr (Abs.RangeExpressionSingle res expr1 expr2) n l k w   = let exprLeft = (genTacExpression expr1 n l k w res) in
                                                                        let exprRight = (genTacExpression expr2 (sel2 exprLeft) l (sel3 exprLeft) w res) in
                                                                            let newC = sel2 exprRight in
                                                                                let newK = sel3 exprRight in
                                                                                    let exprLeftTac = (sel1 exprLeft) in
                                                                                        let exprRightTac = (sel1 exprRight) in
                                                                                            ((Abs.RangeExpressionSingle (merge2Tacs (expression_content exprLeftTac) (expression_content exprRightTac)) exprLeftTac exprRightTac),newC,newK,sel4 exprLeft,sel4 exprRight)
                                                                            

genTacWhileDoStatement :: Abs.WHILESTATEMENT TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> Label -> (Abs.WHILESTATEMENT TAC, Prelude.Integer, Prelude.Integer)
genTacWhileDoStatement (Abs.WhileStateSimpleDo res expr stat) n l k w = let guardExpr = (genTacExpression expr n l k w res) in 
                                                                            let exprTac = sel1 guardExpr in
                                                                                let nextLab = newLabel "next" ((sel3 guardExpr)+2) in
                                                                                    let statement = (genTacStatement stat (sel2 guardExpr) l ((sel3 guardExpr)+2) nextLab res) in 
                                                                                        let statTac = sel1 statement in 
                                                                                            let exprAddr = sel4 guardExpr in
                                                                                                let guardLab = newLabel "guard" ((sel3 guardExpr)+1) in
                                                                                                    ((Abs.WhileStateSimpleDo (mergeTacs [(TAC [TacJump guardLab,TacLabel l]),(statement_content statTac),(TAC [TacLabel guardLab]),(expression_content exprTac),(TAC [TacConditionalJump l True exprAddr]),(TAC [TacLabel nextLab])]) exprTac statTac),sel2 statement, sel3 statement)
genTacWhileDoStatement (Abs.WhileStateSimpleWDo res expr b@(Abs.BlockStatement _ statements)) n l k w = let guardExpr = (genTacExpression expr n l k w res) in 
                                                                                                            let exprTac = sel1 guardExpr in
                                                                                                                let nextLab = newLabel "next" ((sel3 guardExpr)+2) in
                                                                                                                    let stats = (genTacStatements statements (sel2 guardExpr) l ((sel3 guardExpr)+2) nextLab) in 
                                                                                                                        let statsTac = sel1 stats in 
                                                                                                                            let exprAddr = sel4 guardExpr in
                                                                                                                                let guardLab = newLabel "guard" ((sel3 guardExpr)+1) in
                                                                                                                                    ((Abs.WhileStateSimpleWDo (mergeTacs [(TAC [TacJump guardLab,TacLabel l]),(statements_content statsTac),(TAC [TacLabel guardLab]),(expression_content exprTac),(TAC [TacConditionalJump l True exprAddr]),(TAC [TacLabel nextLab])]) exprTac (Abs.BlockStatement (TAC []) statsTac)),sel2 stats, sel3 stats)
--genTacWhileDoStatement (Abs.WhileStateCtrlDo res ctrl state) n l k w  =
--genTacWhileDoStatement (Abs.WhileStateCtrlWDo res ctrl b) n l k w     =

genTacDoWhileStatement :: Abs.DOSTATEMENT TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> Label -> (Abs.DOSTATEMENT TAC, Prelude.Integer, Prelude.Integer)
genTacDoWhileStatement (Abs.DoWhileState res stat expr) n l k w = let statement = (genTacStatement stat n l k w res) in
                                                                    let statTac = sel1 statement in 
                                                                        let guardExpr = (genTacExpression expr (sel2 statement) l (sel3 statement) w res) in 
                                                                            let exprTac = sel1 guardExpr in
                                                                                let exprAddr = sel4 guardExpr in
                                                                                    ((Abs.DoWhileState (mergeTacs [(TAC [TacLabel l]),(statement_content statTac),(expression_content exprTac),(TAC [TacConditionalJump l True exprAddr])]) statTac exprTac),sel2 guardExpr, sel3 guardExpr)

genTacBlock :: Abs.B TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> Label -> (Abs.B TAC,Prelude.Integer,Prelude.Integer)
genTacBlock (Abs.BlockStatement res statements) n l k w = let statsTac = genTacStatements statements n l k w in ((Abs.BlockStatement (statements_content (sel1 statsTac)) (sel1 statsTac)),(sel2 statsTac),(sel3 statsTac))

genTacConditionalStatement :: Abs.CONDITIONALSTATE TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> Label -> (Abs.CONDITIONALSTATE TAC,Prelude.Integer,Prelude.Integer)
genTacConditionalStatement (Abs.ConditionalStatementSimpleThen res exp state elseState) n l k w     = let expTac = genTacExpression exp n l k w res in -- res è il giusto tcheck? TODO
                                                                                                        let statTac = genTacStatement state (sel2 expTac) l (sel3 expTac) w res in                
                                                                                                            let expAddr = sel4 expTac in
                                                                                                                let statAddr = sel4 statTac in -- SERVE? TODO
                                                                                                                    case elseState of
                                                                                                                        (Abs.ElseStateEmpty _)  -> ((Abs.ConditionalStatementSimpleThen (mergeTacs [(expression_content (sel1 expTac)),(TAC [TacConditionalJump l False expAddr]),(statement_content (sel1 statTac)),(TAC [TacLabel l])]) (sel1 expTac) (sel1 statTac) (Abs.ElseStateEmpty (TAC []))),(sel2 statTac),(sel3 statTac))   -- if expr then ...
                                                                                                                        (Abs.ElseState _ elsestats)     -> let elseStatesTac = genTacStatement elsestats (sel2 statTac) l (sel3 statTac) w res in
                                                                                                                                                                let elseLab = newLabel "next" (sel3 elseStatesTac) in
                                                                                                                                                                    ((Abs.ConditionalStatementSimpleThen (mergeTacs [(expression_content (sel1 expTac)),(TAC [TacConditionalJump l False expAddr]), (statement_content (sel1 statTac)), (TAC [TacJump elseLab]), (TAC [TacLabel l]), (statement_content (sel1 elseStatesTac)), (TAC [TacLabel elseLab])]) (sel1 expTac) (sel1 statTac) (Abs.ElseState (TAC []) (sel1 elseStatesTac)),(sel2 elseStatesTac),(sel3 elseStatesTac))) -- if expr then ... else ...
genTacConditionalStatement (Abs.ConditionalStatementSimpleWThen res exp b@(Abs.BlockStatement _ statements) elseState) n l k w  = let expTac = genTacExpression exp n l k w res in -- res è il giusto tcheck? TODO
                                                                                                                                    let statTacs = genTacStatements statements (sel2 expTac) l (sel3 expTac) w in
                                                                                                                                        let expAddr = sel4 expTac in 
                                                                                                                                            case elseState of
                                                                                                                                                (Abs.ElseStateEmpty _)          -> ((Abs.ConditionalStatementSimpleWThen (mergeTacs [(expression_content (sel1 expTac)),TAC [TacConditionalJump l False expAddr],(statements_content (sel1 statTacs)),(TAC [TacLabel l])]) (sel1 expTac) (Abs.BlockStatement (TAC []) (sel1 statTacs)) (Abs.ElseStateEmpty (TAC []))),(sel2 statTacs),(sel3 statTacs))   -- if expr then ...
                                                                                                                                                (Abs.ElseState _ elsestats)     -> let elseStatesTac = genTacStatement elsestats (sel2 statTacs) l (sel3 statTacs) w res in
                                                                                                                                                                                        let elseLab = newLabel "next" (sel3 elseStatesTac) in
                                                                                                                                                                                            ((Abs.ConditionalStatementSimpleWThen (mergeTacs [(expression_content (sel1 expTac)),(TAC [TacConditionalJump l False expAddr]), (statements_content (sel1 statTacs)), (TAC [TacJump elseLab]), (TAC [TacLabel l]), (statement_content (sel1 elseStatesTac)), (TAC [TacLabel elseLab])]) (sel1 expTac) (Abs.BlockStatement (TAC []) (sel1 statTacs)) (Abs.ElseState (TAC []) (sel1 elseStatesTac)),(sel2 elseStatesTac),(sel3 elseStatesTac))) -- if expr then ... else ...
--genTacConditionalStatement (Abs.ConditionalStatementCtrlThen res ctrlState state elseState) n l k w =        
--genTacConditionalStatement (Abs.ConditionalStatementCtrlWThen res ctrlState b elseState) n l k w    =

genTacVariableType :: Abs.VARIABLETYPE TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> Label ->  (Abs.VARIABLETYPE TAC,Prelude.Integer,Prelude.Integer,Address)
genTacVariableType (Abs.VariableTypeParam res) n l k w      = (Abs.VariableTypeParam    (TAC []),n,k,AddrNULL)
genTacVariableType (Abs.VariableTypeConst res) n l k w      = (Abs.VariableTypeConst    (TAC []),n,k,AddrNULL)
genTacVariableType (Abs.VariableTypeVar res) n l k w        = (Abs.VariableTypeVar      (TAC []),n,k,AddrNULL)
genTacVariableType (Abs.VariableTypeRef res) n l k w        = (Abs.VariableTypeRef      (TAC []),n,k,AddrNULL)
genTacVariableType (Abs.VariableTypeConstRef res) n l k w   = (Abs.VariableTypeConstRef (TAC []),n,k,AddrNULL)

genTacVarDecList :: Abs.VARDECLIST TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> Label -> TCheckResult -> (Abs.VARDECLIST TAC,Prelude.Integer,Prelude.Integer,[Address],Address)
genTacVarDecList (Abs.VariableDeclarationSingle res vardecId) n l k w tres = let vardecIdTac = genTacVarDecId vardecId n l k w tres in
                                                                            let vardecIdAddr = sel4 vardecIdTac in
                                                                                let initAddr = sel5 vardecIdTac in
                                                                                (Abs.VariableDeclarationSingle (vardecid_content (sel1 vardecIdTac)) (sel1 vardecIdTac),(sel2 vardecIdTac),(sel3 vardecIdTac),vardecIdAddr,initAddr)

genTacVarDecId :: Abs.VARDECID TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> Label -> TCheckResult -> (Abs.VARDECID TAC,Prelude.Integer,Prelude.Integer,[Address],Address)
genTacVarDecId (Abs.VariableDeclaration res@(TResult _ ty _) idlist typepart initpart) n l k w tres = case initpart of
                                                                                    InitializzationPartEmpty resi -> let idlistTac = genTacIdentifierList idlist n l k w tres in
                                                                                                                        let tacId = identlist_content (sel1 idlistTac) in
                                                                                                                            let addrIdList = sel4 idlistTac in
                                                                                                                                let initAddr = AddrNULL in
                                                                                                                                    (Abs.VariableDeclaration tacId (sel1 idlistTac) (Abs.TypePart (TAC []) (TypeExpression (TAC []) (Abs.PrimitiveTypeInt (TAC [])))) (Abs.InitializzationPartEmpty (TAC [])),(sel2 idlistTac),(sel3 idlistTac),addrIdList,initAddr)
                                                                                    InitializzationPart resi expr -> let idlistTac = genTacIdentifierList idlist n l k w tres in
                                                                                                                        let tacId = identlist_content (sel1 idlistTac) in
                                                                                                                            let addrIdList = sel4 idlistTac in
                                                                                                                                let exprTac = (genTacExpression expr (sel2 idlistTac) l (sel3 idlistTac) w tres) in
                                                                                                                                    let initTac = (Abs.InitializzationPart (expression_content (sel1 exprTac)) (sel1 exprTac)) in
                                                                                                                                        let initAddr = sel4 exprTac in
                                                                                                                                            (Abs.VariableDeclaration (expression_content (sel1 exprTac)) (sel1 idlistTac) (Abs.TypePart (TAC []) (TypeExpression (TAC []) (Abs.PrimitiveTypeInt (TAC [])))) initTac ,(sel2 exprTac),(sel3 exprTac),addrIdList,initAddr)
                                                                                    --InitializzationPartArray resi array -> 

genTacExpression :: Abs.EXPRESSION TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> Label -> TCheckResult -> (Abs.EXPRESSION TAC,Prelude.Integer,Prelude.Integer,Address)
genTacExpression (Abs.ExpressionInteger res value@(Abs.Integer val resi))       n l k w tres = (Abs.ExpressionInteger (TAC []) (Abs.Integer val (TAC [])),n,k, AddrInt val)
genTacExpression (Abs.ExpressionBoolean res value@(Abs.Boolean_true resi))      n l k w tres = (Abs.ExpressionBoolean (TAC []) (Abs.Boolean_true (TAC [])),n,k, AddrBool True)
genTacExpression (Abs.ExpressionBoolean res value@(Abs.Boolean_false resi))     n l k w tres = (Abs.ExpressionBoolean (TAC []) (Abs.Boolean_false (TAC [])),n,k, AddrBool False)
genTacExpression (Abs.ExpressionBoolean res value@(Abs.Boolean_True resi))      n l k w tres = (Abs.ExpressionBoolean (TAC []) (Abs.Boolean_True (TAC [])),n,k, AddrBool True)
genTacExpression (Abs.ExpressionBoolean res value@(Abs.Boolean_False resi))     n l k w tres = (Abs.ExpressionBoolean (TAC []) (Abs.Boolean_False (TAC [])),n,k, AddrBool False)
genTacExpression (Abs.ExpressionChar res value@(Abs.Char val resi))             n l k w tres = (Abs.ExpressionChar (TAC []) (Abs.Char val (TAC [])),n,k, AddrChar val)
genTacExpression (Abs.ExpressionString res value@(Abs.String val resi))         n l k w tres = (Abs.ExpressionString (TAC []) (Abs.String val (TAC [])),n,k, AddrString val)
genTacExpression (Abs.ExpressionReal res value@(Abs.Real val resi))             n l k w tres = (Abs.ExpressionReal (TAC []) (Abs.Real val (TAC [])),n,k, AddrReal val)
genTacExpression (Abs.ExpressionBracket res exp)                                n l k w tres = let exprTac = genTacExpression exp n l k w tres in (Abs.ExpressionBracket (expression_content (sel1 exprTac)) (sel1 exprTac),(sel2 exprTac),(sel3 exprTac),(sel4 exprTac))
{-genTacExpression (Abs.ExpressionCast res def tipo)  =-}   
genTacExpression (Abs.ExpressionUnary res@(TResult env ty pos) unary def)       n l k w tres = let defTac = genTacDefault def (n+1) l k w tres in 
                                                                                                let defAddr = sel4 defTac in
                                                                                                    let temp = newTemp n in
                                                                                                        case unary of 
                                                                                                            UnaryOperationPositive _ -> (Abs.ExpressionUnary (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Pos defAddr ty]) ) (Abs.UnaryOperationPositive (TAC [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp) 
                                                                                                            UnaryOperationNegative _ -> (Abs.ExpressionUnary (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Neg defAddr ty]) ) (Abs.UnaryOperationNegative (TAC [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp) 
                                                                                                            UnaryOperationNot      _ -> (Abs.ExpressionUnary (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Not defAddr ty]) ) (Abs.UnaryOperationNot (TAC [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp) 
                                                                                                            UnaryOperationPointer  _ -> (Abs.ExpressionUnary (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Point defAddr ty]) ) (Abs.UnaryOperationPointer (TAC [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp)
genTacExpression (Abs.ExpressionBinaryPlus res@(TResult env t pos) expr1 expr2) n l k w tres = let expr1Tac = genTacExpression expr1 (n+1) l k w tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) w tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryPlus (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "plus") (sel4 expr1Tac) (sel4 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryMinus res@(TResult env t pos) expr1 expr2) n l k w tres = let expr1Tac = genTacExpression expr1 (n+1) l k w tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) w tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryMinus (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "minus") (sel4 expr1Tac) (sel4 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryProduct res@(TResult env t pos) expr1 expr2) n l k w tres = let expr1Tac = genTacExpression expr1 (n+1) l k w tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) w tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryProduct (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "product") (sel4 expr1Tac) (sel4 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryDivision res@(TResult env t pos) expr1 expr2) n l k w tres = let expr1Tac = genTacExpression expr1 (n+1) l k w tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) w tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryDivision (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "division") (sel4 expr1Tac) (sel4 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryModule res@(TResult env t pos) expr1 expr2) n l k w tres = let expr1Tac = genTacExpression expr1 (n+1) l k w tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) w tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryModule (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "module") (sel4 expr1Tac) (sel4 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryPower res@(TResult env t pos) expr1 expr2) n l k w tres = let expr1Tac = genTacExpression expr1 (n+1) l k w tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) w tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryPower (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "power") (sel4 expr1Tac) (sel4 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryAnd res@(TResult env t pos) expr1 expr2) n l k w tres = let expr1Tac = genTacExpression expr1 (n+1) l k w tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) w tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryAnd (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "and") (sel4 expr1Tac) (sel4 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryOr res@(TResult env t pos) expr1 expr2) n l k w tres = let expr1Tac = genTacExpression expr1 (n+1) l k w tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) w tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryOr (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "or") (sel4 expr1Tac) (sel4 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryEq res@(TResult env t pos) expr1 expr2) n l k w tres = let expr1Tac = genTacExpression expr1 (n+1) l k w tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) w tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryEq (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "eq") (sel4 expr1Tac) (sel4 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)                                                                                                    
genTacExpression (Abs.ExpressionBinaryNotEq res@(TResult env t pos) expr1 expr2) n l k w tres = let expr1Tac = genTacExpression expr1 (n+1) l k w tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) w tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryNotEq (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "noteq") (sel4 expr1Tac) (sel4 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)                                                                                                    
genTacExpression (Abs.ExpressionBinaryGratherEq res@(TResult env t pos) expr1 expr2) n l k w tres = let expr1Tac = genTacExpression expr1 (n+1) l k w tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) w tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryGratherEq (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "grathereq") (sel4 expr1Tac) (sel4 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)                                                                                                    
genTacExpression (Abs.ExpressionBinaryGrather res@(TResult env t pos) expr1 expr2) n l k w tres = let expr1Tac = genTacExpression expr1 (n+1) l k w tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) w tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryGrather (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "grather") (sel4 expr1Tac) (sel4 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)                                                                                                    
genTacExpression (Abs.ExpressionBinaryLessEq res@(TResult env t pos) expr1 expr2) n l k w tres = let expr1Tac = genTacExpression expr1 (n+1) l k w tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) w tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryLessEq (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "lesseq") (sel4 expr1Tac) (sel4 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)                                                                                                    
genTacExpression (Abs.ExpressionBinaryLess res@(TResult env t pos) expr1 expr2) n l k w tres = let expr1Tac = genTacExpression expr1 (n+1) l k w tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) w tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryLess (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "less") (sel4 expr1Tac) (sel4 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)                                                                                                    

{-genTacExpression (Abs.ExpressionIdent res id index) =_ ->
genTacExpression (Abs.ExpressionCall res id exps) = -}

genTacDefault :: Abs.DEFAULT TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> Label -> TCheckResult -> (Abs.DEFAULT TAC,Prelude.Integer,Prelude.Integer,Address)
genTacDefault (Abs.ExpressionIntegerD res value@(Abs.Integer val resi))       n l k w tres = (Abs.ExpressionIntegerD (TAC []) (Abs.Integer val (TAC [])),n,k, AddrInt val)
genTacDefault (Abs.ExpressionBooleanD res value@(Abs.Boolean_true resi))      n l k w tres = (Abs.ExpressionBooleanD (TAC []) (Abs.Boolean_true (TAC [])),n,k, AddrBool True)
genTacDefault (Abs.ExpressionBooleanD res value@(Abs.Boolean_false resi))     n l k w tres = (Abs.ExpressionBooleanD (TAC []) (Abs.Boolean_false (TAC [])),n,k, AddrBool False)
genTacDefault (Abs.ExpressionBooleanD res value@(Abs.Boolean_True resi))      n l k w tres = (Abs.ExpressionBooleanD (TAC []) (Abs.Boolean_True (TAC [])),n,k, AddrBool True)
genTacDefault (Abs.ExpressionBooleanD res value@(Abs.Boolean_False resi))     n l k w tres = (Abs.ExpressionBooleanD (TAC []) (Abs.Boolean_False (TAC [])),n,k, AddrBool False)
genTacDefault (Abs.ExpressionCharD res value@(Abs.Char val resi))             n l k w tres = (Abs.ExpressionCharD (TAC []) (Abs.Char val (TAC [])),n,k, AddrChar val)
genTacDefault (Abs.ExpressionStringD res value@(Abs.String val resi))         n l k w tres = (Abs.ExpressionStringD (TAC []) (Abs.String val (TAC [])),n,k, AddrString val)
genTacDefault (Abs.ExpressionRealD res value@(Abs.Real val resi))             n l k w tres = (Abs.ExpressionRealD (TAC []) (Abs.Real val (TAC [])),n,k, AddrReal val)
genTacDefault (Abs.ExpressionBracketD res exp)                                n l k w tres = let exprTac = genTacExpression exp n l k w tres in (Abs.ExpressionBracketD (expression_content (sel1 exprTac)) (sel1 exprTac),(sel2 exprTac),(sel3 exprTac), (sel4 exprTac))
{-genTacDefault (Abs.ExpressionCastD res def tipo)  = -}  
genTacDefault (Abs.ExpressionUnaryD res@(TResult env ty pos) unary def)       n l k w tres = let defTac = genTacDefault def (n+1) l k w tres in 
                                                                                            let temp = newTemp n in
                                                                                                case def of
                                                                                                    --Abs.ExpressionCastD res def tipo   
                                                                                                    --Abs.ExpressionUnaryD res@(TResult env ty pos) unary def
                                                                                                    --Abs.ExpressionIdentD res id index
                                                                                                    --Abs.ExpressionCallD res id exps
                                                                                                    _ -> case unary of 
                                                                                                            UnaryOperationPositive _ -> (Abs.ExpressionUnaryD (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Pos (sel4 defTac) ty])) (Abs.UnaryOperationPositive (TAC [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp) 
                                                                                                            UnaryOperationNegative _ -> (Abs.ExpressionUnaryD (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Neg (sel4 defTac) ty])) (Abs.UnaryOperationNegative (TAC [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp) 
                                                                                                            UnaryOperationNot      _ -> (Abs.ExpressionUnaryD (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Not (sel4 defTac) ty])) (Abs.UnaryOperationNot (TAC [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp) 
                                                                                                            UnaryOperationPointer  _ -> (Abs.ExpressionUnaryD (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Point (sel4 defTac) ty])) (Abs.UnaryOperationPointer (TAC [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp)
{-genTacDefault (Abs.ExpressionIdentD res id index) =
genTacDefault (Abs.ExpressionCallD res id exps) = -}


genTacIdentifierList :: Abs.IDENTLIST TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> Label -> TCheckResult -> (Abs.IDENTLIST TAC,Prelude.Integer,Prelude.Integer,[Address])
genTacIdentifierList (Abs.IdentifierSingle res@(TResult _ _ pos) ident@(Abs.Ident id resi)) n l k w tres       = (Abs.IdentifierSingle (TAC []) (Abs.Ident id (TAC [])),n,k,[buildIDAddr pos id])
genTacIdentifierList (Abs.IdentifierList res@(TResult _ _ pos) ident@(Abs.Ident id resi) idlist) n l k w tres  = let idlistTac = (genTacIdentifierList idlist n l k w tres) in
                                                                                                                    let idlistAddr = sel4 idlistTac in
                                                                                                                        (Abs.IdentifierList (TAC []) (Abs.Ident id (TAC [])) (sel1 idlistTac),(sel2 idlistTac),(sel3 idlistTac),[buildIDAddr pos id] ++ idlistAddr)
