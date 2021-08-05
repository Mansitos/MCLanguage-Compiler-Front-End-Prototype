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

class Sel2 a b | a -> b where sel2 :: a -> b
instance Sel2 (a1,a2) a2 where sel2 (_,x) = x
instance Sel2 (a1,a2,a3) a2 where sel2 (_,x,_) = x
instance Sel2 (a1,a2,a3,a4) a2 where sel2 (_,x,_,_) = x

class Sel3 a b | a -> b where sel3 :: a -> b
instance Sel3 (a1,a2,a3) a3 where sel3 (_,_,x) = x
instance Sel3 (a1,a2,a3,a4) a3 where sel3 (_,_,x,_) = x

class Sel4 a b | a -> b where sel4 :: a -> b
instance Sel4 (a1,a2,a3,a4) a4 where sel4 (_,_,_,x) = x
instance Sel4 (a1,a2,a3,a4,a5) a4 where sel4 (_,_,_,x,_) = x
instance Sel4 (a1,a2,a3,a4,a5,a6) a4 where sel4 (_,_,_,x,_,_) = x
------------------------------------------------------------------------

newLabel :: Prelude.Integer -> Label
newLabel n = Label ("L"++show n++":")

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
genTAC (Abs.StartCode tres stats) = let endLab = newLabel 0 in
                                        let statsTac = sel1 (genTacStatements stats 1 endLab) in
                                            let tacs = (statements_content statsTac) in
                                                (Abs.StartCode (TAC ((content tacs)++(TacLabel endLab):[ExitTac])) statsTac)

genTacStatements :: Abs.STATEMENTS TCheckResult -> Prelude.Integer -> Label -> (Abs.STATEMENTS TAC,Prelude.Integer)
genTacStatements (Abs.ListStatements tres stat stats) n l = case stats of
                                                                Abs.ListStatements tres _ _ -> let statTac = sel1 (genTacStatement stat n l tres) in
                                                                                                    let newC = sel2 (genTacStatement stat n l tres) in
                                                                                                        let newL = newLabel n in
                                                                                                            let statsTac = (sel1 (genTacStatements stats (n+1) newL)) in
                                                                                                                (Abs.ListStatements (merge2Tacs (statement_content statTac) (statements_content statsTac)) statTac statsTac,newC)
                                                                Abs.EmptyStatement tres -> let statTac = sel1 (genTacStatement stat n l tres) in
                                                                                                let newC = sel2 (genTacStatement stat n l tres) in
                                                                                                    let newL = newLabel n in
                                                                                                        (Abs.ListStatements (statement_content statTac) statTac (sel1 (genTacStatements stats (n+1) newL)),newC)
genTacStatements (Abs.EmptyStatement tres) n l = ((Abs.EmptyStatement (TAC [])),n)

genTacStatement :: Abs.STATEMENT TCheckResult -> Prelude.Integer -> Label -> TCheckResult -> (Abs.STATEMENT TAC,Prelude.Integer,Address)
genTacStatement (Abs.VariableDeclarationStatement res@(TResult _ ty _) tipo vardec) n l tres = let tipoTac = sel1 (genTacVariableType tipo n l) in
                                                                                                    let tipoContent = variabletype_content tipoTac in
                                                                                                        let vardecTac = genTacVarDecList vardec n l tres in
                                                                                                            let vardecContent = vardeclist_content (sel1 vardecTac) in
                                                                                                                let vardecAddrs = sel3 vardecTac in -- variable addresses # >1
                                                                                                                    let initAddr = sel4 vardecTac in
                                                                                                                        (Abs.VariableDeclarationStatement (merge2Tacs (merge2Tacs vardecContent (TAC (buildTacEntriesForVarsDecl vardecAddrs initAddr ty)))
                                                                                                                                                             tipoContent) tipoTac (sel1 vardecTac) ,n,AddrAddress "")
{-genTacStatement Abs.BreakStatement tres)                          = 
genTacStatement (Abs.ContinueStatement tres)                        = 
genTacStatement (Abs.ReturnStatement tres ret)                      =
-} 
genTacStatement (Abs.Statement res block) n l tres                 = let newL = newLabel (n+1) in 
                                                                        let newC = sel2 (genTacBlock block n newL) in
                                                                            let blockTac = sel1 (genTacBlock block n newL) in (Abs.Statement (b_content blockTac) blockTac,newC,AddrAddress "") -- Statement {statement_content::a, statement_b::(B a)}
{-
genTacStatement (Abs.ExpressionStatement tres exp)                  =
genTacStatement (Abs.AssignmentStatement tres lval assignOp exp)    =
genTacStatement (Abs.VariableDeclarationStatement tres tipo vardec) = (Abs.VariableDeclarationStatement (TAC []) (genTacVariableDeclarationStatement vardec))-}
genTacStatement (Abs.ConditionalStatement res condition) n l tres  = let newL = newLabel (n+1) in 
                                                                        let condStatementTac = sel1 (genTacConditionalStatement condition n newL) in
                                                                            let newC = sel2 (genTacConditionalStatement condition n newL) in
                                                                                ((Abs.ConditionalStatement (conditionalstate_content condStatementTac) condStatementTac),newC,AddrAddress "")
{-genTacStatement (Abs.WhileDoStatement tres whileStaement)           = 
genTacStatement (Abs.DoWhileStatement tres doStatement)             = 
genTacStatement (Abs.ForStatement tres forStatement)                = 
genTacStatement (Abs.ProcedureStatement tres id param states)       =                                              
genTacStatement (Abs.FunctionStatement tres id param tipo states)   =-}

genTacBlock :: Abs.B TCheckResult -> Prelude.Integer -> Label -> (Abs.B TAC, Prelude.Integer)
genTacBlock (Abs.BlockStatement res statements) n l = let statsTac = sel1 (genTacStatements statements n l) in ((Abs.BlockStatement (statements_content statsTac) statsTac),n)

genTacConditionalStatement :: Abs.CONDITIONALSTATE TCheckResult -> Prelude.Integer -> Label -> (Abs.CONDITIONALSTATE TAC,Prelude.Integer)
genTacConditionalStatement (Abs.ConditionalStatementSimpleThen res exp state elseState) n l     = let statTac = sel1 (genTacStatement state n l res) in
                                                                                                                        let expTac = sel1 (genTacExpression exp n l res) in -- res è il giusto tcheck? TODO
                                                                                                                            let expAddr = sel3 (genTacExpression exp n l res) in
                                                                                                                                let statAddr = sel3 (genTacStatement state n l res) in -- SERVE? TODO
                                                                                                                                    case elseState of
                                                                                                                                        (Abs.ElseStateEmpty _)  -> ((Abs.ConditionalStatementSimpleThen (merge2Tacs (merge2Tacs (TAC [TacConditionalJump l False expAddr]) (statement_content statTac)) (TAC [TacLabel l])) expTac statTac (Abs.ElseStateEmpty (TAC []))),n)   -- if expr then ...
                                                                                                                                        (Abs.ElseState _ elsestats)     -> let elseStatesTac = sel1 (genTacStatement elsestats n l res) in
                                                                                                                                                                                let elseLab = newLabel (sel2 (genTacStatement elsestats n l res)) in
                                                                                                                                                                                    ((Abs.ConditionalStatementSimpleThen (mergeTacs [(TAC [TacConditionalJump l False expAddr]), (statement_content statTac), (TAC [TacJump elseLab]), (TAC [TacLabel l]), (statement_content elseStatesTac), (TAC [TacLabel elseLab])]) expTac statTac (Abs.ElseState (TAC []) elseStatesTac),n)) -- if expr then ... else ...
genTacConditionalStatement (Abs.ConditionalStatementSimpleWThen res exp b@(Abs.BlockStatement _ statements) elseState) n l  = let statTacs = sel1 (genTacStatements statements n l) in
                                                                                                                                    let expTac = sel1 (genTacExpression exp n l res) in -- res è il giusto tcheck? TODO
                                                                                                                                        let expAddr = sel3 (genTacExpression exp n l res) in 
                                                                                                                                            case elseState of
                                                                                                                                                (Abs.ElseStateEmpty _)          -> ((Abs.ConditionalStatementSimpleWThen (merge2Tacs (merge2Tacs (TAC [TacConditionalJump l False expAddr]) (statements_content statTacs)) (TAC [TacLabel l])) expTac (Abs.BlockStatement (TAC []) statTacs) (Abs.ElseStateEmpty (TAC []))),n)   -- if expr then ...
                                                                                                                                                (Abs.ElseState _ elsestats)     -> let elseStatesTac = sel1 (genTacStatement elsestats n l res) in
                                                                                                                                                                                        let elseLab = newLabel (sel2 (genTacStatement elsestats n l res)) in
                                                                                                                                                                                            ((Abs.ConditionalStatementSimpleWThen (mergeTacs [(TAC [TacConditionalJump l False expAddr]), (statements_content statTacs), (TAC [TacJump elseLab]), (TAC [TacLabel l]), (statement_content elseStatesTac), (TAC [TacLabel elseLab])]) expTac (Abs.BlockStatement (TAC []) statTacs) (Abs.ElseState (TAC []) elseStatesTac),n)) -- if expr then ... else ...
--genTacConditionalStatement (Abs.ConditionalStatementCtrlThen res ctrlState state elseState) n l =        
--genTacConditionalStatement (Abs.ConditionalStatementCtrlWThen res ctrlState b elseState) n l    =

genTacVariableType :: Abs.VARIABLETYPE TCheckResult -> Prelude.Integer -> Label ->  (Abs.VARIABLETYPE TAC,Prelude.Integer,Address)
genTacVariableType (Abs.VariableTypeParam res) n l      = (Abs.VariableTypeParam (TAC []),n,AddrAddress "")
genTacVariableType (Abs.VariableTypeConst res) n l      = (Abs.VariableTypeConst (TAC []),n,AddrAddress "")
genTacVariableType (Abs.VariableTypeVar res) n l        = (Abs.VariableTypeVar   (TAC []),n,AddrAddress "")
genTacVariableType (Abs.VariableTypeRef res) n l        = (Abs.VariableTypeRef   (TAC []),n,AddrAddress "")
genTacVariableType (Abs.VariableTypeConstRef res) n l   = (Abs.VariableTypeConstRef (TAC []),n,AddrAddress "")

genTacVarDecList :: Abs.VARDECLIST TCheckResult -> Prelude.Integer -> Label -> TCheckResult -> (Abs.VARDECLIST TAC,Prelude.Integer,[Address],Address)
genTacVarDecList (Abs.VariableDeclarationSingle res vardecId) n l tres = let vardecIdTac = genTacVarDecId vardecId n l tres in
                                                                            let vardecIdAddr = sel3 vardecIdTac in
                                                                                let initAddr = sel4 vardecIdTac in
                                                                                (Abs.VariableDeclarationSingle (vardecid_content (sel1 vardecIdTac)) (sel1 vardecIdTac),n,vardecIdAddr,initAddr)

genTacVarDecId :: Abs.VARDECID TCheckResult -> Prelude.Integer -> Label -> TCheckResult -> (Abs.VARDECID TAC,Prelude.Integer,[Address],Address)
genTacVarDecId (Abs.VariableDeclaration res@(TResult _ ty _) idlist typepart initpart) n l tres = case initpart of
                                                                                    InitializzationPartEmpty resi -> let idlistTac = genTacIdentifierList idlist n l tres in
                                                                                                                        let tacId = identlist_content (sel1 idlistTac) in
                                                                                                                            let addrIdList = sel3 idlistTac in
                                                                                                                                let initAddr = AddrNULL in
                                                                                                                                    (Abs.VariableDeclaration tacId (sel1 idlistTac) (Abs.TypePart (TAC []) (TypeExpression (TAC []) (Abs.PrimitiveTypeInt (TAC [])))) (Abs.InitializzationPartEmpty (TAC [])),n,addrIdList,initAddr)
                                                                                    InitializzationPart resi expr -> let idlistTac = genTacIdentifierList idlist n l tres in
                                                                                                                        let tacId = identlist_content (sel1 idlistTac) in
                                                                                                                            let addrIdList = sel3 idlistTac in
                                                                                                                                let exprTac = (genTacExpression expr n l tres) in
                                                                                                                                    let initTac = (Abs.InitializzationPart (expression_content (sel1 exprTac)) (sel1 exprTac)) in
                                                                                                                                        let initAddr = sel3 exprTac in
                                                                                                                                            (Abs.VariableDeclaration (expression_content (sel1 exprTac)) (sel1 idlistTac) (Abs.TypePart (TAC []) (TypeExpression (TAC []) (Abs.PrimitiveTypeInt (TAC [])))) initTac ,n,addrIdList,initAddr)
                                                                                    --InitializzationPartArray resi array -> 

genTacExpression :: Abs.EXPRESSION TCheckResult -> Prelude.Integer -> Label -> TCheckResult -> (Abs.EXPRESSION TAC,Prelude.Integer,Address)
genTacExpression (Abs.ExpressionInteger res value@(Abs.Integer val resi))       n l tres = (Abs.ExpressionInteger (TAC []) (Abs.Integer val (TAC [])),n, AddrInt val)
genTacExpression (Abs.ExpressionBoolean res value@(Abs.Boolean_true resi))      n l tres = (Abs.ExpressionBoolean (TAC []) (Abs.Boolean_true (TAC [])),n, AddrBool True)
genTacExpression (Abs.ExpressionBoolean res value@(Abs.Boolean_false resi))     n l tres = (Abs.ExpressionBoolean (TAC []) (Abs.Boolean_false (TAC [])),n, AddrBool False)
genTacExpression (Abs.ExpressionBoolean res value@(Abs.Boolean_True resi))      n l tres = (Abs.ExpressionBoolean (TAC []) (Abs.Boolean_True (TAC [])),n, AddrBool True)
genTacExpression (Abs.ExpressionBoolean res value@(Abs.Boolean_False resi))     n l tres = (Abs.ExpressionBoolean (TAC []) (Abs.Boolean_False (TAC [])),n, AddrBool False)
genTacExpression (Abs.ExpressionChar res value@(Abs.Char val resi))             n l tres = (Abs.ExpressionChar (TAC []) (Abs.Char val (TAC [])),n, AddrChar val)
genTacExpression (Abs.ExpressionString res value@(Abs.String val resi))         n l tres = (Abs.ExpressionString (TAC []) (Abs.String val (TAC [])),n, AddrString val)
genTacExpression (Abs.ExpressionReal res value@(Abs.Real val resi))             n l tres = (Abs.ExpressionReal (TAC []) (Abs.Real val (TAC [])),n, AddrReal val)
genTacExpression (Abs.ExpressionBracket res exp)                                n l tres = let exprTac = genTacExpression exp n l tres in (Abs.ExpressionBracket (expression_content (sel1 exprTac)) (sel1 exprTac),n, (sel3 exprTac))
{-genTacExpression (Abs.ExpressionCast res def tipo)  =-}   
genTacExpression (Abs.ExpressionUnary res@(TResult env ty pos) unary def)       n l tres = let defTac = genTacDefault def (n+1) l tres in 
                                                                                                let defAddr = sel3 defTac in
                                                                                                    let temp = newTemp n in
                                                                                                        case unary of 
                                                                                                            UnaryOperationPositive _ -> (Abs.ExpressionUnary (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Pos defAddr ty]) ) (Abs.UnaryOperationPositive (TAC [])) (sel1 defTac),n,temp) 
                                                                                                            UnaryOperationNegative _ -> (Abs.ExpressionUnary (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Neg defAddr ty]) ) (Abs.UnaryOperationNegative (TAC [])) (sel1 defTac),n,temp) 
                                                                                                            UnaryOperationNot      _ -> (Abs.ExpressionUnary (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Not defAddr ty]) ) (Abs.UnaryOperationNot (TAC [])) (sel1 defTac),n,temp) 
                                                                                                            UnaryOperationPointer  _ -> (Abs.ExpressionUnary (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Point defAddr ty]) ) (Abs.UnaryOperationPointer (TAC [])) (sel1 defTac),n,temp)
genTacExpression (Abs.ExpressionBinaryPlus res@(TResult env t pos) expr1 expr2) n l tres = let expr1Tac = genTacExpression expr1 (n+1) l tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryPlus (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "plus") (sel3 expr1Tac) (sel3 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryMinus res@(TResult env t pos) expr1 expr2) n l tres = let expr1Tac = genTacExpression expr1 (n+1) l tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryMinus (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "minus") (sel3 expr1Tac) (sel3 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryProduct res@(TResult env t pos) expr1 expr2) n l tres = let expr1Tac = genTacExpression expr1 (n+1) l tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryProduct (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "product") (sel3 expr1Tac) (sel3 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryDivision res@(TResult env t pos) expr1 expr2) n l tres = let expr1Tac = genTacExpression expr1 (n+1) l tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryDivision (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "division") (sel3 expr1Tac) (sel3 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryModule res@(TResult env t pos) expr1 expr2) n l tres = let expr1Tac = genTacExpression expr1 (n+1) l tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryModule (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "module") (sel3 expr1Tac) (sel3 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryPower res@(TResult env t pos) expr1 expr2) n l tres = let expr1Tac = genTacExpression expr1 (n+1) l tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryPower (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "power") (sel3 expr1Tac) (sel3 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryAnd res@(TResult env t pos) expr1 expr2) n l tres = let expr1Tac = genTacExpression expr1 (n+1) l tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryAnd (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "and") (sel3 expr1Tac) (sel3 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryOr res@(TResult env t pos) expr1 expr2) n l tres = let expr1Tac = genTacExpression expr1 (n+1) l tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryOr (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "or") (sel3 expr1Tac) (sel3 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryEq res@(TResult env t pos) expr1 expr2) n l tres = let expr1Tac = genTacExpression expr1 (n+1) l tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryEq (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "eq") (sel3 expr1Tac) (sel3 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),temp)                                                                                                    
genTacExpression (Abs.ExpressionBinaryNotEq res@(TResult env t pos) expr1 expr2) n l tres = let expr1Tac = genTacExpression expr1 (n+1) l tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryNotEq (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "noteq") (sel3 expr1Tac) (sel3 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),temp)                                                                                                    
genTacExpression (Abs.ExpressionBinaryGratherEq res@(TResult env t pos) expr1 expr2) n l tres = let expr1Tac = genTacExpression expr1 (n+1) l tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryGratherEq (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "grathereq") (sel3 expr1Tac) (sel3 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),temp)                                                                                                    
genTacExpression (Abs.ExpressionBinaryGrather res@(TResult env t pos) expr1 expr2) n l tres = let expr1Tac = genTacExpression expr1 (n+1) l tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryGrather (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "grather") (sel3 expr1Tac) (sel3 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),temp)                                                                                                    
genTacExpression (Abs.ExpressionBinaryLessEq res@(TResult env t pos) expr1 expr2) n l tres = let expr1Tac = genTacExpression expr1 (n+1) l tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryLessEq (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "lesseq") (sel3 expr1Tac) (sel3 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),temp)                                                                                                    
genTacExpression (Abs.ExpressionBinaryLess res@(TResult env t pos) expr1 expr2) n l tres = let expr1Tac = genTacExpression expr1 (n+1) l tres in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l tres in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryLess (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "less") (sel3 expr1Tac) (sel3 expr2Tac) t])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),temp)                                                                                                    

{-genTacExpression (Abs.ExpressionIdent res id index) =_ ->
genTacExpression (Abs.ExpressionCall res id exps) = -}

genTacDefault :: Abs.DEFAULT TCheckResult -> Prelude.Integer -> Label -> TCheckResult -> (Abs.DEFAULT TAC,Prelude.Integer,Address)
genTacDefault (Abs.ExpressionIntegerD res value@(Abs.Integer val resi))       n l tres = (Abs.ExpressionIntegerD (TAC []) (Abs.Integer val (TAC [])),n, AddrInt val)
genTacDefault (Abs.ExpressionBooleanD res value@(Abs.Boolean_true resi))      n l tres = (Abs.ExpressionBooleanD (TAC []) (Abs.Boolean_true (TAC [])),n, AddrBool True)
genTacDefault (Abs.ExpressionBooleanD res value@(Abs.Boolean_false resi))     n l tres = (Abs.ExpressionBooleanD (TAC []) (Abs.Boolean_false (TAC [])),n, AddrBool False)
genTacDefault (Abs.ExpressionBooleanD res value@(Abs.Boolean_True resi))      n l tres = (Abs.ExpressionBooleanD (TAC []) (Abs.Boolean_True (TAC [])),n, AddrBool True)
genTacDefault (Abs.ExpressionBooleanD res value@(Abs.Boolean_False resi))     n l tres = (Abs.ExpressionBooleanD (TAC []) (Abs.Boolean_False (TAC [])),n, AddrBool False)
genTacDefault (Abs.ExpressionCharD res value@(Abs.Char val resi))             n l tres = (Abs.ExpressionCharD (TAC []) (Abs.Char val (TAC [])),n, AddrChar val)
genTacDefault (Abs.ExpressionStringD res value@(Abs.String val resi))         n l tres = (Abs.ExpressionStringD (TAC []) (Abs.String val (TAC [])),n, AddrString val)
genTacDefault (Abs.ExpressionRealD res value@(Abs.Real val resi))             n l tres = (Abs.ExpressionRealD (TAC []) (Abs.Real val (TAC [])),n, AddrReal val)
genTacDefault (Abs.ExpressionBracketD res exp)                                n l tres = let exprTac = genTacExpression exp n l tres in (Abs.ExpressionBracketD (expression_content (sel1 exprTac)) (sel1 exprTac),n, (sel3 exprTac))
{-genTacDefault (Abs.ExpressionCastD res def tipo)  = -}  
genTacDefault (Abs.ExpressionUnaryD res@(TResult env ty pos) unary def)       n l tres = let defTac = genTacDefault def (n+1) l tres in 
                                                                                            let temp = newTemp n in
                                                                                                case def of
                                                                                                    --Abs.ExpressionCastD res def tipo   
                                                                                                    --Abs.ExpressionUnaryD res@(TResult env ty pos) unary def
                                                                                                    --Abs.ExpressionIdentD res id index
                                                                                                    --Abs.ExpressionCallD res id exps
                                                                                                    _ -> case unary of 
                                                                                                            UnaryOperationPositive _ -> (Abs.ExpressionUnaryD (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Pos (sel3 defTac) ty])) (Abs.UnaryOperationPositive (TAC [])) (sel1 defTac),n,temp) 
                                                                                                            UnaryOperationNegative _ -> (Abs.ExpressionUnaryD (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Neg (sel3 defTac) ty])) (Abs.UnaryOperationNegative (TAC [])) (sel1 defTac),n,temp) 
                                                                                                            UnaryOperationNot      _ -> (Abs.ExpressionUnaryD (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Not (sel3 defTac) ty])) (Abs.UnaryOperationNot (TAC [])) (sel1 defTac),n,temp) 
                                                                                                            UnaryOperationPointer  _ -> (Abs.ExpressionUnaryD (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Point (sel3 defTac) ty])) (Abs.UnaryOperationPointer (TAC [])) (sel1 defTac),n,temp)
{-genTacDefault (Abs.ExpressionIdentD res id index) =
genTacDefault (Abs.ExpressionCallD res id exps) = -}


genTacIdentifierList :: Abs.IDENTLIST TCheckResult -> Prelude.Integer -> Label -> TCheckResult -> (Abs.IDENTLIST TAC,Prelude.Integer,[Address])
genTacIdentifierList (Abs.IdentifierSingle res ident@(Abs.Ident id resi)) n l tres@(TResult env ty pos) = (Abs.IdentifierSingle (TAC []) (Abs.Ident id (TAC [])),n,[buildIDAddr pos id])
genTacIdentifierList (Abs.IdentifierList res ident@(Abs.Ident id resi) idlist) n l tres@(TResult env ty pos)  = let idlistTac = (genTacIdentifierList idlist n l tres) in
                                                                                                                    let idlistAddr = sel3 idlistTac in
                                                                                                                        (Abs.IdentifierList (TAC []) (Abs.Ident id (TAC [])) (sel1 idlistTac),n,[buildIDAddr pos id] ++ idlistAddr)
