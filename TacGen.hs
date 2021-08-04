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

buildIDAddr :: TCheckResult -> Prelude.String -> Address
buildIDAddr (TResult env t pos) id = case Data.Map.lookup id env of
                                Just [Variable tv posv@(Pn a r c) mode override] -> AddrAddress (id++"@"++show r++","++show c)
                                Nothing -> AddrAddress (id++"NOTTTTTTTTTTTTTTTTT")

mergeTac :: TAC -> TAC -> TAC
mergeTac (TAC []) (TAC []) = TAC []
mergeTac (TAC [x]) (TAC []) = TAC [x]
mergeTac (TAC [x]) (TAC (y:ys)) = TAC (x:y:ys)

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
                                                                                                                (Abs.ListStatements (mergeTac (statement_content statTac) (statements_content statsTac)) statTac statsTac,newC)
                                                                Abs.EmptyStatement tres -> let statTac = sel1 (genTacStatement stat n l tres) in
                                                                                                let newC = sel2 (genTacStatement stat n l tres) in
                                                                                                    let newL = newLabel n in
                                                                                                        (Abs.ListStatements (statement_content statTac) statTac (sel1 (genTacStatements stats (n+1) newL)),newC)
genTacStatements (Abs.EmptyStatement tres) n l = ((Abs.EmptyStatement (TAC [])),n)

genTacStatement :: Abs.STATEMENT TCheckResult -> Prelude.Integer -> Label -> TCheckResult -> (Abs.STATEMENT TAC,Prelude.Integer,Address)
genTacStatement (Abs.VariableDeclarationStatement res@(TResult _ ty _) tipo vardec) n l tres = let tipoTac = sel1 (genTacVariableType tipo n l) in
                                                                                let vardecTac = genTacVarDecList vardec n l tres in
                                                                                    let vardecContent = vardeclist_content (sel1 vardecTac) in
                                                                                        let vardecAddrs = sel3 vardecTac in -- variable addresses # >1
                                                                                            let initAddr = sel4 vardecTac in
                                                                                                (Abs.VariableDeclarationStatement (TAC (buildTacEntriesForVarsDecl vardecAddrs initAddr ty)) tipoTac (sel1 vardecTac) ,n,AddrAddress "")
{-genTacStatement Abs.BreakStatement tres)                          = 
genTacStatement (Abs.ContinueStatement tres)                        = 
genTacStatement (Abs.ReturnStatement tres ret)                      = 
genTacStatement (Abs.Statement tres block)                          =
genTacStatement (Abs.ExpressionStatement tres exp)                  =
genTacStatement (Abs.AssignmentStatement tres lval assignOp exp)    =
genTacStatement (Abs.VariableDeclarationStatement tres tipo vardec) = (Abs.VariableDeclarationStatement (TAC []) (genTacVariableDeclarationStatement vardec))
genTacStatement (Abs.ConditionalStatement res condition) n l tres  = ((Abs.ContinueStatement (TAC [])),n,AddrAddress "")
genTacStatement (Abs.WhileDoStatement tres whileStaement)           = 
genTacStatement (Abs.DoWhileStatement tres doStatement)             = 
genTacStatement (Abs.ForStatement tres forStatement)                = 
genTacStatement (Abs.ProcedureStatement tres id param states)       =                                              
genTacStatement (Abs.FunctionStatement tres id param tipo states)   =-}



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
genTacVarDecId (Abs.VariableDeclaration res idlist typepart initpart) n l tres = case initpart of
                                                                                InitializzationPartEmpty resi -> let idlistTac = genTacIdentifierList idlist n l tres in
                                                                                                                    let tacId = identlist_content (sel1 idlistTac) in
                                                                                                                        let addrIdList = sel3 idlistTac in
                                                                                                                            let initAddr = AddrNULL in
                                                                                                                                (Abs.VariableDeclaration (TAC []) (sel1 idlistTac) (Abs.TypePart (TAC []) (TypeExpression (TAC []) (Abs.PrimitiveTypeInt (TAC [])))) (Abs.InitializzationPartEmpty (TAC [])),n,addrIdList,initAddr)
                                                                                InitializzationPart resi expr -> let idlistTac = genTacIdentifierList idlist n l tres in
                                                                                                                    let tacId = identlist_content (sel1 idlistTac) in
                                                                                                                        let addrIdList = sel3 idlistTac in
                                                                                                                            let exprTac = (genTacExpression expr n l tres) in
                                                                                                                                let initTac = (Abs.InitializzationPart (TAC []) (sel1 exprTac)) in
                                                                                                                                    let initAddr = sel3 exprTac in
                                                                                                                                        (Abs.VariableDeclaration (TAC []) (sel1 idlistTac) (Abs.TypePart (TAC []) (TypeExpression (TAC []) (Abs.PrimitiveTypeInt (TAC [])))) initTac ,n,addrIdList,initAddr)
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
genTacExpression (Abs.ExpressionBracket res exp)                                n l tres = let exprTac = genTacExpression exp n l tres in (Abs.ExpressionBracket (TAC []) (sel1 exprTac),n, (sel3 exprTac))
{-genTacExpression (Abs.ExpressionCast res def tipo)  =-}   
genTacExpression (Abs.ExpressionUnary res unary def)                            n l tres = let defTac = genTacDefault def n l tres in (case unary of 
                                                                                                                                            UnaryOperationPositive _ -> (Abs.ExpressionUnary (TAC []) Abs.UnaryOperationPositive (TAC [])
                                                                                                                                            UnaryOperationNegative _ -> (Abs.ExpressionUnary (TAC []) Abs.UnaryOperationNegative (TAC [])
                                                                                                                                            UnaryOperationNot      _ -> (Abs.ExpressionUnary (TAC []) Abs.UnaryOperationNot (TAC [])
                                                                                                                                            UnaryOperationPointer  _ -> (Abs.ExpressionUnary (TAC []) Abs.UnaryOperationPointer (TAC []))
                                                                                                                                        (sel1 defTac),n,(sel3 defTac)) 
{-genTacExpression (Abs.ExpressionBinary res def binary) =
genTacExpression (Abs.ExpressionIdent res id index) =
genTacExpression (Abs.ExpressionCall res id exps) = -}
-- TacAssignUnaryOp  {getAddr:: Address, unaryOp  :: TacUnaryOp,  first::Address, second :: Address, assignType::Type} --        x = + y

genTacDefault :: Abs.DEFAULT TCheckResult -> Prelude.Integer -> Label -> TCheckResult -> (Abs.DEFAULT TAC,Prelude.Integer,Address)
genTacDefault (Abs.ExpressionIntegerD res value@(Abs.Integer val resi))       n l tres = (Abs.ExpressionIntegerD (TAC []) (Abs.Integer val (TAC [])),n, AddrInt val)
genTacDefault (Abs.ExpressionBooleanD res value@(Abs.Boolean_true resi))      n l tres = (Abs.ExpressionBooleanD (TAC []) (Abs.Boolean_true (TAC [])),n, AddrBool True)
genTacDefault (Abs.ExpressionBooleanD res value@(Abs.Boolean_false resi))     n l tres = (Abs.ExpressionBooleanD (TAC []) (Abs.Boolean_false (TAC [])),n, AddrBool False)
genTacDefault (Abs.ExpressionBooleanD res value@(Abs.Boolean_True resi))      n l tres = (Abs.ExpressionBooleanD (TAC []) (Abs.Boolean_True (TAC [])),n, AddrBool True)
genTacDefault (Abs.ExpressionBooleanD res value@(Abs.Boolean_False resi))     n l tres = (Abs.ExpressionBooleanD (TAC []) (Abs.Boolean_False (TAC [])),n, AddrBool False)
genTacDefault (Abs.ExpressionCharD res value@(Abs.Char val resi))             n l tres = (Abs.ExpressionCharD (TAC []) (Abs.Char val (TAC [])),n, AddrChar val)
genTacDefault (Abs.ExpressionStringD res value@(Abs.String val resi))         n l tres = (Abs.ExpressionStringD (TAC []) (Abs.String val (TAC [])),n, AddrString val)
genTacDefault (Abs.ExpressionRealD res value@(Abs.Real val resi))             n l tres = (Abs.ExpressionRealD (TAC []) (Abs.Real val (TAC [])),n, AddrReal val)
genTacDefault (Abs.ExpressionBracketD res exp)                                n l tres = let exprTac = genTacExpression exp n l tres in (Abs.ExpressionBracketD (TAC []) (sel1 exprTac),n, (sel3 exprTac))
{-genTacDefault (Abs.ExpressionCastD res def tipo)  =   
genTacDefault (Abs.ExpressionUnaryD res unary def)                            n l tres = let defTac = genTacDefault def n l tres in (Abs.ExpressionUnary (TAC []) (case unary of ...) (sel1 defTac)) 
genTacDefault (Abs.ExpressionIdentD res id index) =
genTacDefault (Abs.ExpressionCallD res id exps) = -}


genTacIdentifierList :: Abs.IDENTLIST TCheckResult -> Prelude.Integer -> Label -> TCheckResult -> (Abs.IDENTLIST TAC,Prelude.Integer,[Address])
genTacIdentifierList (Abs.IdentifierSingle res ident@(Abs.Ident id resi)) n l tres = (Abs.IdentifierSingle (TAC []) (Abs.Ident id (TAC [])),n,[buildIDAddr tres id])
genTacIdentifierList (Abs.IdentifierList res ident@(Abs.Ident id resi) idlist) n l tres = let idlistTac = (genTacIdentifierList idlist n l tres) in
                                                                                            let idlistAddr = sel3 idlistTac in
                                                                                                (Abs.IdentifierList (TAC []) (Abs.Ident id (TAC [])) (sel1 idlistTac),n,[buildIDAddr tres id] ++ idlistAddr)
