module TacGen where

import AbsTac as Tac
import AbsProgettoPar as Abs
import LexProgettoPar (Posn(..))
import TypeChecker
import Type
import Data.Map

first :: (a,b,c) -> a
first (a,b,c) = a

second :: (a,b,c) -> b
second (a,b,c) = b

third :: (a,b,c) -> c
third (a,b,c) = c

newLabel :: Prelude.Integer -> Label
newLabel n = Label ("L"++show n++":")

getID :: TCheckResult -> Prelude.String -> Address
getID (TResult env t pos) id = case Data.Map.lookup id env of
                                Just [Variable tv posv@(Pn a r c) mode override] -> AddrAddress (id++"_"++show r++","++show c)

mergeTac :: TAC -> TAC -> TAC
mergeTac (TAC []) (TAC []) = TAC []
mergeTac (TAC [x]) (TAC []) = TAC [x]
mergeTac (TAC [x]) (TAC (y:ys)) = TAC (x:y:ys)

getAddrContent :: Address -> Prelude.String 
getAddrContent (AddrAddress s) = s
getAddrContent (AddrString s) = s

getTacEntry :: TAC -> [TACEntry]
getTacEntry (TAC e) = e

mergeAddr :: Address -> Address -> Address
mergeAddr (AddrAddress s1) (AddrAddress s2) = AddrAddress (s1++" "++s2)
mergeAddr (AddrAddress s1) (AddrString s2) = AddrAddress (s1++" "++s2)
mergeAddr (AddrString s1) (AddrAddress s2) = AddrAddress (s1++" "++s2)
mergeAddr (AddrString s1) (AddrString s2) = AddrString (s1++" "++s2)

removePos :: Prelude.String -> Prelude.String
removePos (x:xs) = if (x=='_') then xs else removePos xs

getListId :: Prelude.String -> Prelude.String -> [Prelude.String] -> [Prelude.String]
getListId [] zs res = [zs]++res
getListId (x:xs) zs res = if (x==',') then getListId xs [] ([zs]++res) else getListId xs (zs++[x]) res

getPos :: Prelude.String  -> Prelude.String -> Prelude.String
getPos (x:xs) zs = if (x=='_') then zs else TacGen.getPos xs ([x]++zs)

-- Given the start of a program (starting node Abs.S); starts the TAC generation process
genTAC :: Abs.S TCheckResult -> Abs.S TAC
genTAC (Abs.StartCode tres stats) = let endLab = newLabel 0 in
                                        let statsTac = TacGen.first (genTacStatements stats 1 endLab) in
                                            let tacs = (statements_content statsTac) in
                                                (Abs.StartCode (TAC ((content tacs)++(TacLabel endLab):[ExitTac])) statsTac)

genTacStatements :: Abs.STATEMENTS TCheckResult -> Prelude.Integer -> Label -> (Abs.STATEMENTS TAC,Prelude.Integer,Address)
genTacStatements (Abs.ListStatements tres stat stats) n l = case stats of
                                                                Abs.ListStatements tres stat stats -> let statTac = TacGen.first (genTacStatement stat n l tres) in
                                                                                                        let newN = TacGen.second (genTacStatement stat n l tres) in
                                                                                                            let newL = newLabel n in
                                                                                                                ((Abs.ListStatements (statement_content statTac) statTac (TacGen.first (genTacStatements stats (n+1) newL)),newN,AddrAddress ""))
                                                                Abs.EmptyStatement tres -> let statTac = TacGen.first (genTacStatement stat n l tres) in
                                                                                                let newN = TacGen.second (genTacStatement stat n l tres) in
                                                                                                    let newL = newLabel n in
                                                                                                                ((Abs.ListStatements (statement_content statTac) statTac (TacGen.first (genTacStatements stats (n+1) newL)),newN,AddrAddress ""))
genTacStatements (Abs.EmptyStatement tres) n l = ((Abs.EmptyStatement (TAC []) ),n,AddrAddress "")

genTacStatement :: Abs.STATEMENT TCheckResult -> Prelude.Integer -> Label -> TCheckResult -> (Abs.STATEMENT TAC,Prelude.Integer,Address)
genTacStatement (Abs.VariableDeclarationStatement res tipo vardec) n l tres = let tipoTac = TacGen.first (genTacVariableType tipo n l) in
                                                                                let vardecTac = genTacVarDecList vardec n l tres in
                                                                                    let vardecContent = vardeclist_content (TacGen.first vardecTac) in
                                                                                        let vardecAddr = third vardecTac in
                                                                                            (Abs.VariableDeclarationStatement (TAC [TacAssignRelOp vardecAddr EqInt (AddrString "") (AddrString "") (B_type Type_Void)]) tipoTac (TacGen.first vardecTac) ,n,AddrAddress "")
{-genTacStatement Abs.BreakStatement tres)                           = 
genTacStatement (Abs.ContinueStatement tres)                        = 
genTacStatement (Abs.ReturnStatement tres ret)                      = 
genTacStatement (Abs.Statement tres block)                          =
genTacStatement (Abs.ExpressionStatement tres exp)                  =
genTacStatement (Abs.AssignmentStatement tres lval assignOp exp)    =
genTacStatement (Abs.VariableDeclarationStatement tres tipo vardec) = (Abs.VariableDeclarationStatement (TAC []) (genTacVariableDeclarationStatement vardec))-}
genTacStatement (Abs.ConditionalStatement res condition) n l tres  = ((Abs.ContinueStatement (TAC [])),n,AddrAddress ""){-
genTacStatement (Abs.WhileDoStatement tres whileStaement)           = 
genTacStatement (Abs.DoWhileStatement tres doStatement)             = 
genTacStatement (Abs.ForStatement tres forStatement)                = 
genTacStatement (Abs.ProcedureStatement tres id param states)       =                                              
genTacStatement (Abs.FunctionStatement tres id param tipo states)   =-}

genTacVariableType :: Abs.VARIABLETYPE TCheckResult -> Prelude.Integer -> Label ->  (Abs.VARIABLETYPE TAC,Prelude.Integer,Address)
genTacVariableType (Abs.VariableTypeParam res) n l = (Abs.VariableTypeParam (TAC []),n,AddrAddress "")
genTacVariableType (Abs.VariableTypeConst res) n l = (Abs.VariableTypeConst (TAC []),n,AddrAddress "")
genTacVariableType (Abs.VariableTypeVar res) n l = (Abs.VariableTypeVar (TAC []),n,AddrAddress "")
genTacVariableType (Abs.VariableTypeRef res) n l = (Abs.VariableTypeRef (TAC []),n,AddrAddress "")
genTacVariableType (Abs.VariableTypeConstRef res) n l= (Abs.VariableTypeConstRef (TAC []),n,AddrAddress "")

genTacVarDecList :: Abs.VARDECLIST TCheckResult -> Prelude.Integer -> Label -> TCheckResult -> (Abs.VARDECLIST TAC,Prelude.Integer,Address)
genTacVarDecList (Abs.VariableDeclarationSingle res vardecId) n l tres = let vardecIdTac = genTacVarDecId vardecId n l tres in
                                                                            let vardecIdAddr = third vardecIdTac in
                                                                                (Abs.VariableDeclarationSingle (vardecid_content (TacGen.first vardecIdTac)) (TacGen.first vardecIdTac),n,vardecIdAddr)

genTacVarDecId :: Abs.VARDECID TCheckResult -> Prelude.Integer -> Label -> TCheckResult -> (Abs.VARDECID TAC,Prelude.Integer,Address)
genTacVarDecId (Abs.VariableDeclaration res idlist typepart initpart) n l tres = case initpart of
                                                                                InitializzationPartEmpty resi -> let idlistTac = genTacIdentifierList idlist n l tres in
                                                                                                                    let tacId = identlist_content (TacGen.first idlistTac) in
                                                                                                                        let addrIdLis = third idlistTac in
                                                                                                                                (Abs.VariableDeclaration (TAC []) (TacGen.first idlistTac) (Abs.TypePart (TAC []) (TypeExpression (TAC []) (Abs.PrimitiveTypeInt (TAC [])))) (Abs.InitializzationPartEmpty (TAC [])),n,addrIdLis)

genTacIdentifierList :: Abs.IDENTLIST TCheckResult -> Prelude.Integer -> Label -> TCheckResult -> (Abs.IDENTLIST TAC,Prelude.Integer,Address)
genTacIdentifierList (Abs.IdentifierSingle res ident@(Abs.Ident id resi)) n l tres = (Abs.IdentifierSingle (TAC []) (Abs.Ident id (TAC [])),n,getID tres id)
--genTacIdentifierList (Abs.IdentifierList res ident@(Abs.Ident id resi) idlist) n l tres = let idlistTac = TacGen.first (genTacIdentifierList idlist n l tres) in
--                                                                                            (Abs.IdentifierList (TAC ([(TacIdentifier (AddrAddress (id++","++(getAddrContent (getAddrTacEntry (identlist_content idlistTac))))))]))
--                                                                                                                 (Abs.Ident id (TAC [])) idlistTac,n)
