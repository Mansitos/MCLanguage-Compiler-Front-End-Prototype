-- Progetto Linguaggi e Compilatori parte 3 - UNIUD 2021
-- Andrea Mansi & Christian Cagnoni

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
instance Sel1 (a1,a2,a3,a4,a5,a6) a1 where sel1 (x,_,_,_,_,_) = x

class Sel2 a b | a -> b where sel2 :: a -> b
instance Sel2 (a1,a2) a2 where sel2 (_,x) = x
instance Sel2 (a1,a2,a3) a2 where sel2 (_,x,_) = x
instance Sel2 (a1,a2,a3,a4) a2 where sel2 (_,x,_,_) = x
instance Sel2 (a1,a2,a3,a4,a5) a2 where sel2 (_,x,_,_,_) = x
instance Sel2 (a1,a2,a3,a4,a5,a6) a2 where sel2 (_,x,_,_,_,_) = x

class Sel3 a b | a -> b where sel3 :: a -> b
instance Sel3 (a1,a2,a3) a3 where sel3 (_,_,x) = x
instance Sel3 (a1,a2,a3,a4) a3 where sel3 (_,_,x,_) = x
instance Sel3 (a1,a2,a3,a4,a5) a3 where sel3 (_,_,x,_,_) = x
instance Sel3 (a1,a2,a3,a4,a5,a6) a3 where sel3 (_,_,x,_,_,_) = x

class Sel4 a b | a -> b where sel4 :: a -> b
instance Sel4 (a1,a2,a3,a4) a4 where sel4 (_,_,_,x) = x
instance Sel4 (a1,a2,a3,a4,a5) a4 where sel4 (_,_,_,x,_) = x
instance Sel4 (a1,a2,a3,a4,a5,a6) a4 where sel4 (_,_,_,x,_,_) = x

class Sel5 a b | a -> b where sel5 :: a -> b
instance Sel5 (a1,a2,a3,a4,a5) a5 where sel5 (_,_,_,_,x) = x
instance Sel5 (a1,a2,a3,a4,a5,a6) a5 where sel5 (_,_,_,_,x,_) = x

class Sel6 a b | a -> b where sel6 :: a -> b
instance Sel6 (a1,a2,a3,a4,a5,a6) a6 where sel6 (_,_,_,_,_,x) = x

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

isElseLabel :: Label -> Prelude.Bool     
isElseLabel (Label (x:xs)) = (x=='e')
isElseLabel _ = False

-- Given an Address, return the string of it's content. Used in printing.
showAddrContent :: Address -> Prelude.String 
showAddrContent (AddrString s) = "\"" ++ s ++ "\""
showAddrContent (AddrInt s) = show s    
showAddrContent (AddrBool s) = show s   
showAddrContent (AddrReal s) = show s   
showAddrContent (AddrChar s) = show s   
showAddrContent (AddrAddress s) = s
showAddrContent (AddrNULL) = "NULL"  

-- Given a list of variable addresses and the value (address) of RightInitialization builds the list of TAC codes for each init/decl.
-- Example: var x,y,z:int = 5
--      the list of address are the address for x,y,z
--      the address for rExpr is the address of 5
--      returns a list of 3 tac entries (one for each variable initialized at addr. of 5)
buildTacEntriesForVarsDecl :: [Address] -> [Address] -> Type -> Prelude.Integer -> Prelude.Integer -> [TACEntry]
------------------------------------------------------   
buildTacEntriesForVarsDecl [x] [r] (Pointer t p) dim n = case r of  -- single, pointer
    AddrNULL -> [TacPointRef (buildArrayId x n dim) (genDefaultInitAddr (Pointer t p))]
    _ -> [TacPointRef (buildArrayId x n dim) r]
buildTacEntriesForVarsDecl [x] [r] (Array t d) dim n = buildTacEntriesForVarsDecl [x] [r] t dim n
buildTacEntriesForVarsDecl [x] [r] ty dim n = case r of     -- single, not pointer
    AddrNULL -> [TacAssignNullOp (buildArrayId x n dim) (genDefaultInitAddr ty) ty]
    _ -> [TacAssignNullOp (buildArrayId x n dim) r ty]
------------------------------------------------------ 
buildTacEntriesForVarsDecl [x] (r:rs) (Pointer t p) dim n = case r of -- TODO
    AddrNULL -> [TacPointRef (buildArrayId x n dim) (genDefaultInitAddr (Pointer t p))] ++ buildTacEntriesForVarsDecl [x] rs (Pointer t p) dim (n+dim)
    _ -> [TacPointRef (buildArrayId x n dim) r] ++ buildTacEntriesForVarsDecl [x] rs (Pointer t p) dim (n+dim)
buildTacEntriesForVarsDecl [x] (r:rs) (Array t d) dim n = buildTacEntriesForVarsDecl [x] (r:rs) t dim n
buildTacEntriesForVarsDecl [x] (r:rs) ty dim n = case r of
    AddrNULL -> [TacAssignNullOp (buildArrayId x n dim) (genDefaultInitAddr ty) ty] ++ buildTacEntriesForVarsDecl [x] rs ty dim (n+dim)
    _ -> [TacAssignNullOp (buildArrayId x n dim) r ty] ++ buildTacEntriesForVarsDecl [x] rs ty dim (n+dim)
------------------------------------------------------ 
buildTacEntriesForVarsDecl (x:xs) [r] (Pointer t p) dim n = case r of -- multiple, pointers
    AddrNULL -> [TacPointRef (buildArrayId x n dim) (genDefaultInitAddr (Pointer t p))] ++ buildTacEntriesForVarsDecl xs [r] (Pointer t p) dim n
    _ -> [TacPointRef (buildArrayId x n dim) r] ++ buildTacEntriesForVarsDecl xs [r] (Pointer t p) dim n
buildTacEntriesForVarsDecl (x:xs) [r] (Array t d) dim n = buildTacEntriesForVarsDecl (x:xs) [r] t dim n
buildTacEntriesForVarsDecl (x:xs) [r] ty dim n = case r of -- multiple, not pointers
    AddrNULL -> [TacAssignNullOp (buildArrayId x n dim) (genDefaultInitAddr ty)  ty] ++ buildTacEntriesForVarsDecl xs [r] ty dim n
    _ -> [TacAssignNullOp (buildArrayId x n dim) r ty] ++ buildTacEntriesForVarsDecl xs [r] ty dim n
------------------------------------------------------ 
-- TODO versione pointers
buildTacEntriesForVarsDecl (x:xs) (r:rs) (Pointer t p) dim n =  [TacPointRef (buildArrayId x n dim) r] ++ buildTacEntriesForVarsDecl [x] rs (Pointer t p) dim (n+dim) ++ buildTacEntriesForVarsDecl xs (r:rs) (Pointer t p) dim 0
buildTacEntriesForVarsDecl (x:xs) (r:rs) (Array t d) dim n = buildTacEntriesForVarsDecl (x:xs) (r:rs) t dim n
buildTacEntriesForVarsDecl (x:xs) (r:rs) ty dim n =  [TacAssignNullOp (buildArrayId x n dim) r ty] ++ buildTacEntriesForVarsDecl [x] rs ty dim (n+dim) ++ buildTacEntriesForVarsDecl xs (r:rs) ty dim 0

buildArrayId :: Address -> Prelude.Integer -> Prelude.Integer -> Address
buildArrayId (AddrAddress str) n dim = case dim of
                                        -1 -> AddrAddress str
                                        _ -> AddrAddress (str++"["++show n++"]")

buildArrayIdNoInteger :: Address -> Address -> Address
buildArrayIdNoInteger (AddrAddress str1) (AddrAddress str2) = AddrAddress (str1++"["++str2++"]")

-- Generate a default address for default values
-- Example: declaring a variable of time int without initialization: the default init. value is 0; so a int address of val. 0 must be generated.
genDefaultInitAddr :: Type -> Address
genDefaultInitAddr ty = case ty of
    B_type Type_Integer  -> AddrInt 0
    B_type Type_Boolean  -> AddrBool False 
    B_type Type_Char     -> AddrChar ' '
    B_type Type_String   -> AddrString ""   
    B_type Type_Real     -> AddrReal  0.0
    Array t _            -> genDefaultInitAddr t
    Pointer t _          -> AddrNULL

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

-- Get a PrimitiveType node of the ABS, returns the correct Type
getTypeFromPrimitive :: Abs.PRIMITIVETYPE TCheckResult -> Type
getTypeFromPrimitive (Abs.PrimitiveTypeVoid _)   = (B_type Type_Void)
getTypeFromPrimitive (Abs.PrimitiveTypeBool _)   = (B_type Type_Boolean)
getTypeFromPrimitive (Abs.PrimitiveTypeInt _)    = (B_type Type_Integer)
getTypeFromPrimitive (Abs.PrimitiveTypeReal _)   = (B_type Type_Real)
getTypeFromPrimitive (Abs.PrimitiveTypeString _) = (B_type Type_String)
getTypeFromPrimitive (Abs.PrimitiveTypeChar _)   = (B_type Type_Char)
getTypeFromPrimitive (Abs.TypeArray _ prim)      = (Type.Array (TacGen.getTypeFromPrimitive prim) 0) -- 0 is placeholder TODO

-- Get a Default node of the ABS, returns the correct Type
getTypeFromDefault :: Abs.DEFAULT TCheckResult -> Type
getTypeFromDefault (Abs.ExpressionIntegerD res@(TResult _ ty _) value) = ty
getTypeFromDefault (Abs.ExpressionBooleanD res@(TResult _ ty _) value) = ty
getTypeFromDefault (Abs.ExpressionCharD    res@(TResult _ ty _) value) = ty
getTypeFromDefault (Abs.ExpressionStringD  res@(TResult _ ty _) value) = ty
getTypeFromDefault (Abs.ExpressionRealD    res@(TResult _ ty _) value) = ty
getTypeFromDefault (Abs.ExpressionBracketD res@(TResult _ ty _) exp)   = ty
getTypeFromDefault (Abs.ExpressionCastD    res@(TResult _ ty _) def tipo)   = ty
getTypeFromDefault (Abs.ExpressionUnaryD   res@(TResult _ ty _) unary def)  = ty
getTypeFromDefault (Abs.ExpressionCallD    res@(TResult _ ty _) ident exps) = ty
getTypeFromDefault (Abs.ExpressionIdentD   res@(TResult _ ty _) ident arrayIndex) = ty

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
buildAssignTac :: Abs.ASSIGNOP TCheckResult -> [Address] -> [TACEntry] -> Address -> Type -> [TACEntry]
buildAssignTac assignOp (leftAddr:xs) (a:arr) rightAddr t = case assignOp of
                                                        (Abs.AssignOperationEq _ )         -> [TacAssignNullOp   leftAddr rightAddr t] ++ [a] ++ buildAssignTac assignOp xs arr rightAddr t
                                                        (Abs.AssignOperationEqPlus _ )     -> [TacAssignBinaryOp leftAddr (buildOp t "plus") leftAddr rightAddr t] ++ [a] ++ buildAssignTac assignOp xs arr rightAddr t
                                                        (Abs.AssignOperationEqMinus _ )    -> [TacAssignBinaryOp leftAddr (buildOp t "minus") leftAddr rightAddr t] ++ [a] ++ buildAssignTac assignOp xs arr rightAddr t
                                                        (Abs.AssignOperationEqProd _ )     -> [TacAssignBinaryOp leftAddr (buildOp t "product") leftAddr rightAddr t] ++ [a] ++ buildAssignTac assignOp xs arr rightAddr t
                                                        (Abs.AssignOperationEqFract _ )    -> [TacAssignBinaryOp leftAddr (buildOp t "division") leftAddr rightAddr t] ++ [a] ++ buildAssignTac assignOp xs arr rightAddr t
                                                        (Abs.AssignOperationEqPercent _ )  -> [TacAssignBinaryOp leftAddr (buildOp t "module") leftAddr rightAddr t] ++ [a] ++ buildAssignTac assignOp xs arr rightAddr t
                                                        (Abs.AssignOperationEqPower _ )    -> [TacAssignBinaryOp leftAddr (buildOp t "power") leftAddr rightAddr t] ++ [a] ++ buildAssignTac assignOp xs arr rightAddr t
buildAssignTac assignOp (leftAddr:xs) [] rightAddr t = case assignOp of
                                                        (Abs.AssignOperationEq _ )         -> [TacAssignNullOp   leftAddr rightAddr t] ++ buildAssignTac assignOp xs [] rightAddr t
                                                        (Abs.AssignOperationEqPlus _ )     -> [TacAssignBinaryOp leftAddr (buildOp t "plus") leftAddr rightAddr t] ++ buildAssignTac assignOp xs [] rightAddr t
                                                        (Abs.AssignOperationEqMinus _ )    -> [TacAssignBinaryOp leftAddr (buildOp t "minus") leftAddr rightAddr t] ++ buildAssignTac assignOp xs [] rightAddr t
                                                        (Abs.AssignOperationEqProd _ )     -> [TacAssignBinaryOp leftAddr (buildOp t "product") leftAddr rightAddr t] ++ buildAssignTac assignOp xs [] rightAddr t
                                                        (Abs.AssignOperationEqFract _ )    -> [TacAssignBinaryOp leftAddr (buildOp t "division") leftAddr rightAddr t] ++ buildAssignTac assignOp xs [] rightAddr t
                                                        (Abs.AssignOperationEqPercent _ )  -> [TacAssignBinaryOp leftAddr (buildOp t "module") leftAddr rightAddr t] ++ buildAssignTac assignOp xs [] rightAddr t
                                                        (Abs.AssignOperationEqPower _ )    -> [TacAssignBinaryOp leftAddr (buildOp t "power") leftAddr rightAddr t] ++ buildAssignTac assignOp xs [] rightAddr t
buildAssignTac _ [] _ _ _ = []

generateDimForArray_ :: Abs.TYPEEXPRESSIONFUNC TCheckResult -> Prelude.Integer
generateDimForArray_ (Abs.TypeExpressionFunction _ typeexp) = generateDimForArray typeexp
generateDimForArray_ (Abs.TypeExpressionArrayOfPointer _ typeexpf) = generateDimForArray_ typeexpf

generateDimForArray :: Abs.TYPEEXPRESSION TCheckResult -> Prelude.Integer
generateDimForArray (Abs.TypeExpression _ prim) = generateDimForArrayPrim prim
generateDimForArray (Abs.TypeExpressionArraySimple _ _ typeexp) = generateDimForArray_ typeexp
generateDimForArray (Abs.TypeExpressionArray _ _ typeexp) = generateDimForArray_ typeexp
generateDimForArray (Abs.TypeExpressionPointer _ prim _) = 2 * generateDimForArrayPrim prim
generateDimForArray (Abs.TypeExpressionPointerOfArray _ typeexp _) = 2 * generateDimForArray_ typeexp

generateDimForArrayPrim :: Abs.PRIMITIVETYPE TCheckResult -> Prelude.Integer
generateDimForArrayPrim (Abs.PrimitiveTypeVoid _ ) = 0
generateDimForArrayPrim (Abs.PrimitiveTypeBool _ ) = 1
generateDimForArrayPrim (Abs.PrimitiveTypeInt  _ ) = 4
generateDimForArrayPrim (Abs.PrimitiveTypeReal _ ) = 8
generateDimForArrayPrim (Abs.PrimitiveTypeString _ ) = 8
generateDimForArrayPrim (Abs.PrimitiveTypeChar _ ) = 1

findArray :: [EnvEntry] -> [EnvEntry]
findArray ((Variable ty@(Array _ _) pos mode override s):xs) = [Variable ty pos mode override s]
findArray (x:xs) = case x of
                    Variable (Pointer t depth) pos mode override s -> let finder = findArray [Variable t pos mode override s] in
                                                                        case finder of
                                                                            [] -> findArray xs
                                                                            _ -> [x]
                    Variable t pos mode override s -> findArray xs
findArray [] = []

generateDimForArrayFromType :: Type -> Prelude.Integer
generateDimForArrayFromType (B_type Type_Void) = 0
generateDimForArrayFromType (B_type Type_Boolean) = 1
generateDimForArrayFromType (B_type Type_Integer) = 4
generateDimForArrayFromType (B_type Type_Real) = 8
generateDimForArrayFromType (B_type Type_String) = 8
generateDimForArrayFromType (B_type Type_Char) = 1
generateDimForArrayFromType (Array t _) = generateDimForArrayFromType t
generateDimForArrayFromType (Pointer t _) = 2 * generateDimForArrayFromType t

buildInitArray :: Address -> Prelude.Integer -> [Address]
buildInitArray a 1 = [a]
buildInitArray a n = [a]++buildInitArray a (n-1)

buildPosArrayNoInteger :: [Address] -> [Prelude.Integer] -> Prelude.Integer -> Prelude.Integer -> ([TACEntry],Prelude.Integer) --forse da eliminare
buildPosArrayNoInteger (i:is) (p:ps) dim n = let next= (buildPosArrayNoInteger is ps dim (n+1)) in
                                                ([TacAssignBinaryOp (newTemp n) IntMul i (AddrInt ((buildPosArray_ ps) * dim)) (B_type Type_Integer)] ++ (sel1 next),sel2 next)
buildPosArrayNoInteger _ _ _ n = ([],n-2)

buildArrayCommentsNoInteger :: [Address] -> [Prelude.Integer] -> Prelude.Integer -> Type -> [TACEntry]
buildArrayCommentsNoInteger (i:is) (p:ps) dim t = let result = buildPosArrayCNoInteger (p:ps) dim in 
                                                    let product = buildProductComment ps in
                                                        [TacComment (product++"sizeof("++showReal t++")="++show result)]                                                        
buildArrayCommentsNoInteger (i:is) [] dim t = let result = (buildPosArrayCNoInteger [] dim)*dim in 
                                                [TacComment ("sizeof("++showReal t++")="++show result)]                                                           
buildArrayCommentsNoInteger _ _ _ _ = []

buildPosArrayCNoInteger :: [Prelude.Integer] -> Prelude.Integer -> Prelude.Integer
buildPosArrayCNoInteger (p:ps) dim = (buildPosArrayNoInteger_ ps) * dim 
buildPosArrayCNoInteger _ _ = 1

buildPosArrayNoInteger_ :: [Prelude.Integer] -> Prelude.Integer
buildPosArrayNoInteger_ (p:ps) = p*(buildPosArrayNoInteger_ ps)
buildPosArrayNoInteger_ [] = 1

buildPosArray :: [Address] -> [Prelude.Integer] -> Prelude.Integer -> Prelude.Integer
buildPosArray (i:is) (p:ps) dim = ((content_addr_int i)-1) * (buildPosArray_ ps) * dim + (buildPosArray is ps dim)
buildPosArray _ _ _ = 0

buildPosArray_ :: [Prelude.Integer] -> Prelude.Integer
buildPosArray_ (p:ps) = p*(buildPosArray_ ps)
buildPosArray_ [] = 1

buildPosArrayC :: [Address] -> [Prelude.Integer] -> Prelude.Integer -> Prelude.Integer
buildPosArrayC (i:is) (p:ps) dim = ((content_addr_int i)-1) * (buildPosArray_ ps) * dim 
buildPosArrayC _ _ _ = 1

showReal :: Type -> Prelude.String
showReal (Array t _) = show t
showReal (Pointer t _) = "&anything"
showReal t = show t

buildArrayComments :: [Address] -> [Prelude.Integer] -> Prelude.Integer -> Type -> [TACEntry]
buildArrayComments (i:is) (p:ps) dim t = let result = buildPosArrayC (i:is) (p:ps) dim in
                                            let product = buildProductComment ps in
                                                [TacComment ((show ((content_addr_int i)-1))++"*"++product++"sizeof("++showReal t++")="++show result)] ++ buildArrayComments is ps dim t
buildArrayComments _ _ _ _ = []

buildProductComment :: [Prelude.Integer] -> Prelude.String
buildProductComment (x:xs) = show x++"*"++buildProductComment xs
buildProductComment [] = ""

mergeComments :: [TACEntry] -> Prelude.String
mergeComments ((TacComment str):xs) = str++"\t"++(if xs==[] then "" else "\t # ")++mergeComments xs
mergeComments [] = ""

getRealTypeFromArray :: Type -> Type
getRealTypeFromArray (Array t _) = getRealTypeFromArray t
getRealTypeFromArray t = t

isIntegerAddress :: [Address] -> Prelude.Bool
isIntegerAddress ((AddrInt _):xs) = isIntegerAddress xs
isIntegerAddress ((_):xs) = False
isIntegerAddress [] = True


getElem :: [Prelude.Integer] -> Prelude.Integer -> [Prelude.Integer]
getElem _ (-1) = []
getElem x n = getElem_ x n []

getElem_ :: [Prelude.Integer] -> Prelude.Integer -> [Prelude.Integer] -> [Prelude.Integer]
getElem_ [] n r = []
getElem_ (x:xs) 0 r = r++[x]
getElem_ (x:xs) n r = getElem_ xs (n-1) (r++[x])

updateTac :: [TACEntry] -> Label -> [TACEntry]
updateTac [TacConditionalJump dest flag first] l = [TacConditionalJump l False first]
updateTac ((TacConditionalJump dest flag first):[x]) l = [TacConditionalJump l False first]++[x]
updateTac (x:xs) l = [x]++updateTac xs l
updateTac [] l = []

removeDuplicates ::  [TACEntry] -> [TACEntry] -> [TACEntry]
removeDuplicates (x:xs) zs = case x of
                                TacLabel {} -> if x `elem` zs then removeDuplicates xs zs  else removeDuplicates xs (zs++[x])
                                _ -> removeDuplicates xs (zs++[x])
removeDuplicates [] zs = zs

getRealTacType :: Type -> Type
getRealTacType (Array t _) =  t
getRealTacType (Pointer t _) =  t
getRealTacType t = t

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
                                                                Abs.ListStatements tres _ _ -> let statTac = genTacStatement stat n l k (w,j) in
                                                                                                    let newC = sel2 statTac in
                                                                                                        let newL = newLabel "" (sel3 statTac) in
                                                                                                            let statsTac = genTacStatements stats newC newL (sel3 statTac) (w,j) in
                                                                                                                (Abs.ListStatements (merge2Tacs (statement_content (sel1 statTac)) (statements_content (sel1 statsTac))) (sel1 statTac) (sel1 statsTac),sel2 statsTac,sel3 statsTac)
                                                                Abs.EmptyStatement tres -> let statTac = genTacStatement stat n l k (w,j) in
                                                                                                let newC = sel2 statTac in
                                                                                                    let newL = newLabel "" (sel3 statTac) in
                                                                                                        (Abs.ListStatements (statement_content (sel1 statTac)) (sel1 statTac) (Abs.EmptyStatement (TAC [] [])),newC,sel3 statTac)
genTacStatements (Abs.EmptyStatement tres) n l k (w,j) = ((Abs.EmptyStatement (TAC [] [])),n,k)

genTacStatement :: Abs.STATEMENT TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.STATEMENT TAC,Prelude.Integer,Prelude.Integer,Address)
genTacStatement (Abs.VariableDeclarationStatement res@(TResult _ ty _) tipo vardec) n l k (w,j) = let tipoTac = genTacVariableType tipo n l k (w,j) in
                                                                                                    let tipoContent = variabletype_content (sel1 tipoTac) in
                                                                                                        let vardecTac = genTacVarDecList vardec n l k (w,j) in
                                                                                                            let vardecContent = vardeclist_content (sel1 vardecTac) in
                                                                                                                let vardecAddrs = sel5 vardecTac in -- variable addresses # >1
                                                                                                                    let initAddr = sel6 vardecTac in
                                                                                                                        let dim = sel4 vardecTac in
                                                                                                                            (Abs.VariableDeclarationStatement (mergeTacs [vardecContent,
                                                                                                                                                                          (TAC (buildTacEntriesForVarsDecl vardecAddrs initAddr ty dim 0) []),
                                                                                                                                                                          tipoContent])
                                                                                                                                                                          (sel1 tipoTac) (sel1 vardecTac) ,(sel2 vardecTac),(sel3 vardecTac),AddrNULL)
genTacStatement (Abs.BreakStatement res) n l k (w,j) = ((Abs.BreakStatement (TAC [TacJump w,TacComment "break jump"] [])),n,k,AddrNULL)
genTacStatement (Abs.ContinueStatement res) n l k (w,j) = ((Abs.ContinueStatement (TAC [TacJump j,TacComment "continue jump"] [])),n,k,AddrNULL)
genTacStatement (Abs.ReturnStatement res ret) n l k (w,j) = case ret of 
    (Abs.ReturnStateEmpty _)  -> ((Abs.ReturnStatement (TAC [TacReturnVoid][]) (Abs.ReturnStateEmpty (TAC [][]))),n,k,AddrNULL)
    (Abs.ReturnState _ expr)  -> let expression = genTacExpression expr n l k (w,j) "" in
                                                                                        ((Abs.ReturnStatement (TAC ((code (expression_content (sel1 expression)))++
                                                                                                               [TacReturn (sel4 expression) (getTypeFromExpr expr)])
                                                                                                               []) (Abs.ReturnState (TAC [][]) (sel1 expression))),(sel2 expression),(sel3 expression),AddrNULL)
genTacStatement (Abs.Statement res block) n l k (w,j) = let newL = newLabel "" k in 
                                                                let newC = sel2 (genTacBlock block n newL k (w,j)) in
                                                                    let blockTac = (genTacBlock block n newL k (w,j)) in (Abs.Statement (b_content (sel1 blockTac)) (sel1 blockTac),newC,(sel3 blockTac),AddrNULL)
genTacStatement (Abs.ExpressionStatement res expstat) n l k (w,j) = let newL = newLabel "" k in
                                                                            let expressionstat = (genTacExpressionStatement expstat n newL k (w,j)) in
                                                                                let newC = sel2 expressionstat in
                                                                                    let exprAddr = sel4 expressionstat in
                                                                                        ((Abs.ExpressionStatement (expressionstatement_content (sel1 expressionstat)) (sel1 expressionstat)),newC,(sel3 expressionstat),exprAddr)
genTacStatement (Abs.AssignmentStatement resres@(TResult _ t _) lval assignOp exp) n l k (w,j) = if t==B_type Type_Boolean
                                                                                                                    then
                                                                                                                        let label = newLabel "endSet" k in
                                                                                                                            let temp = newTemp n in
                                                                                                                                let leftVal = (genTacLeftVal lval (n+1) label (k+1) (w,j)) in
                                                                                                                                    let rightVal = (genTacExpression exp (sel2 leftVal) label (sel3 leftVal) (w,j) "or") in
                                                                                                                                        let newC = sel2 rightVal in
                                                                                                                                            let exprAddr = sel4 rightVal in
                                                                                                                                                let leftValAddrs = sel4 leftVal in
                                                                                                                                                    let lTac = (code (lvalueexpression_content (sel1 leftVal))) in
                                                                                                                                                        let assignTac = case lTac of
                                                                                                                                                                            [] -> (buildAssignTac assignOp leftValAddrs [] temp t) 
                                                                                                                                                                            _ -> case head lTac of
                                                                                                                                                                                TacComment _ -> (buildAssignTac assignOp leftValAddrs (code (lvalueexpression_content (sel1 leftVal))) temp t) 
                                                                                                                                                                                _ -> (code (lvalueexpression_content (sel1 leftVal)))++(buildAssignTac assignOp leftValAddrs [] temp t) in
                                                                                                                                                        ((Abs.AssignmentStatement (mergeTacs [
                                                                                                                                                                                                (TAC [TacAssignNullOp temp (AddrBool True) (B_type Type_Boolean)] []),
                                                                                                                                                                                                (TAC (code (expression_content (sel1 rightVal)))   -- expression (rval) evaluation tac code
                                                                                                                                                                                                        []),
                                                                                                                                                                                                (TAC [TacAssignNullOp temp (AddrBool False) (B_type Type_Boolean)] []),
                                                                                                                                                                                                (TAC [TacLabel label] []),
                                                                                                                                                                                                (TAC assignTac [])
                                                                                                                                                                                            ]) (sel1 leftVal) (genTacAssignOp assignOp) (sel1 rightVal)),newC,(sel3 rightVal)+1,AddrNULL)
                                                                                                                    else
                                                                                                                        let newL = newLabel "" k in
                                                                                                                            let leftVal = (genTacLeftVal lval n newL k (w,j)) in
                                                                                                                                let rightVal = (genTacExpression exp (sel2 leftVal) newL (sel3 leftVal) (w,j) "") in
                                                                                                                                    let newC = sel2 rightVal in
                                                                                                                                        let exprAddr = sel4 rightVal in
                                                                                                                                            let leftValAddrs = sel4 leftVal in
                                                                                                                                                let lTac = (code (lvalueexpression_content (sel1 leftVal))) in
                                                                                                                                                    let assignTac = case lTac of
                                                                                                                                                                        [] -> (buildAssignTac assignOp leftValAddrs [] exprAddr t) 
                                                                                                                                                                        _ -> case head lTac of
                                                                                                                                                                            TacComment _ -> (buildAssignTac assignOp leftValAddrs (code (lvalueexpression_content (sel1 leftVal))) exprAddr t) 
                                                                                                                                                                            _ -> (code (lvalueexpression_content (sel1 leftVal)))++(buildAssignTac assignOp leftValAddrs [] exprAddr t) in
                                                                                                                                                    ((Abs.AssignmentStatement (TAC (code (expression_content (sel1 rightVal)) ++   -- expression (rval) evaluation tac code
                                                                                                                                                                                    assignTac)                                     -- assignements tac (list)                    
                                                                                                                                                                                    []) (sel1 leftVal) (genTacAssignOp assignOp) (sel1 rightVal)),newC,(sel3 rightVal),AddrNULL)
genTacStatement (Abs.ConditionalStatement res condition) n l k (w,j) = let newL = newLabel "else" k in 
                                                                                let condStatementTac = (genTacConditionalStatement condition n newL (k+1) (w,j)) in
                                                                                    let newC = sel2 condStatementTac in
                                                                                        ((Abs.ConditionalStatement (conditionalstate_content (sel1 condStatementTac)) (sel1 condStatementTac)),newC,(sel3 condStatementTac),AddrNULL)
genTacStatement (Abs.WhileDoStatement res while) n l k (w,j) = let newL = newLabel "body" k in 
                                                                        let whileStatement = (genTacWhileDoStatement while n newL (k+1) (w,j)) in
                                                                            let whileStatementTac = sel1 whileStatement in
                                                                                let newC = sel2 whileStatement in
                                                                                    let newK = sel3 whileStatement in
                                                                                        ((Abs.WhileDoStatement (whilestatement_content whileStatementTac) whileStatementTac),newC,newK,AddrNULL)
genTacStatement (Abs.DoWhileStatement res doStat) n l k (w,j) = let newL = newLabel "body" k in 
                                                                        let doStatement = (genTacDoWhileStatement doStat n newL (k+1) (w,j)) in
                                                                            let doStatementTac = sel1 doStatement in
                                                                                let newC = sel2 doStatement in
                                                                                    let newK = sel3 doStatement in
                                                                                        ((Abs.DoWhileStatement (dostatement_content doStatementTac) doStatementTac),newC,newK,AddrNULL)
genTacStatement (Abs.ForStatement res forStat) n l k (w,j) = let newL = newLabel "body" k in
                                                                        let forStatement = (genTacForStatement forStat n newL (k+1) (w,j)) in
                                                                            let newC = sel2 forStatement in
                                                                                let newK = sel3 forStatement in
                                                                                    ((Abs.ForStatement (forstatement_content (sel1 forStatement)) (sel1 forStatement)),newC,newK,AddrNULL)

                                                                                    
genTacStatement (Abs.ProcedureStatement res ident@(Abs.Ident id resI@(TResult _ _ (Pn a r c))) param states) n l k (w,j) = let newL = Label (id ++ "@" ++show r++","++show c) in
                                                                                                                                let endL = Label ("endProc_" ++ id ++ "@" ++show r++","++show c) in
                                                                                                                                    let statements = (genTacStatements states n newL k (w,j)) in
                                                                                                                                        let newC = sel2 statements in
                                                                                                                                            let newK = sel3 statements in
                                                                                                                                                ((Abs.ProcedureStatement (mergeTacs [(TAC [] [TacLabel newL]),  -- start func code label
                                                                                                                                                                                     (TAC [] (code (statements_content (sel1 statements)))), -- tac of statements inside the body (no funcs. decl. tacs.)
                                                                                                                                                                                     (TAC [] [TacLabel endL]),  -- end func code label   
                                                                                                                                                                                     (TAC [] (funcs (statements_content (sel1 statements)))) -- functions declared inside
                                                                                                                                                                                     ]) (Abs.Ident id (TAC [] [])) (Abs.ParameterListEmpty (TAC [] [])) (Abs.EmptyStatement (TAC [] []))),(sel2 statements),(sel3 statements),AddrNULL)                                           
genTacStatement (Abs.FunctionStatement res ident@(Abs.Ident id resI@(TResult _ _ (Pn a r c))) param tipo states) n l k (w,j) = let newL = Label (id ++ "@" ++show r++","++show c) in 
                                                                                                                                    let endL = Label ("endFun_" ++ id ++ "@" ++show r++","++show c) in
                                                                                                                                        let statements = (genTacStatements states n newL k (w,j)) in
                                                                                                                                            let newC = sel2 statements in
                                                                                                                                                let newK = sel3 statements in
                                                                                                                                                    ((Abs.FunctionStatement (mergeTacs [(TAC [] [TacLabel newL]),  -- start func code label
                                                                                                                                                                                        (TAC [] (code (statements_content (sel1 statements)))), -- tac of statements inside the body (no funcs. decl. tacs.)
                                                                                                                                                                                        (TAC [] [TacLabel endL]),  -- end func code label   
                                                                                                                                                                                        (TAC [] (funcs (statements_content (sel1 statements)))) -- functions declared inside
                                                                                                                                                                                        ]) (Abs.Ident id (TAC [] [])) (Abs.ParameterListEmpty (TAC [] [])) (Abs.TypeExpressionFunction (TAC [] []) (Abs.TypeExpression (TAC [] []) (Abs.PrimitiveTypeVoid (TAC [] [])))) (Abs.EmptyStatement (TAC [] []))),(sel2 statements),(sel3 statements),AddrNULL)                                           

genTacAssignOp :: Abs.ASSIGNOP TCheckResult -> Abs.ASSIGNOP TAC
genTacAssignOp (Abs.AssignOperationEq _ )        = (Abs.AssignOperationEq (TAC [] []))       
genTacAssignOp (Abs.AssignOperationEqPlus _ )    = (Abs.AssignOperationEqPlus (TAC [] []))   
genTacAssignOp (Abs.AssignOperationEqMinus _ )   = (Abs.AssignOperationEqMinus(TAC [] []))   
genTacAssignOp (Abs.AssignOperationEqProd _ )    = (Abs.AssignOperationEqProd (TAC [] []))   
genTacAssignOp (Abs.AssignOperationEqFract _ )   = (Abs.AssignOperationEqFract (TAC [] [])) 
genTacAssignOp (Abs.AssignOperationEqPercent _ ) = (Abs.AssignOperationEqPercent (TAC [] []))
genTacAssignOp (Abs.AssignOperationEqPower _ )   = (Abs.AssignOperationEqPower (TAC [] []))  

genTacLeftVal :: Abs.LVALUEEXPRESSION  TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.LVALUEEXPRESSION  TAC, Prelude.Integer, Prelude.Integer, [Address])
genTacLeftVal (Abs.LvalueExpressions res@(TResult env _ _) ident@(Abs.Ident id resi) arrayindex lval) n l k (w,j) = case arrayindex of  
                                                                                                    (Abs.ArrayIndexElementEmpty _) -> case Data.Map.lookup id env of
                                                                                                        Just (entry:entries) ->  case findEntryOfType (entry:entries) "var" of
                                                                                                            ((Variable _ posv _ _ _):xs) -> let leftAddr = buildIDAddr posv id in
                                                                                                                                            let lvalAddr = (genTacLeftVal lval n l k (w,j)) in
                                                                                                                                                ((Abs.LvalueExpressions (TAC ([TacComment ""]++(code (lvalueexpression_content (sel1 lvalAddr)))) []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElementEmpty (TAC [] [])) (sel1 lvalAddr)),n,k,[leftAddr]++(sel4 lvalAddr))
                                                                                                    (Abs.ArrayIndexElement _ typeindex) -> case Data.Map.lookup id env of
                                                                                                                                                Just (entry:entries) ->  case findEntryOfType (entry:entries) "var" of
                                                                                                                                                    (x:xs) -> case findArray (x:xs) of
                                                                                                                                                        [Variable ty@(Array t _) posv _ _ s] -> let typeIndexTac = genTacTypeIndex typeindex n l k (w,j) 0 [] (-1) in
                                                                                                                                                                                                    let lvalAddr = (genTacLeftVal lval (sel2 typeIndexTac) l (sel3 typeIndexTac) (w,j)) in
                                                                                                                                                                                                        let dim = generateDimForArrayFromType ty in
                                                                                                                                                                                                            let leftAddr = buildIDAddr posv id in
                                                                                                                                                                                                                if (isIntegerAddress (sel4 typeIndexTac)) 
                                                                                                                                                                                                                    then
                                                                                                                                                                                                                        let posArr = buildPosArray (sel4 typeIndexTac) s dim in
                                                                                                                                                                                                                            let leftAddrArray = buildArrayId leftAddr posArr 0 in
                                                                                                                                                                                                                                let comment = TacComment (mergeComments (buildArrayComments (sel4 typeIndexTac) s dim t)) in
                                                                                                                                                                                                                                    ((Abs.LvalueExpressions (TAC ([comment]++(code (lvalueexpression_content (sel1 lvalAddr)))) []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElement (TAC [] []) (sel1 typeIndexTac)) (sel1 lvalAddr)),(sel2 lvalAddr),(sel3 lvalAddr),[leftAddrArray]++(sel4 lvalAddr))
                                                                                                                                                                                                                    else
                                                                                                                                                                                                                        let typeIndexTac = genTacTypeIndex typeindex n l k (w,j) dim s (-1) in
                                                                                                                                                                                                                            let posArr = buildPosArrayNoInteger (sel4 typeIndexTac) s dim (sel2 typeIndexTac) in
                                                                                                                                                                                                                                let leftAddrArray = buildArrayIdNoInteger leftAddr (newTemp ((sel2 typeIndexTac)-1)) in
                                                                                                                                                                                                                                    ((Abs.LvalueExpressions (TAC ((code (typeindex_content (sel1 typeIndexTac)))++(code (lvalueexpression_content (sel1 lvalAddr)))) []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElement (TAC [] []) (sel1 typeIndexTac)) (sel1 lvalAddr)),(sel2 lvalAddr),(sel3 typeIndexTac),[leftAddrArray]++(sel4 lvalAddr))                                                                         
                                                                                                    (Abs.ArrayIndexElements _ arrayIndex typeindex ) -> case Data.Map.lookup id env of
                                                                                                                                                            Just (entry:entries) ->  case findEntryOfType (entry:entries) "var" of
                                                                                                                                                                (x:xs) ->  case findArray (x:xs) of
                                                                                                                                                                    [Variable ty@(Array t _) posv _ _ s] -> let realT = getRealTypeFromArray t in
                                                                                                                                                                                                                let typeIndexTac = genTacTypeIndex typeindex n l k (w,j) 0 [] (-1) in
                                                                                                                                                                                                                    let arrayIndexTac = genTacArrayIndexElements arrayIndex (sel2 typeIndexTac) l (sel3 typeIndexTac) (w,j) 0 [] (-1) in
                                                                                                                                                                                                                        let lvalAddr = (genTacLeftVal lval (sel2 arrayIndexTac) l (sel3 arrayIndexTac) (w,j)) in
                                                                                                                                                                                                                            let dim = generateDimForArrayFromType ty in
                                                                                                                                                                                                                                let leftAddr = buildIDAddr posv id in
                                                                                                                                                                                                                                    if (isIntegerAddress ((sel4 arrayIndexTac)++(sel4 typeIndexTac))) 
                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                            let posArr = buildPosArray ((sel4 arrayIndexTac)++(sel4 typeIndexTac)) s dim in
                                                                                                                                                                                                                                            let leftAddrArray = buildArrayId leftAddr posArr 0 in
                                                                                                                                                                                                                                                let comment = TacComment (mergeComments (buildArrayComments ((sel4 arrayIndexTac)++(sel4 typeIndexTac)) s dim realT)) in
                                                                                                                                                                                                                                                        ((Abs.LvalueExpressions (TAC ([comment]++(code (lvalueexpression_content (sel1 lvalAddr)))) []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElements (TAC [] [])  (sel1 arrayIndexTac) (sel1 typeIndexTac)) (sel1 lvalAddr)),(sel2 lvalAddr)+1,(sel3 lvalAddr),[leftAddrArray]++(sel4 lvalAddr))
                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                            let arrayIndexTac = genTacArrayIndexElements (Abs.ArrayIndexElementsMultiple res arrayIndex typeindex) n l k (w,j) dim s (-1) in
                                                                                                                                                                                                                                                let posArr = buildPosArrayNoInteger (sel4 arrayIndexTac) s dim (sel2 arrayIndexTac) in
                                                                                                                                                                                                                                                    let leftAddrArray = buildArrayIdNoInteger leftAddr (newTemp ((sel2 arrayIndexTac)-1)) in
                                                                                                                                                                                                                                                        ((Abs.LvalueExpressions (TAC (code (arrayindexelements_content (sel1 arrayIndexTac))) []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElements (TAC [] [])  (sel1 arrayIndexTac) (sel1 typeIndexTac)) (sel1 lvalAddr)),(sel2 lvalAddr),(sel3 lvalAddr),[leftAddrArray]++(sel4 lvalAddr))
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
genTacLeftVal (Abs.LvalueExpression res@(TResult env _ _) ident@(Abs.Ident id resi) arrayindex) n l k (w,j) = case arrayindex of 
                                                                                                    (Abs.ArrayIndexElementEmpty _) -> case Data.Map.lookup id env of
                                                                                                        Just (entry:entries) ->  case findEntryOfType (entry:entries) "var" of
                                                                                                            ((Variable _ posv _ _ _):xs) -> let leftAddr = buildIDAddr posv id in
                                                                                                                                            ((Abs.LvalueExpression (TAC [] []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElementEmpty (TAC [] []))),n,k,[leftAddr])
                                                                                                    (Abs.ArrayIndexElement _ typeindex) -> case Data.Map.lookup id env of
                                                                                                                                                Just (entry:entries) ->  case findEntryOfType (entry:entries) "var" of
                                                                                                                                                    (x:xs) -> case findArray (x:xs) of
                                                                                                                                                        [Variable ty@(Array t _) posv _ _ s] -> let typeIndexTac = genTacTypeIndex typeindex n l k (w,j) 0 [] (-1) in
                                                                                                                                                                                                    let dim = generateDimForArrayFromType ty in
                                                                                                                                                                                                        let leftAddr = buildIDAddr posv id in
                                                                                                                                                                                                            if (isIntegerAddress (sel4 typeIndexTac)) 
                                                                                                                                                                                                                then
                                                                                                                                                                                                                    let posArr = buildPosArray (sel4 typeIndexTac) s dim in
                                                                                                                                                                                                                        let leftAddrArray = buildArrayId leftAddr posArr 0 in
                                                                                                                                                                                                                            let comment = TacComment (mergeComments (buildArrayComments (sel4 typeIndexTac) s dim t)) in
                                                                                                                                                                                                                                ((Abs.LvalueExpression (TAC [comment] []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElement (TAC [] []) (sel1 typeIndexTac))),(sel2 typeIndexTac),(sel3 typeIndexTac),[leftAddrArray])
                                                                                                                                                                                                                else
                                                                                                                                                                                                                    let typeIndexTac = genTacTypeIndex typeindex n l k (w,j) dim s (-1) in
                                                                                                                                                                                                                        let posArr = buildPosArrayNoInteger (sel4 typeIndexTac) s dim (sel2 typeIndexTac) in
                                                                                                                                                                                                                            let leftAddrArray = buildArrayIdNoInteger leftAddr (newTemp ((sel2 typeIndexTac)-1)) in
                                                                                                                                                                                                                                ((Abs.LvalueExpression (TAC (code (typeindex_content (sel1 typeIndexTac))) []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElement (TAC [] []) (sel1 typeIndexTac))),(sel2 typeIndexTac),(sel3 typeIndexTac),[leftAddrArray])                                                                         
                                                                                                    (Abs.ArrayIndexElements _ arrayIndex typeindex ) -> case Data.Map.lookup id env of
                                                                                                                                                            Just (entry:entries) ->  case findEntryOfType (entry:entries) "var" of
                                                                                                                                                                (x:xs) ->  case findArray (x:xs) of
                                                                                                                                                                    [Variable ty@(Array t _) posv _ _ s] -> let realT = getRealTypeFromArray t in
                                                                                                                                                                                                                let typeIndexTac = genTacTypeIndex typeindex n l k (w,j) 0 [] (-1) in
                                                                                                                                                                                                                    let arrayIndexTac = genTacArrayIndexElements arrayIndex (sel2 typeIndexTac) l (sel3 typeIndexTac) (w,j) 0 [] (-1) in
                                                                                                                                                                                                                        let dim = generateDimForArrayFromType ty in
                                                                                                                                                                                                                            let leftAddr = buildIDAddr posv id in
                                                                                                                                                                                                                                if (isIntegerAddress ((sel4 arrayIndexTac)++(sel4 typeIndexTac))) 
                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                        let posArr = buildPosArray ((sel4 arrayIndexTac)++(sel4 typeIndexTac)) s dim in
                                                                                                                                                                                                                                            let leftAddrArray = buildArrayId leftAddr posArr 0 in
                                                                                                                                                                                                                                                let comment = TacComment (mergeComments (buildArrayComments ((sel4 arrayIndexTac)++(sel4 typeIndexTac)) s dim realT)) in
                                                                                                                                                                                                                                                        ((Abs.LvalueExpression (TAC [comment] []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElements (TAC [] [])  (sel1 arrayIndexTac) (sel1 typeIndexTac))),(sel2 arrayIndexTac)+1,(sel3 arrayIndexTac),[leftAddrArray])
                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                        let arrayIndexTac = genTacArrayIndexElements (Abs.ArrayIndexElementsMultiple res arrayIndex typeindex) n l k (w,j) dim s (-1) in
                                                                                                                                                                                                                                            let posArr = buildPosArrayNoInteger (sel4 arrayIndexTac) s dim (sel2 arrayIndexTac) in
                                                                                                                                                                                                                                                let leftAddrArray = buildArrayIdNoInteger leftAddr (newTemp ((sel2 arrayIndexTac)-1)) in
                                                                                                                                                                                                                                                    ((Abs.LvalueExpression (TAC (code (arrayindexelements_content (sel1 arrayIndexTac))) []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElements (TAC [] [])  (sel1 arrayIndexTac) (sel1 typeIndexTac))),(sel2 arrayIndexTac)+1,(sel3 arrayIndexTac),[leftAddrArray])

genTacTypeIndex :: Abs.TYPEINDEX  TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> Prelude.Integer -> [Prelude.Integer] -> Prelude.Integer -> (Abs.TYPEINDEX  TAC, Prelude.Integer, Prelude.Integer, [Address])
genTacTypeIndex (Abs.TypeOfIndexIntSingle res@(TResult env t pos) val@(Abs.Integer value resI)) n l k (w,j) d s p = case s of
                                                                                                                        [] -> (Abs.TypeOfIndexIntSingle (TAC [][]) (Abs.Integer value (TAC [][])),n,k,[AddrInt value])
                                                                                                                        _ -> let temp = newTemp n in
                                                                                                                                let comment = TAC (buildArrayCommentsNoInteger [temp] s d t) [] in
                                                                                                                                    let result = if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger (if(p>=0) then ([1]++ (getElem (reverse s) p)) else (getElem s p)) d) in
                                                                                                                                        (Abs.TypeOfIndexIntSingle (mergeTacs [TAC [TacAssignBinaryOp temp IntMul (AddrInt (result)) (AddrInt (value-1)) t] [], comment]) (Abs.Integer value (TAC [][])),n+1,k,[temp])
genTacTypeIndex (Abs.TypeOfIndexInt res@(TResult env t pos) typeIndex val@(Abs.Integer value resI)) n l k (w,j) d s p = let typeIndexTac = genTacTypeIndex typeIndex n l k (w,j) d s (p+1) in
                                                                                                                            case s of
                                                                                                                                [] -> (Abs.TypeOfIndexInt (TAC [][]) (sel1 typeIndexTac) (Abs.Integer value (TAC [][])),(sel2 typeIndexTac),(sel3 typeIndexTac),sel4 typeIndexTac++[AddrInt value])
                                                                                                                                _ -> let temp = newTemp (sel2 typeIndexTac) in
                                                                                                                                        let temp2 = newTemp ((sel2 typeIndexTac)+1) in
                                                                                                                                            let comment = TAC (buildArrayCommentsNoInteger [temp] (if(p>=0) then ([1]++ (getElem (reverse s) p)) else (getElem s p)) d t) [] in
                                                                                                                                                let result = if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger (if(p>=0) then ([1]++ (getElem (reverse s) p)) else (getElem s p)) d) in
                                                                                                                                                    (Abs.TypeOfIndexInt (mergeTacs [
                                                                                                                                                                                     (typeindex_content (sel1 typeIndexTac)),
                                                                                                                                                                                     TAC [TacAssignBinaryOp temp IntMul (AddrInt (result)) (AddrInt (value-1)) t] [],
                                                                                                                                                                                     comment,
                                                                                                                                                                                     TAC [TacAssignBinaryOp temp2 (buildOp t "plus") temp (head (sel4 typeIndexTac)) t] []
                                                                                                                                                                                    ]) (sel1 typeIndexTac) (Abs.Integer value (TAC [][])),(sel2 typeIndexTac)+2,k,[temp2]++sel4 typeIndexTac)
genTacTypeIndex (Abs.TypeOfIndexPointerSingle res@(TResult env t pos) unary def ) n l k (w,j) d s p = let exprTac = genTacExpression (Abs.ExpressionUnary res unary def) n l k (w,j) "" in
                                                                                                        let defTac = genTacDefault def n l k (w,j) in 
                                                                                                            let temp = newTemp (sel2 exprTac) in
                                                                                                                    let comment = TAC (buildArrayCommentsNoInteger [temp] s d t) [] in
                                                                                                                        (Abs.TypeOfIndexPointerSingle (mergeTacs [
                                                                                                                                                                        (expression_content (sel1 exprTac)),
                                                                                                                                                                        (TAC [TacAssignBinaryOp temp (buildOp t "product") (sel4 exprTac) (AddrInt (if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger s d))) t] []),
                                                                                                                                                                        comment
                                                                                                                                                                    ]) (Abs.UnaryOperationPointer (TAC [] [])) (sel1 defTac),(sel2 exprTac)+1,(sel3 exprTac),[temp])
genTacTypeIndex (Abs.TypeOfIndexPointer res@(TResult env t pos) typeindex unary def) n l k (w,j) d s p = let typeindexTac = genTacTypeIndex typeindex n l k (w,j) d s (p+1) in
                                                                                                            let exprTac = genTacExpression (Abs.ExpressionUnary res unary def) (sel2 typeindexTac) l (sel3 typeindexTac) (w,j) "" in
                                                                                                                let defTac = genTacDefault def n l k (w,j) in 
                                                                                                                    let temp = newTemp (sel2 exprTac) in
                                                                                                                        let temp2 = newTemp ((sel2 exprTac)+1) in
                                                                                                                            let comment = TAC (buildArrayCommentsNoInteger [temp] s d t) [] in
                                                                                                                                (Abs.TypeOfIndexPointer (mergeTacs [
                                                                                                                                                                        (typeindex_content (sel1 typeindexTac)),
                                                                                                                                                                        (expression_content (sel1 exprTac)),
                                                                                                                                                                        (TAC [TacAssignBinaryOp temp (buildOp t "product") (sel4 exprTac) (AddrInt (if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger s d))) t] []),
                                                                                                                                                                        comment,
                                                                                                                                                                        (TAC [TacAssignBinaryOp temp2 (buildOp t "plus") (head (sel4 typeindexTac)) temp t] [])
                                                                                                                                                                    ]) (sel1 typeindexTac) (Abs.UnaryOperationPointer (TAC [] [])) (sel1 defTac),(sel2 exprTac)+1,(sel3 exprTac),sel4 typeindexTac++[temp2])
genTacTypeIndex (Abs.TypeOfIndexBinaryPlusSingle res@(TResult env t pos) expr1 expr2) n l k (w,j) d s p = let expr1Tac = genTacExpression expr1 n l k (w,j) "" in 
                                                                                                            let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) "" in
                                                                                                                let temp = newTemp (sel2 expr2Tac) in
                                                                                                                    case s of
                                                                                                                                [] -> (Abs.TypeOfIndexBinaryPlusSingle (mergeTacs [
                                                                                                                                                                                        (expression_content (sel1 expr1Tac)),
                                                                                                                                                                                        (expression_content (sel1 expr2Tac)),
                                                                                                                                                                                        (TAC [TacAssignBinaryOp temp (buildOp t "plus") (sel4 expr1Tac) (sel4 expr2Tac) t] [])
                                                                                                                                                                                    ]) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+1,(sel3 expr2Tac),[temp])
                                                                                                                                _ -> let comment = TAC (buildArrayCommentsNoInteger [temp] s d t) [] in
                                                                                                                                        let temp2 = newTemp ((sel2 expr2Tac)+1) in
                                                                                                                                                (Abs.TypeOfIndexBinaryPlusSingle (mergeTacs [
                                                                                                                                                                                                (expression_content (sel1 expr1Tac)),
                                                                                                                                                                                                (expression_content (sel1 expr2Tac)),
                                                                                                                                                                                                (TAC [TacAssignBinaryOp temp (buildOp t "plus") (sel4 expr1Tac) (sel4 expr2Tac) t] []),
                                                                                                                                                                                                (TAC [TacAssignBinaryOp temp2 (buildOp t "product") temp (AddrInt (if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger s d))) t] []),
                                                                                                                                                                                                comment
                                                                                                                                                                                            ]) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+2,(sel3 expr2Tac),[temp2])
genTacTypeIndex (Abs.TypeOfIndexBinaryPlus res@(TResult env t pos) typeindex expr1 expr2) n l k (w,j) d s p = let typeindexTac = genTacTypeIndex typeindex n l k (w,j) d s (p+1) in
                                                                                                                let expr1Tac = genTacExpression expr1 (sel2 typeindexTac) l (sel3 typeindexTac) (w,j) "" in 
                                                                                                                    let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) "" in
                                                                                                                        let temp = newTemp (sel2 expr2Tac) in
                                                                                                                            case s of
                                                                                                                                [] ->
                                                                                                                                    (Abs.TypeOfIndexBinaryPlus (mergeTacs [
                                                                                                                                                                            (typeindex_content (sel1 typeindexTac)),
                                                                                                                                                                            (expression_content (sel1 expr1Tac)),
                                                                                                                                                                            (expression_content (sel1 expr2Tac)),
                                                                                                                                                                            (TAC [TacAssignBinaryOp temp (buildOp t "plus") (sel4 expr1Tac) (sel4 expr2Tac) t] [])
                                                                                                                                                                        ]) (sel1 typeindexTac) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+1,(sel3 expr2Tac),sel4 typeindexTac++[temp])
                                                                                                                                _ -> let comment = TAC (buildArrayCommentsNoInteger [temp] (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d t) [] in
                                                                                                                                        let temp2 = newTemp ((sel2 expr2Tac)+1) in
                                                                                                                                            let temp3 = newTemp ((sel2 expr2Tac)+2) in
                                                                                                                                                (Abs.TypeOfIndexBinaryPlus (mergeTacs [
                                                                                                                                                                                    (typeindex_content (sel1 typeindexTac)),
                                                                                                                                                                                    (expression_content (sel1 expr1Tac)),
                                                                                                                                                                                    (expression_content (sel1 expr2Tac)),
                                                                                                                                                                                    (TAC [TacAssignBinaryOp temp (buildOp t "plus") (sel4 expr1Tac) (sel4 expr2Tac) t] []),
                                                                                                                                                                                    (TAC [TacAssignBinaryOp temp2 (buildOp t "product") temp (AddrInt (if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d))) t] []),
                                                                                                                                                                                    comment,
                                                                                                                                                                                    (TAC [TacAssignBinaryOp temp3 (buildOp t "plus") (head (sel4 typeindexTac)) temp2 t] [])
                                                                                                                                                                                ]) (sel1 typeindexTac) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+3,(sel3 expr2Tac),sel4 typeindexTac++[temp3])
genTacTypeIndex (Abs.TypeOfIndexBinaryMinusSingle res@(TResult env t pos) expr1 expr2) n l k (w,j) d s p = let expr1Tac = genTacExpression expr1 n l k (w,j) "" in 
                                                                                                            let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) "" in
                                                                                                                let temp = newTemp (sel2 expr2Tac) in
                                                                                                                    case s of
                                                                                                                                [] -> (Abs.TypeOfIndexBinaryMinusSingle (mergeTacs [
                                                                                                                                                                                        (expression_content (sel1 expr1Tac)),
                                                                                                                                                                                        (expression_content (sel1 expr2Tac)),
                                                                                                                                                                                        (TAC [TacAssignBinaryOp temp (buildOp t "minus") (sel4 expr1Tac) (sel4 expr2Tac) t] [])
                                                                                                                                                                                    ]) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+1,(sel3 expr2Tac),[temp])
                                                                                                                                _ -> let comment = TAC (buildArrayCommentsNoInteger [temp] s d t) [] in
                                                                                                                                        let temp2 = newTemp ((sel2 expr2Tac)+1) in
                                                                                                                                                (Abs.TypeOfIndexBinaryMinusSingle (mergeTacs [
                                                                                                                                                                                                (expression_content (sel1 expr1Tac)),
                                                                                                                                                                                                (expression_content (sel1 expr2Tac)),
                                                                                                                                                                                                (TAC [TacAssignBinaryOp temp (buildOp t "minus") (sel4 expr1Tac) (sel4 expr2Tac) t] []),
                                                                                                                                                                                                (TAC [TacAssignBinaryOp temp2 (buildOp t "product") temp (AddrInt (if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger s d))) t] []),
                                                                                                                                                                                                comment
                                                                                                                                                                                            ]) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+2,(sel3 expr2Tac),[temp2])
genTacTypeIndex (Abs.TypeOfIndexBinaryMinus res@(TResult env t pos) typeindex expr1 expr2) n l k (w,j) d s p = let typeindexTac = genTacTypeIndex typeindex n l k (w,j) d s (p+1) in
                                                                                                                let expr1Tac = genTacExpression expr1 (sel2 typeindexTac) l (sel3 typeindexTac) (w,j) "" in 
                                                                                                                    let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) "" in
                                                                                                                        let temp = newTemp (sel2 expr2Tac) in
                                                                                                                            case s of
                                                                                                                                [] ->
                                                                                                                                    (Abs.TypeOfIndexBinaryMinus (mergeTacs [
                                                                                                                                                                            (typeindex_content (sel1 typeindexTac)),
                                                                                                                                                                            (expression_content (sel1 expr1Tac)),
                                                                                                                                                                            (expression_content (sel1 expr2Tac)),
                                                                                                                                                                            (TAC [TacAssignBinaryOp temp (buildOp t "minus") (sel4 expr1Tac) (sel4 expr2Tac) t] [])
                                                                                                                                                                        ]) (sel1 typeindexTac) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+1,(sel3 expr2Tac),sel4 typeindexTac++[temp])
                                                                                                                                _ -> let comment = TAC (buildArrayCommentsNoInteger [temp] (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d t) [] in
                                                                                                                                        let temp2 = newTemp ((sel2 expr2Tac)+1) in
                                                                                                                                            let temp3 = newTemp ((sel2 expr2Tac)+2) in
                                                                                                                                                (Abs.TypeOfIndexBinaryMinus (mergeTacs [
                                                                                                                                                                                    (typeindex_content (sel1 typeindexTac)),
                                                                                                                                                                                    (expression_content (sel1 expr1Tac)),
                                                                                                                                                                                    (expression_content (sel1 expr2Tac)),
                                                                                                                                                                                    (TAC [TacAssignBinaryOp temp (buildOp t "minus") (sel4 expr1Tac) (sel4 expr2Tac) t] []),
                                                                                                                                                                                    (TAC [TacAssignBinaryOp temp2 (buildOp t "product") temp (AddrInt (if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d))) t] []),
                                                                                                                                                                                    comment,
                                                                                                                                                                                    (TAC [TacAssignBinaryOp temp3 (buildOp t "plus") (head (sel4 typeindexTac)) temp2 t] [])
                                                                                                                                                                                ]) (sel1 typeindexTac) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+3,(sel3 expr2Tac),sel4 typeindexTac++[temp3])
genTacTypeIndex (Abs.TypeOfIndexBinaryProductSingle res@(TResult env t pos) expr1 expr2) n l k (w,j) d s p = let expr1Tac = genTacExpression expr1 n l k (w,j) "" in 
                                                                                                        let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) "" in
                                                                                                            let temp = newTemp (sel2 expr2Tac) in
                                                                                                                case s of
                                                                                                                            [] -> (Abs.TypeOfIndexBinaryProductSingle (mergeTacs [
                                                                                                                                                                                    (expression_content (sel1 expr1Tac)),
                                                                                                                                                                                    (expression_content (sel1 expr2Tac)),
                                                                                                                                                                                    (TAC [TacAssignBinaryOp temp (buildOp t "product") (sel4 expr1Tac) (sel4 expr2Tac) t] [])
                                                                                                                                                                                ]) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+1,(sel3 expr2Tac),[temp])
                                                                                                                            _ -> let comment = TAC (buildArrayCommentsNoInteger [temp] s d t) [] in
                                                                                                                                    let temp2 = newTemp ((sel2 expr2Tac)+1) in
                                                                                                                                            (Abs.TypeOfIndexBinaryProductSingle (mergeTacs [
                                                                                                                                                                                            (expression_content (sel1 expr1Tac)),
                                                                                                                                                                                            (expression_content (sel1 expr2Tac)),
                                                                                                                                                                                            (TAC [TacAssignBinaryOp temp (buildOp t "product") (sel4 expr1Tac) (sel4 expr2Tac) t] []),
                                                                                                                                                                                            (TAC [TacAssignBinaryOp temp2 (buildOp t "product") temp (AddrInt (if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger s d))) t] []),
                                                                                                                                                                                            comment
                                                                                                                                                                                        ]) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+2,(sel3 expr2Tac),[temp2])
genTacTypeIndex (Abs.TypeOfIndexBinaryProduct res@(TResult env t pos) typeindex expr1 expr2) n l k (w,j) d s p = let typeindexTac = genTacTypeIndex typeindex n l k (w,j) d s (p+1) in
                                                                                                                    let expr1Tac = genTacExpression expr1 (sel2 typeindexTac) l (sel3 typeindexTac) (w,j) "" in 
                                                                                                                        let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) "" in
                                                                                                                            let temp = newTemp (sel2 expr2Tac) in
                                                                                                                                case s of
                                                                                                                                    [] ->
                                                                                                                                        (Abs.TypeOfIndexBinaryProduct (mergeTacs [
                                                                                                                                                                                (typeindex_content (sel1 typeindexTac)),
                                                                                                                                                                                (expression_content (sel1 expr1Tac)),
                                                                                                                                                                                (expression_content (sel1 expr2Tac)),
                                                                                                                                                                                (TAC [TacAssignBinaryOp temp (buildOp t "product") (sel4 expr1Tac) (sel4 expr2Tac) t] [])
                                                                                                                                                                            ]) (sel1 typeindexTac) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+1,(sel3 expr2Tac),sel4 typeindexTac++[temp])
                                                                                                                                    _ -> let comment = TAC (buildArrayCommentsNoInteger [temp] (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d t) [] in
                                                                                                                                            let temp2 = newTemp ((sel2 expr2Tac)+1) in
                                                                                                                                                let temp3 = newTemp ((sel2 expr2Tac)+2) in
                                                                                                                                                    (Abs.TypeOfIndexBinaryProduct (mergeTacs [
                                                                                                                                                                                        (typeindex_content (sel1 typeindexTac)),
                                                                                                                                                                                        (expression_content (sel1 expr1Tac)),
                                                                                                                                                                                        (expression_content (sel1 expr2Tac)),
                                                                                                                                                                                        (TAC [TacAssignBinaryOp temp (buildOp t "product") (sel4 expr1Tac) (sel4 expr2Tac) t] []),
                                                                                                                                                                                        (TAC [TacAssignBinaryOp temp2 (buildOp t "product") temp (AddrInt (if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d))) t] []),
                                                                                                                                                                                        comment,
                                                                                                                                                                                        (TAC [TacAssignBinaryOp temp3 (buildOp t "plus") (head (sel4 typeindexTac)) temp2 t] [])
                                                                                                                                                                                    ]) (sel1 typeindexTac) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+3,(sel3 expr2Tac),sel4 typeindexTac++[temp3])
genTacTypeIndex (Abs.TypeOfIndexBinaryDivisionSingle res@(TResult env t pos) expr1 expr2) n l k (w,j) d s p = let expr1Tac = genTacExpression expr1 n l k (w,j) "" in 
                                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) "" in
                                                                                                                    let temp = newTemp (sel2 expr2Tac) in
                                                                                                                        case s of
                                                                                                                                    [] -> (Abs.TypeOfIndexBinaryDivisionSingle (mergeTacs [
                                                                                                                                                                                            (expression_content (sel1 expr1Tac)),
                                                                                                                                                                                            (expression_content (sel1 expr2Tac)),
                                                                                                                                                                                            (TAC [TacAssignBinaryOp temp (buildOp t "division") (sel4 expr1Tac) (sel4 expr2Tac) t] [])
                                                                                                                                                                                        ]) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+1,(sel3 expr2Tac),[temp])
                                                                                                                                    _ -> let comment = TAC (buildArrayCommentsNoInteger [temp] s d t) [] in
                                                                                                                                            let temp2 = newTemp ((sel2 expr2Tac)+1) in
                                                                                                                                                    (Abs.TypeOfIndexBinaryDivisionSingle (mergeTacs [
                                                                                                                                                                                                    (expression_content (sel1 expr1Tac)),
                                                                                                                                                                                                    (expression_content (sel1 expr2Tac)),
                                                                                                                                                                                                    (TAC [TacAssignBinaryOp temp (buildOp t "division") (sel4 expr1Tac) (sel4 expr2Tac) t] []),
                                                                                                                                                                                                    (TAC [TacAssignBinaryOp temp2 (buildOp t "product") temp (AddrInt (if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger s d))) t] []),
                                                                                                                                                                                                    comment
                                                                                                                                                                                                ]) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+2,(sel3 expr2Tac),[temp2])
genTacTypeIndex (Abs.TypeOfIndexBinaryDivision res@(TResult env t pos) typeindex expr1 expr2) n l k (w,j) d s p = let typeindexTac = genTacTypeIndex typeindex n l k (w,j) d s (p+1) in
                                                                                                                    let expr1Tac = genTacExpression expr1 (sel2 typeindexTac) l (sel3 typeindexTac) (w,j) "" in 
                                                                                                                        let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) "" in
                                                                                                                            let temp = newTemp (sel2 expr2Tac) in
                                                                                                                                case s of
                                                                                                                                    [] ->
                                                                                                                                        (Abs.TypeOfIndexBinaryDivision (mergeTacs [
                                                                                                                                                                                (typeindex_content (sel1 typeindexTac)),
                                                                                                                                                                                (expression_content (sel1 expr1Tac)),
                                                                                                                                                                                (expression_content (sel1 expr2Tac)),
                                                                                                                                                                                (TAC [TacAssignBinaryOp temp (buildOp t "division") (sel4 expr1Tac) (sel4 expr2Tac) t] [])
                                                                                                                                                                            ]) (sel1 typeindexTac) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+1,(sel3 expr2Tac),sel4 typeindexTac++[temp])
                                                                                                                                    _ -> let comment = TAC (buildArrayCommentsNoInteger [temp] (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d t) [] in
                                                                                                                                            let temp2 = newTemp ((sel2 expr2Tac)+1) in
                                                                                                                                                let temp3 = newTemp ((sel2 expr2Tac)+2) in
                                                                                                                                                    (Abs.TypeOfIndexBinaryDivision (mergeTacs [
                                                                                                                                                                                        (typeindex_content (sel1 typeindexTac)),
                                                                                                                                                                                        (expression_content (sel1 expr1Tac)),
                                                                                                                                                                                        (expression_content (sel1 expr2Tac)),
                                                                                                                                                                                        (TAC [TacAssignBinaryOp temp (buildOp t "division") (sel4 expr1Tac) (sel4 expr2Tac) t] []),
                                                                                                                                                                                        (TAC [TacAssignBinaryOp temp2 (buildOp t "product") temp (AddrInt (if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d))) t] []),
                                                                                                                                                                                        comment,
                                                                                                                                                                                        (TAC [TacAssignBinaryOp temp3 (buildOp t "plus") (head (sel4 typeindexTac)) temp2 t] [])
                                                                                                                                                                                    ]) (sel1 typeindexTac) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+3,(sel3 expr2Tac),sel4 typeindexTac++[temp3])
genTacTypeIndex (Abs.TypeOfIndexBinaryModuleSingle res@(TResult env t pos) expr1 expr2) n l k (w,j) d s p = let expr1Tac = genTacExpression expr1 n l k (w,j) "" in 
                                                                                                        let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) "" in
                                                                                                            let temp = newTemp (sel2 expr2Tac) in
                                                                                                                case s of
                                                                                                                            [] -> (Abs.TypeOfIndexBinaryModuleSingle (mergeTacs [
                                                                                                                                                                                    (expression_content (sel1 expr1Tac)),
                                                                                                                                                                                    (expression_content (sel1 expr2Tac)),
                                                                                                                                                                                    (TAC [TacAssignBinaryOp temp (buildOp t "module") (sel4 expr1Tac) (sel4 expr2Tac) t] [])
                                                                                                                                                                                ]) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+1,(sel3 expr2Tac),[temp])
                                                                                                                            _ -> let comment = TAC (buildArrayCommentsNoInteger [temp] s d t) [] in
                                                                                                                                    let temp2 = newTemp ((sel2 expr2Tac)+1) in
                                                                                                                                            (Abs.TypeOfIndexBinaryModuleSingle (mergeTacs [
                                                                                                                                                                                            (expression_content (sel1 expr1Tac)),
                                                                                                                                                                                            (expression_content (sel1 expr2Tac)),
                                                                                                                                                                                            (TAC [TacAssignBinaryOp temp (buildOp t "module") (sel4 expr1Tac) (sel4 expr2Tac) t] []),
                                                                                                                                                                                            (TAC [TacAssignBinaryOp temp2 (buildOp t "product") temp (AddrInt (if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger s d))) t] []),
                                                                                                                                                                                            comment
                                                                                                                                                                                        ]) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+2,(sel3 expr2Tac),[temp2])
genTacTypeIndex (Abs.TypeOfIndexBinaryModule res@(TResult env t pos) typeindex expr1 expr2) n l k (w,j) d s p = let typeindexTac = genTacTypeIndex typeindex n l k (w,j) d s (p+1) in
                                                                                                                let expr1Tac = genTacExpression expr1 (sel2 typeindexTac) l (sel3 typeindexTac) (w,j) "" in 
                                                                                                                    let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) "" in
                                                                                                                        let temp = newTemp (sel2 expr2Tac) in
                                                                                                                            case s of
                                                                                                                                [] ->
                                                                                                                                    (Abs.TypeOfIndexBinaryModule (mergeTacs [
                                                                                                                                                                            (typeindex_content (sel1 typeindexTac)),
                                                                                                                                                                            (expression_content (sel1 expr1Tac)),
                                                                                                                                                                            (expression_content (sel1 expr2Tac)),
                                                                                                                                                                            (TAC [TacAssignBinaryOp temp (buildOp t "module") (sel4 expr1Tac) (sel4 expr2Tac) t] [])
                                                                                                                                                                        ]) (sel1 typeindexTac) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+1,(sel3 expr2Tac),sel4 typeindexTac++[temp])
                                                                                                                                _ -> let comment = TAC (buildArrayCommentsNoInteger [temp] (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d t) [] in
                                                                                                                                        let temp2 = newTemp ((sel2 expr2Tac)+1) in
                                                                                                                                            let temp3 = newTemp ((sel2 expr2Tac)+2) in
                                                                                                                                                (Abs.TypeOfIndexBinaryModule (mergeTacs [
                                                                                                                                                                                    (typeindex_content (sel1 typeindexTac)),
                                                                                                                                                                                    (expression_content (sel1 expr1Tac)),
                                                                                                                                                                                    (expression_content (sel1 expr2Tac)),
                                                                                                                                                                                    (TAC [TacAssignBinaryOp temp (buildOp t "module") (sel4 expr1Tac) (sel4 expr2Tac) t] []),
                                                                                                                                                                                    (TAC [TacAssignBinaryOp temp2 (buildOp t "product") temp (AddrInt (if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d))) t] []),
                                                                                                                                                                                    comment,
                                                                                                                                                                                    (TAC [TacAssignBinaryOp temp3 (buildOp t "plus") (head (sel4 typeindexTac)) temp2 t] [])
                                                                                                                                                                                ]) (sel1 typeindexTac) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+3,(sel3 expr2Tac),sel4 typeindexTac++[temp3])
genTacTypeIndex (Abs.TypeOfIndexBinaryPowerSingle res@(TResult env t pos) expr1 expr2) n l k (w,j) d s p = let expr1Tac = genTacExpression expr1 n l k (w,j) "" in 
                                                                                                        let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) "" in
                                                                                                            let temp = newTemp (sel2 expr2Tac) in
                                                                                                                case s of
                                                                                                                            [] -> (Abs.TypeOfIndexBinaryPowerSingle (mergeTacs [
                                                                                                                                                                                    (expression_content (sel1 expr1Tac)),
                                                                                                                                                                                    (expression_content (sel1 expr2Tac)),
                                                                                                                                                                                    (TAC [TacAssignBinaryOp temp (buildOp t "power") (sel4 expr1Tac) (sel4 expr2Tac) t] [])
                                                                                                                                                                                ]) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+1,(sel3 expr2Tac),[temp])
                                                                                                                            _ -> let comment = TAC (buildArrayCommentsNoInteger [temp] s d t) [] in
                                                                                                                                    let temp2 = newTemp ((sel2 expr2Tac)+1) in
                                                                                                                                            (Abs.TypeOfIndexBinaryPowerSingle (mergeTacs [
                                                                                                                                                                                            (expression_content (sel1 expr1Tac)),
                                                                                                                                                                                            (expression_content (sel1 expr2Tac)),
                                                                                                                                                                                            (TAC [TacAssignBinaryOp temp (buildOp t "power") (sel4 expr1Tac) (sel4 expr2Tac) t] []),
                                                                                                                                                                                            (TAC [TacAssignBinaryOp temp2 (buildOp t "product") temp (AddrInt (if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger s d))) t] []),
                                                                                                                                                                                            comment
                                                                                                                                                                                        ]) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+2,(sel3 expr2Tac),[temp2])
genTacTypeIndex (Abs.TypeOfIndexBinaryPower res@(TResult env t pos) typeindex expr1 expr2) n l k (w,j) d s p = let typeindexTac = genTacTypeIndex typeindex n l k (w,j) d s (p+1) in
                                                                                                                let expr1Tac = genTacExpression expr1 (sel2 typeindexTac) l (sel3 typeindexTac) (w,j) "" in 
                                                                                                                    let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) "" in
                                                                                                                        let temp = newTemp (sel2 expr2Tac) in
                                                                                                                            case s of
                                                                                                                                [] ->
                                                                                                                                    (Abs.TypeOfIndexBinaryPower (mergeTacs [
                                                                                                                                                                            (typeindex_content (sel1 typeindexTac)),
                                                                                                                                                                            (expression_content (sel1 expr1Tac)),
                                                                                                                                                                            (expression_content (sel1 expr2Tac)),
                                                                                                                                                                            (TAC [TacAssignBinaryOp temp (buildOp t "power") (sel4 expr1Tac) (sel4 expr2Tac) t] [])
                                                                                                                                                                        ]) (sel1 typeindexTac) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+1,(sel3 expr2Tac),sel4 typeindexTac++[temp])
                                                                                                                                _ -> let comment = TAC (buildArrayCommentsNoInteger [temp] (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d t) [] in
                                                                                                                                        let temp2 = newTemp ((sel2 expr2Tac)+1) in
                                                                                                                                            let temp3 = newTemp ((sel2 expr2Tac)+2) in
                                                                                                                                                (Abs.TypeOfIndexBinaryPower (mergeTacs [
                                                                                                                                                                                    (typeindex_content (sel1 typeindexTac)),
                                                                                                                                                                                    (expression_content (sel1 expr1Tac)),
                                                                                                                                                                                    (expression_content (sel1 expr2Tac)),
                                                                                                                                                                                    (TAC [TacAssignBinaryOp temp (buildOp t "power") (sel4 expr1Tac) (sel4 expr2Tac) t] []),
                                                                                                                                                                                    (TAC [TacAssignBinaryOp temp2 (buildOp t "product") temp (AddrInt (if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d))) t] []),
                                                                                                                                                                                    comment,
                                                                                                                                                                                    (TAC [TacAssignBinaryOp temp3 (buildOp t "plus") (head (sel4 typeindexTac)) temp2 t] [])
                                                                                                                                                                                ]) (sel1 typeindexTac) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac)+3,(sel3 expr2Tac),sel4 typeindexTac++[temp3])
genTacTypeIndex (Abs.TypeOfIndexExpressionBracketSingle res@(TResult env t pos) expr) n l k (w,j) d s p = let exprTac = genTacExpression expr n l k (w,j) "" in
                                                                                                                case s of
                                                                                                                    [] ->
                                                                                                                        (Abs.TypeOfIndexExpressionBracketSingle (expression_content (sel1 exprTac)) (sel1 exprTac),(sel2 exprTac),(sel3 exprTac),[sel4 exprTac])
                                                                                                                    _ -> let temp = newTemp (sel2 exprTac) in
                                                                                                                            let comment = TAC (buildArrayCommentsNoInteger [temp] (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d t) [] in
                                                                                                                                    (Abs.TypeOfIndexExpressionBracketSingle (mergeTacs [
                                                                                                                                                                                        (expression_content (sel1 exprTac)),
                                                                                                                                                                                        (TAC [TacAssignBinaryOp temp (buildOp t "product") (sel4 exprTac) (AddrInt (if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d))) t] []),
                                                                                                                                                                                        comment
                                                                                                                                                                                    ]) (sel1 exprTac) ,(sel2 exprTac)+1,(sel3 exprTac),[temp])

genTacTypeIndex (Abs.TypeOfIndexExpressionBracket res@(TResult env t pos) typeindex expr) n l k (w,j) d s p = let typeindexTac = genTacTypeIndex typeindex n l k (w,j) d s (p+1) in
                                                                                                                let exprTac = genTacExpression expr (sel2 typeindexTac) l (sel3 typeindexTac) (w,j) "" in 
                                                                                                                            case s of
                                                                                                                                [] ->
                                                                                                                                    (Abs.TypeOfIndexExpressionBracket (mergeTacs [
                                                                                                                                                                            (typeindex_content (sel1 typeindexTac)),
                                                                                                                                                                            (expression_content (sel1 exprTac))
                                                                                                                                                                        ]) (sel1 typeindexTac) (sel1 exprTac),(sel2 exprTac),(sel3 exprTac),sel4 typeindexTac++[sel4 exprTac])
                                                                                                                                _ -> let temp = newTemp (sel2 exprTac) in
                                                                                                                                            let temp2 = newTemp ((sel2 exprTac)+1) in
                                                                                                                                                let comment = TAC (buildArrayCommentsNoInteger [temp] (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d t) [] in
                                                                                                                                                    (Abs.TypeOfIndexExpressionBracket (mergeTacs [
                                                                                                                                                                                        (typeindex_content (sel1 typeindexTac)),
                                                                                                                                                                                        (expression_content (sel1 exprTac)),
                                                                                                                                                                                        (TAC [TacAssignBinaryOp temp (buildOp t "product") (sel4 exprTac) (AddrInt (if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d))) t] []),
                                                                                                                                                                                        comment,
                                                                                                                                                                                        (TAC [TacAssignBinaryOp temp2 (buildOp t "plus") (head (sel4 typeindexTac)) temp t] [])
                                                                                                                                                                                    ]) (sel1 typeindexTac) (sel1 exprTac),(sel2 exprTac)+2,(sel3 exprTac),sel4 typeindexTac++[temp2])
                                                                                                                                                                                                                                                                                                                                                              
genTacTypeIndex (Abs.TypeOfIndexExpressionCallSingle res@(TResult env t pos) ident@(Abs.Ident id _) exprs) n l k (w,j) d s p = let exprsTac = genTacExpressions exprs n l k (w,j) in
                                                                                                                                let exprCallTac = genTacExpression (Abs.ExpressionCall res ident exprs) (sel2 exprsTac) l (sel3 exprsTac) (w,j) "" in
                                                                                                                                    case s of
                                                                                                                                        [] ->
                                                                                                                                            (Abs.TypeOfIndexExpressionCallSingle (expression_content (sel1 exprCallTac)) (Abs.Ident id (TAC [] [])) (sel1 exprsTac),(sel2 exprCallTac),(sel3 exprCallTac),[sel4 exprCallTac])
                                                                                                                                        _ -> let temp = newTemp (sel2 exprCallTac) in
                                                                                                                                                let comment = TAC (buildArrayCommentsNoInteger [temp] (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d t) [] in
                                                                                                                                                        (Abs.TypeOfIndexExpressionCallSingle (mergeTacs [
                                                                                                                                                                                                            (expression_content (sel1 exprCallTac)),
                                                                                                                                                                                                            (TAC [TacAssignBinaryOp temp (buildOp t "product") (sel4 exprCallTac) (AddrInt (if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d))) t] []),
                                                                                                                                                                                                            comment
                                                                                                                                                                                                        ]) (Abs.Ident id (TAC [] [])) (sel1 exprsTac) ,(sel2 exprCallTac)+1,(sel3 exprCallTac),[temp])

genTacTypeIndex (Abs.TypeOfIndexExpressionCall res@(TResult env t pos) typeindex ident@(Abs.Ident id _) exprs) n l k (w,j) d s p = let typeindexTac = genTacTypeIndex typeindex n l k (w,j) d s (p+1) in
                                                                                                                                        let exprsTac = genTacExpressions exprs (sel2 typeindexTac) l (sel3 typeindexTac) (w,j) in
                                                                                                                                            let exprCallTac = genTacExpression (Abs.ExpressionCall res ident exprs) (sel2 typeindexTac) l (sel3 typeindexTac) (w,j) "" in
                                                                                                                                                    case s of
                                                                                                                                                        [] ->
                                                                                                                                                            (Abs.TypeOfIndexExpressionCall (mergeTacs [
                                                                                                                                                                                                    (typeindex_content (sel1 typeindexTac)),
                                                                                                                                                                                                    (expression_content (sel1 exprCallTac))
                                                                                                                                                                                                ]) (sel1 typeindexTac) (Abs.Ident id (TAC [] [])) (sel1 exprsTac),(sel2 exprCallTac),(sel3 exprCallTac),sel4 typeindexTac++[sel4 exprCallTac])
                                                                                                                                                        _ -> let temp = newTemp (sel2 exprCallTac) in
                                                                                                                                                                    let temp2 = newTemp ((sel2 exprCallTac)+1) in
                                                                                                                                                                        let comment = TAC (buildArrayCommentsNoInteger [temp] (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d t) [] in
                                                                                                                                                                            (Abs.TypeOfIndexExpressionCall (mergeTacs [
                                                                                                                                                                                                                (typeindex_content (sel1 typeindexTac)),
                                                                                                                                                                                                                (expression_content (sel1 exprCallTac)),
                                                                                                                                                                                                                (TAC [TacAssignBinaryOp temp (buildOp t "product") (sel4 exprCallTac) (AddrInt (if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d))) t] []),
                                                                                                                                                                                                                comment,
                                                                                                                                                                                                                (TAC [TacAssignBinaryOp temp2 (buildOp t "plus") (head (sel4 typeindexTac)) temp t] [])
                                                                                                                                                                                                            ]) (sel1 typeindexTac) (Abs.Ident id (TAC [] [])) (sel1 exprsTac),(sel2 exprCallTac)+2,(sel3 exprCallTac),sel4 typeindexTac++[temp2])
                                                                                                                                                                                                                                                                                                                                                              
genTacTypeIndex (Abs.TypeOfIndexVarSingle res@(TResult env t pos) ident@(Abs.Ident id _) arrayIndex) n l k (w,j) d s p = let indexTac = case arrayIndex of
                                                                                                                                            Abs.ArrayIndexElementEmpty _ -> Abs.ArrayIndexElementEmpty (TAC [] [])
                                                                                                                                            Abs.ArrayIndexElement _ typeindex -> let typeindexTac = genTacTypeIndex typeindex n l k (w,j) 0 [] (-1) in
                                                                                                                                                                                    Abs.ArrayIndexElement (typeindex_content (sel1 typeindexTac)) (sel1 typeindexTac)
                                                                                                                                            Abs.ArrayIndexElements _ arrayIndexs typeindex -> let typeindexTac = genTacTypeIndex typeindex n l k (w,j) 0 [] (-1) in
                                                                                                                                                                                                let arrayIndexTac = genTacArrayIndexElements arrayIndexs n l k (w,j) 0 [] (-1) in
                                                                                                                                                                                                    Abs.ArrayIndexElements (mergeTacs [(typeindex_content (sel1 typeindexTac)),(arrayindexelements_content (sel1 arrayIndexTac))])  (sel1 arrayIndexTac) (sel1 typeindexTac)
                                                                                                                                            in
                                                                                                                                let exprIdentTac = genTacExpression (Abs.ExpressionIdent res ident arrayIndex) n l k (w,j) "" in
                                                                                                                                    case s of
                                                                                                                                        [] ->
                                                                                                                                            (Abs.TypeOfIndexVarSingle (expression_content (sel1 exprIdentTac)) (Abs.Ident id (TAC [] [])) indexTac,(sel2 exprIdentTac),(sel3 exprIdentTac),[sel4 exprIdentTac])
                                                                                                                                        _ -> let temp = newTemp (sel2 exprIdentTac) in
                                                                                                                                                let comment = TAC (buildArrayCommentsNoInteger [temp] (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d t) [] in
                                                                                                                                                        (Abs.TypeOfIndexVarSingle (mergeTacs [
                                                                                                                                                                                                (expression_content (sel1 exprIdentTac)),
                                                                                                                                                                                                (TAC [TacAssignBinaryOp temp (buildOp t "product") (sel4 exprIdentTac) (AddrInt (if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d))) t] []),
                                                                                                                                                                                                comment
                                                                                                                                                                                            ]) (Abs.Ident id (TAC [] [])) indexTac ,(sel2 exprIdentTac)+1,(sel3 exprIdentTac),[temp])

genTacTypeIndex (Abs.TypeOfIndexVar res@(TResult env t pos) typeindex ident@(Abs.Ident id _) arrayIndex) n l k (w,j) d s p = let typeindexTac = genTacTypeIndex typeindex n l k (w,j) d s (p+1) in
                                                                                                                                let indexTac = case arrayIndex of
                                                                                                                                            Abs.ArrayIndexElementEmpty _ -> Abs.ArrayIndexElementEmpty (TAC [] [])
                                                                                                                                            Abs.ArrayIndexElement _ typeindex -> let typeindexTac = genTacTypeIndex typeindex n l k (w,j) 0 [] (-1) in
                                                                                                                                                                                    Abs.ArrayIndexElement (typeindex_content (sel1 typeindexTac)) (sel1 typeindexTac)
                                                                                                                                            Abs.ArrayIndexElements _ arrayIndexs typeindex -> let typeindexTac = genTacTypeIndex typeindex n l k (w,j) 0 [] (-1) in
                                                                                                                                                                                                let arrayIndexTac = genTacArrayIndexElements arrayIndexs n l k (w,j) 0 [] (-1) in
                                                                                                                                                                                                    Abs.ArrayIndexElements (mergeTacs [(typeindex_content (sel1 typeindexTac)),(arrayindexelements_content (sel1 arrayIndexTac))])  (sel1 arrayIndexTac) (sel1 typeindexTac)
                                                                                                                                            in
                                                                                                                                    let exprIdentTac = genTacExpression (Abs.ExpressionIdent res ident arrayIndex) (sel2 typeindexTac) l (sel3 typeindexTac) (w,j) "" in
                                                                                                                                        case s of
                                                                                                                                                        [] ->
                                                                                                                                                            (Abs.TypeOfIndexVar (mergeTacs [
                                                                                                                                                                                                (typeindex_content (sel1 typeindexTac)),
                                                                                                                                                                                                (expression_content (sel1 exprIdentTac))
                                                                                                                                                                                            ]) (sel1 typeindexTac) (Abs.Ident id (TAC [] [])) indexTac,(sel2 exprIdentTac),(sel3 exprIdentTac),sel4 typeindexTac++[sel4 exprIdentTac])
                                                                                                                                                        _ -> let temp = newTemp (sel2 exprIdentTac) in
                                                                                                                                                                    let temp2 = newTemp ((sel2 exprIdentTac)+1) in
                                                                                                                                                                        let comment = TAC (buildArrayCommentsNoInteger [temp] (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d t) [] in
                                                                                                                                                                            (Abs.TypeOfIndexVar (mergeTacs [
                                                                                                                                                                                                                (typeindex_content (sel1 typeindexTac)),
                                                                                                                                                                                                                (expression_content (sel1 exprIdentTac)),
                                                                                                                                                                                                                (TAC [TacAssignBinaryOp temp (buildOp t "product") (sel4 exprIdentTac) (AddrInt (if p==(-1) then (buildPosArrayCNoInteger (getElem s p) d) *d else (buildPosArrayCNoInteger (if(p>=0) then ([1]++ (getElem s p)) else (getElem s p)) d))) t] []),
                                                                                                                                                                                                                comment,
                                                                                                                                                                                                                (TAC [TacAssignBinaryOp temp2 (buildOp t "plus") (head (sel4 typeindexTac)) temp t] [])
                                                                                                                                                                                                            ]) (sel1 typeindexTac) (Abs.Ident id (TAC [] [])) indexTac,(sel2 exprIdentTac)+2,(sel3 exprIdentTac),sel4 typeindexTac++[temp2])
                                                                                                                                                                                                                                                                                                                                                              

genTacArrayIndexElements :: Abs.ARRAYINDEXELEMENTS TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> Prelude.Integer -> [Prelude.Integer] -> Prelude.Integer -> (Abs.ARRAYINDEXELEMENTS  TAC, Prelude.Integer, Prelude.Integer, [Address])
genTacArrayIndexElements (Abs.ArrayIndexElementsSingle _ typeindex) n l k (w,j) d s p = let typeindexTac = genTacTypeIndex typeindex n l k (w,j) d s p in
                                                                                            (Abs.ArrayIndexElementsSingle (typeindex_content (sel1 typeindexTac)) (sel1 typeindexTac),(sel2 typeindexTac),(sel3 typeindexTac),sel4 typeindexTac)
                                                                                                

genTacArrayIndexElements (Abs.ArrayIndexElementsMultiple _ arrayindex typeindex) n l k (w,j) d s p = if s==[]
                                                                                                        then
                                                                                                            let typeindexTac = genTacTypeIndex typeindex n l k (w,j) d s p in
                                                                                                                let arrayIndexTac = genTacArrayIndexElements arrayindex (sel2 typeindexTac) l (sel3 typeindexTac) (w,j) d s p in
                                                                                                                    (Abs.ArrayIndexElementsMultiple (mergeTacs [
                                                                                                                                                                (arrayindexelements_content (sel1 arrayIndexTac)),
                                                                                                                                                                (typeindex_content (sel1 typeindexTac))
                                                                                                                                                                ])  (sel1 arrayIndexTac) (sel1 typeindexTac),(sel2 arrayIndexTac)+1,(sel3 arrayIndexTac),(sel4 arrayIndexTac)++(sel4 typeindexTac))
                                                                                                        else
                                                                                                            let typeN = (countIndex_ typeindex)-1 in
                                                                                                                let typeindexTac = genTacTypeIndex typeindex n l k (w,j) d (getElem s typeN) p in
                                                                                                                    let arrayIndexTac = genTacArrayIndexElements arrayindex (sel2 typeindexTac) l (sel3 typeindexTac) (w,j) d s typeN in
                                                                                                                        let temp= newTemp (sel2 arrayIndexTac) in
                                                                                                                            (Abs.ArrayIndexElementsMultiple (mergeTacs [
                                                                                                                                                                        (arrayindexelements_content (sel1 arrayIndexTac)),
                                                                                                                                                                        (typeindex_content (sel1 typeindexTac)),
                                                                                                                                                                        (TAC [TacAssignBinaryOp temp IntAdd (head (sel4 arrayIndexTac)) (head (sel4 typeindexTac)) (B_type Type_Integer)] [])
                                                                                                                                                                        ])  (sel1 arrayIndexTac) (sel1 typeindexTac),(sel2 arrayIndexTac)+1,(sel3 arrayIndexTac),(sel4 arrayIndexTac)++[temp])

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
genTacNamedExpression (Abs.NamedExpressionList res namedexpr@(Abs.NamedExpression _ expr)) n l k (w,j) = let expression = genTacExpression expr n l k (w,j) "" in
                                                                                                            let exprTac = (sel1 expression) in
                                                                                                                let exprAddr = (sel4 expression) in
                                                                                                                    let p_type = getTypeFromExpr expr in
                                                                                                                        ((Abs.NamedExpressionList (mergeTacs [(expression_content exprTac),         -- evaluation of the param
                                                                                                                                                              (TAC [TacParam exprAddr p_type] [])])    -- param tac
                                                                                                                                                              (Abs.NamedExpression (TAC [] []) exprTac)),(sel2 expression),(sel3 expression))
genTacNamedExpression (Abs.NamedExpressionLists res namedexpr@(Abs.NamedExpression _ expr) namedexprs) n l k (w,j) = let expression = genTacExpression expr n l k (w,j) "" in
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
                                                                            let guardLabel = newLabel "guard" ((sel3 rangeExp)+1) in
                                                                                let nextLabel = newLabel "next" ((sel3 rangeExp)+2) in
                                                                                    let statement = (genTacStatement stat (sel2 rangeExp) l ((sel3 rangeExp )+3) (nextLabel,guardLabel)) in
                                                                                        let statTac = sel1 statement in
                                                                                            let rangeExpTac = sel1 rangeExp in
                                                                                                case rangeExpTac of
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
                                                                                let guardLabel = newLabel "guard" (k+1) in
                                                                                    let nextLabel = newLabel "next" (k+2) in
                                                                                        let statements = (genTacStatements stats (sel2 rangeExp) l ((sel3 rangeExp )+1) (nextLabel,guardLabel)) in
                                                                                            let statsTac = sel1 statements in
                                                                                                let rangeExpTac = sel1 rangeExp in
                                                                                                    case rangeExpTac of
                                                                                                    (Abs.RangeExpressionSingle tac expr1 expr2) -> let expr1Addr = sel4 rangeExp in
                                                                                                                                                    let expr2Addr = sel5 rangeExp in
                                                                                                                                                        let guardAddr = buildIDAddr pos id in -- getting guard variable address
                                                                                                                                                        ((Abs.ForStateIndexWDo (mergeTacs [(rangeexp_content rangeExpTac),                      -- rangeExpr TACS (evaluation of expr1 and expr2 code)
                                                                                                                                                                                        (TAC [TacAssignNullOp guardAddr expr1Addr (B_type Type_Integer)] []),  -- guard initialization to expr1 val
                                                                                                                                                                                        (TAC [TacJump guardLabel] []),                          -- jump to guard label
                                                                                                                                                                                        (TAC [TacLabel l] []),                                  -- body label              
                                                                                                                                                                                        (statements_content statsTac),                          -- body TAC code
                                                                                                                                                                                        (TAC [TacAssignBinaryOp guardAddr IntAdd guardAddr (AddrInt 1) (B_type Type_Integer)] []), -- guard++
                                                                                                                                                                                        (TAC [TacLabel guardLabel] []),                         -- guard label
                                                                                                                                                                                        (TAC [TacRelConditionalJump l False LeqInt guardAddr expr2Addr] []), -- check of guard <= end (relation jump)
                                                                                                                                                                                        (TAC [TacLabel nextLabel] [])                           -- end of for 
                                                                                                                                                                                        ]) (Abs.IndexVarDeclaration (TAC [] []) (Abs.Ident id (TAC [] []))) rangeExpTac (Abs.BlockStatement (TAC [] []) statsTac)),sel2 statements, sel3 statements)                                                    
genTacForStatement (Abs.ForStateExprDo res rangexp stat)        n l k (w,j) = let rangeExp = (genTacRangeExpr rangexp n l k (w,j)) in -- for range do stats
                                                                                let guardLabel = newLabel "guard" (sel3 rangeExp) in
                                                                                    let nextLabel = newLabel "next" ((sel3 rangeExp )+1) in
                                                                                        let statement = (genTacStatement stat ((sel2 rangeExp)+1) l ((sel3 rangeExp )+2) (nextLabel,guardLabel)) in
                                                                                        let statTac = sel1 statement in
                                                                                            let rangeExpTac = sel1 rangeExp in
                                                                                                case rangeExpTac of
                                                                                                    (Abs.RangeExpressionSingle tac expr1 expr2) -> let expr1Addr = sel4 rangeExp in
                                                                                                                                                    let expr2Addr = sel5 rangeExp in
                                                                                                                                                     let guardTempAddr = (newTemp (sel2 rangeExp)) in -- generating temp variable for guard address
                                                                                                                                                        ((Abs.ForStateExprDo (mergeTacs [(rangeexp_content rangeExpTac),                       -- rangeExpr TACS (evaluation of expr1 and expr2 code)
                                                                                                                                                                                        (TAC [TacAssignNullOp guardTempAddr expr1Addr (B_type Type_Integer)] []),  -- guard temp initialization to expr1 val
                                                                                                                                                                                        (TAC [TacJump guardLabel] []),                         -- jump to guard label
                                                                                                                                                                                        (TAC [TacLabel l] []),                                 -- body label              
                                                                                                                                                                                        (statement_content statTac),                           -- body TAC code
                                                                                                                                                                                        (TAC [TacAssignBinaryOp guardTempAddr IntAdd guardTempAddr (AddrInt 1) (B_type Type_Integer)] []), -- guard++
                                                                                                                                                                                        (TAC [TacLabel guardLabel] []),                        -- guard label
                                                                                                                                                                                        (TAC [TacRelConditionalJump l False LeqInt guardTempAddr expr2Addr] []),  -- check of guard <= end (relation jump)
                                                                                                                                                                                        (TAC [TacLabel nextLabel] [])                          -- end of for
                                                                                                                                                                                        ]) rangeExpTac statTac),sel2 statement, sel3 statement)                                                                                      
genTacForStatement (Abs.ForStateExprWDo res rangexp b@(Abs.BlockStatement _ stats)) n l k (w,j) = let rangeExp = (genTacRangeExpr rangexp n l k (w,j)) in -- for range do stats
                                                                                                    let guardLabel = newLabel "guard" (k+1) in
                                                                                                        let nextLabel = newLabel "next" (k+2) in
                                                                                                            let statements = (genTacStatements stats (sel2 rangeExp) l ((sel3 rangeExp )+1) (nextLabel,guardLabel)) in 
                                                                                                            let statsTac = sel1 statements in
                                                                                                                let rangeExpTac = sel1 rangeExp in
                                                                                                                    case rangeExpTac of
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
genTacRangeExpr (Abs.RangeExpressionSingle res expr1 expr2) n l k (w,j) = let exprLeft = (genTacExpression expr1 n l k (w,j) "") in
                                                                            let exprRight = (genTacExpression expr2 (sel2 exprLeft) l (sel3 exprLeft) (w,j) "") in
                                                                                let newC = sel2 exprRight in
                                                                                    let newK = sel3 exprRight in
                                                                                        let exprLeftTac = (sel1 exprLeft) in
                                                                                            let exprRightTac = (sel1 exprRight) in
                                                                                                ((Abs.RangeExpressionSingle (merge2Tacs (expression_content exprLeftTac) (expression_content exprRightTac)) exprLeftTac exprRightTac),newC,newK,sel4 exprLeft,sel4 exprRight)
                                                                            

genTacWhileDoStatement :: Abs.WHILESTATEMENT TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.WHILESTATEMENT TAC, Prelude.Integer, Prelude.Integer)
genTacWhileDoStatement (Abs.WhileStateSimpleDo res expr stat) n l k (w,j) = let guardExpr = (genTacExpression expr n l k (w,j) "wor") in 
                                                                                let exprTac = sel1 guardExpr in
                                                                                    let guardLab = newLabel "guard" ((sel3 guardExpr)+1) in
                                                                                        let nextLab = newLabel "next" ((sel3 guardExpr)+2) in
                                                                                            let statement = (genTacStatement stat (sel2 guardExpr) l ((sel3 guardExpr)+3) (nextLab,guardLab)) in 
                                                                                                let statTac = sel1 statement in 
                                                                                                    let exprAddr = sel4 guardExpr in
                                                                                                        ((Abs.WhileStateSimpleDo (mergeTacs [(TAC [TacJump guardLab,TacLabel l] []),        -- jump to guard label + body label
                                                                                                                                             (statement_content statTac),                   -- body code tac
                                                                                                                                             (TAC [TacLabel guardLab] []),                  -- guard label
                                                                                                                                             (expression_content exprTac),                  -- code for guard expression eval.
                                                                                                                                             (TAC [TacLabel nextLab] [])])                     -- next (end of while block) label
                                                                                                                                             exprTac statTac), sel2 statement, sel3 statement)
genTacWhileDoStatement (Abs.WhileStateSimpleWDo res expr b@(Abs.BlockStatement _ statements)) n l k (w,j) = let guardExpr = (genTacExpression expr n l k (w,j) "wor") in 
                                                                                                                let exprTac = sel1 guardExpr in
                                                                                                                    let guardLab = newLabel "guard" ((sel3 guardExpr)+1) in
                                                                                                                        let nextLab = newLabel "next" ((sel3 guardExpr)+2) in
                                                                                                                            let stats = (genTacStatements statements (sel2 guardExpr) l ((sel3 guardExpr)+3) (nextLab,guardLab)) in 
                                                                                                                                let statsTac = sel1 stats in 
                                                                                                                                    let exprAddr = sel4 guardExpr in
                                                                                                                                        ((Abs.WhileStateSimpleWDo (mergeTacs [(TAC [TacJump guardLab,TacLabel l] []),     -- jump to guard label + body label   
                                                                                                                                                                              (statements_content statsTac),              -- body code tac
                                                                                                                                                                              (TAC [TacLabel guardLab] []),               -- guard label
                                                                                                                                                                              (expression_content exprTac),               -- code for guard expression eval.
                                                                                                                                                                              (TAC [TacLabel nextLab] [])])                  -- next (end of while block) label
                                                                                                                                                                              exprTac (Abs.BlockStatement (TAC [] []) statsTac)),sel2 stats, sel3 stats)
genTacWhileDoStatement (Abs.WhileStateCtrlDo res ctrlState state) n l k (w,j)  = let ctrlStatement = genTacControlStatement ctrlState n l k (w,j) in
                                                                                    let guardLab = l in -- continue will jump directly to code label because guard is not present (it's true or while is ignored (when ctrl decl is false no tac is generated))
                                                                                        let nextLab = newLabel "next" (sel3 ctrlStatement) in 
                                                                                            let statTac = genTacStatement state (sel2 ctrlStatement) l ((sel3 ctrlStatement)+1) (nextLab,guardLab) in
                                                                                                let flagValue = checkControlDeclarationStatement ctrlState in -- parte di funzioni tac da propagare
                                                                                                    let tac = case flagValue of
                                                                                                                False -> (TAC [] [])
                                                                                                                True  -> (mergeTacs [(ctrldecstatement_content (sel1 ctrlStatement)),
                                                                                                                                     (TAC [TacComment "CtrlDeclStat was valid; guard is set to True (break statements are the only way to exit the loop!)",TacLabel l] []),  -- body label
                                                                                                                                     (statement_content (sel1 statTac)),   -- Tac of body code (if no break: DEADLOCK)
                                                                                                                                     (TAC [TacJump l,TacComment "Guard is set to True, there are no exit conditions to be evaluated!"] []), -- jump to code: loop
                                                                                                                                     (TAC [TacLabel nextLab] [])])          -- next lab (for break jumps)
                                                                                                                    in ((Abs.WhileStateCtrlDo tac (sel1 ctrlStatement) (sel1 statTac)),if flagValue then (sel2 statTac) else n, if flagValue then (sel3 statTac) else k)
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
                                                                                                                                                in ((Abs.WhileStateCtrlWDo tac (sel1 ctrlStatement) (Abs.BlockStatement (TAC [] []) (sel1 statsTac))),if flagValue then (sel2 statsTac) else n, if flagValue then (sel3 statsTac) else k)

genTacDoWhileStatement :: Abs.DOSTATEMENT TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.DOSTATEMENT TAC, Prelude.Integer, Prelude.Integer)
genTacDoWhileStatement (Abs.DoWhileState res stat expr) n l k (w,j) = let nextLab = newLabel "next" k in                              
                                                                        let statement = (genTacStatement stat n l (k+1) (nextLab,l)) in
                                                                            let guardExpr = (genTacExpression expr (sel2 statement) l (sel3 statement) (w,j) "wor") in 
                                                                                let statTac = sel1 statement in 
                                                                                    let exprTac = sel1 guardExpr in
                                                                                        let exprAddr = sel4 guardExpr in
                                                                                            ((Abs.DoWhileState (mergeTacs [(TAC [TacLabel l] []),                       -- body label 
                                                                                                                           (statement_content statTac),                 -- body tac code (must be executed at least once in do-while blocks)
                                                                                                                           (expression_content exprTac),                -- code for guard expression eval.
                                                                                                                           (TAC [TacLabel nextLab] [])])                   -- next (end of do-while block) label
                                                                                                                           statTac exprTac),sel2 guardExpr, sel3 guardExpr)

genTacBlock :: Abs.B TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.B TAC,Prelude.Integer,Prelude.Integer)
genTacBlock (Abs.BlockStatement res statements) n l k (w,j) = let statsTac = genTacStatements statements n l k (w,j) in ((Abs.BlockStatement (statements_content (sel1 statsTac)) (sel1 statsTac)),(sel2 statsTac),(sel3 statsTac))

genTacConditionalStatement :: Abs.CONDITIONALSTATE TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.CONDITIONALSTATE TAC,Prelude.Integer,Prelude.Integer)
genTacConditionalStatement (Abs.ConditionalStatementSimpleThen res exp state elseState) n l k (w,j) = let expTac = genTacExpression exp n l k (w,j) "" in -- res è il giusto tcheck? TODO
                                                                                                        let statTac = genTacStatement state (sel2 expTac) l ((sel3 expTac)+1) (w,j) in        
                                                                                                            let expTacMod = TAC (updateTac (code (expression_content (sel1 expTac))) l) [] in        
                                                                                                                let expAddr = sel4 expTac in
                                                                                                                    case elseState of 
                                                                                                                        -- if EXPR then CODE
                                                                                                                        (Abs.ElseStateEmpty _)  -> ((Abs.ConditionalStatementSimpleThen (TAC (removeDuplicates (code (mergeTacs [expTacMod,             -- guard code eval. tac
                                                                                                                                                                                                    (case exp of
                                                                                                                                                                                                     (Abs.ExpressionBinaryOr _ _ _) -> (TAC [TacLabel (newLabel "true_or" (sel3 expTac))] [])
                                                                                                                                                                                                     _ -> TAC [] []
                                                                                                                                                                                                    ), 
                                                                                                                                                                                                    (statement_content (sel1 statTac)),             -- if_true code
                                                                                                                                                                                                    (TAC [TacLabel l] [])])) []) [])                            -- if_false label jump (guard jump destination)
                                                                                                                                                                                                    (sel1 expTac) (sel1 statTac) (Abs.ElseStateEmpty (TAC [] []))),(sel2 statTac),(sel3 statTac)) 
                                                                                                                        -- if EXPR then CODE else CODE  
                                                                                                                        (Abs.ElseState _ elsestats) -> let elseStatesTac = genTacStatement elsestats (sel2 statTac) l (sel3 statTac) (w,j) in
                                                                                                                                                            let nextLab = newLabel "next" (sel3 elseStatesTac) in
                                                                                                                                                                ((Abs.ConditionalStatementSimpleThen (TAC (removeDuplicates (code (mergeTacs [expTacMod,            -- guard code eval. tac(case exp of
                                                                                                                                                                                                                (case exp of
                                                                                                                                                                                                                 (Abs.ExpressionBinaryOr _ _ _) -> (TAC [TacLabel (newLabel "true_or" (sel3 expTac))] [])
                                                                                                                                                                                                                 _ -> TAC [] []
                                                                                                                                                                                                                ),
                                                                                                                                                                                                                (statement_content (sel1 statTac)),             -- if_true code
                                                                                                                                                                                                                (TAC [TacJump nextLab] []),                        -- jump to end of if label (next label)
                                                                                                                                                                                                                (TAC [TacLabel l] []),                             -- if_false label jump (guard jump destination)
                                                                                                                                                                                                                (statement_content (sel1 elseStatesTac)),       -- else code tac
                                                                                                                                                                                                                (TAC [TacLabel nextLab] [])])) []) [])                      -- next (end of if) label
                                                                                                                                                                                                                (sel1 expTac) (sel1 statTac) (Abs.ElseState (TAC [] []) (sel1 elseStatesTac)),(sel2 elseStatesTac),(sel3 elseStatesTac)+1)) -- if expr then ... else ...

genTacConditionalStatement (Abs.ConditionalStatementSimpleWThen res exp b@(Abs.BlockStatement _ statements) elseState) n l k (w,j) = let expTac = genTacExpression exp n l k (w,j) "" in -- res è il giusto tcheck? TODO
                                                                                                                                       let statTacs = genTacStatements statements (sel2 expTac) l (sel3 expTac) (w,j) in
                                                                                                                                           let expAddr = sel4 expTac in 
                                                                                                                                               case elseState of
                                                                                                                                                   (Abs.ElseStateEmpty _)      -> ((Abs.ConditionalStatementSimpleWThen (TAC (removeDuplicates (code (mergeTacs [(expression_content (sel1 expTac)), -- same as previous cases, but syntax has blocks!
                                                                                                                                                                                                                                    (case exp of
                                                                                                                                                                                                                                     (Abs.ExpressionBinaryOr _ _ _) -> (TAC [TacLabel (newLabel "true_or" (sel3 expTac))] [])
                                                                                                                                                                                                                                     _ -> TAC [] []
                                                                                                                                                                                                                                    ),
                                                                                                                                                                                                                                    (statements_content (sel1 statTacs)),
                                                                                                                                                                                                                                    (TAC [TacLabel l] [])])) []) [])
                                                                                                                                                                                                                                    (sel1 expTac) (Abs.BlockStatement (TAC [] []) (sel1 statTacs)) (Abs.ElseStateEmpty (TAC [] []))),(sel2 statTacs),(sel3 statTacs))   -- if expr then ...
                                                                                                                                                   (Abs.ElseState _ elsestats) -> let elseStatesTac = genTacStatement elsestats (sel2 statTacs) l (sel3 statTacs) (w,j) in
                                                                                                                                                                                           let nextLab = newLabel "next" (sel3 elseStatesTac) in
                                                                                                                                                                                               ((Abs.ConditionalStatementSimpleWThen (TAC (removeDuplicates (code (mergeTacs [(expression_content (sel1 expTac)), -- same as previous cases, but syntax has blocks!
                                                                                                                                                                                                                                                 (case exp of
                                                                                                                                                                                                                                                 (Abs.ExpressionBinaryOr _ _ _) -> (TAC [TacLabel (newLabel "true_or" (sel3 expTac))] [])
                                                                                                                                                                                                                                                 _ -> TAC [] []
                                                                                                                                                                                                                                                ),
                                                                                                                                                                                                                                                 (statements_content (sel1 statTacs)),
                                                                                                                                                                                                                                                 (TAC [TacJump nextLab] []),
                                                                                                                                                                                                                                                 (TAC [TacLabel l] []), (statement_content (sel1 elseStatesTac)),
                                                                                                                                                                                                                                                 (TAC [TacLabel nextLab] [])])) []) [])
                                                                                                                                                                                                                                                 (sel1 expTac) (Abs.BlockStatement (TAC [] []) (sel1 statTacs)) (Abs.ElseState (TAC [] []) (sel1 elseStatesTac)),(sel2 elseStatesTac),(sel3 elseStatesTac)+1)) -- if expr then ... else ...
genTacConditionalStatement (Abs.ConditionalStatementCtrlThen res ctrlState state elseState) n l k (w,j) = let ctrlStatement = genTacControlStatement ctrlState n l (k-1) (w,j) in
                                                                                                              let statTac = genTacStatement state (sel2 ctrlStatement) l (sel3 ctrlStatement) (w,j) in
                                                                                                                  let flagValue = checkControlDeclarationStatement ctrlState in   -- get the result of the control declaration statement! valid declaration = true; invalid declaration = false flag!
                                                                                                                      case elseState of                                           -- We already know at COMPILE-TIME which code block (then or else) will be executed; there's no need of jumps
                                                                                                                          -- if CTRLDECL FLAG then CODE                           -- We ignore else code if the ctrl declaration was valid, and the opposite!
                                                                                                                          (Abs.ElseStateEmpty _)  -> let tac = case flagValue of
                                                                                                                                                                  True  -> TAC ((code (ctrldecstatement_content (sel1 ctrlStatement))) ++ [TacComment "CtrlDeclStat was valid; else code is ignored."] ++ (code (statement_content (sel1 statTac)))) [] -- we know then_code must be executed, tac = ctrldecl tac + tac of then block
                                                                                                                                                                  False -> TAC [] [] -- we know that else_code must be executed but else is empty! tac = empty
                                                                                                                                                                      in ((Abs.ConditionalStatementCtrlThen tac (sel1 ctrlStatement) (sel1 statTac) (Abs.ElseStateEmpty (TAC [] []))),if flagValue then (sel2 statTac) else (sel2 ctrlStatement),if flagValue then (sel3 statTac) else (sel3 ctrlStatement)) -- if ... then ...
                                                                                                                          -- if CTRLDECL FLAG then CODE else CODE  
                                                                                                                          (Abs.ElseState _ elsestats) -> let elseStatesTac = genTacStatement elsestats (if flagValue then (sel2 statTac) else (sel2 ctrlStatement)) l (if flagValue then (sel3 statTac) else (sel3 ctrlStatement)) (w,j) in
                                                                                                                                                              let nextLab = newLabel "next" (sel3 elseStatesTac) in
                                                                                                                                                                  let tac = case flagValue of
                                                                                                                                                                              True  -> TAC ((code (ctrldecstatement_content (sel1 ctrlStatement))) ++ [TacComment "CtrlDeclStat was valid; else code is ignored."] ++ (code (statement_content (sel1 statTac)))) [] -- we know then_code  must be executed, tac = ctrldecl tac + tac of then block
                                                                                                                                                                              False -> TAC ((code (ctrldecstatement_content (sel1 ctrlStatement))) ++ [TacComment "CtrlDeclStat was invalid; then code is ignored."] ++ (code (statement_content (sel1 elseStatesTac)))) [] -- we know else_code must be executed, tac = ctrldecl tac + tac of else block
                                                                                                                                                                                          in ((Abs.ConditionalStatementCtrlThen tac (sel1 ctrlStatement) (sel1 statTac) (Abs.ElseState (TAC [] []) (sel1 elseStatesTac)),if flagValue then (sel2 statTac) else (sel2 elseStatesTac),if flagValue then (sel3 statTac) else (sel3 elseStatesTac)+1)) -- if expr then ... else ...        
genTacConditionalStatement (Abs.ConditionalStatementCtrlWThen res ctrlState b@(Abs.BlockStatement _ states) elseState) n l k (w,j) = let ctrlStatement = genTacControlStatement ctrlState n l (k-1) (w,j) in
                                                                                                                                      let statsTac = genTacStatements states (sel2 ctrlStatement) l (sel3 ctrlStatement) (w,j) in
                                                                                                                                          let flagValue = checkControlDeclarationStatement ctrlState in   -- get the result of the control declaration statement! valid declaration = true; invalid declaration = false flag!
                                                                                                                                              case elseState of                                           -- We already know at COMPILE-TIME which code block (then or else) will be executed; there's no need of jumps
                                                                                                                                                  -- if CTRLDECL FLAG then CODE                           -- We ignore else code if the ctrl declaration was valid, and the opposite!
                                                                                                                                                  (Abs.ElseStateEmpty _)  -> let tac = case flagValue of
                                                                                                                                                                                          True  -> TAC ((code (ctrldecstatement_content (sel1 ctrlStatement))) ++ [TacComment "CtrlDeclStat was valid; else code is ignored."] ++ (code (statements_content (sel1 statsTac)))) [] -- we know then_code must be executed, tac = ctrldecl tac + tac of then block
                                                                                                                                                                                          False -> TAC [] [] -- we know that else_code must be executed but else is empty! tac = empty
                                                                                                                                                                                              in ((Abs.ConditionalStatementCtrlWThen tac (sel1 ctrlStatement) (Abs.BlockStatement (TAC [] []) (sel1 statsTac)) (Abs.ElseStateEmpty (TAC [] []))),if flagValue then (sel2 statsTac) else (sel2 ctrlStatement),if flagValue then (sel3 statsTac) else (sel3 ctrlStatement)) -- if ... then ...
                                                                                                                                                  -- if CTRLDECL FLAG then CODE else CODE  
                                                                                                                                                  (Abs.ElseState _ elsestats) -> let elseStatesTac = genTacStatement elsestats (if flagValue then (sel2 statsTac) else (sel2 ctrlStatement)) l (if flagValue then (sel3 statsTac) else (sel3 ctrlStatement)) (w,j) in
                                                                                                                                                                                      let nextLab = newLabel "next" (sel3 elseStatesTac) in
                                                                                                                                                                                          let tac = case flagValue of
                                                                                                                                                                                                      True  -> TAC ((code (ctrldecstatement_content (sel1 ctrlStatement))) ++ [TacComment "CtrlDeclStat was valid; else code is ignored."]  ++ (code (statements_content (sel1 statsTac)))) [] -- we know then_code  must be executed, tac = ctrldecl tac + tac of then block
                                                                                                                                                                                                      False -> TAC ((code (ctrldecstatement_content (sel1 ctrlStatement))) ++ [TacComment "CtrlDeclStat was invalid; then code is ignored."] ++ (code (statement_content (sel1 elseStatesTac)))) [] -- we know else_code must be executed, tac = ctrldecl tac + tac of else block
                                                                                                                                                                                                                  in ((Abs.ConditionalStatementCtrlWThen tac (sel1 ctrlStatement) (Abs.BlockStatement (TAC [] []) (sel1 statsTac)) (Abs.ElseState (TAC [] []) (sel1 elseStatesTac)),if flagValue then (sel2 statsTac) else (sel2 elseStatesTac),if flagValue then (sel3 statsTac) else (sel3 elseStatesTac)+1)) -- if expr then ... else ...        

genTacControlStatement :: Abs.CTRLDECSTATEMENT TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) ->  (Abs.CTRLDECSTATEMENT TAC,Prelude.Integer,Prelude.Integer)
genTacControlStatement (Abs.CtrlDecStateVar res@(TResult _ ty _) ident@(Abs.Ident id resi@(TResult _ _ pos)) typepart@(Abs.TypePart (TResult _ typePart _) _) expr) n l k (w,j) = case ty of 
                                                                                                                                            B_type Type_Void -> let expression = genTacExpression expr n l k (w,j) "" in 
                                                                                                                                                                    ((Abs.CtrlDecStateVar (TAC [TacAssignNullOp (buildIDAddr pos id) (genDefaultInitAddr typePart) typePart]    -- the ctrl decl statement was invalid; so ctrl var is initialized with default value
                                                                                                                                                                                                []) (Abs.Ident id (TAC [] [])) (Abs.TypePart (TAC [] []) (Abs.TypeExpression (TAC [] []) (Abs.PrimitiveTypeVoid (TAC [] [])))) (sel1 expression)),(sel2 expression),(sel3 expression))  -- it wasn't a correct ctrldecl assignment! so initialize at def. value!
                                                                                                                                            _                -> let expression = genTacExpression expr n l k (w,j) "" in
                                                                                                                                                                    let exprAddr = sel4 expression in
                                                                                                                                                                        ((Abs.CtrlDecStateVar (TAC (code (expression_content (sel1 expression)) ++              -- tac code of rval expr evaluation
                                                                                                                                                                                                   [TacAssignNullOp (buildIDAddr pos id) exprAddr ty])         -- the ctrl decl statement was valid; so ctrl var is initialized with the initialization expr. value
                                                                                                                                                                                                   []) (Abs.Ident id (TAC [] [])) (Abs.TypePart (TAC [] []) (Abs.TypeExpression (TAC [] []) (Abs.PrimitiveTypeVoid (TAC [] [])))) (sel1 expression)),(sel2 expression),(sel3 expression))  -- it was a correct ctrldecl assignment
                                                                                                                                                                                                   
                                                                                                                                                                                                   
genTacControlStatement (Abs.CtrlDecStateConst res@(TResult _ ty _) ident@(Abs.Ident id resi@(TResult _ _ pos)) typepart@(Abs.TypePart (TResult _ typePart _) _) expr) n l k (w,j) = case ty of
                                                                                                                                            B_type Type_Void -> let expression = genTacExpression expr n l k (w,j) "" in 
                                                                                                                                                                ((Abs.CtrlDecStateConst (TAC [TacAssignNullOp (buildIDAddr pos id) (genDefaultInitAddr typePart) typePart]    -- the ctrl decl statement was invalid; so ctrl var is initialized with default value
                                                                                                                                                                                            []) (Abs.Ident id (TAC [] [])) (Abs.TypePart (TAC [] []) (Abs.TypeExpression (TAC [] []) (Abs.PrimitiveTypeVoid (TAC [] [])))) (sel1 expression)),(sel2 expression),(sel3 expression))  -- it wasn't a correct ctrldecl assignment! so initialize at def. value!
                                                                                                                                            _                -> let expression = genTacExpression expr n l k (w,j) "" in
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

genTacVariableType :: Abs.VARIABLETYPE TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.VARIABLETYPE TAC,Prelude.Integer,Prelude.Integer,Address)
genTacVariableType (Abs.VariableTypeParam res) n l k (w,j)      = (Abs.VariableTypeParam    (TAC [] []),n,k,AddrNULL)
genTacVariableType (Abs.VariableTypeConst res) n l k (w,j)      = (Abs.VariableTypeConst    (TAC [] []),n,k,AddrNULL)
genTacVariableType (Abs.VariableTypeVar res) n l k (w,j)        = (Abs.VariableTypeVar      (TAC [] []),n,k,AddrNULL)
genTacVariableType (Abs.VariableTypeRef res) n l k (w,j)        = (Abs.VariableTypeRef      (TAC [] []),n,k,AddrNULL)
genTacVariableType (Abs.VariableTypeConstRef res) n l k (w,j)   = (Abs.VariableTypeConstRef (TAC [] []),n,k,AddrNULL)

genTacVarDecList :: Abs.VARDECLIST TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.VARDECLIST TAC,Prelude.Integer,Prelude.Integer,Prelude.Integer,[Address],[Address])
genTacVarDecList (Abs.VariableDeclarationSingle res vardecId) n l k (w,j) = let vardecIdTac = genTacVarDecId vardecId n l k (w,j) in
                                                                            let vardecIdAddr = sel5 vardecIdTac in
                                                                                let initAddr = sel6 vardecIdTac in
                                                                                (Abs.VariableDeclarationSingle (vardecid_content (sel1 vardecIdTac)) (sel1 vardecIdTac),(sel2 vardecIdTac),(sel3 vardecIdTac),sel4 vardecIdTac,vardecIdAddr,initAddr)

genTacVarDecId :: Abs.VARDECID TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.VARDECID TAC,Prelude.Integer,Prelude.Integer,Prelude.Integer,[Address],[Address])
genTacVarDecId (Abs.VariableDeclaration res@(TResult _ ty _) idlist typepart@(Abs.TypePart _ typeExp) initpart) n l k (w,j) = case initpart of
                                                                            Abs.InitializzationPartEmpty resi -> let idlistTac = genTacIdentifierList idlist n l k (w,j) in
                                                                                                                    let tacId = identlist_content (sel1 idlistTac) in
                                                                                                                        let addrIdList = sel4 idlistTac in
                                                                                                                            let initAddr = AddrNULL in
                                                                                                                                let dim = generateDimForArray typeExp in
                                                                                                                                    let length = getDimFromType typepart in
                                                                                                                                        case typeExp of
                                                                                                                                            Abs.TypeExpressionArraySimple _ _ _ -> (Abs.VariableDeclaration tacId (sel1 idlistTac) (Abs.TypePart (TAC [] []) (TypeExpression (TAC [] []) (Abs.PrimitiveTypeInt (TAC [] [])))) (Abs.InitializzationPartEmpty (TAC [] [])),(sel2 idlistTac),(sel3 idlistTac),dim,addrIdList,buildInitArray initAddr length)
                                                                                                                                            Abs.TypeExpressionArray _ _ _ -> (Abs.VariableDeclaration tacId (sel1 idlistTac) (Abs.TypePart (TAC [] []) (TypeExpression (TAC [] []) (Abs.PrimitiveTypeInt (TAC [] [])))) (Abs.InitializzationPartEmpty (TAC [] [])),(sel2 idlistTac),(sel3 idlistTac),dim,addrIdList,buildInitArray initAddr length)
                                                                                                                                            _ -> (Abs.VariableDeclaration tacId (sel1 idlistTac) (Abs.TypePart (TAC [] []) (TypeExpression (TAC [] []) (Abs.PrimitiveTypeInt (TAC [] [])))) (Abs.InitializzationPartEmpty (TAC [] [])),(sel2 idlistTac),(sel3 idlistTac),-1,addrIdList,[initAddr])
                                                                            Abs.InitializzationPart resi expr -> if ty==B_type Type_Boolean
                                                                                                                    then
                                                                                                                         let temp = newTemp n in
                                                                                                                            let label = newLabel "endSet" k in
                                                                                                                                let idlistTac = genTacIdentifierList idlist (n+1) l (k+1) (w,j) in
                                                                                                                                    let tacId = identlist_content (sel1 idlistTac) in
                                                                                                                                        let addrIdList = sel4 idlistTac in
                                                                                                                                            let exprTac = (genTacExpression expr (sel2 idlistTac) label (sel3 idlistTac) (w,j) "or") in
                                                                                                                                                let initTac = (Abs.InitializzationPart (expression_content (sel1 exprTac)) (sel1 exprTac)) in
                                                                                                                                                    let initAddr = sel4 exprTac in
                                                                                                                                                        (Abs.VariableDeclaration (mergeTacs[ (TAC [TacAssignNullOp temp (AddrBool True) (B_type Type_Boolean)] []),
                                                                                                                                                                                            (expression_content (sel1 exprTac)),
                                                                                                                                                                                            (TAC [TacAssignNullOp temp (AddrBool False) (B_type Type_Boolean)] []),
                                                                                                                                                                                            (TAC [TacLabel label] [])
                                                                                                                                                                                            ]) (sel1 idlistTac) (Abs.TypePart (TAC [] []) (TypeExpression (TAC [] []) (Abs.PrimitiveTypeInt (TAC [] [])))) initTac ,(sel2 exprTac),(sel3 exprTac),-1,addrIdList,[temp])
                                                                                                                    else let idlistTac = genTacIdentifierList idlist n l k (w,j) in
                                                                                                                            let tacId = identlist_content (sel1 idlistTac) in
                                                                                                                                let addrIdList = sel4 idlistTac in
                                                                                                                                    let exprTac = (genTacExpression expr (sel2 idlistTac) l (sel3 idlistTac) (w,j) "or") in
                                                                                                                                        let initTac = (Abs.InitializzationPart (expression_content (sel1 exprTac)) (sel1 exprTac)) in
                                                                                                                                            let initAddr = sel4 exprTac in
                                                                                                                                                (Abs.VariableDeclaration (expression_content (sel1 exprTac)) (sel1 idlistTac) (Abs.TypePart (TAC [] []) (TypeExpression (TAC [] []) (Abs.PrimitiveTypeInt (TAC [] [])))) initTac ,(sel2 exprTac),(sel3 exprTac),-1,addrIdList,[initAddr])
                                                                            Abs.InitializzationPartArray resi array -> let idlistTac = genTacIdentifierList idlist n l k (w,j) in
                                                                                                                    let tacId = identlist_content (sel1 idlistTac) in
                                                                                                                        let addrIdList = sel4 idlistTac in
                                                                                                                            let dim = generateDimForArray typeExp in
                                                                                                                                let arrayInitTac = (genTacArrayInit array (sel2 idlistTac) l (sel3 idlistTac) (w,j)) in
                                                                                                                                    let initTac = (Abs.InitializzationPartArray (arrayinit_content (sel1 arrayInitTac)) (sel1 arrayInitTac)) in
                                                                                                                                        (Abs.VariableDeclaration (arrayinit_content (sel1 arrayInitTac)) (sel1 idlistTac) (Abs.TypePart (TAC [] []) (TypeExpression (TAC [] []) (Abs.PrimitiveTypeInt (TAC [] [])))) initTac ,(sel2 arrayInitTac),(sel3 arrayInitTac),dim,addrIdList,sel4 arrayInitTac)

genTacArrayInit :: Abs.ARRAYINIT TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.ARRAYINIT TAC,Prelude.Integer,Prelude.Integer,[Address])
genTacArrayInit (Abs.ArrayInitElems res listelementarray ) n l k (w,j) = let listElementTac = genTacListElementOfArray listelementarray n l k (w,j) in
                                                                                (Abs.ArrayInitElems (listelementarray_content (sel1 listElementTac)) (sel1 listElementTac),(sel2 listElementTac),(sel3 listElementTac),(sel4 listElementTac))
genTacArrayInit (Abs.ArrayInitSingle res arrayInit) n l k (w,j) = let arrayInitTac = genTacArrayInit arrayInit n l k (w,j) in
                                                                                    (Abs.ArrayInitSingle (arrayinit_content (sel1 arrayInitTac)) (sel1 arrayInitTac),(sel2 arrayInitTac),(sel3 arrayInitTac),sel4 arrayInitTac)
genTacArrayInit (Abs.ArrayInit res arrayInit1 arrayInit2) n l k (w,j) = let arrayInitTac1 = genTacArrayInit arrayInit1 n l k (w,j) in
                                                                            let arrayInitTac2 = genTacArrayInit arrayInit2 (sel2 arrayInitTac1) l (sel3 arrayInitTac1) (w,j) in
                                                                                    (Abs.ArrayInit (mergeTacs [(arrayinit_content (sel1 arrayInitTac1)),
                                                                                                                (arrayinit_content (sel1 arrayInitTac2))]) (sel1 arrayInitTac1) (sel1 arrayInitTac2),(sel2 arrayInitTac2),(sel3 arrayInitTac2),(sel4 arrayInitTac1)++(sel4 arrayInitTac2))  

genTacListElementOfArray :: Abs.LISTELEMENTARRAY TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.LISTELEMENTARRAY TAC,Prelude.Integer,Prelude.Integer,[Address])
genTacListElementOfArray (Abs.ListElementOfArray res exp)  n l k (w,j) = let expTac = genTacExpression exp n l k (w,j) "" in
                                                                            (Abs.ListElementOfArray (TAC (code (expression_content (sel1 expTac))) []) (sel1 expTac),(sel2 expTac),(sel3 expTac),[sel4 expTac])
genTacListElementOfArray (Abs.ListElementsOfArray res exp listelement)  n l k (w,j) = let expTac = genTacExpression exp n l k (w,j) "" in
                                                                                        let listelementTac = genTacListElementOfArray listelement (sel2 expTac) l (sel3 expTac) (w,j) in
                                                                                        (Abs.ListElementsOfArray (TAC ((code (expression_content (sel1 expTac))) ++ (code (listelementarray_content (sel1 listelementTac)))) []) (sel1 expTac) (sel1 listelementTac),(sel2 listelementTac),(sel3 listelementTac),[sel4 expTac]++(sel4 listelementTac))

genTacExpression :: Abs.EXPRESSION TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> Prelude.String -> (Abs.EXPRESSION TAC,Prelude.Integer,Prelude.Integer,Address)
genTacExpression (Abs.ExpressionInteger res value@(Abs.Integer val resi))       n l k (w,j) str = (Abs.ExpressionInteger (TAC [] []) (Abs.Integer val (TAC [] []))  ,n,k, AddrInt val)
genTacExpression (Abs.ExpressionBoolean res value@(Abs.Boolean_true resi))      n l k (w,j) str = (Abs.ExpressionBoolean (TAC [] []) (Abs.Boolean_true (TAC [] [])) ,n,k, AddrBool True)
genTacExpression (Abs.ExpressionBoolean res value@(Abs.Boolean_false resi))     n l k (w,j) str = (Abs.ExpressionBoolean (TAC [] []) (Abs.Boolean_false (TAC [] [])),n,k, AddrBool False)
genTacExpression (Abs.ExpressionBoolean res value@(Abs.Boolean_True resi))      n l k (w,j) str = (Abs.ExpressionBoolean (TAC [] []) (Abs.Boolean_True (TAC [] [])) ,n,k, AddrBool True)
genTacExpression (Abs.ExpressionBoolean res value@(Abs.Boolean_False resi))     n l k (w,j) str = (Abs.ExpressionBoolean (TAC [] []) (Abs.Boolean_False (TAC [] [])),n,k, AddrBool False)
genTacExpression (Abs.ExpressionChar res value@(Abs.Char val resi))             n l k (w,j) str = (Abs.ExpressionChar    (TAC [] []) (Abs.Char val (TAC [] []))     ,n,k, AddrChar val)
genTacExpression (Abs.ExpressionString res value@(Abs.String val resi))         n l k (w,j) str = (Abs.ExpressionString  (TAC [] []) (Abs.String val (TAC [] []))   ,n,k, AddrString val)
genTacExpression (Abs.ExpressionReal res value@(Abs.Real val resi))             n l k (w,j) str = (Abs.ExpressionReal    (TAC [] []) (Abs.Real val (TAC [] []))     ,n,k, AddrReal val)
genTacExpression (Abs.ExpressionBracket res exp)                                n l k (w,j) str = let exprTac = genTacExpression exp n l k (w,j) str in (Abs.ExpressionBracket (expression_content (sel1 exprTac)) (sel1 exprTac),(sel2 exprTac),(sel3 exprTac),(sel4 exprTac))
genTacExpression (Abs.ExpressionCast res def tipo)                              n l k (w,j) str = let defTac = genTacDefault def n l k (w,j) in
                                                                                                        let tipoTac = genTacTipo tipo (sel2 defTac) l (sel3 defTac) (w,j) in
                                                                                                            let temp = newTemp (sel2 tipoTac) in
                                                                                                                let fromType = getTypeFromDefault def in
                                                                                                                    let toType = TacGen.getTypeFromPrimitive tipo in
                                                                                                                        ((Abs.ExpressionCast (TAC ((code (default_content (sel1 defTac))) ++ -- tac of default (left part)
                                                                                                                                                   [TacCastConversion temp (sel4 defTac) fromType toType]) -- Tac instruction for conversion (cast)
                                                                                                                                                   []) (sel1 defTac) (sel1 tipoTac)),(sel2 tipoTac)+1,(sel3 tipoTac),temp)
genTacExpression (Abs.ExpressionUnary res@(TResult env ty pos) unary def)       n l k (w,j) str = let defTac = genTacDefault def (n+1) l k (w,j) in 
                                                                                                    let defAddr = sel4 defTac in
                                                                                                        let temp = newTemp n in
                                                                                                            case unary of 
                                                                                                                Abs.UnaryOperationPositive _ -> (Abs.ExpressionUnary (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Pos defAddr ty] [])  ) (Abs.UnaryOperationPositive (TAC [] [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp) 
                                                                                                                Abs.UnaryOperationNegative _ -> (Abs.ExpressionUnary (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Neg defAddr ty] [])  ) (Abs.UnaryOperationNegative (TAC [] [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp) 
                                                                                                                Abs.UnaryOperationNot      _ -> (Abs.ExpressionUnary (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Not defAddr ty] [])  ) (Abs.UnaryOperationNot (TAC [] [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp) 
                                                                                                                Abs.UnaryOperationPointer  _ -> (Abs.ExpressionUnary (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Point defAddr ty] [])) (Abs.UnaryOperationPointer (TAC [] [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp)
genTacExpression (Abs.ExpressionBinaryPlus res@(TResult env t pos) expr1 expr2) n l k (w,j) str = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) str in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) str in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryPlus (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "plus") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryMinus res@(TResult env t pos) expr1 expr2) n l k (w,j) str = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) str in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) str in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryMinus (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "minus") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryProduct res@(TResult env t pos) expr1 expr2) n l k (w,j) str = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) str in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) str in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryProduct (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "product") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryDivision res@(TResult env t pos) expr1 expr2) n l k (w,j) str = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) str in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) str in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryDivision (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "division") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryModule res@(TResult env t pos) expr1 expr2) n l k (w,j) str = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) str in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) str in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryModule (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "module") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryPower res@(TResult env t pos) expr1 expr2) n l k (w,j) str = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) str in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) str in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryPower (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignBinaryOp temp (buildOp t "power") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)
genTacExpression (Abs.ExpressionBinaryAnd res@(TResult env t pos) expr1 expr2) n l k (w,j) str = let falseL = newLabel "false_and" (if str=="wor" then k else (k+1)) in
                                                                                                let expr1Tac = genTacExpression expr1 n (if str=="or" || str=="wor" then falseL else l) (if str=="wor" then k else (k+1)) (w,j) "" in 
                                                                                                    let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (if str=="wor" then k else (k+1)) (w,j) "" in
                                                                                                        let addrLeft = (sel4 expr1Tac) in
                                                                                                            let addrRight = (sel4 expr2Tac) in
                                                                                                                (Abs.ExpressionBinaryAnd (mergeTacs [(expression_content (sel1 expr1Tac)),
                                                                                                                                                              (if (addrLeft == AddrNULL) then TAC [] [] else (TAC [TacConditionalJump (if str=="or" || str=="wor" then falseL else l) False addrLeft] [])),
                                                                                                                                                              (expression_content (sel1 expr2Tac)),
                                                                                                                                                              (if (addrRight == AddrNULL) then TAC [] [] else (TAC [TacConditionalJump l (if str=="or" || str=="wor" then True else False) addrRight] [])),
                                                                                                                                                              (if (str=="or" || str=="wor") then TAC [TacLabel falseL] []else TAC [][])
                                                                                                                                                              ]) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),AddrNULL)   
genTacExpression (Abs.ExpressionBinaryOr res@(TResult env t pos) expr1 expr2) n l k (w,j) str = let trueL = newLabel "true_or" (k) in
                                                                                                    let expr1Tac = genTacExpression expr1 n (if str=="or" || str=="wor" then l else trueL) (if str=="or" || str=="wor" then k-1 else k) (w,j) "or" in 
                                                                                                        let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) str in -- A OR B     | TacConditionalJump    {destination::Label, flag::Prelude.Bool, first::Address}    
                                                                                                            let addrLeft = (sel4 expr1Tac) in
                                                                                                                let addrRight = (sel4 expr2Tac) in
                                                                                                                    ((Abs.ExpressionBinaryOr (mergeTacs [(expression_content (sel1 expr1Tac)),
                                                                                                                                                              (if (addrLeft == AddrNULL) then TAC [] [] else (TAC [TacConditionalJump (if str=="or" || str=="wor" then l else trueL) True addrLeft] [])),
                                                                                                                                                              (expression_content (sel1 expr2Tac)),
                                                                                                                                                              (if (addrRight == AddrNULL) then TAC [] [] else (TAC [TacConditionalJump (if str=="" || str=="or" || str=="wor" then l else trueL) True addrRight] [])),
                                                                                                                                                              (if (str=="") then TAC [TacLabel trueL] []else TAC [][])
                                                                                                                                                              ]) (sel1 expr1Tac) (sel1 expr2Tac)),(sel2 expr2Tac),(sel3 expr2Tac),AddrNULL)                                                                                                                                  
genTacExpression (Abs.ExpressionBinaryEq res@(TResult env t pos) expr1 expr2) n l k (w,j) str = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) str in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) str in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryEq (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "eq") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)                                                                                                    
genTacExpression (Abs.ExpressionBinaryNotEq res@(TResult env t pos) expr1 expr2) n l k (w,j) str = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) str in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) str in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryNotEq (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "noteq") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)                                                                                                    
genTacExpression (Abs.ExpressionBinaryGratherEq res@(TResult env t pos) expr1 expr2) n l k (w,j) str = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) str in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) str in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryGratherEq (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "grathereq") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)                                                                                                    
genTacExpression (Abs.ExpressionBinaryGrather res@(TResult env t pos) expr1 expr2) n l k (w,j) str = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) str in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) str in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryGrather (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "grather") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)                                                                                                    
genTacExpression (Abs.ExpressionBinaryLessEq res@(TResult env t pos) expr1 expr2) n l k (w,j) str = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) str in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) str in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryLessEq (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "lesseq") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)                                                                                                    
genTacExpression (Abs.ExpressionBinaryLess res@(TResult env t pos) expr1 expr2) n l k (w,j) str = let expr1Tac = genTacExpression expr1 (n+1) l k (w,j) str in 
                                                                                                let expr2Tac = genTacExpression expr2 (sel2 expr1Tac) l (sel3 expr1Tac) (w,j) str in
                                                                                                    let temp = newTemp n in
                                                                                                        (Abs.ExpressionBinaryLess (merge2Tacs (merge2Tacs (expression_content (sel1 expr1Tac)) (expression_content (sel1 expr2Tac))) (TAC [TacAssignRelOp temp (buildROp (getTypeFromExpr expr1) (getTypeFromExpr expr2) "less") (sel4 expr1Tac) (sel4 expr2Tac) t] [])) (sel1 expr1Tac) (sel1 expr2Tac),(sel2 expr2Tac),(sel3 expr2Tac),temp)                                                                                                    

genTacExpression (Abs.ExpressionIdent res ident@(Abs.Ident id resi@(TResult env t pos)) index) n l k (w,j) str = case Data.Map.lookup id env of
                                                                                                                  Just (entry:entries) -> case findEntryOfType (entry:entries) "var" of
                                                                                                                                            (x@(Variable _ posv _ _ _):xs) -> case index of
                                                                                                                                                                            (Abs.ArrayIndexElementEmpty _) -> ((Abs.ExpressionIdent (TAC [] []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElementEmpty (TAC [] []))),n,k,buildIDAddr posv id)
                                                                                                                                                                            (Abs.ArrayIndexElement _ typeindex) -> case findArray (x:xs) of
                                                                                                                                                                                                                        [Variable ty@(Array t _) posv _ _ s] -> let typeIndexTac = genTacTypeIndex typeindex n l k (w,j) 0 [] (-1) in
                                                                                                                                                                                                                                                                    let dim = generateDimForArrayFromType ty in
                                                                                                                                                                                                                                                                        let leftAddr = buildIDAddr posv id in
                                                                                                                                                                                                                                                                            if (isIntegerAddress (sel4 typeIndexTac)) 
                                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                                    let posArr = buildPosArray (sel4 typeIndexTac) s dim in
                                                                                                                                                                                                                                                                                        let leftAddrArray = buildArrayId leftAddr posArr 0 in
                                                                                                                                                                                                                                                                                            let comment = buildArrayComments (sel4 typeIndexTac) s dim t in
                                                                                                                                                                                                                                                                                                let temp = newTemp (sel2 typeIndexTac) in
                                                                                                                                                                                                                                                                                                    ((Abs.ExpressionIdent (TAC ([TacAssignNullOp temp leftAddrArray t]++comment) []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElement (TAC [] []) (sel1 typeIndexTac))),(sel2 typeIndexTac)+1,(sel3 typeIndexTac),temp)
                                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                                    let typeIndexTac = genTacTypeIndex typeindex n l k (w,j) dim s (-1) in
                                                                                                                                                                                                                                                                                        let posArr = buildPosArrayNoInteger (sel4 typeIndexTac) s dim (sel2 typeIndexTac) in
                                                                                                                                                                                                                                                                                            let leftAddrArray = buildArrayIdNoInteger leftAddr (newTemp ((sel2 typeIndexTac)-1)) in
                                                                                                                                                                                                                                                                                                let temp = newTemp (sel2 typeIndexTac) in
                                                                                                                                                                                                                                                                                                    ((Abs.ExpressionIdent (TAC ((code (typeindex_content (sel1 typeIndexTac)))++[TacAssignNullOp temp leftAddrArray t]) []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElement (TAC [] []) (sel1 typeIndexTac))),(sel2 typeIndexTac)+1,(sel3 typeIndexTac),temp)                                                                         
                                                                                                                                                                            (Abs.ArrayIndexElements _ arrayIndex typeindex ) -> case findArray (x:xs) of
                                                                                                                                                                                                                                    [Variable ty@(Array t _) posv _ _ s] -> let realT = getRealTypeFromArray t in
                                                                                                                                                                                                                                                                                let typeIndexTac = genTacTypeIndex typeindex n l k (w,j) 0 [] (-1) in
                                                                                                                                                                                                                                                                                    let arrayIndexTac = genTacArrayIndexElements arrayIndex (sel2 typeIndexTac) l (sel3 typeIndexTac) (w,j) 0 [] (-1) in
                                                                                                                                                                                                                                                                                        let dim = generateDimForArrayFromType ty in
                                                                                                                                                                                                                                                                                            let leftAddr = buildIDAddr posv id in
                                                                                                                                                                                                                                                                                                if (isIntegerAddress ((sel4 arrayIndexTac)++(sel4 typeIndexTac))) 
                                                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                                                        let posArr = buildPosArray ((sel4 arrayIndexTac)++(sel4 typeIndexTac)) s dim in
                                                                                                                                                                                                                                                                                                            let leftAddrArray = buildArrayId leftAddr posArr 0 in
                                                                                                                                                                                                                                                                                                                let comment = buildArrayComments ((sel4 arrayIndexTac)++ (sel4 typeIndexTac)) s dim realT in
                                                                                                                                                                                                                                                                                                                    let temp = newTemp (sel2 arrayIndexTac) in
                                                                                                                                                                                                                                                                                                                        ((Abs.ExpressionIdent (TAC ([TacAssignNullOp temp leftAddrArray realT]++comment) []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElements (TAC [] [])  (sel1 arrayIndexTac) (sel1 typeIndexTac))),(sel2 arrayIndexTac)+1,(sel3 arrayIndexTac),temp)
                                                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                                                        let arrayIndexTac = genTacArrayIndexElements (Abs.ArrayIndexElementsMultiple res arrayIndex typeindex) n l k (w,j) dim s (-1) in
                                                                                                                                                                                                                                                                                                            let posArr = buildPosArrayNoInteger (sel4 arrayIndexTac) s dim (sel2 arrayIndexTac) in
                                                                                                                                                                                                                                                                                                                let leftAddrArray = buildArrayIdNoInteger leftAddr (newTemp ((sel2 arrayIndexTac)-1)) in
                                                                                                                                                                                                                                                                                                                        let temp = newTemp (sel2 arrayIndexTac) in
                                                                                                                                                                                                                                                                                                                            ((Abs.ExpressionIdent (TAC ((code (arrayindexelements_content (sel1 arrayIndexTac)))++[TacAssignNullOp temp leftAddrArray realT]) []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElements (TAC [] [])  (sel1 arrayIndexTac) (sel1 typeIndexTac))),(sel2 arrayIndexTac)+1,(sel3 arrayIndexTac),temp)
                                                                                                                                                                                                                                                                                                
genTacExpression (Abs.ExpressionCall res@(TResult env _ _) ident@(Abs.Ident id resi) exps) n l k (w,j) str = case Data.Map.lookup id env of    
                                                                                                                Just (entry:entries) -> case findEntryOfType (entry:entries) "func" of
                                                                                                                    ((Function ty pos _ _):xs) -> let funcReturn = newTemp n in
                                                                                                                                                    let funcAddr = buildIDAddr pos id in
                                                                                                                                                    case exps of
                                                                                                                                                        (Abs.Expressions rese expr exprs) -> let expression = genTacExpression expr (n+1) l k (w,j) str in
                                                                                                                                                                                              let expressions = genTacExpressions exprs (sel2 expression) l (sel3 expression) (w,j) in
                                                                                                                                                                                                  ((Abs.ExpressionCall (TAC ((code (expression_content (sel1 expression))) ++       -- evaluation of the first param value
                                                                                                                                                                                                                             [TacParam (sel4 expression) (getTypeFromExpr expr)] ++  -- first param tac
                                                                                                                                                                                                                             (code (expressions_content (sel1 expressions))) ++     -- tac of others param
                                                                                                                                                                                                                             [TacAssignNullOp funcReturn funcAddr ty])              -- call tac
                                                                                                                                                                                                                             []) (Abs.Ident id (TAC [][])) (Abs.Expressions (TAC [][]) (sel1 expression) (sel1 expressions))),(sel2 expressions),(sel3 expressions),funcReturn) 
                                                                                                                                                        (Abs.Expression rese expr)        -> let expression = genTacExpression expr (n+1) l k (w,j) str in
                                                                                                                                                                                                  ((Abs.ExpressionCall (TAC ((code (expression_content (sel1 expression))) ++        -- evaluation of the param value
                                                                                                                                                                                                                            [(TacParam (sel4 expression) (getTypeFromExpr expr)),    -- param tac
                                                                                                                                                                                                                             (TacAssignNullOp funcReturn funcAddr ty)])              -- call tac
                                                                                                                                                                                                                             []) (Abs.Ident id (TAC [][])) (Abs.Expression (TAC [][]) (sel1 expression))),(sel2 expression),(sel3 expression),funcReturn) 
                                                                                                                                                        (Abs.ExpressionEmpty rese)        -> ((Abs.ExpressionCall (TAC [TacAssignNullOp funcReturn funcAddr ty]   -- call tac
                                                                                                                                                                                                                         []) (Abs.Ident id (TAC [][])) (Abs.ExpressionEmpty (TAC [][]))),n+1,k,funcReturn)
-- for functions R calls (expressions param lists)
genTacExpressions :: Abs.EXPRESSIONS TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.EXPRESSIONS TAC,Prelude.Integer,Prelude.Integer,Address)
genTacExpressions (Abs.Expressions res expr exprs) n l k (w,j) = let expression = genTacExpression expr n l k (w,j) "" in 
                                                                    let expressions = genTacExpressions exprs (sel2 expression) l (sel3 expression) (w,j) in
                                                                        ((Abs.Expressions (TAC ((code (expression_content (sel1 expression))) ++     
                                                                                                [TacParam (sel4 expression) (getTypeFromExpr expr)] ++
                                                                                                (code (expressions_content (sel1 expressions))))
                                                                                                []) (sel1 expression) (sel1 expressions)),(sel2 expressions),(sel3 expressions),(sel4 expression))
genTacExpressions (Abs.Expression res expr) n l k (w,j) = let expression = genTacExpression expr n l k (w,j) "" in 
                                                            ((Abs.Expression (TAC ((code (expression_content (sel1 expression))) ++     
                                                                                   [TacParam (sel4 expression) (getTypeFromExpr expr)]) 
                                                                                   []) (sel1 expression)),(sel2 expression),(sel3 expression),(sel4 expression))
genTacExpressions (Abs.ExpressionEmpty res) n l k (w,j)  = ((Abs.ExpressionEmpty (TAC [][])),n,k,AddrNULL)

genTacTipo :: Abs.PRIMITIVETYPE TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.PRIMITIVETYPE TAC,Prelude.Integer,Prelude.Integer)
genTacTipo (Abs.PrimitiveTypeVoid _) n l k (w,j)   = ((Abs.PrimitiveTypeVoid   (TAC [] [])),n,k)
genTacTipo (Abs.PrimitiveTypeBool _) n l k (w,j)   = ((Abs.PrimitiveTypeBool   (TAC [] [])),n,k)
genTacTipo (Abs.PrimitiveTypeInt _) n l k (w,j)    = ((Abs.PrimitiveTypeInt    (TAC [] [])),n,k)
genTacTipo (Abs.PrimitiveTypeReal _) n l k (w,j)   = ((Abs.PrimitiveTypeReal   (TAC [] [])),n,k)
genTacTipo (Abs.PrimitiveTypeString _) n l k (w,j) = ((Abs.PrimitiveTypeString (TAC [] [])),n,k)
genTacTipo (Abs.PrimitiveTypeChar _) n l k (w,j)   = ((Abs.PrimitiveTypeChar   (TAC [] [])),n,k) 
genTacTipo (Abs.TypeArray _ prim) n l k (w,j)      = ((Abs.TypeArray (TAC [] []) (sel1 (genTacTipo prim n l k (w,j)))),n,k)

{-

var x:[1..2]int$=[1,2];
var y:int;
y=$x[1];
y=$x[2];
var z:[1..2]int$$=[x[1],x[2]];
y = $$z[1];
y = $$z[2];

var x:([1..2]int)$;//=[1,2];
var y:([]int)$;//=[1,2];
var z:int;
z=$x[1+1];
z=$x[2];

var x:([1..2]int)$$;
var z:int;
z=$ $ x[1];

var x : ([1 .. 2] int) $;
var z : int;
z = $ x [1];

-}

genTacDefault :: Abs.DEFAULT TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.DEFAULT TAC,Prelude.Integer,Prelude.Integer,Address)
genTacDefault (Abs.ExpressionIntegerD res value@(Abs.Integer val resi))       n l k (w,j) = (Abs.ExpressionIntegerD (TAC [] []) (Abs.Integer val   (TAC [] [])),n,k, AddrInt val)
genTacDefault (Abs.ExpressionBooleanD res value@(Abs.Boolean_true resi))      n l k (w,j) = (Abs.ExpressionBooleanD (TAC [] []) (Abs.Boolean_true  (TAC [] [])),n,k, AddrBool True)
genTacDefault (Abs.ExpressionBooleanD res value@(Abs.Boolean_false resi))     n l k (w,j) = (Abs.ExpressionBooleanD (TAC [] []) (Abs.Boolean_false (TAC [] [])),n,k, AddrBool False)
genTacDefault (Abs.ExpressionBooleanD res value@(Abs.Boolean_True resi))      n l k (w,j) = (Abs.ExpressionBooleanD (TAC [] []) (Abs.Boolean_True  (TAC [] [])),n,k, AddrBool True)
genTacDefault (Abs.ExpressionBooleanD res value@(Abs.Boolean_False resi))     n l k (w,j) = (Abs.ExpressionBooleanD (TAC [] []) (Abs.Boolean_False (TAC [] [])),n,k, AddrBool False)
genTacDefault (Abs.ExpressionCharD res value@(Abs.Char val resi))             n l k (w,j) = (Abs.ExpressionCharD    (TAC [] []) (Abs.Char val      (TAC [] [])),n,k, AddrChar val)
genTacDefault (Abs.ExpressionStringD res value@(Abs.String val resi))         n l k (w,j) = (Abs.ExpressionStringD  (TAC [] []) (Abs.String val    (TAC [] [])),n,k, AddrString val)
genTacDefault (Abs.ExpressionRealD res value@(Abs.Real val resi))             n l k (w,j) = (Abs.ExpressionRealD    (TAC [] []) (Abs.Real val      (TAC [] [])),n,k, AddrReal val)
genTacDefault (Abs.ExpressionBracketD res exp)                                n l k (w,j) = let exprTac = genTacExpression exp n l k (w,j) "" in (Abs.ExpressionBracketD (expression_content (sel1 exprTac)) (sel1 exprTac),(sel2 exprTac),(sel3 exprTac), (sel4 exprTac))
genTacDefault (Abs.ExpressionCastD res def tipo)                              n l k (w,j) = let defTac = genTacDefault def n l k (w,j) in
                                                                                                    let tipoTac = genTacTipo tipo (sel2 defTac) l (sel3 defTac) (w,j) in
                                                                                                        let temp = newTemp (sel2 tipoTac) in
                                                                                                            let fromType = getTypeFromDefault def in
                                                                                                                let toType = TacGen.getTypeFromPrimitive tipo in
                                                                                                                    ((Abs.ExpressionCastD (TAC ((code (default_content (sel1 defTac))) ++ -- tac of default (left part)
                                                                                                                                                [TacCastConversion temp (sel4 defTac) fromType toType]) -- Tac instruction for conversion (cast)
                                                                                                                                                []) (sel1 defTac) (sel1 tipoTac)),(sel2 tipoTac)+1,(sel3 tipoTac),temp) 
genTacDefault (Abs.ExpressionUnaryD res@(TResult env ty pos) unary def)       n l k (w,j) = let defTac = genTacDefault def (n+1) l k (w,j) in 
                                                                                                let temp = newTemp n in
                                                                                                    case unary of 
                                                                                                        Abs.UnaryOperationPositive _ -> (Abs.ExpressionUnaryD (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Pos (sel4 defTac) ty] [])) (Abs.UnaryOperationPositive (TAC [] [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp) 
                                                                                                        Abs.UnaryOperationNegative _ -> (Abs.ExpressionUnaryD (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Neg (sel4 defTac) ty] [])) (Abs.UnaryOperationNegative (TAC [] [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp) 
                                                                                                        Abs.UnaryOperationNot      _ -> (Abs.ExpressionUnaryD (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Not (sel4 defTac) ty] [])) (Abs.UnaryOperationNot (TAC [] [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp) 
                                                                                                        Abs.UnaryOperationPointer  _ -> (Abs.ExpressionUnaryD (merge2Tacs (default_content (sel1 defTac)) (TAC [TacAssignUnaryOp temp Point (sel4 defTac) ty] [])) (Abs.UnaryOperationPointer (TAC [] [])) (sel1 defTac),(sel2 defTac),(sel3 defTac),temp)
genTacDefault (Abs.ExpressionIdentD res@(TResult env _ _) ident@(Abs.Ident id resI) index)  n l k (w,j) = case Data.Map.lookup id env of
                                                                                                                    Just (entry:entries) -> case findEntryOfType (entry:entries) "var" of
                                                                                                                                              (x@(Variable _ posv _ _ _):xs) -> case index of
                                                                                                                                                                                    (Abs.ArrayIndexElementEmpty _) -> ((Abs.ExpressionIdentD (TAC [] []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElementEmpty (TAC [] []))),n,k,buildIDAddr posv id)
                                                                                                                                                                                    (Abs.ArrayIndexElement _ typeindex) -> case findArray (x:xs) of
                                                                                                                                                                                                                        [Variable ty@(Array t _) posv _ _ s] -> let typeIndexTac = genTacTypeIndex typeindex n l k (w,j) 0 [] (-1) in
                                                                                                                                                                                                                                                                    let dim = generateDimForArrayFromType ty in
                                                                                                                                                                                                                                                                        let leftAddr = buildIDAddr posv id in
                                                                                                                                                                                                                                                                            if (isIntegerAddress (sel4 typeIndexTac)) 
                                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                                    let posArr = buildPosArray (sel4 typeIndexTac) s dim in
                                                                                                                                                                                                                                                                                        let leftAddrArray = buildArrayId leftAddr posArr 0 in
                                                                                                                                                                                                                                                                                            let comment = buildArrayComments (sel4 typeIndexTac) s dim t in
                                                                                                                                                                                                                                                                                                let temp = newTemp (sel2 typeIndexTac) in
                                                                                                                                                                                                                                                                                                    ((Abs.ExpressionIdentD (TAC ([TacAssignNullOp temp leftAddrArray t]++comment) []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElement (TAC [] []) (sel1 typeIndexTac))),(sel2 typeIndexTac)+1,(sel3 typeIndexTac),temp)
                                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                                    let typeIndexTac = genTacTypeIndex typeindex n l k (w,j) dim s (-1) in
                                                                                                                                                                                                                                                                                        let posArr = buildPosArrayNoInteger (sel4 typeIndexTac) s dim (sel2 typeIndexTac) in
                                                                                                                                                                                                                                                                                            let leftAddrArray = buildArrayIdNoInteger leftAddr (newTemp ((sel2 typeIndexTac)-1)) in
                                                                                                                                                                                                                                                                                                let temp = newTemp (sel2 typeIndexTac) in
                                                                                                                                                                                                                                                                                                    ((Abs.ExpressionIdentD (TAC ((code (typeindex_content (sel1 typeIndexTac)))++[TacAssignNullOp temp leftAddrArray t]) []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElement (TAC [] []) (sel1 typeIndexTac))),(sel2 typeIndexTac)+1,(sel3 typeIndexTac),temp)                                                                         
                                                                                                                                                                                                                        [Variable ty@(Pointer t _) posv _ _ s] -> let realT = getRealTacType t in
                                                                                                                                                                                                                                                                    let typeIndexTac = genTacTypeIndex typeindex n l k (w,j) 0 [] (-1) in
                                                                                                                                                                                                                                                                        let dim = generateDimForArrayFromType t in
                                                                                                                                                                                                                                                                            let leftAddr = buildIDAddr posv id in
                                                                                                                                                                                                                                                                                if (isIntegerAddress (sel4 typeIndexTac)) 
                                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                                        let comment = buildArrayComments (sel4 typeIndexTac) s dim t in
                                                                                                                                                                                                                                                                                            let temp = newTemp (sel2 typeIndexTac) in
                                                                                                                                                                                                                                                                                                ((Abs.ExpressionIdentD (TAC ([TacAssignBinaryOp temp AddrIntAdd leftAddr (AddrInt (buildPosArrayC (sel4 typeIndexTac) s dim)) (Pointer t 0)]++comment) []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElement (TAC [] []) (sel1 typeIndexTac))),(sel2 typeIndexTac)+1,(sel3 typeIndexTac),temp)
                                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                                        let typeIndexTac = genTacTypeIndex typeindex n l k (w,j) dim s (-1) in
                                                                                                                                                                                                                                                                                            let temp = newTemp (sel2 typeIndexTac) in
                                                                                                                                                                                                                                                                                                ((Abs.ExpressionIdentD (TAC ((code (typeindex_content (sel1 typeIndexTac)))++[TacAssignBinaryOp temp AddrIntAdd leftAddr (head (sel4 typeIndexTac)) (Pointer t 0)]) []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElement (TAC [] []) (sel1 typeIndexTac))),(sel2 typeIndexTac)+1,(sel3 typeIndexTac),temp)
                                                                                                                                                                                    (Abs.ArrayIndexElements _ arrayIndex typeindex ) -> case findArray (x:xs) of
                                                                                                                                                                                                                                    [Variable ty@(Array t _) posv _ _ s] -> let realT = getRealTypeFromArray t in
                                                                                                                                                                                                                                                                                let typeIndexTac = genTacTypeIndex typeindex n l k (w,j) 0 [] (-1) in
                                                                                                                                                                                                                                                                                    let arrayIndexTac = genTacArrayIndexElements arrayIndex (sel2 typeIndexTac) l (sel3 typeIndexTac) (w,j) 0 [] (-1) in
                                                                                                                                                                                                                                                                                        let dim = generateDimForArrayFromType ty in
                                                                                                                                                                                                                                                                                            let leftAddr = buildIDAddr posv id in
                                                                                                                                                                                                                                                                                                if (isIntegerAddress ((sel4 arrayIndexTac)++(sel4 typeIndexTac))) 
                                                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                                                        let posArr = buildPosArray ((sel4 arrayIndexTac)++(sel4 typeIndexTac)) s dim in
                                                                                                                                                                                                                                                                                                            let leftAddrArray = buildArrayId leftAddr posArr 0 in
                                                                                                                                                                                                                                                                                                                let comment = buildArrayComments ((sel4 arrayIndexTac)++(sel4 typeIndexTac)) s dim realT in
                                                                                                                                                                                                                                                                                                                    let temp = newTemp (sel2 arrayIndexTac) in
                                                                                                                                                                                                                                                                                                                        ((Abs.ExpressionIdentD (TAC ([TacAssignNullOp temp leftAddrArray realT]++comment) []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElements (TAC [] [])  (sel1 arrayIndexTac) (sel1 typeIndexTac))),(sel2 arrayIndexTac)+1,(sel3 arrayIndexTac),temp)
                                                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                                                        let arrayIndexTac = genTacArrayIndexElements (Abs.ArrayIndexElementsMultiple res arrayIndex typeindex) n l k (w,j) dim s (-1) in
                                                                                                                                                                                                                                                                                                            let posArr = buildPosArrayNoInteger (sel4 arrayIndexTac) s dim (sel2 arrayIndexTac) in
                                                                                                                                                                                                                                                                                                                let leftAddrArray = buildArrayIdNoInteger leftAddr (newTemp ((sel2 arrayIndexTac)-1)) in
                                                                                                                                                                                                                                                                                                                        let temp = newTemp (sel2 arrayIndexTac) in
                                                                                                                                                                                                                                                                                                                            ((Abs.ExpressionIdentD (TAC ((code (arrayindexelements_content (sel1 arrayIndexTac)))++[TacAssignNullOp temp leftAddrArray realT]) []) (Abs.Ident id (TAC [] [])) (Abs.ArrayIndexElements (TAC [] [])  (sel1 arrayIndexTac) (sel1 typeIndexTac))),(sel2 arrayIndexTac)+1,(sel3 arrayIndexTac),temp)
genTacDefault (Abs.ExpressionCallD res@(TResult env _ _) ident@(Abs.Ident id resI) exps)    n l k (w,j) = case Data.Map.lookup id env of
                                                                                                        Just (entry:entries) -> case findEntryOfType (entry:entries) "func" of
                                                                                                            ((Function ty pos _ _):xs) -> let funcReturn = newTemp n in
                                                                                                                                            let funcAddr = buildIDAddr pos id in
                                                                                                                                            case exps of
                                                                                                                                                (Abs.Expressions rese expr exprs) -> let expression = genTacExpression expr (n+1) l k (w,j) "" in
                                                                                                                                                                                      let expressions = genTacExpressions exprs (sel2 expression) l (sel3 expression) (w,j) in
                                                                                                                                                                                          ((Abs.ExpressionCallD (TAC ((code (expression_content (sel1 expression))) ++       -- evaluation of the first param value
                                                                                                                                                                                                                     [TacParam (sel4 expression) (getTypeFromExpr expr)] ++  -- first param tac
                                                                                                                                                                                                                     (code (expressions_content (sel1 expressions))) ++     -- tac of others param
                                                                                                                                                                                                                     [TacAssignNullOp funcReturn funcAddr ty])              -- call tac
                                                                                                                                                                                                                     []) (Abs.Ident id (TAC [][])) (Abs.Expressions (TAC [][]) (sel1 expression) (sel1 expressions))),(sel2 expressions),(sel3 expressions),funcReturn) 
                                                                                                                                                (Abs.Expression rese expr)        -> let expression = genTacExpression expr (n+1) l k (w,j) "" in
                                                                                                                                                                                          ((Abs.ExpressionCallD (TAC ((code (expression_content (sel1 expression))) ++        -- evaluation of the param value
                                                                                                                                                                                                                    [(TacParam (sel4 expression) (getTypeFromExpr expr)),    -- param tac
                                                                                                                                                                                                                     (TacAssignNullOp funcReturn funcAddr ty)])              -- call tac
                                                                                                                                                                                                                     []) (Abs.Ident id (TAC [][])) (Abs.Expression (TAC [][]) (sel1 expression))),(sel2 expression),(sel3 expression),funcReturn) 
                                                                                                                                                (Abs.ExpressionEmpty rese)        -> ((Abs.ExpressionCallD (TAC [TacAssignNullOp funcReturn funcAddr ty]   -- call tac
                                                                                                                                                                                                                 []) (Abs.Ident id (TAC [][])) (Abs.ExpressionEmpty (TAC [][]))),n+1,k,funcReturn)



genTacIdentifierList :: Abs.IDENTLIST TCheckResult -> Prelude.Integer -> Label -> Prelude.Integer -> (Label,Label) -> (Abs.IDENTLIST TAC,Prelude.Integer,Prelude.Integer,[Address])
genTacIdentifierList (Abs.IdentifierSingle res ident@(Abs.Ident id resi@(TResult _ _ pos))) n l k (w,j) = (Abs.IdentifierSingle (TAC [] []) (Abs.Ident id (TAC [] [])),n,k,[buildIDAddr pos id])
genTacIdentifierList (Abs.IdentifierList res ident@(Abs.Ident id resi@(TResult _ _ pos)) idlist) n l k (w,j) = let idlistTac = (genTacIdentifierList idlist n l k (w,j)) in
                                                                                                                        let idlistAddr = sel4 idlistTac in
                                                                                                                            (Abs.IdentifierList (TAC [] []) (Abs.Ident id (TAC [] [])) (sel1 idlistTac),(sel2 idlistTac),(sel3 idlistTac),[buildIDAddr pos id] ++ idlistAddr)
