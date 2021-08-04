-- Progetto LC Mansi Cagnoni UNIUD
module AbsTac where

import AbsProgettoPar as Abs
import Type

data TAC = TAC {content::[TACEntry]}
    deriving (Eq, Ord, Show, Read)

data TACEntry
    = TacAssignUnaryOp  {unaryOp  :: TacUnaryOp} --{getValue:: Value, unaryOp  :: TacUnaryOp,  first::Value, second::Value, assignType::Type}
    | TacAssignBinaryOp {binaryOp :: TacBinaryOp} --{getValue:: Value, binaryOp :: TacBinaryOp, first::Value, second::Value, assignType::Type}
    | TacAssignRelOp    {getValue:: Address, relOp :: TacRelOp, first::Address, second :: Address, assignType::Type}
    | TacProcCall
    | TacFuncCall
    | TacJump
    | TacCopy
    {- todo -}
    | TacLabel          Label
    | TacComment        Prelude.String  -- for comments on TAC print
    | TacError          Prelude.String  -- array index out of bounds and function control reach
    | ExitTac           -- last tac entry (end of generation)
  deriving (Eq, Ord, Show, Read)

{-data Value a
    = IntVal {intVal::AbsProgettoPar.Integer a}
    | BoolVal {boolVal::AbsProgettoPar.Boolean a}
    | RealVal {realVal::AbsProgettoPar.Real a}
    | CharVal {charVal::AbsProgettoPar.Char a}
    | StringVal {stringVal::AbsProgettoPar.String a}
    deriving (C.Eq, C.Ord, C.Show, C.Read)-}

{- TODO: Show del tac tree -}


data TacUnaryOp     = IntCastToInt | Pos | Neg | Not | Point  
    deriving (Eq, Ord, Read)

data TacBinaryOp    = IntAdd | RealAdd | IntSub | RealSub | IntMul | RealMul | IntDiv | RealDiv | IntMod | IntPow | RealPow 
    deriving (Eq, Ord, Read)
                    
data TacRelOp       = EqInt | EqReal | EqString | EqChar | EqBool
                    | NeqInt | NeqReal | NeqString | NeqChar | NeqBool
                    | GeqInt | GeqReal | GeqString | GeqChar
                    | LeqInt | LeqReal | LeqString | LeqChar
                    | GtInt | GtReal | GtString | GtChar
                    | LtInt | LtReal | LtString | LtChar
                    | And | Or
    deriving (Eq, Ord, Read)

instance Show TacUnaryOp where
    show op = case op of
        IntCastToInt -> "int_to_real"
        Pos          -> "pos"
        Neg          -> "neg"
        Not          -> "not"
        Point        -> "ptr_ref"
        

instance Show TacBinaryOp where
    show op = case op of
        IntAdd  ->  "add_int"
        RealAdd ->  "add_real"
        IntSub  ->  "sub_int"
        RealSub ->  "sub_real"
        IntMul  ->  "mul_int"
        RealMul ->  "mul_real"
        IntDiv  ->  "div_int"
        RealDiv ->  "div_real"
        IntMod  ->  "mod_int"
        IntPow  ->  "pow_int"
        RealPow ->  "pow_real"        

instance Show TacRelOp where
    show op = case op of
        EqInt       -> "eq_int"
        EqReal      -> "eq_real"
        EqString    -> "eq_str"
        EqChar      -> "eq_char"
        EqBool      -> "eq_bool"
        NeqInt      -> "neq_int"
        NeqReal     -> "neq_real"
        NeqString   -> "neq_str"
        NeqChar     -> "neq_char"
        NeqBool     -> "neq_bool"
        GeqInt      -> "geq_int"
        GeqReal     -> "geq_real"
        GeqString   -> "geq_str"
        GeqChar     -> "geq_char"
        LeqInt      -> "leq_int"
        LeqReal     -> "leq_real"
        LeqString   -> "leq_str"
        LeqChar     -> "leq_char"
        GtInt       -> "gt_int"
        GtReal      -> "gt_real"
        GtString    -> "gt_str"
        GtChar      -> "gt_char"
        LtInt       -> "lt_int"
        LtReal      -> "lt_real"
        LtString    -> "lt_str"
        LtChar      -> "lt_char"
        And         -> "and"
        Or          -> "or"


data Label = Label {label_id :: Prelude.String}
    deriving (Eq, Ord, Show, Read)

data Address = AddrString {content_addr_string :: Prelude.String}
             | AddrAddress {content_addr_addr :: Prelude.String}
    deriving (Eq, Ord, Show, Read)