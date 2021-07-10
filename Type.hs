module Type where

-- Data definitions for Basic and Composed types

data BasicType
    = Type_Integer
    | Type_Boolean
    | Type_Char
    | Type_String
    | Type_Void
    | Type_Real
    deriving (Eq, Ord, Read)

data Type
    = B_type {b_type::BasicType}
    | Array {c_type::Type}
    | Pointer {c_type::Type}
    deriving (Eq, Ord, Read)

-- Show for types

instance Show BasicType where
    show b_type = case b_type of
        Type_Integer -> "int"
        Type_Boolean -> "bool"
        Type_Char -> "char"
        Type_String -> "string"
        Type_Void -> "void"
        Type_Real -> "real"

instance Show Type where
    show tb_type = case tb_type of
        B_type b_type -> show b_type
        Array c_type -> "array[" ++ show c_type ++"]"
        Pointer c_type -> "pointer:" ++ show c_type        