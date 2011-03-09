
C qualifying spec {

  type C_Spec =
    {
     name                  : String,
     includes              : Strings,
     defines	           : Strings,
     constDefns            : C_VarDefns,      % constant expressions defined by #define's
     vars                  : C_VarDecls,
     fns                   : C_FnDecls,
     axioms                : C_Exps,
     structUnionTypeDefns  : C_StructUnionTypeDefns,
     varDefns              : C_VarDefns,      % constant expressions computable at compile-time
     fnDefns               : C_FnDefns
    }

  type C_StructUnionTypeDefn = | C_Struct   C_StructDefn
                               | C_Union    C_UnionDefn
                               | C_TypeDefn C_TypeDefn

  type C_StructUnionTypeDefns = List C_StructUnionTypeDefn

  type C_VarDecl    = String * C_Type
  type C_VarDecl1   = String * C_Type * Option C_Exp
  type C_FnDecl     = String * C_Types * C_Type
  type C_TypeDefn   = String * C_Type
  type C_StructDefn = String * C_VarDecls
  type C_UnionDefn  = String * C_VarDecls
  type C_VarDefn    = String * C_Type * C_Exp
  type C_FnDefn     = String * C_VarDecls * C_Type * C_Stmt


  type C_Block      = C_VarDecls1 * C_Stmts

  type C_Type =
    | C_Void
    | C_Char
    | C_Short
    | C_Int
    | C_Long
    | C_UnsignedChar
    | C_UnsignedShort
    | C_UnsignedInt
    | C_UnsignedLong
    | C_Float
    | C_Double
    | C_LongDouble
    | C_Base           String
    | C_Struct         String
    | C_Union          String
    | C_Ptr            C_Type
    | C_Array          C_Type
    | C_ArrayWithSize  String (*name of constant*) * C_Type
    | C_Fn             C_Types * C_Type
    | C_ConstField

  type C_Stmt =
    | C_Exp     C_Exp
    | C_Block   C_Block
    | C_If      C_Exp * C_Stmt * C_Stmt
    | C_Return  C_Exp
    | C_ReturnVoid
    | C_Break
    | C_While   C_Exp * C_Stmt
    | C_Label   String
    | C_Goto    String
    | C_IfThen  C_Exp * C_Stmt
    | C_Switch  C_Exp * C_Stmts
    | C_Case    C_Const
    | C_Nop


  type C_Exp =
    | C_Const       C_Const
    | C_Fn          C_FnDecl
    | C_Var         C_VarDecl
    | C_Apply       C_Exp * C_Exps
    | C_Unary       C_UnaryOp * C_Exp
    | C_Binary      C_BinaryOp * C_Exp * C_Exp
    | C_Cast        C_Type * C_Exp
    | C_StructRef   C_Exp * String
    | C_UnionRef    C_Exp * String
    | C_ArrayRef    C_Exp * C_Exp
    | C_IfExp       C_Exp * C_Exp * C_Exp 
    | C_Comma       C_Exp * C_Exp
    | C_SizeOfType  C_Type
    | C_SizeOfExp   C_Exp
    | C_Field       C_Exps

  type C_Const =
    | C_Char   Char
    | C_Int    Boolean * Nat
    | C_Float  String
    | C_String String

  type C_UnaryOp =
    | C_Contents
    | C_Address
    | C_Negate
    | C_BitNot
    | C_LogNot
    | C_PreInc  | C_PreDec
    | C_PostInc | C_PostDec

  type C_BinaryOp =
    | C_Set
    | C_Add | C_Sub | C_Mul | C_Div | C_Mod
    | C_BitAnd | C_BitOr | C_BitXor
    | C_ShiftLeft | C_ShiftRight
    | C_SetAdd | C_SetSub | C_SetMul | C_SetDiv | C_SetMod
    | C_SetBitAnd | C_SetBitOr | C_SetBitXor
    | C_SetShiftLeft | C_SetShiftRight
    | C_LogAnd | C_LogOr
    | C_Eq  | C_NotEq
    | C_Lt | C_Gt | C_Le | C_Ge

  type Strings       = List String
  type C_VarDecls    = List C_VarDecl
  type C_VarDecls1   = List C_VarDecl1
  type C_FnDecls     = List C_FnDecl
  type C_TypeDefns   = List C_TypeDefn
  type C_StructDefns = List C_StructDefn
  type C_UnionDefns  = List C_UnionDefn
  type C_FnDefns     = List C_FnDefn
  type C_VarDefns    = List C_VarDefn
  type C_Types       = List C_Type
  type C_Exps        = List C_Exp
  type C_Stmts       = List C_Stmt

}

