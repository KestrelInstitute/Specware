
C qualifying spec {

  type CSpec =
    {
     name                  : String,
     includes              : Strings,
     defines	           : Strings,
     constDefns            : CVarDefns,      % constant expressions defined by #define's
     vars                  : CVarDecls,
     fns                   : CFnDecls,
     axioms                : CExps,
     structUnionTypeDefns  : CStructUnionTypeDefns,
     varDefns              : CVarDefns,      % constant expressions computable at compile-time
     fnDefns               : CFnDefns
    }

  type CStructUnionTypeDefn = | Struct   CStructDefn
                              | Union    CUnionDefn
                              | TypeDefn CTypeDefn

  type CStructUnionTypeDefns = List CStructUnionTypeDefn

  type CVarDecl    = String * CType
  type CVarDecl1   = String * CType * Option(CExp)
  type CFnDecl     = String * CTypes * CType
  type CTypeDefn   = String * CType
  type CStructDefn = String * CVarDecls
  type CUnionDefn  = String * CVarDecls
  type CVarDefn    = String * CType * CExp
  type CFnDefn     = String * CVarDecls * CType * CStmt


  type CBlock      = CVarDecls1 * CStmts

  type CType =
    | Void
    | Char
    | Short
    | Int
    | Long
    | UnsignedChar
    | UnsignedShort
    | UnsignedInt
    | UnsignedLong
    | Float
    | Double
    | LongDouble
    | Base     String
    | Struct   String
    | Union    String
    | Ptr      CType
    | Array    CType
    | ArrayWithSize  (String (*name of constant*) * CType)
    | Fn       CTypes * CType
    | ConstField

  type CStmt =
    | Exp     CExp
    | Block   CBlock
    | If      CExp * CStmt * CStmt
    | Return  CExp
    | ReturnVoid
    | Break
    | While   CExp * CStmt
    | Label   String
    | Goto    String
    | IfThen  CExp * CStmt
    | Switch  CExp * CStmts
    | Case    CVal
    | Nop


  type CExp =
    | Const       CVal
    | Fn          CFnDecl
    | Var         CVarDecl
    | Apply       CExp * CExps
    | Unary       CUnaryOp * CExp
    | Binary      CBinaryOp * CExp * CExp
    | Cast        CType * CExp
    | StructRef   CExp * String
    | UnionRef    CExp * String
    | ArrayRef    CExp * CExp
    | IfExp       CExp * CExp * CExp 
    | Comma       CExp * CExp
    | SizeOfType  CType
    | SizeOfExp   CExp
    | Field       CExps

  type CVal =
    | Char        Char
    | Int         Boolean * Nat
    | Float       String
    | String      String

  type CUnaryOp =
    | Contents
    | Address
    | Negate
    | BitNot
    | LogNot
    | PreInc | PreDec
    | PostInc | PostDec

  type CBinaryOp =
    | Set
    | Add | Sub | Mul | Div | Mod
    | BitAnd | BitOr | BitXor
    | ShiftLeft | ShiftRight
    | SetAdd | SetSub | SetMul | SetDiv | SetMod
    | SetBitAnd | SetBitOr | SetBitXor
    | SetShiftLeft | SetShiftRight
    | LogAnd | LogOr
    | Eq  | NotEq
    | Lt | Gt | Le | Ge

  type Strings      = List String
  type CVarDecls    = List CVarDecl
  type CVarDecls1   = List CVarDecl1
  type CFnDecls     = List CFnDecl
  type CTypeDefns   = List CTypeDefn
  type CStructDefns = List CStructDefn
  type CUnionDefns  = List CUnionDefn
  type CFnDefns     = List CFnDefn
  type CVarDefns    = List CVarDefn
  type CTypes       = List CType
  type CExps        = List CExp
  type CStmts       = List CStmt

}

