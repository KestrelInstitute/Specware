
C qualifying spec {

  sort CSpec =
    {
     name                  : String,
     includes              : Strings,
     defines	           : Strings,
     constDefns            : VarDefns,      % constant expressions defined by #define's
     vars                  : VarDecls,
     fns                   : FnDecls,
     axioms                : Exps,
     structUnionTypeDefns  : StructUnionTypeDefns,
     varDefns              : VarDefns,      % constant expressions computable at compile-time
     fnDefns               : FnDefns
    }

  sort StructUnionTypeDefn = | Struct   StructDefn
                             | Union    UnionDefn
                             | TypeDefn TypeDefn

  sort StructUnionTypeDefns = List StructUnionTypeDefn

  sort VarDecl    = String * Type
  sort VarDecl1   = String * Type * Option(Exp)
  sort FnDecl     = String * Types * Type
  sort TypeDefn   = String * Type
  sort StructDefn = String * VarDecls
  sort UnionDefn  = String * VarDecls
  sort VarDefn    = String * Type * Exp
  sort FnDefn     = String * VarDecls * Type * Stmt


  sort Block      = VarDecls1 * Stmts

  sort Type =
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
    | Ptr      Type
    | Array    Type
    | ArrayWithSize  (String (*name of constant*) * Type)
    | Fn       Types * Type
    | ConstField

  sort Stmt =
    | Exp     Exp
    | Block   Block
    | If      Exp * Stmt * Stmt
    | Return  Exp
    | ReturnVoid
    | Break
    | While   Exp * Stmt
    | Label   String
    | Goto    String
    | IfThen  Exp * Stmt
    | Switch  Exp * Stmts
    | Case    Val
    | Nop


  sort Exp =
    | Const       Val
    | Fn          FnDecl
    | Var         VarDecl
    | Apply       Exp * Exps
    | Unary       UnaryOp * Exp
    | Binary      BinaryOp * Exp * Exp
    | Cast        Type * Exp
    | StructRef   Exp * String
    | UnionRef    Exp * String
    | ArrayRef    Exp * Exp
    | IfExp       Exp * Exp * Exp 
    | Comma       Exp * Exp
    | SizeOfType  Type
    | SizeOfExp   Exp
    | Field       Exps

  sort Val =
    | Char        Char
    | Int         Boolean * Nat
    | Float       String
    | String      String

  sort UnaryOp =
    | Contents
    | Address
    | Negate
    | BitNot
    | LogNot
    | PreInc | PreDec
    | PostInc | PostDec

  sort BinaryOp =
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

  sort Strings     = List (String)
  sort VarDecls    = List (VarDecl)
  sort VarDecls1   = List (VarDecl1)
  sort FnDecls     = List (FnDecl)
  sort TypeDefns   = List (TypeDefn)
  sort StructDefns = List (StructDefn)
  sort UnionDefns  = List (UnionDefn)
  sort FnDefns     = List (FnDefn)
  sort VarDefns    = List (VarDefn)
  sort Types       = List (Type)
  sort Exps        = List (Exp)
  sort Stmts       = List (Stmt)

}

