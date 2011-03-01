
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

  type CStructUnionTypeDefn = | CStruct   CStructDefn
                              | CUnion    CUnionDefn
                              | CTypeDefn CTypeDefn

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
    | CVoid
    | CChar
    | CShort
    | CInt
    | CLong
    | CUnsignedChar
    | CUnsignedShort
    | CUnsignedInt
    | CUnsignedLong
    | CFloat
    | CDouble
    | CLongDouble
    | CBase     String
    | CStruct   String
    | CUnion    String
    | CPtr      CType
    | CArray    CType
    | CArrayWithSize  (String (*name of constant*) * CType)
    | CFn       CTypes * CType
    | CConstField

  type CStmt =
    | CExp     CExp
    | CBlock   CBlock
    | CIf      CExp * CStmt * CStmt
    | CReturn  CExp
    | CReturnVoid
    | CBreak
    | CWhile   CExp * CStmt
    | CLabel   String
    | CGoto    String
    | CIfThen  CExp * CStmt
    | CSwitch  CExp * CStmts
    | CCase    CVal
    | CNop


  type CExp =
    | CConst       CVal
    | CFn          CFnDecl
    | CVar         CVarDecl
    | CApply       CExp * CExps
    | CUnary       CUnaryOp * CExp
    | CBinary      CBinaryOp * CExp * CExp
    | CCast        CType * CExp
    | CStructRef   CExp * String
    | CUnionRef    CExp * String
    | CArrayRef    CExp * CExp
    | CIfExp       CExp * CExp * CExp 
    | CComma       CExp * CExp
    | CSizeOfType  CType
    | CSizeOfExp   CExp
    | CField       CExps

  type CVal =
    | CChar        Char
    | CInt         Boolean * Nat
    | CFloat       String
    | CString      String

  type CUnaryOp =
    | CContents
    | CAddress
    | CNegate
    | CBitNot
    | CLogNot
    | CPreInc  | CPreDec
    | CPostInc | CPostDec

  type CBinaryOp =
    | CSet
    | CAdd | CSub | CMul | CDiv | CMod
    | CBitAnd | CBitOr | CBitXor
    | CShiftLeft | CShiftRight
    | CSetAdd | CSetSub | CSetMul | CSetDiv | CSetMod
    | CSetBitAnd | CSetBitOr | CSetBitXor
    | CSetShiftLeft | CSetShiftRight
    | CLogAnd | CLogOr
    | CEq  | CNotEq
    | CLt | CGt | CLe | CGe

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

