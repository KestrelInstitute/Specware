(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

C qualifying spec
{

  import /Library/IO/Unicode/UnicodeSig  % for UString, UChar

  type C_Spec =
    {
     %% these are used for both .c and .h files:
     name                 : String,
     headers              : Strings,         % e.g. copyright notices
     trailers             : Strings,

     %% these go into .h file:
     hincludes            : Strings,         % the .c file will always include the .h file
     hverbatims           : Strings,
     defines	          : C_Defines,
     constDefns           : C_VarDefns,      % constant expressions defined by #define's
     vars                 : C_VarDecls,
     fns                  : C_FnDecls,
     structUnionTypeDefns : C_StructUnionTypeDefns,

     %% these go into .c file:
     cincludes            : Strings,         
     cverbatims           : Strings,
     axioms               : C_Exps,          % ??
     varDefns             : C_VarDefns,      % constant expressions computable at compile-time
     fnDefns              : C_FnDefns
    }

  type C_StructUnionTypeDefns = List C_StructUnionTypeDefn

  type C_Define     = String * String
  type C_VarDecl    = String * C_Type
  type C_VarDecl1   = String * C_Type * Option C_Exp
  type C_FnDecl     = String * C_Types * C_Type

  type C_TypeDefn   = String * C_Type
  type C_StructDefn = String * C_VarDecls
  type C_UnionDefn  = String * C_VarDecls
  type C_EnumDefn   = String * Strings

  type C_StructUnionTypeDefn = | Type    C_TypeDefn
                               | Struct  C_StructDefn
                               | Union   C_UnionDefn
                               | Enum    C_EnumDefn


  type C_VarDefn    = String * C_Type * C_Exp
  type C_FnDefn     = String * C_VarDecls * C_Type * C_Stmt

  type C_Block      = C_VarDecls1 * C_Stmts

  type C_NameSpace  = | Type | Struct | Enum | Union

  type C_Type =
    | C_Void
    | C_Char                   % 'char', logically distinct from 'signed char' and 'unsigned char', 
                               % but could be the same as either, depending on version of C,
                               % hence could be same as C_Int8 or C_UInt8, depending on version

    %% These integer types are unambiguous, but may correspond to a variety of types
    %% in different versions of C:
    | C_Int8                   % same as 'signed char'                                  or 'char'
    | C_Int16                  % same as 'signed short int'   or 'signed int'           or 'int'
    | C_Int32                  % same as 'signed int'         or 'signed long int'      or 'int'
    | C_Int64                  % same as 'signed long int'    or 'signed long long int'
    | C_IntInf                 % unbounded ints, no simple representation

    | C_UInt8                  % same as 'unsigned char'      or 'char'
    | C_UInt16                 % same as 'unsigned short int' or 'unsigned int'         
    | C_UInt32                 % same as 'unsigned int'       or 'unsigned long int'
    | C_UInt64                 % same as 'unsigned long int'  or 'unsigned long long int'
    | C_UIntInf                % unbounded unsigned ints, no simple representation

    | C_Size                   % used as coercion from ptrs, length of arrays, etc. -- machine dependent

    | C_Float                  % 'float'
    | C_Double                 % ''double'
    | C_LongDouble             % 'long double'

    | C_WChar                  % wide char: L'xx'
    | C_UTF8                   % unicode - TODO: obscure rules
    | C_UTF16                  % unicode - TODO: obscure rules
    | C_UTF32                  % unicode - TODO: obscure rules

    | C_Base           String  * C_NameSpace

    | C_Ptr            C_Type             % '*void', '*int*,   etc.
    | C_Array          C_Type             % 'int[]', 'char[]', etc.
    | C_ArrayWithSize  C_Exps  * C_Type   % 'int[10][20]',     etc.
    | C_Fn             C_Types * C_Type   % '(int, int) : int' etc.

    | C_ConstField
    | C_Problem        String

  %% types commonly used when building signatures:
  %% TODO:  we abuse the naming conventions for op's to make these 
  %%        look like constructors (good idea or bad?)
  op C_VoidPtr  : C_Type = C_Ptr C_Void  
  op C_String   : C_Type = C_Ptr C_Char
  op C_Selector : C_Type = C_Int16

  type C_Stmt =
    | C_Exp         C_Exp
    | C_Block       C_Block
    | C_If          C_Exp * C_Stmt * C_Stmt
    | C_Return      C_Exp
    | C_ReturnVoid
    | C_Break
    | C_While       C_Exp * C_Stmt
    | C_Label       String
    | C_Goto        String
    | C_IfThen      C_Exp * C_Stmt
    | C_Switch      C_Exp * C_Stmts
    | C_Case        C_Const
    | C_Nop


  type C_EnumName    = String
  type C_FieldName   = String
  type C_VariantName = String

  type C_Exp =
    | C_Const       C_Const                      % 3, 3.5, 'A', "abc", L"abc"
    | C_Fn          C_FnDecl                     % 'int foo (int, int)'
    | C_Var         C_VarDecl                    % 'int x'
    | C_Apply       C_Exp * C_Exps               % f(x,y,z)
    | C_Unary       C_UnaryOp * C_Exp            % -x
    | C_Binary      C_BinaryOp * C_Exp * C_Exp   % x+y
    | C_Cast        C_Type * C_Exp               % (int)x
    | C_EnumRef     C_EnumName                   % foo
    | C_StructRef   C_Exp * C_FieldName          % x.field
    | C_UnionRef    C_Exp * C_VariantName        % x.variant
    | C_ArrayRef    C_Exp * C_Exp                % x[y]
    | C_IfExp       C_Exp * C_Exp * C_Exp        % if x then y else z
    | C_Comma       C_Exp * C_Exp                % (x; y)
    | C_SizeOfType  C_Type                       % sizeof(int)
    | C_SizeOfExp   C_Exp                        % sizeof(x)
    | C_Field       C_Exps                       % TODO: ?
    | C_Ignore                                   % similar to None, to avoid need for Option C_Exp
    | C_Problem     String

  type C_Const =
    | C_Char   Char                                   % 'A'
    | C_WChar  UChar                                  % TODO: example L'...' 
    | C_Int    Bool * Nat                             % 3, -3   [sign? and magnitude]
    | C_Str    String                                 % "abc"
    | C_WStr   UString                                % L"abc"  [unicode]
    | C_Macro  String                                 % TODO: hack to accomodate macros used as constants
    | C_Float  Bool * Nat * Nat * Option (Bool * Nat) % -3.7, 2.48e-10, etc.

  type C_UnaryOp =
    | C_Contents       % *x
    | C_Address        % &x
    | C_Negate         % -x
    | C_BitNot         % ~x
    | C_LogNot         % !x
    | C_PreInc         % ++x
    | C_PreDec         % --x
    | C_PostInc        % x++
    | C_PostDec        % x--

  type C_BinaryOp =
    | C_Set            %  x = y
    | C_Add            %  x + y
    | C_Sub            %  x - y
    | C_Mul            %  x * y
    | C_Div            %  x / y
    | C_Mod            %  x % y
    | C_BitAnd         %  x & y
    | C_BitOr          %  x | y
    | C_BitXor         %  x xor y
    | C_ShiftLeft      %  x << y
    | C_ShiftRight     %  x >> y

    | C_SetAdd         %  x += y
    | C_SetSub         %  x -= y
    | C_SetMul         %  x *= y
    | C_SetDiv         %  x /= y
    | C_SetMod         %  x %= y
    | C_SetBitAnd      %  x &= y
    | C_SetBitOr       %  x |= y
    | C_SetBitXor      %  x ^= y
    | C_SetShiftLeft   %  x <<= y
    | C_SetShiftRight  %  x >>= y

    | C_LogAnd         %  x && y
    | C_LogOr          %  x || y
    | C_Eq             %  x == y
    | C_NotEq          %  x != y
    | C_Lt             %  x <  y
    | C_Gt             %  x >  y
    | C_Le             %  x <= y
    | C_Ge             %  x >= y


  type Strings       = List String
  type C_Defines     = List C_Define
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
