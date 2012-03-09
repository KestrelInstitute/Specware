PrintAsC qualifying spec 

 import PrintAsCUtils

 %% ========================================================================
 %%  CLevel controls the printing of IfThenElse as statement vs. expression.
 %% ========================================================================

 type CLevel = | Statement
               | Expression

 %% ========================================================================
 %%  We wrap parens around a sub-term if its precedence is less than the 
 %%  expected precdence,
 %% ========================================================================

 type CPrecedence = {n : Nat | 0 <= n && n <= 17}

 op CPrecedence_NO_PARENS      : CPrecedence =  0 % if this is passed to PrintTermAsC, no parens will be added
 op CPrecedence_EXPR           : CPrecedence =  1
 op CPrecedence_COND           : CPrecedence =  2
 op CPrecedence_LOR            : CPrecedence =  3
 op CPrecedence_LAND           : CPrecedence =  4
 op CPrecedence_IOR            : CPrecedence =  5
 op CPrecedence_XOR            : CPrecedence =  6
 op CPrecedence_AND            : CPrecedence =  7
 op CPrecedence_EQ             : CPrecedence =  8
 op CPrecedence_REL            : CPrecedence =  9
 op CPrecedence_SHIFT          : CPrecedence = 10
 op CPrecedence_ADD            : CPrecedence = 11
 op CPrecedence_MUL            : CPrecedence = 12
 op CPrecedence_CAST           : CPrecedence = 13
 op CPrecedence_UNARY          : CPrecedence = 14
 op CPrecedence_POST           : CPrecedence = 15
 op CPrecedence_PRIMARY        : CPrecedence = 16
 op CPrecedence_REQUIRE_PARENS : CPrecedence = 17 % if this is passed to PrintTermAsC, parens will be added
 
 %% ========================================================================
 %%  CFixity describes the pattern and keyword for a term to be applied.
 %%  If the operator is clearly illegal, we report that and return None.
 %%  If the term is complex (not a Fun) we punt and return Some Unknown.
 %% ========================================================================

 type InfixData   = {operator : String, result: CPrecedence, left:  CPrecedence, right: CPrecedence}
 type PrefixData  = {operator : String, result: CPrecedence,                     right: CPrecedence}
 type PostfixData = {operator : String, result: CPrecedence, left:  CPrecedence}

 type CFixity  = | Prefix      PrefixData
                 | Cast        String      % could use Prefix, but this is simpler
                 | Call        String      % could use Prefix, but this is simpler
                 | Postfix     PostfixData
                 | Infix       InfixData
                 | Constant    String
                 | ArrayAccess 
                 | NoOp
                 | Illegal     String

 %% ========================================================================
 %% Many Ops qualified by "C" have special meanings...
 %% ========================================================================

 op cfixityForCOp (status : CGenStatus, id : Id) : CFixity =
  %% Qualifier is "C"
  let plainCharsAreSigned? = status.plainCharsAreSigned? in
  case id of
              
    %% =========================================================================
    %% Special function used to convert conditional expressions from Int to Bool
    %% =========================================================================

    | "test" -> NoOp
      
    %% =========================================================================
    %% Constant operators
    %% =========================================================================
              
    | "sintConstant"     -> Constant ""
    | "slongConstant"    -> Constant "L"
    | "sllongConstant"   -> Constant "LL"
      
    | "uintConstant"     -> Constant "U"
    | "ulongConstant"    -> Constant "UL"
    | "ullongConstant"   -> Constant "ULL"
      
    %% =========================================================================
    %% Prefix unary operators: +, -, ~, !
    %% =========================================================================
      
    %% unary +
    | "+_1_sint"         -> Prefix {operator = "+",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "+_1_slong"        -> Prefix {operator = "+",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "+_1_sllong"       -> Prefix {operator = "+",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "+_1_uint"         -> Prefix {operator = "+",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "+_1_ulong"        -> Prefix {operator = "+",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "+_1_ullong"       -> Prefix {operator = "+",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
      
    %% unary -
    | "-_1_sint"         -> Prefix {operator = "-",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "-_1_slong"        -> Prefix {operator = "-",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "-_1_sllong"       -> Prefix {operator = "-",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "-_1_uint"         -> Prefix {operator = "-",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "-_1_ulong"        -> Prefix {operator = "-",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "-_1_ullong"       -> Prefix {operator = "-",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
                
      %% ~
    | "~_1_sint"         -> Prefix {operator = "~",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "~_1_slong"        -> Prefix {operator = "~",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "~_1_sllong"       -> Prefix {operator = "~",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "~_1_uint"         -> Prefix {operator = "~",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "~_1_ulong"        -> Prefix {operator = "~",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "~_1_ullong"       -> Prefix {operator = "~",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
      
      %% !
    | "!_1_char"         -> Prefix {operator = "!",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "!_1_schar"        -> Prefix {operator = "!",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "!_1_uchar"        -> Prefix {operator = "!",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "!_1_sint"         -> Prefix {operator = "!",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "!_1_uint"         -> Prefix {operator = "!",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "!_1_slong"        -> Prefix {operator = "!",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "!_1_ulong"        -> Prefix {operator = "!",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "!_1_sllong"       -> Prefix {operator = "!",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
    | "!_1_ullong"       -> Prefix {operator = "!",  result = CPrecedence_UNARY,  right = CPrecedence_UNARY} 
      
    %% =========================================================================
    %% Postfix operators
    %% =========================================================================
      
    %% =========================================================================
    %% Infix operators: arithmetic,  comparison,  bitwise,  logical
    %% =========================================================================
      
    %% ---------------------------------------------------
    %% Infix arithmetic "multiply" operations: *,  /,  %
    %% ---------------------------------------------------
      
    %% *
    | "*_sint"           -> Infix {operator = "*",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "*_slong"          -> Infix {operator = "*",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "*_sllong"         -> Infix {operator = "*",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "*_uint"           -> Infix {operator = "*",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "*_ulong"          -> Infix {operator = "*",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "*_ullong"         -> Infix {operator = "*",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
      
    %% /
    | "/_sint"           -> Infix {operator = "/",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "/_slong"          -> Infix {operator = "/",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "/_sllong"         -> Infix {operator = "/",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "/_uint"           -> Infix {operator = "/",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "/_ulong"          -> Infix {operator = "/",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "/_ullong"         -> Infix {operator = "/",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
      
    %% %
    | "//_sint"          -> Infix {operator = "%",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "//_slong"         -> Infix {operator = "%",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "//_sllong"        -> Infix {operator = "%",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "//_uint"          -> Infix {operator = "%",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "//_ulong"         -> Infix {operator = "%",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "//_ullong"        -> Infix {operator = "%",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
      
    %% ---------------------------------------------------
    %% Infix arithmetic "add" operations: +,  -
    %% ---------------------------------------------------

    %% +
    | "+_sint"           -> Infix {operator = "+",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
    | "+_slong"          -> Infix {operator = "+",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
    | "+_sllong"         -> Infix {operator = "+",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
    | "+_uint"           -> Infix {operator = "+",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
    | "+_ulong"          -> Infix {operator = "+",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
    | "+_ullong"         -> Infix {operator = "+",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
      
    %% -
    | "-_sint"           -> Infix {operator = "-",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
    | "-_slong"          -> Infix {operator = "-",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
    | "-_sllong"         -> Infix {operator = "-",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
    | "-_uint"           -> Infix {operator = "-",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
    | "-_ulong"          -> Infix {operator = "-",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
    | "-_ullong"         -> Infix {operator = "-",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
      
    %% ---------------------------------------------------
    %% Infix arithmetic shifts: <<,  >>
    %% ---------------------------------------------------

    %% << (6*6 versions)
    | "<<_sint_sint"     -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_sint_slong"    -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_sint_sllong"   -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_sint_uint"     -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_sint_ulong"    -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_sint_ullong"   -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
      
    | "<<_slong_sint"    -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_slong_slong"   -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_slong_sllong"  -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_slong_uint"    -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_slong_ulong"   -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_slong_ullong"  -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
      
    | "<<_sllong_sint"   -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_sllong_slong"  -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_sllong_sllong" -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_sllong_uint"   -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_sllong_ulong"  -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_sllong_ullong" -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
      
    | "<<_uint_sint"     -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_uint_slong"    -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_uint_sllong"   -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_uint_uint"     -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_uint_ulong"    -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_uint_ullong"   -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
      
    | "<<_ulong_sint"    -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_ulong_slong"   -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_ulong_sllong"  -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_ulong_uint"    -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_ulong_ulong"   -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_ulong_ullong"  -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
      
    | "<<_ullong_sint"   -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_ullong_slong"  -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_ullong_sllong" -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_ullong_uint"   -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_ullong_ulong"  -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | "<<_ullong_ullong" -> Infix {operator = "<<",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
      
    %% >> (6*6 versions)
    | ">>_sint_sint"     -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_sint_slong"    -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_sint_sllong"   -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_sint_uint"     -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_sint_ulong"    -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_sint_ullong"   -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
      
    | ">>_slong_sint"    -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_slong_slong"   -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_slong_sllong"  -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_slong_uint"    -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_slong_ulong"   -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_slong_ullong"  -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
      
    | ">>_sllong_sint"   -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_sllong_slong"  -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_sllong_sllong" -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_sllong_uint"   -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_sllong_ulong"  -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_sllong_ullong" -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
      
    | ">>_uint_sint"     -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_uint_slong"    -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_uint_sllong"   -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_uint_uint"     -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_uint_ulong"    -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_uint_ullong"   -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
      
    | ">>_ulong_sint"    -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_ulong_slong"   -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_ulong_sllong"  -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_ulong_uint"    -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_ulong_ulong"   -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_ulong_ullong"  -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
      
    | ">>_ullong_sint"   -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_ullong_slong"  -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_ullong_sllong" -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_ullong_uint"   -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_ullong_ulong"  -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
    | ">>_ullong_ullong" -> Infix {operator = ">>",  result = CPrecedence_SHIFT,  left = CPrecedence_SHIFT,  right = CPrecedence_ADD}
      
    %% ---------------------------------------------------
    %% Infix arithmetic relations: <,  >,  <=,  >=
    %% ---------------------------------------------------
      
    %% <
    | "<_sint"          -> Infix {operator = "<",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | "<_slong"         -> Infix {operator = "<",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | "<_sllong"        -> Infix {operator = "<",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | "<_uint"          -> Infix {operator = "<",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | "<_ulong"         -> Infix {operator = "<",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | "<_ullong"        -> Infix {operator = "<",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
      
    %% >
    | ">_sint"          -> Infix {operator = ">",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | ">_slong"         -> Infix {operator = ">",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | ">_sllong"        -> Infix {operator = ">",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | ">_uint"          -> Infix {operator = ">",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | ">_ulong"         -> Infix {operator = ">",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | ">_ullong"        -> Infix {operator = ">",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
      
    %% <=
    | "<=_sint"         -> Infix {operator = "<=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | "<=_slong"        -> Infix {operator = "<=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | "<=_sllong"       -> Infix {operator = "<=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | "<=_uint"         -> Infix {operator = "<=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | "<=_ulong"        -> Infix {operator = "<=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | "<=_ullong"       -> Infix {operator = "<=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
      
    %% >=
    | ">=_sint"         -> Infix {operator = ">=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | ">=_slong"        -> Infix {operator = ">=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | ">=_sllong"       -> Infix {operator = ">=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | ">=_uint"         -> Infix {operator = ">=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | ">=_ulong"        -> Infix {operator = ">=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | ">=_ullong"       -> Infix {operator = ">=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
      
    %% ---------------------------------------------------
    %% Infix arithmetic equalities: ==,  !=
    %% ---------------------------------------------------

    %% ==
    | "==_sint"         -> Infix {operator = "==",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
    | "==_slong"        -> Infix {operator = "==",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
    | "==_sllong"       -> Infix {operator = "==",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
    | "==_uint"         -> Infix {operator = "==",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
    | "==_ulong"        -> Infix {operator = "==",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
    | "==_ullong"       -> Infix {operator = "==",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
      
    %% !=
    | "!=_sint"         -> Infix {operator = "!=",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
    | "!=_slong"        -> Infix {operator = "!=",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
    | "!=_sllong"       -> Infix {operator = "!=",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
    | "!=_uint"         -> Infix {operator = "!=",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
    | "!=_ulong"        -> Infix {operator = "!=",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
    | "!=_ullong"       -> Infix {operator = "!=",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
      
    %% ---------------------------------------------------
    %% Infix bitwise operations: &,  ^,  |
    %% ---------------------------------------------------
      
    %% &
    | "&_sint"          -> Infix {operator = "&",    result = CPrecedence_AND,    left = CPrecedence_AND,    right = CPrecedence_EQ}
    | "&_slong"         -> Infix {operator = "&",    result = CPrecedence_AND,    left = CPrecedence_AND,    right = CPrecedence_EQ}
    | "&_sllong"        -> Infix {operator = "&",    result = CPrecedence_AND,    left = CPrecedence_AND,    right = CPrecedence_EQ}
    | "&_uint"          -> Infix {operator = "&",    result = CPrecedence_AND,    left = CPrecedence_AND,    right = CPrecedence_EQ}
    | "&_ulong"         -> Infix {operator = "&",    result = CPrecedence_AND,    left = CPrecedence_AND,    right = CPrecedence_EQ}
    | "&_ullong"        -> Infix {operator = "&",    result = CPrecedence_AND,    left = CPrecedence_AND,    right = CPrecedence_EQ}
      
    %% ^
    | "^_sint"          -> Infix {operator = "^",    result = CPrecedence_XOR,    left = CPrecedence_XOR,    right = CPrecedence_AND}
    | "^_slong"         -> Infix {operator = "^",    result = CPrecedence_XOR,    left = CPrecedence_XOR,    right = CPrecedence_AND}
    | "^_sllong"        -> Infix {operator = "^",    result = CPrecedence_XOR,    left = CPrecedence_XOR,    right = CPrecedence_AND}
    | "^_uint"          -> Infix {operator = "^",    result = CPrecedence_XOR,    left = CPrecedence_XOR,    right = CPrecedence_AND}
    | "^_ulong"         -> Infix {operator = "^",    result = CPrecedence_XOR,    left = CPrecedence_XOR,    right = CPrecedence_AND}
    | "^_ullong"        -> Infix {operator = "^",    result = CPrecedence_XOR,    left = CPrecedence_XOR,    right = CPrecedence_AND}
      
    %% |
    | "|_sint"          -> Infix {operator = "|",    result = CPrecedence_IOR,    left = CPrecedence_IOR,    right = CPrecedence_XOR}
    | "|_slong"         -> Infix {operator = "|",    result = CPrecedence_IOR,    left = CPrecedence_IOR,    right = CPrecedence_XOR}
    | "|_sllong"        -> Infix {operator = "|",    result = CPrecedence_IOR,    left = CPrecedence_IOR,    right = CPrecedence_XOR}
    | "|_uint"          -> Infix {operator = "|",    result = CPrecedence_IOR,    left = CPrecedence_IOR,    right = CPrecedence_XOR}
    | "|_ulong"         -> Infix {operator = "|",    result = CPrecedence_IOR,    left = CPrecedence_IOR,    right = CPrecedence_XOR}
    | "|_ullong"        -> Infix {operator = "|",    result = CPrecedence_IOR,    left = CPrecedence_IOR,    right = CPrecedence_XOR}
      
    %% ---------------------------------------------------
    %% Infix logical operations: &&, ||
    %% ---------------------------------------------------
      
    %% && -- primitive MetaSlang operator -- see above
    %% || -- primitive MetaSlang operator -- see above
      
    %% =========================================================================
    %% Array access
    %% =========================================================================
      
    | "@_char"   -> ArrayAccess
    | "@_schar"  -> ArrayAccess
    | "@_uchar"  -> ArrayAccess
      
    | "@_sshort" -> ArrayAccess
    | "@_ushort" -> ArrayAccess
      
    | "@_sint"   -> ArrayAccess
    | "@_uint"   -> ArrayAccess
      
    | "@_slong"  -> ArrayAccess
    | "@_ulong"  -> ArrayAccess
      
    | "@_sllong" -> ArrayAccess
    | "@_ullong" -> ArrayAccess
      
    %% =========================================================================
    %% Structure operators
    %% =========================================================================

    %% =========================================================================
    %% Conversion operators among the 11 integer types:
    %%    char, uchar, schar, ushort, sshort, uint, sint, ulong, slong, ullong, sllong
    %%    110 operators (11 types * 10 other types)
    %% =========================================================================
      
    %% cast to char
    | "charOfUChar"     -> if plainCharsAreSigned? then Cast "(char) " else NoOp
    | "charOfUshort"    -> Cast "(char) "
    | "charOfUint"      -> Cast "(char) "
    | "charOfUlong"     -> Cast "(char) "
    | "charOfUllong"    -> Cast "(char) "
    | "charOfSchar"     -> if plainCharsAreSigned? then NoOp else Cast "(char) "
    | "charOfSshort"    -> Cast "(char) "
    | "charOfSint"      -> Cast "(char) "
    | "charOfSlong"     -> Cast "(char) "
    | "charOfSllong"    -> Cast "(char) "
      
    %% cast to unsigned char
    | "ucharOfChar"     -> if plainCharsAreSigned? then Cast "(unsigned char) " else NoOp
    | "ucharOfUshort"   -> Cast "(unsigned char) "
    | "ucharOfUint"     -> Cast "(unsigned char) "
    | "ucharOfUlong"    -> Cast "(unsigned char) "
    | "ucharOfUllong"   -> Cast "(unsigned char) "
    | "ucharOfSchar"    -> Cast "(unsigned char) "
    | "ucharOfSshort"   -> Cast "(unsigned char) "
    | "ucharOfSint"     -> Cast "(unsigned char) "
    | "ucharOfSlong"    -> Cast "(unsigned char) "
    | "ucharOfSllong"   -> Cast "(unsigned char) "
      
    %% cast to unsigned short
    | "ushortOfChar"    -> if plainCharsAreSigned? then Cast "(unsigned short) " else NoOp
    | "ushortOfUChar"   -> NoOp
    | "ushortOfUint"    -> Cast "(unsigned short) "
    | "ushortOfUlong"   -> Cast "(unsigned short) "
    | "ushortOfUllong"  -> Cast "(unsigned short) "
    | "ushortOfSchar"   -> Cast "(unsigned short) "
    | "ushortOfSshort"  -> Cast "(unsigned short) "
    | "ushortOfSint"    -> Cast "(unsigned short) "
    | "ushortOfSlong"   -> Cast "(unsigned short) "
    | "ushortOfSllong"  -> Cast "(unsigned short) "
      
    %% cast to unsigned int
    | "uintOfChar"      -> if plainCharsAreSigned? then Cast "(unsigned int) " else NoOp
    | "uintOfUChar"     -> NoOp
    | "uintOfUshort"    -> NoOp
    | "uintOfUlong"     -> Cast "(unsigned int) "
    | "uintOfUllong"    -> Cast "(unsigned int) "
    | "uintOfSchar"     -> Cast "(unsigned int) "
    | "uintOfSshort"    -> Cast "(unsigned int) "
    | "uintOfSint"      -> Cast "(unsigned int) "
    | "uintOfSlong"     -> Cast "(unsigned int) "
    | "uintOfSllong"    -> Cast "(unsigned int) "
      
    %% cast to unsigned long
    | "ulongOfChar"     -> if plainCharsAreSigned? then Cast "(unsigned long) " else NoOp
    | "ulongOfUChar"    -> NoOp
    | "ulongOfUshort"   -> NoOp
    | "ulongOfUint"     -> NoOp
    | "ulongOfUllong"   -> Cast "(unsigned long) "
    | "ulongOfSchar"    -> Cast "(unsigned long) "
    | "ulongOfSshort"   -> Cast "(unsigned long) "
    | "ulongOfSint"     -> Cast "(unsigned long) "
    | "ulongOfSlong"    -> Cast "(unsigned long) "
    | "ulongOfSllong"   -> Cast "(unsigned long) "
      
    %% cast to unsigned long long
    | "ullongOfChar"    -> if plainCharsAreSigned? then Cast "(unsigned long long) " else NoOp
    | "ullongOfUChar"   -> NoOp
    | "ullongOfUshort"  -> NoOp
    | "ullongOfUint"    -> NoOp
    | "ullongOfUlong"   -> NoOp
    | "ullongOfSchar"   -> Cast "(unsigned long long) "
    | "ullongOfSshort"  -> Cast "(unsigned long long) "
    | "ullongOfSint"    -> Cast "(unsigned long long) "
    | "ullongOfSlong"   -> Cast "(unsigned long long) "
    | "ullongOfSllong"  -> Cast "(unsigned long long) "
      
    %% cast to signed char
    | "scharOfChar"     -> if plainCharsAreSigned? then NoOp else Cast "(signed char) "
    | "scharOfUChar"    -> Cast "(signed char) "
    | "scharOfUshort"   -> Cast "(signed char) "
    | "scharOfUint"     -> Cast "(signed char) "
    | "scharOfUlong"    -> Cast "(signed char) "
    | "scharOfUllong"   -> Cast "(signed char) "
    | "scharOfSshort"   -> Cast "(signed char) "
    | "scharOfSint"     -> Cast "(signed char) "
    | "scharOfSlong"    -> Cast "(signed char) "
    | "scharOfSllong"   -> Cast "(signed char) "
      
    %% cast to signed short
    | "sshortOfChar"    -> if plainCharsAreSigned? then NoOp else Cast "(signed short) "
    | "sshortOfUChar"   -> Cast "(signed short) "
    | "sshortOfUshort"  -> Cast "(signed short) "
    | "sshortOfUint"    -> Cast "(signed short) "
    | "sshortOfUlong"   -> Cast "(signed short) "
    | "sshortOfUllong"  -> Cast "(signed short) "
    | "sshortOfSchar"   -> NoOp
    | "sshortOfSint"    -> Cast "(signed short) "
    | "sshortOfSlong"   -> Cast "(signed short) "
    | "sshortOfSllong"  -> Cast "(signed short) "
      
    %% cast to signed int
    | "sintOfChar"      -> if plainCharsAreSigned? then NoOp else Cast "(signed int) "
    | "sintOfUChar"     -> Cast "(signed int) "
    | "sintOfUshort"    -> Cast "(signed int) "
    | "sintOfUint"      -> Cast "(signed int) "
    | "sintOfUlong"     -> Cast "(signed int) "
    | "sintOfUllong"    -> Cast "(signed int) "
    | "sintOfSchar"     -> NoOp
    | "sintOfSshort"    -> NoOp
    | "sintOfSlong"     -> Cast "(signed int) "
    | "sintOfSllong"    -> Cast "(signed int) "
      
    %% cast to signed long
    | "slongOfChar"     -> if plainCharsAreSigned? then NoOp else Cast "(signed long) "
    | "slongOfUChar"    -> Cast "(signed long) "
    | "slongOfUshort"   -> Cast "(signed long) "
    | "slongOfUint"     -> Cast "(signed long) "
    | "slongOfUlong"    -> Cast "(signed long) "
    | "slongOfUllong"   -> Cast "(signed long) "
    | "slongOfSchar"    -> NoOp
    | "slongOfSshort"   -> NoOp
    | "slongOfSint"     -> NoOp
    | "slongOfSllong"   -> Cast "(signed long) "
      
    %% cast to signed long long
    | "sllongOfChar"    -> if plainCharsAreSigned? then NoOp else Cast "(signed long long) "
    | "sllongOfUChar"   -> Cast "(signed long long) "
    | "sllongOfUshort"  -> Cast "(signed long long) "
    | "sllongOfUint"    -> Cast "(signed long long) "
    | "sllongOfUlong"   -> Cast "(signed long long) "
    | "sllongOfUllong"  -> Cast "(signed long long) "
    | "sllongOfSchar"   -> NoOp
    | "sllongOfSshort"  -> NoOp
    | "sllongOfSint"    -> NoOp
    | "sllongOfSlong"   -> NoOp
      
    %% =========================================================================
    %% These C ops should not appear in final spec to be printed.
    %% =========================================================================

    | "mathIntOfChar"   -> Illegal ("should have been removed: " ^ id)
    | "mathIntOfUchar"  -> Illegal ("should have been removed: " ^ id)
    | "mathIntOfUshort" -> Illegal ("should have been removed: " ^ id)
    | "mathIntOfUint"   -> Illegal ("should have been removed: " ^ id)
    | "mathIntOfUlong"  -> Illegal ("should have been removed: " ^ id)
    | "mathIntOfUllong" -> Illegal ("should have been removed: " ^ id)
    | "mathIntOfSchar"  -> Illegal ("should have been removed: " ^ id)
    | "mathIntOfSshort" -> Illegal ("should have been removed: " ^ id)
    | "mathIntOfSint"   -> Illegal ("should have been removed: " ^ id)
    | "mathIntOfSlong"  -> Illegal ("should have been removed: " ^ id)
    | "mathIntOfSllong" -> Illegal ("should have been removed: " ^ id)

    | "charOfMathInt"   -> Illegal ("should have been removed: " ^ id)
    | "ucharOfMathInt"  -> Illegal ("should have been removed: " ^ id)
    | "ushortOfMathInt" -> Illegal ("should have been removed: " ^ id)
    | "uintOfMathInt"   -> Illegal ("should have been removed: " ^ id)
    | "ulongOfMathInt"  -> Illegal ("should have been removed: " ^ id)
    | "ullongOfMathInt" -> Illegal ("should have been removed: " ^ id)
    | "scharOfMathInt"  -> Illegal ("should have been removed: " ^ id)
    | "sshortOfMathInt" -> Illegal ("should have been removed: " ^ id)
    | "sintOfMathInt"   -> Illegal ("should have been removed: " ^ id)
    | "slongOfMathInt"  -> Illegal ("should have been removed: " ^ id)
    | "sllongOfMathInt" -> Illegal ("should have been removed: " ^ id)

    %% =========================================================================
    %% All other C ops are treated as normal ops
    %% =========================================================================

    | _  -> 
      if legal_C_Id? id then
        Call id
      else
        Illegal ("illegal id for C op: " ^ id)

 op cfixity (status : CGenStatus, tm : MSTerm) : CFixity =
  case tm of 
    | Fun (fun, _, _) -> 
      (case fun of
         | And       -> Infix {operator = "&&", result = CPrecedence_LAND, left = CPrecedence_LAND, right = CPrecedence_IOR}
         | Or        -> Infix {operator = "||", result = CPrecedence_LOR,  left = CPrecedence_LOR,  right = CPrecedence_LAND}
         | Equals    -> Infix {operator = "==", result = CPrecedence_EQ,   left = CPrecedence_EQ,   right = CPrecedence_REL}  % for non integer values
         | NotEquals -> Infix {operator = "!=", result = CPrecedence_EQ,   left = CPrecedence_EQ,   right = CPrecedence_REL}  % for non integer values

         | Project f -> 
           if legal_C_Id? f then
             Postfix {operator = "." ^ f, result = CPrecedence_POST, left = CPrecedence_POST} 
           else
             Illegal ("illegal id for projection: " ^ f)

         | Op (qid as Qualified ("C", id), _) -> cfixityForCOp (status, id)

         | Op (qid as Qualified (q,   id), _) -> 
           if legal_C_Id? id then
             Call id  % for now, we ignore q
           else
             Illegal ("illegal id for non-C op: " ^ show qid))

    | _ -> 
      Illegal ("unknown fixity for " ^ printTerm tm)

 %% ========================================================================
 %% Implicit constants (Nat, Char, String)
 %% ========================================================================

 op printFunAsC (status : CGenStatus, fun : MSFun) : Pretty * CGenStatus =
  case fun of
    | Nat     n  -> (string (show n), status)
    | Char    c  -> (string (show c), status)
    | String  s  -> (string s,        status)
    | _ -> 
      (string "??",
       reportError ("unrecognized fun: " ^ anyToString fun, status))

 %% ========================================================================
 %% Explicit numeric constants (Hex, Oct, Dec)
 %% ========================================================================

 op printNumericConstantAsC (status : CGenStatus, suffix : String, tm : MSTerm, radix : MSTerm) 
  : Pretty * Bool * CGenStatus = 
  let

    def get_nat_value tm =
      case tm of
        | Fun (Nat n, _, _) -> Some n
        | _ -> None

    def digit n =
      case n of
        |  0 -> #0
        |  1 -> #1
        |  2 -> #2
        |  3 -> #3
        |  4 -> #4
        |  5 -> #5
        |  6 -> #6
        |  7 -> #7
        |  8 -> #8
        |  9 -> #9
        | 10 -> #A
        | 11 -> #B
        | 12 -> #C
        | 13 -> #D
        | 14 -> #E
        | 15 -> #F
          
    def digitize (prefix, n, base, suffix) =
      let
        def aux (digits, n) =
          if n < base then
            implode ([digit n] ++ digits)
          else
            let i = n div base in
            let j = n - (base * i) in
            aux ([digit j] ++ digits, i)
      in
      let suffix = 
          %% TODO: what are the correct rules for dropping suffix?
          case suffix of
            | "U" | n <= 0x7FFF -> ""
            | _ -> suffix
      in
      prefix ^ (aux ([], n)) ^ suffix
      
    def oct (n, suffix) = digitize ("0" , n,  8, suffix)
    def dec (n, suffix) = digitize (""  , n, 10, suffix)
    def hex (n, suffix) = digitize ("0x", n, 16, suffix)

  in
  case get_nat_value tm of
    | Some n ->
      % type IntConstBase = | dec | hex | oct
      (string (case radix of
                 | Fun (Embed ("hex", _), _, _) -> hex (n, suffix)
                 | Fun (Embed ("oct", _), _, _) -> oct (n, suffix)
                 | Fun (Embed ("dec", _), _, _) -> dec (n, suffix)
                 | _                            -> dec (n, suffix)), % default to dec
       false,
       status)
    | _ ->
      (string "??",
       false,
       reportError ("no Nat value for " ^ printTerm tm, status))

 %% ========================================================================
 %% Main print routine for terms.
 %%
 %%  For vars, prints name (if legal)
 %%
 %%  For typed terms, recurs into untyped term
 %%
 %%  For primitive terms (Fun's):
 %%    Prints implicit Nat/Char/String constants using printFunAsC.
 %%    TODO:  Should Nat constants be handled that implicitly?
 %%
 %%  For applications:
 %%
 %%    First uncurries and flattens tuple arguments, e.g. 
 %%      foo a (b, c) (d, e)
 %%       =>
 %%      foo (a, (b, c), (d, e))
 %%       =>
 %%      foo (a, b, c, d, e)
 %%
 %%    Then calls cfixity to get pattern for operator.
 %%    Then prints according to that pattern.
 %%     (If pattern cannot be found, returns None.)
 %%
 %%  For other terms, returns None.
 %%
 %% ========================================================================


 op uncurry (t1 : MSTerm, args : MSTerms) : CFunCall =
  case t1 of
    | Apply (t2, t3, _) -> uncurry (t2, [t3] ++ args)
    | _ -> {f = t1, args = args}

 op flattenRecordArgs (args : MSTerms) : MSTerms =
  foldl (fn (args, arg) ->
           case arg of
             | Record (("1", arg1) :: pairs, _) ->
               args ++ [arg1] ++ (map (fn (_, arg) -> arg) pairs)
             | _ ->
               args ++ [arg])
        []
        args
             
 op wrapReturn (pretty : Pretty) : Pretty = 
  blockNone (0, [(0, string "return "), (0, pretty), (0, string "; ")])

 op printTermAsCExp (status : CGenStatus, tm : MSTerm, expected : CPrecedence) 
  : Pretty * CGenStatus = 
  let (p, _, status) = printTermAsC (status, tm, expected, Expression) in
  (p, status)

 op printTermsAsCList (status       : CGenStatus, 
                       pretty_open  : Line,
                       terms        : MSTerms,
                       pretty_close : Line)
  : Lines * CGenStatus =
  let (lines, _, status) =
      foldl (fn ((lines, first?, status), tm) ->
               let (block, status) = printTermAsCExp (status, tm, CPrecedence_NO_PARENS) in
               let line = (0, block) in
               let lines = lines ++ (if first? then [line] else [line, L0_comma_space]) in
               (lines, false, status))
            ([pretty_open], true, status)
            terms
  in
  (lines ++ [pretty_close], status)

 op printTermAsC (status   : CGenStatus,
                  tm       : MSTerm, 
                  expected : CPrecedence, 
                  level    : CLevel) 
  : Pretty * Bool * CGenStatus = 
  %% if precedence of term is less than expected precedence, wrap parens
  case tm of

    | Var ((id, _), _) -> 
      if legal_C_Id? id then
        (string id, false, status)
      else
        (string "", false, reportError ("illegal C variable name: " ^ id, status))

    | Fun (fun, _, _) -> 
      let (pretty, status) = printFunAsC  (status, fun) in
      (pretty, false, status)

    | TypedTerm  (t1, _, _) -> 
      printTermAsC (status, t1, expected, level)

    | IfThenElse (t1, t2, t3, _) -> 
      let (p1, _,            status) = printTermAsC (status, t1, CPrecedence_REQUIRE_PARENS, Expression) in
      let (p2, p2hasreturn?, status) = printTermAsC (status, t2, CPrecedence_NO_PARENS,      level)      in
      let (p3, p3hasreturn?, status) = printTermAsC (status, t3, CPrecedence_NO_PARENS,      level)      in
      if level = Statement then
        let p2 = if p2hasreturn? then p2 else wrapReturn p2 in
        let p3 = if p3hasreturn? then p3 else wrapReturn p3 in
        (blockAll (0, [(0, blockNone (0, [L0_if, (0, p1), L0_space])),
                       (2, p2), 
                       L0_else,
                       (2, p3)]),
         true,
         status)
      else
        (blockLinear (0, [(0, p1), 
                          (2, blockNone (0, [L0_expr_then, (0, p2)])), 
                          (2, blockNone (0, [L0_expr_else, (0, p3)]))]),
         false,
         status)

    | Apply (t1, t2, _) -> 
      (let {f, args} = uncurry (t1, [t2]) in
       let args   = flattenRecordArgs args in
       let fixity = cfixity (status, f)    in
       case (fixity, args) of

         | (Call fname, args) ->
           let (lines, status) = printTermsAsCList (status, L0_lparen, args, L0_rparen) in
           let lines = [(0, string fname)] ++ lines in
           (blockNone (0, lines), false, status)
           
         | (Prefix fixity, [arg]) ->
           let (p1, status) = printTermAsCExp (status, arg, fixity.right) in
           let lines = [(0, string fixity.operator), (0, p1)] in
           (blockNone (0, lines), false, status)

         | (Cast c_str, [arg]) ->
           let (p1, status) = printTermAsCExp (status, arg, CPrecedence_CAST) in
           let lines = [(0, string c_str), (0, p1)] in
           (blockNone (0, lines), false, status)
           
         | (Postfix fixity, [arg]) ->
           let (p1, status) = printTermAsCExp (status, arg, fixity.left) in
           let lines = [(0, p1), (0, string fixity.operator)] in
           (blockNone (0, lines), false, status)
           
         | (Infix fixity, [arg1, arg2]) ->
           let (p1, status) = printTermAsCExp (status, arg1, fixity.left)  in
           let (p2, status) = printTermAsCExp (status, arg2, fixity.right) in
           let prefix  = if fixity.result < expected then
                           [L0_lparen, (0, p1), L0_space]
                         else
                           [(0, p1), L0_space]
           in
           let middle  = [(0, string fixity.operator), L0_space] in
           let postfix = if fixity.result < expected then
                           [(0, p2), L0_rparen]
                         else
                           [(0, p2)]
           in
           (blockLinear (0, [(0, blockNone (0, prefix)),
                             (0, blockNone (0, middle)),
                             (0, blockNone (0, postfix))]),
            false,
            status)
           
         | (Constant suffix, [tm, radix]) -> 
           printNumericConstantAsC (status, suffix, tm, radix)
           
         | (ArrayAccess, array :: indices) ->
           let (pretty_array_name, status) = printTermAsCExp (status, array, CPrecedence_EXPR) in
           let (lines, status) = printTermsAsCList (status, L0_lsquare, reverse indices, L0_rsquare) in
           let lines = [(0, pretty_array_name)] ++ lines in
           (blockNone (0, lines), false, status)
           
         | (NoOp, [t1]) ->
           let (p1, status) = printTermAsCExp (status, t1, expected) in
           (p1, false, status)

         | (Illegal error_msg, _) ->
           (string "??", false, reportError (error_msg, status)))
                   
    | _ -> 
      (string "??",
       false,
       reportError ("unrecognized term: " ^ printTerm tm, status))

 %% ========================================================================

endspec
