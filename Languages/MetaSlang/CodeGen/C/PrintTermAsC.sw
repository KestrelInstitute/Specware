(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

PrintAsC qualifying spec 

 (*
  * Note: In the following, [C99 ...] refers to ISO/IEC 9899:TC3, Sept 7, 2007.
  *       This draft version updates the 1999 version by incorporating 3 revisions 
  *       for errata.
  *)

 %% Search for "not yet implemented" to get the "to do" list:

 %% Floating constants             not yet implemented
 %% Enumeration constants          not yet implemented
 %% Character constants            not yet implemented
 %% String literals                not yet implemented
 %%  ++  (post-increment)          not yet implemented
 %%  --  (post-decrement)          not yet implemented
 %%  (_){_}                        not yet implemented
 %%  ++  (pre-increment)           not yet implemented
 %%  --  (pre-decrement)           not yet implemented
 %%  &  (address)                  not yet implemented
 %%  *  (indirection)              not yet implemented
 %%  sizeof                        not yet implemented
 %%  =    (assign)                 not yet implemented
 %%  *=   (assign product)         not yet implemented
 %%  /=   (assign quotient)        not yet implemented
 %%  %=   (assign remainder)       not yet implemented
 %%  +=   (assign sum)             not yet implemented
 %%  -=   (assign difference)      not yet implemented
 %%  <<=  (assign left shift)      not yet implemented
 %%  >>=  (assign right shift)     not yet implemented
 %%  &=   (assign bitwise and)     not yet implemented
 %%  ^=   (assign bitwise xor)     not yet implemented
 %%  |=   (assign bitwise or)      not yet implemented
 %%  ,  (sequence)                 not yet implemented

 %% also to do: what are the correct rules for dropping suffix on integer constants?

 import PrintAsCUtils

 %% ========================================================================
 %%  We wrap parens around a sub-term if its precedence is less than the 
 %%  expected precedence,  Two extreme values are included for clarity.
 %% ========================================================================

 type CPrecedence = {n : Nat | 0 <= n && n <= 17}

 op CPrecedence_NO_PARENS      : CPrecedence =  0  % if this is passed to PrintTermAsC, no parens will be added
 op CPrecedence_EXPR           : CPrecedence =  1  % this has same effect as NO_PARENS
 op CPrecedence_COND           : CPrecedence =  2  % _?_:_ 
 op CPrecedence_LOR            : CPrecedence =  3  % _||_
 op CPrecedence_LAND           : CPrecedence =  4  % _&&_
 op CPrecedence_IOR            : CPrecedence =  5  % _|_
 op CPrecedence_XOR            : CPrecedence =  6  % _^_
 op CPrecedence_AND            : CPrecedence =  7  % _&_
 op CPrecedence_EQ             : CPrecedence =  8  % _==_  _!_  _=_
 op CPrecedence_REL            : CPrecedence =  9  % _<_  _<=_  _=>_  _>_
 op CPrecedence_SHIFT          : CPrecedence = 10  % _<<_  _>>_
 op CPrecedence_ADD            : CPrecedence = 11  % _+_  _-_ 
 op CPrecedence_MUL            : CPrecedence = 12  % _*_  _/_  _%_
 op CPrecedence_CAST           : CPrecedence = 13  % (_)_
 op CPrecedence_UNARY          : CPrecedence = 14  % _++_  _--_  _&_  _*_  _+_  _-_  _~_  _!_
 op CPrecedence_POST           : CPrecedence = 15  % _[_]  _(_)  _._  _->_  _++  _--  (_){_} 
 op CPrecedence_SUBSCRIPT      : CPrecedence = CPrecedence_POST         % [C99 6.5.2 "Postfix operators"]
 op CPrecedence_CALL           : CPrecedence = CPrecedence_POST         % [C99 6.5.2 "Postfix operators"]
 op CPrecedence_PRIMARY        : CPrecedence = 16
 op CPrecedence_REQUIRE_PARENS : CPrecedence = 17  % if this is passed to PrintTermAsC, parens will be added
 op CPrecedence_HAVE_PARENS    : CPrecedence = 17  % if this is returned, no parens will be added
 
 %% ========================================================================
 %%  CFixity describes the pattern and keyword for a term to be applied.
 %%  If the operator is clearly illegal, we report that and return None.
 %%  If the term is complex (not a Fun) we punt and return Some Unknown.
 %% ========================================================================

 type InfixData = {operator : String, result: CPrecedence, left:  CPrecedence, right: CPrecedence}

 type CFixity  = | Cast        String      
                 | Unary       String      
                 | Postfix     String
                 | Constant    String
                 | Infix       InfixData
                 | Call                    % function application
                 | Subscript               % array access
                 | NoOp                    % 'test', redundant casts, etc.
                 | Illegal     String

 %% ========================================================================
 %% Many Ops qualified by "C" have special meanings...
 %% ========================================================================

 op cfixityForCOp (status : CGenStatus, id : Id) : CFixity =
  %% Qualifier is "C"
  let plainCharsAreSigned? = status.plainCharsAreSigned? in
  case id of
              
    %% ==============================================================================
    %% 'test' is an ad-hoc function used by Specware to map the Integer values 
    %% returned by relational operators into the Bool value required by IfThenElse.
    %% We simply skip over it when printing C terms.
    %% ==============================================================================

    | "test" -> NoOp
      
    %% ==============================================================================
    %% [C99 6.4.4 "Constants"]
    %% ==============================================================================

    %% ------------------------------------------------------------
    %% [C99 6.4.4.1 "Integer constants"]
    %% ------------------------------------------------------------

    %%  Note: printNumericConstantAsC applies additional rules for oct/dec/hex 

    | "sintConstant"     -> Constant ""   
    | "slongConstant"    -> Constant "L"  
    | "sllongConstant"   -> Constant "LL"
      
    | "uintConstant"     -> Constant "U"
    | "ulongConstant"    -> Constant "UL"
    | "ullongConstant"   -> Constant "ULL"
      
    %% ------------------------------------------------------------
    %% [C99 6.4.4.2 "Floating constants"]
    %% ------------------------------------------------------------

    %% Floating constants             not yet implemented

    %% ------------------------------------------------------------
    %% [C99 6.4.4.3 "Enumeration constants"]
    %% ------------------------------------------------------------

    %% Enumeration constants          not yet implemented

    %% ------------------------------------------------------------
    %% [C99 6.4.4.4 "Character constants"]
    %% ------------------------------------------------------------

    %% Character constants            not yet implemented

    %% ==============================================================================
    %% [C99 6.4.5 "String literals"]
    %% ==============================================================================

    %% String literals                not yet implemented

    %% ==============================================================================
    %% [C99 6.5.2 "Postfix operators"]
    %%
    %% These have CPrecedence_POST and expect a preceding arg with CPrecedence_POST
    %% ==============================================================================
      
    %% ------------------------------------------------------------
    %% [C99 6.5.2.1  "Array subscripting"]
    %% ------------------------------------------------------------
      
    | "@_char"   -> Subscript
    | "@_schar"  -> Subscript
    | "@_uchar"  -> Subscript
      
    | "@_sshort" -> Subscript
    | "@_ushort" -> Subscript
      
    | "@_sint"   -> Subscript
    | "@_uint"   -> Subscript
      
    | "@_slong"  -> Subscript
    | "@_ulong"  -> Subscript
      
    | "@_sllong" -> Subscript
    | "@_ullong" -> Subscript
  
    %% ------------------------------------------------------------
    %% [C99 6.5.2.2  "Function calls"]
    %% ------------------------------------------------------------

    %%  _(_)  See below, since function names won't be qualified with "C"
  
    %% ------------------------------------------------------------
    %% [C99 6.5.2.3  "Structure and union members"]
    %% ------------------------------------------------------------

    %%  .     See main cfixity routine, since field names won't be qualified with "C"

    %%  ->    See main cfixity routine, since field names won't be qualified with "C"

    %% ------------------------------------------------------------
    %% [C99 6.5.2.4  "Postfix increment and decrement operators"]
    %% ------------------------------------------------------------

    %%  ++  (post-increment)          not yet implemented

    %%  --  (post-decrement)          not yet implemented

    %% ------------------------------------------------------------
    %% [C99 6.5.2.5  "Compound literals"]
    %% ------------------------------------------------------------

    %%  (_){_}                        not yet implemented

    %% ==============================================================================
    %% [C99 6.5.3 "Unary operators"]
    %%
    %% These have CPrecedence_UNARY and expect a following arg with CPrecedence_UNARY
    %% ==============================================================================
      
    %% ------------------------------------------------------------
    %% [C99 6.5.3.1  "Prefix increment and decrement operators"]
    %% ------------------------------------------------------------

    %%  ++  (pre-increment)           not yet implemented

    %%  --  (pre-decrement)           not yet implemented

    %% ------------------------------------------------------------
    %% [C99 6.5.3.2  "Address and indirection operators"]
    %% ------------------------------------------------------------

    %%  &  (address)                  not yet implemented

    %%  *  (indirection)              not yet implemented

    %% ------------------------------------------------------------
    %% [C99 6.5.3.3  "Unary arithmetic pointers"]
    %% ------------------------------------------------------------

    %%  +  (plus)                

    | "+_1_sint"   -> Unary "+"
    | "+_1_slong"  -> Unary "+"
    | "+_1_sllong" -> Unary "+"
    | "+_1_uint"   -> Unary "+"
    | "+_1_ulong"  -> Unary "+"
    | "+_1_ullong" -> Unary "+"
      
    %%  -  (minus)  

    | "-_1_sint"   -> Unary "-"
    | "-_1_slong"  -> Unary "-"
    | "-_1_sllong" -> Unary "-"
    | "-_1_uint"   -> Unary "-"
    | "-_1_ulong"  -> Unary "-"
    | "-_1_ullong" -> Unary "-"
                
    %%  ~  (bitwise complement) 

    | "~_sint"   -> Unary "~"
    | "~_slong"  -> Unary "~"
    | "~_sllong" -> Unary "~"
    | "~_uint"   -> Unary "~"
    | "~_ulong"  -> Unary "~"
    | "~_ullong" -> Unary "~"
      
    %%  !  (logical negation)   

    | "!_char"   -> Unary "!"
    | "!_schar"  -> Unary "!"
    | "!_uchar"  -> Unary "!"
    | "!_sshort" -> Unary "!"
    | "!_ushort" -> Unary "!"
    | "!_sint"   -> Unary "!"
    | "!_uint"   -> Unary "!"
    | "!_slong"  -> Unary "!"
    | "!_ulong"  -> Unary "!"
    | "!_sllong" -> Unary "!"
    | "!_ullong" -> Unary "!"
      
    %% ------------------------------------------------------------
    %%  [C99 6.5.3.5  "The sizeof operator"]
    %% ------------------------------------------------------------

    %%  sizeof                        not yet implemented

    %% ==============================================================================
    %% [C99 6.5.4 "Cast operators"]
    %% ==============================================================================

    %% Conversion operators among the 11 integer types:
    %%  char, uchar, schar, ushort, sshort, uint, sint, ulong, slong, ullong, sllong
    %%  110 operators (11 types * 10 other types)
      
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
      
    %% ==============================================================================
    %% [C99 6.5.5 "Multiplicative operators"]
    %% ==============================================================================

    %%  *  (multiplication)      

    | "*_sint"           -> Infix {operator = "*",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "*_slong"          -> Infix {operator = "*",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "*_sllong"         -> Infix {operator = "*",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "*_uint"           -> Infix {operator = "*",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "*_ulong"          -> Infix {operator = "*",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "*_ullong"         -> Infix {operator = "*",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
      
    %%  /  (quotient)

    | "/_sint"           -> Infix {operator = "/",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "/_slong"          -> Infix {operator = "/",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "/_sllong"         -> Infix {operator = "/",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "/_uint"           -> Infix {operator = "/",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "/_ulong"          -> Infix {operator = "/",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "/_ullong"         -> Infix {operator = "/",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
      
    %%  %  (remainder)

    | "//_sint"          -> Infix {operator = "%",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "//_slong"         -> Infix {operator = "%",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "//_sllong"        -> Infix {operator = "%",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "//_uint"          -> Infix {operator = "%",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "//_ulong"         -> Infix {operator = "%",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
    | "//_ullong"        -> Infix {operator = "%",   result = CPrecedence_MUL,    left = CPrecedence_MUL,    right = CPrecedence_CAST}
      
    %% ==============================================================================
    %% [C99 6.5.6 "Additive operators"]
    %% ==============================================================================

    %%  +  (addition)            

    | "+_sint"           -> Infix {operator = "+",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
    | "+_slong"          -> Infix {operator = "+",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
    | "+_sllong"         -> Infix {operator = "+",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
    | "+_uint"           -> Infix {operator = "+",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
    | "+_ulong"          -> Infix {operator = "+",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
    | "+_ullong"         -> Infix {operator = "+",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
      
    %%  -  (subtraction) 

    | "-_sint"           -> Infix {operator = "-",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
    | "-_slong"          -> Infix {operator = "-",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
    | "-_sllong"         -> Infix {operator = "-",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
    | "-_uint"           -> Infix {operator = "-",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
    | "-_ulong"          -> Infix {operator = "-",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
    | "-_ullong"         -> Infix {operator = "-",   result = CPrecedence_ADD,    left = CPrecedence_ADD,    right = CPrecedence_MUL}
      
    %% ==============================================================================
    %% [C99 6.5.7  "Bitwise shift operators"]
    %% ==============================================================================

    %% << (left shift)   6*6 versions

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
      
    %% >> (right shift)   6*6 versions

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
      
    %% ==============================================================================
    %% [C99 6.5.8  "Relational operators"]
    %% ==============================================================================
      
    %%  <  (less than)

    | "<_sint"          -> Infix {operator = "<",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | "<_slong"         -> Infix {operator = "<",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | "<_sllong"        -> Infix {operator = "<",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | "<_uint"          -> Infix {operator = "<",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | "<_ulong"         -> Infix {operator = "<",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | "<_ullong"        -> Infix {operator = "<",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
      
    %%  >  (greater than)

    | ">_sint"          -> Infix {operator = ">",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | ">_slong"         -> Infix {operator = ">",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | ">_sllong"        -> Infix {operator = ">",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | ">_uint"          -> Infix {operator = ">",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | ">_ulong"         -> Infix {operator = ">",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | ">_ullong"        -> Infix {operator = ">",    result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
      
    %%  <=  (less than or equal)

    | "<=_sint"         -> Infix {operator = "<=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | "<=_slong"        -> Infix {operator = "<=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | "<=_sllong"       -> Infix {operator = "<=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | "<=_uint"         -> Infix {operator = "<=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | "<=_ulong"        -> Infix {operator = "<=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | "<=_ullong"       -> Infix {operator = "<=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
      
    %%  >=  (greater than or equal)

    | ">=_sint"         -> Infix {operator = ">=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | ">=_slong"        -> Infix {operator = ">=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | ">=_sllong"       -> Infix {operator = ">=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | ">=_uint"         -> Infix {operator = ">=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | ">=_ulong"        -> Infix {operator = ">=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
    | ">=_ullong"       -> Infix {operator = ">=",   result = CPrecedence_REL,    left = CPrecedence_REL,    right = CPrecedence_SHIFT}
      
    %% ==============================================================================
    %% [C99 6.5.9  "Equality operators"]
    %% ==============================================================================

    %%  ==  (equal)

    | "==_sint"         -> Infix {operator = "==",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
    | "==_slong"        -> Infix {operator = "==",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
    | "==_sllong"       -> Infix {operator = "==",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
    | "==_uint"         -> Infix {operator = "==",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
    | "==_ulong"        -> Infix {operator = "==",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
    | "==_ullong"       -> Infix {operator = "==",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
      
    %%  !=  (not equal)

    | "!=_sint"         -> Infix {operator = "!=",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
    | "!=_slong"        -> Infix {operator = "!=",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
    | "!=_sllong"       -> Infix {operator = "!=",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
    | "!=_uint"         -> Infix {operator = "!=",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
    | "!=_ulong"        -> Infix {operator = "!=",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
    | "!=_ullong"       -> Infix {operator = "!=",   result = CPrecedence_EQ,     left = CPrecedence_EQ,     right = CPrecedence_REL}
      
    %% ==============================================================================
    %% [C99 6.5.10 "Bitwise AND operator"]
    %% ==============================================================================
      
    %%  &  (bitwise and)

    | "&_sint"          -> Infix {operator = "&",    result = CPrecedence_AND,    left = CPrecedence_AND,    right = CPrecedence_EQ}
    | "&_slong"         -> Infix {operator = "&",    result = CPrecedence_AND,    left = CPrecedence_AND,    right = CPrecedence_EQ}
    | "&_sllong"        -> Infix {operator = "&",    result = CPrecedence_AND,    left = CPrecedence_AND,    right = CPrecedence_EQ}
    | "&_uint"          -> Infix {operator = "&",    result = CPrecedence_AND,    left = CPrecedence_AND,    right = CPrecedence_EQ}
    | "&_ulong"         -> Infix {operator = "&",    result = CPrecedence_AND,    left = CPrecedence_AND,    right = CPrecedence_EQ}
    | "&_ullong"        -> Infix {operator = "&",    result = CPrecedence_AND,    left = CPrecedence_AND,    right = CPrecedence_EQ}
      
    %% ==============================================================================
    %% [C99 6.5.11 "Bitwise exclusive OR operator"]
    %% ==============================================================================

    %%  ^  (bitwise exclusive or)

    | "^_sint"          -> Infix {operator = "^",    result = CPrecedence_XOR,    left = CPrecedence_XOR,    right = CPrecedence_AND}
    | "^_slong"         -> Infix {operator = "^",    result = CPrecedence_XOR,    left = CPrecedence_XOR,    right = CPrecedence_AND}
    | "^_sllong"        -> Infix {operator = "^",    result = CPrecedence_XOR,    left = CPrecedence_XOR,    right = CPrecedence_AND}
    | "^_uint"          -> Infix {operator = "^",    result = CPrecedence_XOR,    left = CPrecedence_XOR,    right = CPrecedence_AND}
    | "^_ulong"         -> Infix {operator = "^",    result = CPrecedence_XOR,    left = CPrecedence_XOR,    right = CPrecedence_AND}
    | "^_ullong"        -> Infix {operator = "^",    result = CPrecedence_XOR,    left = CPrecedence_XOR,    right = CPrecedence_AND}
      
    %% ==============================================================================
    %% [C99 6.5.12 "Bitwise inclusive OR operator"]
    %% ==============================================================================

    %%  |  (bitwise inclusive or)

    | "|_sint"          -> Infix {operator = "|",    result = CPrecedence_IOR,    left = CPrecedence_IOR,    right = CPrecedence_XOR}
    | "|_slong"         -> Infix {operator = "|",    result = CPrecedence_IOR,    left = CPrecedence_IOR,    right = CPrecedence_XOR}
    | "|_sllong"        -> Infix {operator = "|",    result = CPrecedence_IOR,    left = CPrecedence_IOR,    right = CPrecedence_XOR}
    | "|_uint"          -> Infix {operator = "|",    result = CPrecedence_IOR,    left = CPrecedence_IOR,    right = CPrecedence_XOR}
    | "|_ulong"         -> Infix {operator = "|",    result = CPrecedence_IOR,    left = CPrecedence_IOR,    right = CPrecedence_XOR}
    | "|_ullong"        -> Infix {operator = "|",    result = CPrecedence_IOR,    left = CPrecedence_IOR,    right = CPrecedence_XOR}
      
    %% ==============================================================================
    %% [C99 6.5.13 "Logical AND operator"]
    %% ==============================================================================
      
    %%  &&  (logical and)             see main cfixity for Specware &&

    %% ==============================================================================
    %% [C99 6.5.14 "Logical OR operator"]
    %% ==============================================================================

    %%  ||  (logical or)              see main cfixity for Specware ||
      
    %% ==============================================================================
    %% [C99 6.5.15 "Conditional operator"]
    %% ==============================================================================

    %%  _ ? _ : _  (conditional)      see main cfixity for Specware IfThenElse as exp
      
    %% ==============================================================================
    %% [C99 6.5.16 "Assignment operators"]
    %% ==============================================================================

    %%  =    (assign)                 not yet implemented
    %%  *=   (assign product)         not yet implemented
    %%  /=   (assign quotient)        not yet implemented
    %%  %=   (assign remainder)       not yet implemented
    %%  +=   (assign sum)             not yet implemented
    %%  -=   (assign difference)      not yet implemented
    %%  <<=  (assign left shift)      not yet implemented
    %%  >>=  (assign right shift)     not yet implemented
    %%  &=   (assign bitwise and)     not yet implemented
    %%  ^=   (assign bitwise xor)     not yet implemented
    %%  |=   (assign bitwise or)      not yet implemented

    %% ==============================================================================
    %% [C99 6.5.17 "Comma operator"]
    %% ==============================================================================

    %%  ,  (sequence)                 not yet implemented

    %% ==============================================================================
    %% [C99 6.6 "Constant expressions"]
    %% ==============================================================================
              
    %% =========================================================================
    %% Other C ops should not appear in final spec to be printed.
    %% =========================================================================

    | _  -> 
      Illegal ("Op not in legal subset for translation to C: C." ^ id)


 op cfixity (status : CGenStatus, tm : MSTerm) : CFixity =
  case tm of 
    | Fun (fun, _, _) -> % 'Fun' just means primitive (fundamental?)
      (case fun of

         %% ------------------------------------------------------------
         %% [C99 6.5.3.3  "Unary arithmetic pointers"]
         %% ------------------------------------------------------------

         | Not       -> Unary "!"

         %% ------------------------------------------------------------
         %% [C99 6.5.13 "Logical AND operator"]
         %% ------------------------------------------------------------

         | And       -> Infix {operator = "&&", result = CPrecedence_LAND, left = CPrecedence_LAND, right = CPrecedence_IOR}

         %% ------------------------------------------------------------
         %% [C99 6.5.14 "Logical OR operator"]
         %% ------------------------------------------------------------

         | Or        -> Infix {operator = "||", result = CPrecedence_LOR,  left = CPrecedence_LOR,  right = CPrecedence_LAND}

         %% ------------------------------------------------------------
         %% [C99 6.5.9  "Equality operators"]
         %% ------------------------------------------------------------

         | Equals    -> Infix {operator = "==", result = CPrecedence_EQ,   left = CPrecedence_EQ,   right = CPrecedence_REL}  % for non integer values
         | NotEquals -> Infix {operator = "!=", result = CPrecedence_EQ,   left = CPrecedence_EQ,   right = CPrecedence_REL}  % for non integer values

         %% ------------------------------------------------------------
         %% [C99 6.5.2.3  "Structure and union members"]
         %% ------------------------------------------------------------

         | Project f -> 
           if legal_C_Id? f then
             Postfix ("." ^ f)
           else
             Illegal ("illegal id for projection: " ^ f)

         | Op (qid as Qualified (q, id), _) -> 
           if q = "C" then
             cfixityForCOp (status, id)  % special cases for built-in C operators
           else if legal_C_Id? id then
             %% ------------------------------------------------------------
             %% [C99 6.5.2.2  "Function calls"]
             %% ------------------------------------------------------------
             Call 
           else
             Illegal ("illegal id for C function: " ^ show qid)

         | _ -> 
           Illegal ("unknown fixity for " ^ printTerm tm))

    | _ -> 
      Illegal ("unknown fixity for " ^ printTerm tm)

 %% ========================================================================
 %% Implicit constants (Nat, Char, String)
 %% Function names
 %%  ?anything else?
 %% ========================================================================

 op printPrimitiveAsC (status : CGenStatus, fun : MSFun) : Pretty * CGenStatus =
  %% 'Fun' means primitive here, and is not short for 'function'
  case fun of
%    | Nat     n  -> (string (show n), status)
%    | Char    c  -> (string (show c), status)
%    | String  s  -> (string s,        status)

    | Op (qid as Qualified (q, id), _) -> 
      if q = "C" then % TODO Think about this check.
        (string "??", reportError ("Op not in legal subset for translation to C: C." ^ id, status))
      else if legal_C_Id? id then
        (string id, status)
      else
        (string id, reportError ("illegal C id: " ^ id, status))

    | _ -> 
      %% Some kind of term we don't handle (yet?)
      (string "??", 
       reportError ("Unrecognized kind of primitive term: " ^ anyToString fun, 
                    status))

 %% ========================================================================
 %% Explicit numeric constants (Hex, Oct, Dec)
 %% ========================================================================

 op printNumericConstantAsC (status : CGenStatus, suffix : String, tm : MSTerm, radix : MSTerm) 
  : CPrecedence * Pretty * CGenStatus = 
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
      (CPrecedence_PRIMARY, 
       string (case radix of
                 | Fun (Embed (Qualified(_,"hex"), _), _, _) -> hex (n, suffix)
                 | Fun (Embed (Qualified(_,"oct"), _), _, _) -> oct (n, suffix)
                 | Fun (Embed (Qualified(_,"dec"), _), _, _) -> dec (n, suffix)
                 | _                            -> dec (n, suffix)), % default to dec ??
       status)
    | _ -> 
      %% ?? can this happen?
      (CPrecedence_PRIMARY, string "??", reportError ("no Nat value for " ^ printTerm tm, status))

 %% ========================================================================
 %% Main print routine for terms. (This comment is somewhat out-of-date. -EWS)
 %%
 %%  For vars, prints name (if legal)
 %%
 %%  For typed terms, recurs into untyped term
 %%
 %%  For primitive terms (Fun's):
 %%    Prints implicit Nat/Char/String constants using printPrimitiveAsC.
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

%TODO Can we do this in Metaslang before calling the C generator?
 op uncurry (t1 : MSTerm, args : MSTerms) : CFunCall =
  case t1 of
    | Apply (t2, t3, _) -> uncurry (t2, [t3] ++ args)
    | _ -> {f = t1, args = args}

%TODO Can we do this in Metaslang before calling the C generator?
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

 op wrapBraces (pretty : Pretty) : Pretty = 
  blockNone (0, [(0, string "{"), (0, pretty), (0, string "}")])

 op printTermsAsCExpressions (status       : CGenStatus, 
                       pretty_open  : Line,
                       terms        : MSTerms,
                       pretty_close : Line)
  : Lines * CGenStatus =
  let (lines, _, status) =
      foldl (fn ((lines, first?, status), tm) ->
               let (block, status) = printTermAsCExpression (status, tm, CPrecedence_NO_PARENS) in 
               let line = (0, block) in
               let lines = lines ++ (if first? then [line] else [L0_comma_space, line]) in
               (lines, false, status))
            ([pretty_open], true, status)
            terms
  in
  (lines ++ [pretty_close], status)

%% Pretty-print a C expression (not a statement).
%% If precedence of tm is less than expected precedence, wrap parens.
%% This does not put in the 'return'; the caller must do that.
 op printTermAsCExpression (status   : CGenStatus, %%this seems to be threaded through
                  	    tm       : MSTerm,
                  	    expected : CPrecedence
                  	    )
  : Pretty * CGenStatus = 

  case tm of

    | Var ((id, _), _) -> 
      if legal_C_Id? id then
        (string id, status)
      else
        (string "", reportError ("illegal C variable name: " ^ id, status))

    | Fun (fun, _, _) -> 
      let (pretty, status) = printPrimitiveAsC  (status, fun) in
      (pretty, status)

    | TypedTerm  (t1, _, _) -> 
      printTermAsCExpression (status, t1, expected)

    | IfThenElse (t1, t2, t3, _) -> 

        %% ==============================================================================
        %% [C99 6.5.15 "Conditional operator"] aka the ?: operator
        %% ==============================================================================

        let (p1, status) = printTermAsCExpression (status, t1, CPrecedence_LOR) in  
        let (p2, status) = printTermAsCExpression (status, t2, CPrecedence_EXPR) in  
        let (p3, status) = printTermAsCExpression (status, t3, CPrecedence_COND) in  

        (blockLinear (0, [(0, p1),
                          (2, blockNone (0, [L0_expr_then, (0, p2)])), 
                          (2, blockNone (0, [L0_expr_else, (0, p3)]))]),
         status)

    | Apply (t1, t2, _) -> 
      let {f, args} = uncurry (t1, [t2])     in
      let args      = flattenRecordArgs args in
      let fixity    = cfixity (status, f)    in
      let (result, pretty, status) =
          case (fixity, args) of

            | (Call, args) ->

              %% ==============================================================================
              %% [C99 6.5.2 "Postfix operators"]
              %% ==============================================================================

              let (pretty_fn, status) = printTermAsCExpression (status, f, CPrecedence_POST)          in % [C99 6.5.2]
              let (lines,     status) = printTermsAsCExpressions (status, L0_lparen, args, L0_rparen) in
              let lines = [(0, pretty_fn)] ++ lines in
              (CPrecedence_CALL, blockNone (0, lines), status)
              
            | (Unary c_str, [arg]) ->
              
              %% ==============================================================================
              %% [C99 6.5.3 "Unary operators"]
              %% ==============================================================================

              let (p1, status) = printTermAsCExpression (status, arg, CPrecedence_UNARY) in
              let lines = [(0, string c_str), (0, p1)] in
              (CPrecedence_UNARY, blockNone (0, lines), status)
              
            | (Postfix c_str, [arg]) ->

              %% ==============================================================================
              %% [C99 6.5.2 "Postfix operators"]
              %% ==============================================================================

              let (p1, status) = printTermAsCExpression (status, arg, CPrecedence_POST) in
              let lines = [(0, p1), (0, string c_str)] in
              (CPrecedence_POST, blockNone (0, lines), status)
              
            | (Cast c_str, [arg]) ->

              %% ==============================================================================
              %% [C99 6.5.2 "Postfix operators"]
              %% ==============================================================================

              let (p1, status) = printTermAsCExpression (status, arg, CPrecedence_CAST) in
              let lines = [(0, string c_str), (0, p1)] in
              (CPrecedence_CAST, blockNone (0, lines), status)
              
            | (Infix fixity, [arg1, arg2]) ->

              %% ==============================================================================
              %% [C99 ... misc sections]
              %% ==============================================================================

              let (p1, status) = printTermAsCExpression (status, arg1, fixity.left)  in
              let (p2, status) = printTermAsCExpression (status, arg2, fixity.right) in
              let lines = [(0, p1),
                           (0, blockNone (0, [L0_space, (0, string fixity.operator), L0_space])),
                           (0, p2)]
              in
              (fixity.result, blockLinear (0, lines), status)
              
            | (Constant suffix, [tm, radix]) -> 

              %% ==============================================================================
              %% [C99 6.4.4 "Constants"]
              %% ==============================================================================

              %% ------------------------------------------------------------
              %% [C99 6.4.4.1 "Integer constants"]
              %% ------------------------------------------------------------

              printNumericConstantAsC (status, suffix, tm, radix)
              
            | (Subscript, array :: indices) ->

              %% ==============================================================================
              %% [C99 6.5.2 "Postfix operators"]
              %% ==============================================================================

              let (pretty_array_name, status) = printTermAsCExpression (status, array, CPrecedence_POST) in % [C99 6.5.2]
              let (lines, status) = printTermsAsCExpressions (status, L0_lsquare, reverse indices, L0_rsquare) in
              let lines = [(0, pretty_array_name)] ++ lines in
              (CPrecedence_SUBSCRIPT, blockNone (0, lines), status)
              
            | (NoOp, [t1]) ->

              %% ==============================================================================
              %% The inner call to printTermAsCExp will handle parens, so there is never any 
              %% need to add more now.
              %% ==============================================================================

              let (p1, status) = printTermAsCExpression (status, t1, expected) in
              (CPrecedence_HAVE_PARENS, p1, status) 
              
            | (Illegal error_msg, _) ->
              (CPrecedence_NO_PARENS, string "??", reportError (error_msg, status))

            | _ ->
              %% This should be impossible.
              (CPrecedence_NO_PARENS, string "impossible", reportError ("impossible", status))
      in
      let pretty = 
          if result < expected then
            blockNone (0, [L0_lparen, (0, pretty), L0_rparen])
          else
            pretty
      in
      (pretty, status)

    | Let (bindings, body, _) -> 
      (string "??", reportError ("We do not allow let terms inside expressions (they must be at the statement level): " ^ printTerm tm, status))

    %% Some kind of term not handled (yet?):
    | _ -> 
      (string "??", reportError ("unrecognized term: " ^ printTerm tm, status))


%% each entry is a pair of a local variable name and its type.
type LocalVarInfo = List (Id * Id)

 %% Translate the body of an op to C.  In general, we expect an op's body to be
 %% a nest of IfThenElses and Lets, with expressions at the leaves.

 op printTermAsCStatement (status   : CGenStatus, %%this seems to be threaded through
                           tm       : MSTerm
                           )
  : Pretty
    * Bool         %% flag for whether it is a compound statement
    * CGenStatus 
    * LocalVarInfo %% names and types of local variables (from Lets)
= 

  case tm of

    | TypedTerm  (t1, _, _) -> 
      printTermAsCStatement (status, t1)

    | Pi (_, t1, _) -> 
      printTermAsCStatement (status, t1)

    | And (t1 :: _, _) -> 
      printTermAsCStatement (status, t1)

    | IfThenElse (t1, t2, t3, _) -> 

      %% ==============================================================================
      %% [C99 6.8.4.1 "The if statement"]
      %% ==============================================================================

      let (p1,            status) = printTermAsCExpression (status, t1, CPrecedence_REQUIRE_PARENS) in
      let (p2, compound2, status, vars2) = printTermAsCStatement (status, t2)  in
      let (p3, compound3, status, vars3) = printTermAsCStatement (status, t3)  in

      let p2 = if compound2 then wrapBraces p2 else p2 in
      let p3 = if compound3 then wrapBraces p3 else p3 in
      (blockAll (0, [(0, blockNone (0, [L0_if, (0, p1), L0_space])),
                     (2, p2), 
                     L0_else,
                     (2, p3)]),
       false,  %%not compound
       status,
       vars2++vars3)

    | Let (bindings, body, _) -> 
        (case bindings of
         | [] -> (string "??", false, reportError ("We do not handle let terms with no bindings: " ^ printTerm tm, status), [])
	 | (pattern, term)::[] ->
           (case pattern of
           | VarPat ((id, ty), _) ->
             (case ty of 
             | Base (typeqid, [], _) ->  %FIXME What is this list following the qid?  It usually seems to be empty.
                (case getCTypeName(typeqid, status) of
                 | None -> 
                   (string "??", false, reportError ("Could not translate the type of a let variable to a C type: " ^ printTerm tm, status), [])
                 | Some typeid ->
                   (let (prettyletbody, level, status, vars) = printTermAsCStatement (status, body) in %FIXME think about parens
                   (let (prettyterm, status) = printTermAsCExpression (status, term, CPrecedence_NO_PARENS) in
                     (blockAll (0, [(0, blockNone(0, [(0, string id), (0, string " = "), (0, prettyterm),  (0, string ";")])), (0, prettyletbody)]),
                               true, % the local variable assignment makes this a compound statement
                               status,
		               (id, typeid)::vars
			       ))))
             | _ -> (string "??", false, reportError ("We do not handle let terms where the type of the bound variable is not a base type: " ^ printTerm tm, status), []))
	   | _ -> (string "??", false, reportError ("We do not handle let terms where the pattern is not a variable: " ^ printTerm tm, status), []))
	 | _ -> (string "??", false, reportError ("We do not handle let terms with more than one binding: " ^ printTerm tm, status), []))

    %% It is not an IfThenElse or a Let, so it must be an expression.  We will translate it and wrap it in a return.
    %% All of the leaves of the IfThenElse / Let nest will be expressions.
    | _ -> let (pretty, status) = printTermAsCExpression (status, tm, CPrecedence_NO_PARENS) in
           (wrapReturn pretty, false, status, [])


endspec
