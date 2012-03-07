PrintAsC qualifying spec 

 import PrintAsCUtils

 %% ========================================================================
 %%  CFixity describes the pattern and keyword for a term to be applied.
 %%  If the operator is clearly illegal, we report that and return None.
 %%  If the term is complex (not a Fun) we punt and return Some Unknown.
 %% ========================================================================

 type CLevel = | Statement
               | Expression

 type CFixity = | Prefix         String   % 
                | PrefixNoParens String
                | Postfix        String
                | Infix          String
                | Cast           String   % prefix, could be ""
                | Constant       String   % suffix, could be ""
                | ArrayAccess 
                | Illegal        String

 op cfixity (status : CGenStatus, tm : MSTerm) : CFixity =
  let plainCharsAreSigned? = status.plainCharsAreSigned? in
  case tm of 
    | Fun (fun, _, _) -> 
      (case fun of
         | And         -> Infix "&&"
         | Or          -> Infix "||"
         | Equals      -> Infix "=="  % for non integer values
         | NotEquals   -> Infix "!="  % for non integer values
         | Project   f -> 
           if legal_C_Id? f then
             Postfix ("." ^ f)
           else
             Illegal ("name of projection is not a legal C id: " ^ f)
         | Op (qid as Qualified ("C", id), _) ->
           (case id of
              
              %% ============================================================
              %% Constant operators
              %% ============================================================
              
              | "sintConstant"    -> Constant ""
              | "slongConstant"   -> Constant "L"
              | "sllongConstant"  -> Constant "LL"
                
              | "uintConstant"    -> Constant "U"
              | "ulongConstant"   -> Constant "UL"
              | "ullongConstant"  -> Constant "ULL"
                
              %% ============================================================
              %% Prefix operators: unary +, unary -, ~, !
              %% ============================================================
              
              %% unary +
              | "+_1_sint"        -> PrefixNoParens "+"
              | "+_1_slong"       -> PrefixNoParens "+"
              | "+_1_sllong"      -> PrefixNoParens "+"
              | "+_1_uint"        -> PrefixNoParens "+"
              | "+_1_ulong"       -> PrefixNoParens "+"
              | "+_1_ullong"      -> PrefixNoParens "+"
                
              %% unary -
              | "-_1_sint"        -> PrefixNoParens "-"
              | "-_1_slong"       -> PrefixNoParens "-"
              | "-_1_sllong"      -> PrefixNoParens "-"
              | "-_1_uint"        -> PrefixNoParens "-"
              | "-_1_ulong"       -> PrefixNoParens "-"
              | "-_1_ullong"      -> PrefixNoParens "-"
                
              %% ~
              | "~_1_sint"        -> PrefixNoParens "~"
              | "~_1_slong"       -> PrefixNoParens "~"
              | "~_1_sllong"      -> PrefixNoParens "~"
              | "~_1_uint"        -> PrefixNoParens "~"
              | "~_1_ulong"       -> PrefixNoParens "~"
              | "~_1_ullong"      -> PrefixNoParens "~"
                
              %% !
              | "!_1_char"        -> PrefixNoParens "!"
              | "!_1_schar"       -> PrefixNoParens "!"
              | "!_1_uchar"       -> PrefixNoParens "!"
              | "!_1_sint"        -> PrefixNoParens "!"
              | "!_1_uint"        -> PrefixNoParens "!"
              | "!_1_slong"       -> PrefixNoParens "!"
              | "!_1_ulong"       -> PrefixNoParens "!"
              | "!_1_sllong"      -> PrefixNoParens "!"
              | "!_1_ullong"      -> PrefixNoParens "!"

              %% ============================================================
              %% Postfix operators
              %% ============================================================

              %% ============================================================
              %% Infix operators: arithmetic, comparison, bitwise, logical
              %% ============================================================

              %% ---------------------------------------------------
              %% Infix arithmetic operations: *, /, %, +, -, <<, >>
              %% ---------------------------------------------------

              %% *
              | "*_sint"           -> Infix "*"
              | "*_slong"          -> Infix "*"
              | "*_sllong"         -> Infix "*"
              | "*_uint"           -> Infix "*"
              | "*_ulong"          -> Infix "*"
              | "*_ullong"         -> Infix "*"

              %% /
              | "/_sint"           -> Infix "/"
              | "/_slong"          -> Infix "/"
              | "/_sllong"         -> Infix "/"
              | "/_uint"           -> Infix "/"
              | "/_ulong"          -> Infix "/"
              | "/_ullong"         -> Infix "/"

              %% %
              | "//_sint"          -> Infix "%"
              | "//_slong"         -> Infix "%"
              | "//_sllong"        -> Infix "%"
              | "//_uint"          -> Infix "%"
              | "//_ulong"         -> Infix "%"
              | "//_ullong"        -> Infix "%"

              %% +
              | "+_sint"           -> Infix "+"
              | "+_slong"          -> Infix "+"
              | "+_sllong"         -> Infix "+"
              | "+_uint"           -> Infix "+"
              | "+_ulong"          -> Infix "+"
              | "+_ullong"         -> Infix "+"

              %% -
              | "-_sint"           -> Infix "-"
              | "-_slong"          -> Infix "-"
              | "-_sllong"         -> Infix "-"
              | "-_uint"           -> Infix "-"
              | "-_ulong"          -> Infix "-"
              | "-_ullong"         -> Infix "-"

              %% << (6*6 versions)
              | "<<_sint_sint"     -> Infix "<<"
              | "<<_sint_slong"    -> Infix "<<"
              | "<<_sint_sllong"   -> Infix "<<"
              | "<<_sint_uint"     -> Infix "<<"
              | "<<_sint_ulong"    -> Infix "<<"
              | "<<_sint_ullong"   -> Infix "<<"

              | "<<_slong_sint"    -> Infix "<<"
              | "<<_slong_slong"   -> Infix "<<"
              | "<<_slong_sllong"  -> Infix "<<"
              | "<<_slong_uint"    -> Infix "<<"
              | "<<_slong_ulong"   -> Infix "<<"
              | "<<_slong_ullong"  -> Infix "<<"

              | "<<_sllong_sint"   -> Infix "<<"
              | "<<_sllong_slong"  -> Infix "<<"
              | "<<_sllong_sllong" -> Infix "<<"
              | "<<_sllong_uint"   -> Infix "<<"
              | "<<_sllong_ulong"  -> Infix "<<"
              | "<<_sllong_ullong" -> Infix "<<"

              | "<<_uint_sint"     -> Infix "<<"
              | "<<_uint_slong"    -> Infix "<<"
              | "<<_uint_sllong"   -> Infix "<<"
              | "<<_uint_uint"     -> Infix "<<"
              | "<<_uint_ulong"    -> Infix "<<"
              | "<<_uint_ullong"   -> Infix "<<"

              | "<<_ulong_sint"    -> Infix "<<"
              | "<<_ulong_slong"   -> Infix "<<"
              | "<<_ulong_sllong"  -> Infix "<<"
              | "<<_ulong_uint"    -> Infix "<<"
              | "<<_ulong_ulong"   -> Infix "<<"
              | "<<_ulong_ullong"  -> Infix "<<"

              | "<<_ullong_sint"   -> Infix "<<"
              | "<<_ullong_slong"  -> Infix "<<"
              | "<<_ullong_sllong" -> Infix "<<"
              | "<<_ullong_uint"   -> Infix "<<"
              | "<<_ullong_ulong"  -> Infix "<<"
              | "<<_ullong_ullong" -> Infix "<<"

              %% >> (6*6 versions)
              | ">>_sint_sint"     -> Infix ">>"
              | ">>_sint_slong"    -> Infix ">>"
              | ">>_sint_sllong"   -> Infix ">>"
              | ">>_sint_uint"     -> Infix ">>"
              | ">>_sint_ulong"    -> Infix ">>"
              | ">>_sint_ullong"   -> Infix ">>"

              | ">>_slong_sint"    -> Infix ">>"
              | ">>_slong_slong"   -> Infix ">>"
              | ">>_slong_sllong"  -> Infix ">>"
              | ">>_slong_uint"    -> Infix ">>"
              | ">>_slong_ulong"   -> Infix ">>"
              | ">>_slong_ullong"  -> Infix ">>"

              | ">>_sllong_sint"   -> Infix ">>"
              | ">>_sllong_slong"  -> Infix ">>"
              | ">>_sllong_sllong" -> Infix ">>"
              | ">>_sllong_uint"   -> Infix ">>"
              | ">>_sllong_ulong"  -> Infix ">>"
              | ">>_sllong_ullong" -> Infix ">>"

              | ">>_uint_sint"     -> Infix ">>"
              | ">>_uint_slong"    -> Infix ">>"
              | ">>_uint_sllong"   -> Infix ">>"
              | ">>_uint_uint"     -> Infix ">>"
              | ">>_uint_ulong"    -> Infix ">>"
              | ">>_uint_ullong"   -> Infix ">>"

              | ">>_ulong_sint"    -> Infix ">>"
              | ">>_ulong_slong"   -> Infix ">>"
              | ">>_ulong_sllong"  -> Infix ">>"
              | ">>_ulong_uint"    -> Infix ">>"
              | ">>_ulong_ulong"   -> Infix ">>"
              | ">>_ulong_ullong"  -> Infix ">>"

              | ">>_ullong_sint"   -> Infix ">>"
              | ">>_ullong_slong"  -> Infix ">>"
              | ">>_ullong_sllong" -> Infix ">>"
              | ">>_ullong_uint"   -> Infix ">>"
              | ">>_ullong_ulong"  -> Infix ">>"
              | ">>_ullong_ullong" -> Infix ">>"

              %% ---------------------------------------------------
              %% Infix arithmetic comparisons: <, >, <=, >=, ==, !=
              %% ---------------------------------------------------

              %% <
              | "<_sint"     -> Infix "<"
              | "<_slong"    -> Infix "<"
              | "<_sllong"   -> Infix "<"
              | "<_uint"     -> Infix "<"
              | "<_ulong"    -> Infix "<"
              | "<_ullong"   -> Infix "<"

              %% >
              | ">_sint"     -> Infix ">"
              | ">_slong"    -> Infix ">"
              | ">_sllong"   -> Infix ">"
              | ">_uint"     -> Infix ">"
              | ">_ulong"    -> Infix ">"
              | ">_ullong"   -> Infix ">"

              %% <=
              | "<=_sint"     -> Infix "<="
              | "<=_slong"    -> Infix "<="
              | "<=_sllong"   -> Infix "<="
              | "<=_uint"     -> Infix "<="
              | "<=_ulong"    -> Infix "<="
              | "<=_ullong"   -> Infix "<="

              %% >=
              | ">=_sint"     -> Infix ">="
              | ">=_slong"    -> Infix ">="
              | ">=_sllong"   -> Infix ">="
              | ">=_uint"     -> Infix ">="
              | ">=_ulong"    -> Infix ">="
              | ">=_ullong"   -> Infix ">="

              %% ==
              | "==_sint"     -> Infix "=="
              | "==_slong"    -> Infix "=="
              | "==_sllong"   -> Infix "=="
              | "==_uint"     -> Infix "=="
              | "==_ulong"    -> Infix "=="
              | "==_ullong"   -> Infix "=="

              %% !=
              | "!=_sint"     -> Infix "!="
              | "!=_slong"    -> Infix "!="
              | "!=_sllong"   -> Infix "!="
              | "!=_uint"     -> Infix "!="
              | "!=_ulong"    -> Infix "!="
              | "!=_ullong"   -> Infix "!="

              %% ---------------------------------------------------
              %% Infix bitwise operations: &, ^, |
              %% ---------------------------------------------------

              %% &
              | "&_sint"      -> Infix "&"
              | "&_slong"     -> Infix "&"
              | "&_sllong"    -> Infix "&"
              | "&_uint"      -> Infix "&"
              | "&_ulong"     -> Infix "&"
              | "&_ullong"    -> Infix "&"

              %% ^
              | "^_sint"      -> Infix "^"
              | "^_slong"     -> Infix "^"
              | "^_sllong"    -> Infix "^"
              | "^_uint"      -> Infix "^"
              | "^_ulong"     -> Infix "^"
              | "^_ullong"    -> Infix "^"

              %% |
              | "|_sint"      -> Infix "|"
              | "|_slong"     -> Infix "|"
              | "|_sllong"    -> Infix "|"
              | "|_uint"      -> Infix "|"
              | "|_ulong"     -> Infix "|"
              | "|_ullong"    -> Infix "|"

              %% ---------------------------------------------------
              %% Infix logical operations: &&, ||
              %% ---------------------------------------------------

              %% && -- primitive MetaSlang operator -- see above
              %% || -- primitive MetaSlang operator -- see above

              %% ============================================================
              %% Array access
              %% ============================================================

              | "@_char"          -> ArrayAccess
              | "@_schar"         -> ArrayAccess
              | "@_uchar"         -> ArrayAccess

              | "@_sshort"        -> ArrayAccess
              | "@_ushort"        -> ArrayAccess

              | "@_sint"          -> ArrayAccess
              | "@_uint"          -> ArrayAccess

              | "@_slong"         -> ArrayAccess
              | "@_ulong"         -> ArrayAccess

              | "@_sllong"        -> ArrayAccess
              | "@_ullong"        -> ArrayAccess

              %% ============================================================
              %% Structure operators
              %% ============================================================

              %% ============================================================
              %% Conversion operators among the 11 integer types:
              %%    char, uchar, schar, ushort, sshort, uint, sint, ulong, slong, ullong, sllong
              %%    110 operators (11 types * 10 other types)
              %% ============================================================

              %% cast to char
              | "charOfUChar"     -> Cast (if plainCharsAreSigned? then " (char) " else "")
              | "charOfUshort"    -> Cast " (char) "
              | "charOfUint"      -> Cast " (char) "
              | "charOfUlong"     -> Cast " (char) "
              | "charOfUllong"    -> Cast " (char) "
              | "charOfSchar"     -> Cast (if plainCharsAreSigned? then "" else " (char) ")
              | "charOfSshort"    -> Cast " (char) "
              | "charOfSint"      -> Cast " (char) "
              | "charOfSlong"     -> Cast " (char) "
              | "charOfSllong"    -> Cast " (char) "

              %% cast to unsigned char
              | "ucharOfChar"     -> Cast (if plainCharsAreSigned? then " (unsigned char) " else "")
              | "ucharOfUshort"   -> Cast " (unsigned char) "
              | "ucharOfUint"     -> Cast " (unsigned char) "
              | "ucharOfUlong"    -> Cast " (unsigned char) "
              | "ucharOfUllong"   -> Cast " (unsigned char) "
              | "ucharOfSchar"    -> Cast " (unsigned char) "
              | "ucharOfSshort"   -> Cast " (unsigned char) "
              | "ucharOfSint"     -> Cast " (unsigned char) "
              | "ucharOfSlong"    -> Cast " (unsigned char) "
              | "ucharOfSllong"   -> Cast " (unsigned char) "

              %% cast to unsigned short
              | "ushortOfChar"    -> Cast (if plainCharsAreSigned? then " (unsigned short) " else "")
              | "ushortOfUChar"   -> Cast ""        
              | "ushortOfUint"    -> Cast " (unsigned short) "
              | "ushortOfUlong"   -> Cast " (unsigned short) "
              | "ushortOfUllong"  -> Cast " (unsigned short) "
              | "ushortOfSchar"   -> Cast " (unsigned short) "
              | "ushortOfSshort"  -> Cast " (unsigned short) "
              | "ushortOfSint"    -> Cast " (unsigned short) "
              | "ushortOfSlong"   -> Cast " (unsigned short) "
              | "ushortOfSllong"  -> Cast " (unsigned short) "

              %% cast to unsigned int
              | "uintOfChar"      -> Cast (if plainCharsAreSigned? then " (unsigned int) " else "")
              | "uintOfUChar"     -> Cast "" 
              | "uintOfUshort"    -> Cast "" 
              | "uintOfUlong"     -> Cast " (unsigned int) " 
              | "uintOfUllong"    -> Cast " (unsigned int) "
              | "uintOfSchar"     -> Cast " (unsigned int) "
              | "uintOfSshort"    -> Cast " (unsigned int) "
              | "uintOfSint"      -> Cast " (unsigned int) "
              | "uintOfSlong"     -> Cast " (unsigned int) "
              | "uintOfSllong"    -> Cast " (unsigned int) "

              %% cast to unsigned long
              | "ulongOfChar"     -> Cast (if plainCharsAreSigned? then " (unsigned long) " else "")
              | "ulongOfUChar"    -> Cast "" 
              | "ulongOfUshort"   -> Cast ""
              | "ulongOfUint"     -> Cast ""
              | "ulongOfUllong"   -> Cast " (unsigned long) "
              | "ulongOfSchar"    -> Cast " (unsigned long) "
              | "ulongOfSshort"   -> Cast " (unsigned long) "
              | "ulongOfSint"     -> Cast " (unsigned long) "
              | "ulongOfSlong"    -> Cast " (unsigned long) "
              | "ulongOfSllong"   -> Cast " (unsigned long) "
 
              %% cast to unsigned long long
              | "ullongOfChar"    -> Cast (if plainCharsAreSigned? then " (unsigned long long) " else "")
              | "ullongOfUChar"   -> Cast ""
              | "ullongOfUshort"  -> Cast ""
              | "ullongOfUint"    -> Cast ""
              | "ullongOfUlong"   -> Cast ""
              | "ullongOfSchar"   -> Cast " (unsigned long long) "
              | "ullongOfSshort"  -> Cast " (unsigned long long) "
              | "ullongOfSint"    -> Cast " (unsigned long long) "
              | "ullongOfSlong"   -> Cast " (unsigned long long) "
              | "ullongOfSllong"  -> Cast " (unsigned long long) "

              %% cast to signed char
              | "scharOfChar"     -> Cast (if plainCharsAreSigned? then "" else " (signed char) ")
              | "scharOfUChar"    -> Cast " (signed char) "
              | "scharOfUshort"   -> Cast " (signed char) "
              | "scharOfUint"     -> Cast " (signed char) "
              | "scharOfUlong"    -> Cast " (signed char) "
              | "scharOfUllong"   -> Cast " (signed char) "
              | "scharOfSshort"   -> Cast " (signed char) "
              | "scharOfSint"     -> Cast " (signed char) "
              | "scharOfSlong"    -> Cast " (signed char) "
              | "scharOfSllong"   -> Cast " (signed char) "

              %% cast to signed short
              | "sshortOfChar"    -> Cast (if plainCharsAreSigned? then "" else " (signed short) ")
              | "sshortOfUChar"   -> Cast " (short) "
              | "sshortOfUshort"  -> Cast " (short) "
              | "sshortOfUint"    -> Cast " (short) "
              | "sshortOfUlong"   -> Cast " (short) "
              | "sshortOfUllong"  -> Cast " (short) "
              | "sshortOfSchar"   -> Cast ""
              | "sshortOfSint"    -> Cast " (short) "
              | "sshortOfSlong"   -> Cast " (short) "
              | "sshortOfSllong"  -> Cast " (short) "

              %% cast to signed int
              | "sintOfChar"      -> Cast (if plainCharsAreSigned? then "" else " (signed int) ")
              | "sintOfUChar"     -> Cast " (signed int) "
              | "sintOfUshort"    -> Cast " (signed int) "
              | "sintOfUint"      -> Cast " (signed int) "
              | "sintOfUlong"     -> Cast " (signed int) "
              | "sintOfUllong"    -> Cast " (signed int) "
              | "sintOfSchar"     -> Cast ""
              | "sintOfSshort"    -> Cast ""
              | "sintOfSlong"     -> Cast " (signed int) "
              | "sintOfSllong"    -> Cast " (signed int) "
 
              %% cast to signed long
              | "slongOfChar"     -> Cast (if plainCharsAreSigned? then "" else " (unsigned long) ")
              | "slongOfUChar"    -> Cast " (unsigned long) "
              | "slongOfUshort"   -> Cast " (unsigned long) "
              | "slongOfUint"     -> Cast " (unsigned long) "
              | "slongOfUlong"    -> Cast " (unsigned long) "
              | "slongOfUllong"   -> Cast " (unsigned long) "
              | "slongOfSchar"    -> Cast ""
              | "slongOfSshort"   -> Cast ""
              | "slongOfSint"     -> Cast ""
              | "slongOfSllong"   -> Cast " (unsigned long) "

              %% cast to signed long long
              | "sllongOfChar"    -> Cast (if plainCharsAreSigned? then "" else " (signed long long) ")
              | "sllongOfUChar"   -> Cast " (signed long long) "
              | "sllongOfUshort"  -> Cast " (signed long long) "
              | "sllongOfUint"    -> Cast " (signed long long) "
              | "sllongOfUlong"   -> Cast " (signed long long) "
              | "sllongOfUllong"  -> Cast " (signed long long) "
              | "sllongOfSchar"   -> Cast ""
              | "sllongOfSshort"  -> Cast ""
              | "sllongOfSint"    -> Cast ""
              | "sllongOfSlong"   -> Cast ""

           (*
            * These should not appear in final spec to be printed.
            *
            * | "mathIntOfChar"   -> Cast MathInt  
            * | "mathIntOfUchar"  -> Cast MathInt
            * | "mathIntOfUshort" -> Cast MathInt  
            * | "mathIntOfUint"   -> Cast MathInt  
            * | "mathIntOfUlong"  -> Cast MathInt  
            * | "mathIntOfUllong" -> Cast MathInt  
            * | "mathIntOfSchar"  -> Cast MathInt  
            * | "mathIntOfSshort" -> Cast MathInt  
            * | "mathIntOfSint"   -> Cast MathInt  
            * | "mathIntOfSlong"  -> Cast MathInt  
            * | "mathIntOfSllong" -> Cast MathInt  
            *
            * | "charOfMathInt"   -> Cast " (char) "     
            * | "ucharOfMathInt"  -> Cast " (unsigned char) "    
            * | "ushortOfMathInt" -> Cast " (unsigned short) "   
            * | "uintOfMathInt"   -> Cast " (unsigned int) "     
            * | "ulongOfMathInt"  -> Cast " (unsigned long) "    
            * | "ullongOfMathInt" -> Cast " (unsigned long long) "   
            * | "scharOfMathInt"  -> Cast " (signed char) "    
            * | "sshortOfMathInt" -> Cast " (short) "   
            * | "sintOfMathInt"   -> Cast " (signed int) "     
            * | "slongOfMathInt"  -> Cast " (unsigned long) "    
            * | "sllongOfMathInt" -> Cast " (signed long long) "   
            *)
 
              | _  -> 
                if legal_C_Id? id then
                  Prefix id
                else
                  Illegal ("illegal id for C op: " ^ show qid))
         | Op (qid as Qualified(q,id), _) ->
           if legal_C_Id? id then
             Prefix (if q in? [UnQualified, "C"] then id else id)    % q ^ "_" ^ id
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
       reportError ("printFunAsC", "unrecognized fun: " ^ anyToString fun, 
                    status))

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
            | "u" | n <= 0x7FFF -> ""
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
       reportError ("printNumericConstantAsC", "no nat value for " ^ printTerm tm, status))

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
  blockNone (0, [(0, string "  return "), (0, pretty), (0, string ";")])

 op printTermAsCExp (status : CGenStatus, tm : MSTerm) : Pretty * CGenStatus = 
  let (p, _, status) = printTermAsC (status : CGenStatus, tm : MSTerm, Expression) in
  (p, status)

 op printTermAsC (status : CGenStatus, tm : MSTerm, level : CLevel) : Pretty * Bool * CGenStatus = 
  case tm of

    | Var       ((id,  _), _) -> 
      if legal_C_Id? id then
        (string id, false, status)
      else
        (string "", false, reportError ("printTermAsC", "illegal var name: " ^ id, status))

    | Fun        (fun, _,     _) -> 
      let (pretty, status) = printFunAsC  (status, fun) in
      (pretty, false, status)

    | TypedTerm  (t1, _,      _) -> 
      printTermAsC (status, t1, level)

    | IfThenElse (t1, t2, t3, _) -> 
      let (p1, _,            status) = printTermAsC (status, t1, Expression) in
      let p1                         = blockNone (0, [(0, string "("), (0, p1), (0, string ")")]) in
      let (p2, p2hasreturn?, status) = printTermAsC (status, t2, level) in
      let (p3, p3hasreturn?, status) = printTermAsC (status, t3, level) in
      if level = Statement then
        let p2 = if p2hasreturn? then p2 else wrapReturn p2 in
        let p3 = if p3hasreturn? then p3 else wrapReturn p3 in
        (blockLinear (0, [(0, blockNone (0, [(0, string "if "), (0, p1)])),
                          (0, p2), 
                          (0, string " else "), 
                          (0, p3)]),
         true,
         status)
      else
        (blockLinear (0, [(0, p1), 
                          (0, blockNone (0, [(0, string " ? "), (0, p2)])), 
                          (0, blockNone (0, [(0, string " : "), (0, p3)]))]),
         false,
         status)

    | Apply      (t1, t2,     _) -> 
      (let {f, args} = uncurry (t1, [t2]) in
       let args   = flattenRecordArgs args in
       let fixity = cfixity (status, f)    in
       case (fixity, args) of

         | (Prefix c_str, args) ->
           let (blocks, status) =
               foldl (fn ((blocks, status), arg) ->
                        let (block, status) = printTermAsCExp (status, arg) in
                        (blocks ++ [block], status))
                     ([], status)
                     args
           in
           let pretty_args = 
               AnnTermPrinter.ppList (fn block -> block)
                                     (string "(", string ", ", string ")")
                                     blocks
           in
           (blockNone (0, 
                       [(0, string c_str),
                        (0, pretty_args)]),
            false,
            status)
           
         | (PrefixNoParens c_str, [arg]) ->
           let (pretty, status) = printTermAsCExp (status, arg) in
           (blockNone (0, 
                       [(0, string c_str),
                        (0, pretty)]),
            false,
            status)
           
         | (Postfix c_str, [arg]) ->
           let (pretty, status) = printTermAsCExp (status, arg) in
           (blockNone (0, 
                       [(0, pretty),
                        (0, string c_str)]),
            false,
            status)
           
         | (Infix c_str, [arg1, arg2]) ->
           let (p1, status) = printTermAsCExp (status, arg1) in
           let (p2, status) = printTermAsCExp (status, arg2) in
           (blockLinear (0, 
                         [(0, p1),
                          (0, string c_str),
                          (0, p2)]),
            false,
            status)
           
         | (Cast c_str, [arg]) ->
           let (pretty, status) = printTermAsCExp (status, arg) in
           (blockNone (0, 
                       [(0, string c_str),
                        (0, pretty)]),
            false,
            status)
           
         | (Constant suffix, [tm, radix]) -> 
           printNumericConstantAsC (status, suffix, tm, radix)
           
         | (ArrayAccess, array :: indices) ->
           let (blocks, status) = 
               foldl (fn ((blocks, status), index) ->
                        let (block, status) = printTermAsCExp (status, index) in
                        (blocks ++ [block], status))
                     ([], status)
                     (reverse indices)
           in
           let (pretty_array_name, status) = printTermAsCExp (status, array) in
           let pretty_indices =
               AnnTermPrinter.ppList (fn block -> block)
                                     (string "[", string ", ", string "]")
                                     blocks
           in
           (blockNone (0, 
                       [(0, pretty_array_name),
                        (0, pretty_indices)]),
            false,
            status)
           
         | (Illegal error_msg, _) ->
           (string "??",
            false,
            reportError ("printTermAsC", error_msg, status)))
                   
    | _ -> 
      (string "??",
       false,
       reportError ("printTermAsC", "unrecognized term: " ^ printTerm tm, status))

 %% ========================================================================

endspec
