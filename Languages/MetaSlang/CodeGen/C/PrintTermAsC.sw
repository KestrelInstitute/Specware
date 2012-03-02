PrintAsC qualifying spec 

 import PrintAsCUtils

 %% ========================================================================
 %%  CFixity describes the pattern and keyword for a term to be applied.
 %%  If the operator is clearly illegal, we report that and return None.
 %%  If the term is complex (not a Fun) we punt and return Some Unknown.
 %% ========================================================================

 type CFixity = | Prefix         String   % 
                | PrefixNoParens String
                | Postfix        String
                | Infix          String
                | Cast           String   % prefix, could be ""
                | Constant       String   % suffix, could be ""
                | ArrayAccess 
                | Unknown

 op cfixity (status : CGenStatus) (tm : MSTerm) : Option CFixity =
  let plainCharsAreSigned? = status.plainCharsAreSigned? in
  case tm of 
    | Fun (fun, _, _) -> 
      (case fun of
         | And         -> Some (Infix "&&")
         | Or          -> Some (Infix "||")
         | Equals      -> Some (Infix "==")  % for non integer values
         | NotEquals   -> Some (Infix "!=")  % for non integer values
         | Project   f -> 
           if legal_C_Id? f then
             Some (Postfix ("." ^ f))
           else
             let _ = writeLine ("Error in cfixity: name of projection is not legal C id: " ^ f) in
             None
         | Op (Qualified ("C", id), _) ->
           (case id of
              
              %% ============================================================
              %% Constant operators
              %% ============================================================
              
              | "sintConstant"    -> Some (Constant "")
              | "slongConstant"   -> Some (Constant "l")
              | "sllongConstant"  -> Some (Constant "ll")
                
              | "uintConstant"    -> Some (Constant "u")
              | "ulongConstant"   -> Some (Constant "lu")
              | "ullongConstant"  -> Some (Constant "llu")
                
              %% ============================================================
              %% Prefix operators: unary +, unary -, ~, !
              %% ============================================================
              
              %% unary +
              | "+_1_sint"        -> Some (PrefixNoParens "+")
              | "+_1_slong"       -> Some (PrefixNoParens "+")
              | "+_1_sllong"      -> Some (PrefixNoParens "+")
              | "+_1_uint"        -> Some (PrefixNoParens "+")
              | "+_1_ulong"       -> Some (PrefixNoParens "+")
              | "+_1_ullong"      -> Some (PrefixNoParens "+")
                
              %% unary -
              | "-_1_sint"        -> Some (PrefixNoParens "-")
              | "-_1_slong"       -> Some (PrefixNoParens "-")
              | "-_1_sllong"      -> Some (PrefixNoParens "-")
              | "-_1_uint"        -> Some (PrefixNoParens "-")
              | "-_1_ulong"       -> Some (PrefixNoParens "-")
              | "-_1_ullong"      -> Some (PrefixNoParens "-")
                
              %% ~
              | "~_1_sint"        -> Some (PrefixNoParens "~")
              | "~_1_slong"       -> Some (PrefixNoParens "~")
              | "~_1_sllong"      -> Some (PrefixNoParens "~")
              | "~_1_uint"        -> Some (PrefixNoParens "~")
              | "~_1_ulong"       -> Some (PrefixNoParens "~")
              | "~_1_ullong"      -> Some (PrefixNoParens "~")
                
              %% !
              | "!_1_char"        -> Some (PrefixNoParens "!")
              | "!_1_schar"       -> Some (PrefixNoParens "!")
              | "!_1_uchar"       -> Some (PrefixNoParens "!")
              | "!_1_sint"        -> Some (PrefixNoParens "!")
              | "!_1_uint"        -> Some (PrefixNoParens "!")
              | "!_1_slong"       -> Some (PrefixNoParens "!")
              | "!_1_ulong"       -> Some (PrefixNoParens "!")
              | "!_1_sllong"      -> Some (PrefixNoParens "!")
              | "!_1_ullong"      -> Some (PrefixNoParens "!")

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
              | "*_sint"           -> Some (Infix "*")
              | "*_slong"          -> Some (Infix "*")
              | "*_sllong"         -> Some (Infix "*")
              | "*_uint"           -> Some (Infix "*")
              | "*_ulong"          -> Some (Infix "*")
              | "*_ullong"         -> Some (Infix "*")

              %% /
              | "/_sint"           -> Some (Infix "/")
              | "/_slong"          -> Some (Infix "/")
              | "/_sllong"         -> Some (Infix "/")
              | "/_uint"           -> Some (Infix "/")
              | "/_ulong"          -> Some (Infix "/")
              | "/_ullong"         -> Some (Infix "/")

              %% %
              | "//_sint"          -> Some (Infix "%")
              | "//_slong"         -> Some (Infix "%")
              | "//_sllong"        -> Some (Infix "%")
              | "//_uint"          -> Some (Infix "%")
              | "//_ulong"         -> Some (Infix "%")
              | "//_ullong"        -> Some (Infix "%")

              %% +
              | "+_sint"           -> Some (Infix "+")
              | "+_slong"          -> Some (Infix "+")
              | "+_sllong"         -> Some (Infix "+")
              | "+_uint"           -> Some (Infix "+")
              | "+_ulong"          -> Some (Infix "+")
              | "+_ullong"         -> Some (Infix "+")

              %% -
              | "-_sint"           -> Some (Infix "-")
              | "-_slong"          -> Some (Infix "-")
              | "-_sllong"         -> Some (Infix "-")
              | "-_uint"           -> Some (Infix "-")
              | "-_ulong"          -> Some (Infix "-")
              | "-_ullong"         -> Some (Infix "-")

              %% << (6*6 versions)
              | "<<_sint_sint"     -> Some (Infix "<<")
              | "<<_sint_slong"    -> Some (Infix "<<")
              | "<<_sint_sllong"   -> Some (Infix "<<")
              | "<<_sint_uint"     -> Some (Infix "<<")
              | "<<_sint_ulong"    -> Some (Infix "<<")
              | "<<_sint_ullong"   -> Some (Infix "<<")

              | "<<_slong_sint"    -> Some (Infix "<<")
              | "<<_slong_slong"   -> Some (Infix "<<")
              | "<<_slong_sllong"  -> Some (Infix "<<")
              | "<<_slong_uint"    -> Some (Infix "<<")
              | "<<_slong_ulong"   -> Some (Infix "<<")
              | "<<_slong_ullong"  -> Some (Infix "<<")

              | "<<_sllong_sint"   -> Some (Infix "<<")
              | "<<_sllong_slong"  -> Some (Infix "<<")
              | "<<_sllong_sllong" -> Some (Infix "<<")
              | "<<_sllong_uint"   -> Some (Infix "<<")
              | "<<_sllong_ulong"  -> Some (Infix "<<")
              | "<<_sllong_ullong" -> Some (Infix "<<")

              | "<<_uint_sint"     -> Some (Infix "<<")
              | "<<_uint_slong"    -> Some (Infix "<<")
              | "<<_uint_sllong"   -> Some (Infix "<<")
              | "<<_uint_uint"     -> Some (Infix "<<")
              | "<<_uint_ulong"    -> Some (Infix "<<")
              | "<<_uint_ullong"   -> Some (Infix "<<")

              | "<<_ulong_sint"    -> Some (Infix "<<")
              | "<<_ulong_slong"   -> Some (Infix "<<")
              | "<<_ulong_sllong"  -> Some (Infix "<<")
              | "<<_ulong_uint"    -> Some (Infix "<<")
              | "<<_ulong_ulong"   -> Some (Infix "<<")
              | "<<_ulong_ullong"  -> Some (Infix "<<")

              | "<<_ullong_sint"   -> Some (Infix "<<")
              | "<<_ullong_slong"  -> Some (Infix "<<")
              | "<<_ullong_sllong" -> Some (Infix "<<")
              | "<<_ullong_uint"   -> Some (Infix "<<")
              | "<<_ullong_ulong"  -> Some (Infix "<<")
              | "<<_ullong_ullong" -> Some (Infix "<<")

              %% >> (6*6 versions)
              | ">>_sint_sint"     -> Some (Infix ">>")
              | ">>_sint_slong"    -> Some (Infix ">>")
              | ">>_sint_sllong"   -> Some (Infix ">>")
              | ">>_sint_uint"     -> Some (Infix ">>")
              | ">>_sint_ulong"    -> Some (Infix ">>")
              | ">>_sint_ullong"   -> Some (Infix ">>")

              | ">>_slong_sint"    -> Some (Infix ">>")
              | ">>_slong_slong"   -> Some (Infix ">>")
              | ">>_slong_sllong"  -> Some (Infix ">>")
              | ">>_slong_uint"    -> Some (Infix ">>")
              | ">>_slong_ulong"   -> Some (Infix ">>")
              | ">>_slong_ullong"  -> Some (Infix ">>")

              | ">>_sllong_sint"   -> Some (Infix ">>")
              | ">>_sllong_slong"  -> Some (Infix ">>")
              | ">>_sllong_sllong" -> Some (Infix ">>")
              | ">>_sllong_uint"   -> Some (Infix ">>")
              | ">>_sllong_ulong"  -> Some (Infix ">>")
              | ">>_sllong_ullong" -> Some (Infix ">>")

              | ">>_uint_sint"     -> Some (Infix ">>")
              | ">>_uint_slong"    -> Some (Infix ">>")
              | ">>_uint_sllong"   -> Some (Infix ">>")
              | ">>_uint_uint"     -> Some (Infix ">>")
              | ">>_uint_ulong"    -> Some (Infix ">>")
              | ">>_uint_ullong"   -> Some (Infix ">>")

              | ">>_ulong_sint"    -> Some (Infix ">>")
              | ">>_ulong_slong"   -> Some (Infix ">>")
              | ">>_ulong_sllong"  -> Some (Infix ">>")
              | ">>_ulong_uint"    -> Some (Infix ">>")
              | ">>_ulong_ulong"   -> Some (Infix ">>")
              | ">>_ulong_ullong"  -> Some (Infix ">>")

              | ">>_ullong_sint"   -> Some (Infix ">>")
              | ">>_ullong_slong"  -> Some (Infix ">>")
              | ">>_ullong_sllong" -> Some (Infix ">>")
              | ">>_ullong_uint"   -> Some (Infix ">>")
              | ">>_ullong_ulong"  -> Some (Infix ">>")
              | ">>_ullong_ullong" -> Some (Infix ">>")

              %% ---------------------------------------------------
              %% Infix arithmetic comparisons: <, >, <=, >=, ==, !=
              %% ---------------------------------------------------

              %% <
              | "<_sint"     -> Some (Infix "<")
              | "<_slong"    -> Some (Infix "<")
              | "<_sllong"   -> Some (Infix "<")
              | "<_uint"     -> Some (Infix "<")
              | "<_ulong"    -> Some (Infix "<")
              | "<_ullong"   -> Some (Infix "<")

              %% >
              | ">_sint"     -> Some (Infix ">")
              | ">_slong"    -> Some (Infix ">")
              | ">_sllong"   -> Some (Infix ">")
              | ">_uint"     -> Some (Infix ">")
              | ">_ulong"    -> Some (Infix ">")
              | ">_ullong"   -> Some (Infix ">")

              %% <=
              | "<=_sint"     -> Some (Infix "<=")
              | "<=_slong"    -> Some (Infix "<=")
              | "<=_sllong"   -> Some (Infix "<=")
              | "<=_uint"     -> Some (Infix "<=")
              | "<=_ulong"    -> Some (Infix "<=")
              | "<=_ullong"   -> Some (Infix "<=")

              %% >=
              | ">=_sint"     -> Some (Infix ">=")
              | ">=_slong"    -> Some (Infix ">=")
              | ">=_sllong"   -> Some (Infix ">=")
              | ">=_uint"     -> Some (Infix ">=")
              | ">=_ulong"    -> Some (Infix ">=")
              | ">=_ullong"   -> Some (Infix ">=")

              %% ==
              | "==_sint"     -> Some (Infix "==")
              | "==_slong"    -> Some (Infix "==")
              | "==_sllong"   -> Some (Infix "==")
              | "==_uint"     -> Some (Infix "==")
              | "==_ulong"    -> Some (Infix "==")
              | "==_ullong"   -> Some (Infix "==")

              %% !=
              | "!=_sint"     -> Some (Infix "!=")
              | "!=_slong"    -> Some (Infix "!=")
              | "!=_sllong"   -> Some (Infix "!=")
              | "!=_uint"     -> Some (Infix "!=")
              | "!=_ulong"    -> Some (Infix "!=")
              | "!=_ullong"   -> Some (Infix "!=")

              %% ---------------------------------------------------
              %% Infix bitwise operations: &, ^, |
              %% ---------------------------------------------------

              %% &
              | "&_sint"      -> Some (Infix "&")
              | "&_slong"     -> Some (Infix "&")
              | "&_sllong"    -> Some (Infix "&")
              | "&_uint"      -> Some (Infix "&")
              | "&_ulong"     -> Some (Infix "&")
              | "&_ullong"    -> Some (Infix "&")

              %% ^
              | "^_sint"      -> Some (Infix "^")
              | "^_slong"     -> Some (Infix "^")
              | "^_sllong"    -> Some (Infix "^")
              | "^_uint"      -> Some (Infix "^")
              | "^_ulong"     -> Some (Infix "^")
              | "^_ullong"    -> Some (Infix "^")

              %% |
              | "|_sint"      -> Some (Infix "|")
              | "|_slong"     -> Some (Infix "|")
              | "|_sllong"    -> Some (Infix "|")
              | "|_uint"      -> Some (Infix "|")
              | "|_ulong"     -> Some (Infix "|")
              | "|_ullong"    -> Some (Infix "|")

              %% ---------------------------------------------------
              %% Infix logical operations: &&, ||
              %% ---------------------------------------------------

              %% && -- primitive MetaSlang operator -- see above
              %% || -- primitive MetaSlang operator -- see above

              %% ============================================================
              %% Array access
              %% ============================================================

              | "@_char"          -> Some (ArrayAccess)
              | "@_schar"         -> Some (ArrayAccess)
              | "@_uchar"         -> Some (ArrayAccess)

              | "@_sshort"        -> Some (ArrayAccess)
              | "@_ushort"        -> Some (ArrayAccess)

              | "@_sint"          -> Some (ArrayAccess)
              | "@_uint"          -> Some (ArrayAccess)

              | "@_slong"         -> Some (ArrayAccess)
              | "@_ulong"         -> Some (ArrayAccess)

              | "@_sllong"        -> Some (ArrayAccess)
              | "@_ullong"        -> Some (ArrayAccess)

              %% ============================================================
              %% Structure operators
              %% ============================================================

              %% ============================================================
              %% Conversion operators among the 11 integer types:
              %%    char, uchar, schar, ushort, sshort, uint, sint, ulong, slong, ullong, sllong
              %%    110 operators (11 types * 10 other types)
              %% ============================================================

              %% cast to char
              | "charOfUChar"     -> Some (Cast (if plainCharsAreSigned? then " (char) " else ""))
              | "charOfUshort"    -> Some (Cast " (char) ")
              | "charOfUint"      -> Some (Cast " (char) ")
              | "charOfUlong"     -> Some (Cast " (char) ")
              | "charOfUllong"    -> Some (Cast " (char) ")
              | "charOfSchar"     -> Some (Cast (if plainCharsAreSigned? then "" else " (char) "))
              | "charOfSshort"    -> Some (Cast " (char) ")
              | "charOfSint"      -> Some (Cast " (char) ")
              | "charOfSlong"     -> Some (Cast " (char) ")
              | "charOfSllong"    -> Some (Cast " (char) ")

              %% cast to unsigned char
              | "ucharOfChar"     -> Some (Cast (if plainCharsAreSigned? then " (unsigned char) " else ""))
              | "ucharOfUshort"   -> Some (Cast " (unsigned char) ")
              | "ucharOfUint"     -> Some (Cast " (unsigned char) ")
              | "ucharOfUlong"    -> Some (Cast " (unsigned char) ")
              | "ucharOfUllong"   -> Some (Cast " (unsigned char) ")
              | "ucharOfSchar"    -> Some (Cast " (unsigned char) ")
              | "ucharOfSshort"   -> Some (Cast " (unsigned char) ")
              | "ucharOfSint"     -> Some (Cast " (unsigned char) ")
              | "ucharOfSlong"    -> Some (Cast " (unsigned char) ")
              | "ucharOfSllong"   -> Some (Cast " (unsigned char) ")

              %% cast to unsigned short
              | "ushortOfChar"    -> Some (Cast (if plainCharsAreSigned? then " (unsigned short) " else ""))
              | "ushortOfUChar"   -> Some (Cast ""        )
              | "ushortOfUint"    -> Some (Cast " (unsigned short) ")
              | "ushortOfUlong"   -> Some (Cast " (unsigned short) ")
              | "ushortOfUllong"  -> Some (Cast " (unsigned short) ")
              | "ushortOfSchar"   -> Some (Cast " (unsigned short) ")
              | "ushortOfSshort"  -> Some (Cast " (unsigned short) ")
              | "ushortOfSint"    -> Some (Cast " (unsigned short) ")
              | "ushortOfSlong"   -> Some (Cast " (unsigned short) ")
              | "ushortOfSllong"  -> Some (Cast " (unsigned short) ")

              %% cast to unsigned int
              | "uintOfChar"      -> Some (Cast (if plainCharsAreSigned? then " (unsigned int) " else ""))
              | "uintOfUChar"     -> Some (Cast "" )
              | "uintOfUshort"    -> Some (Cast "" )
              | "uintOfUlong"     -> Some (Cast " (unsigned int) " )
              | "uintOfUllong"    -> Some (Cast " (unsigned int) ")
              | "uintOfSchar"     -> Some (Cast " (unsigned int) ")
              | "uintOfSshort"    -> Some (Cast " (unsigned int) ")
              | "uintOfSint"      -> Some (Cast " (unsigned int) ")
              | "uintOfSlong"     -> Some (Cast " (unsigned int) ")
              | "uintOfSllong"    -> Some (Cast " (unsigned int) ")

              %% cast to unsigned long
              | "ulongOfChar"     -> Some (Cast (if plainCharsAreSigned? then " (unsigned long) " else ""))
              | "ulongOfUChar"    -> Some (Cast "" )
              | "ulongOfUshort"   -> Some (Cast "")
              | "ulongOfUint"     -> Some (Cast "")
              | "ulongOfUllong"   -> Some (Cast " (unsigned long) ")
              | "ulongOfSchar"    -> Some (Cast " (unsigned long) ")
              | "ulongOfSshort"   -> Some (Cast " (unsigned long) ")
              | "ulongOfSint"     -> Some (Cast " (unsigned long) ")
              | "ulongOfSlong"    -> Some (Cast " (unsigned long) ")
              | "ulongOfSllong"   -> Some (Cast " (unsigned long) ")
 
              %% cast to unsigned long long
              | "ullongOfChar"    -> Some (Cast (if plainCharsAreSigned? then " (unsigned long long) " else ""))
              | "ullongOfUChar"   -> Some (Cast "")
              | "ullongOfUshort"  -> Some (Cast "")
              | "ullongOfUint"    -> Some (Cast "")
              | "ullongOfUlong"   -> Some (Cast "")
              | "ullongOfSchar"   -> Some (Cast " (unsigned long long) ")
              | "ullongOfSshort"  -> Some (Cast " (unsigned long long) ")
              | "ullongOfSint"    -> Some (Cast " (unsigned long long) ")
              | "ullongOfSlong"   -> Some (Cast " (unsigned long long) ")
              | "ullongOfSllong"  -> Some (Cast " (unsigned long long) ")

              %% cast to signed char
              | "scharOfChar"     -> Some (Cast (if plainCharsAreSigned? then "" else " (signed char) "))
              | "scharOfUChar"    -> Some (Cast " (signed char) ")
              | "scharOfUshort"   -> Some (Cast " (signed char) ")
              | "scharOfUint"     -> Some (Cast " (signed char) ")
              | "scharOfUlong"    -> Some (Cast " (signed char) ")
              | "scharOfUllong"   -> Some (Cast " (signed char) ")
              | "scharOfSshort"   -> Some (Cast " (signed char) ")
              | "scharOfSint"     -> Some (Cast " (signed char) ")
              | "scharOfSlong"    -> Some (Cast " (signed char) ")
              | "scharOfSllong"   -> Some (Cast " (signed char) ")

              %% cast to signed short
              | "sshortOfChar"    -> Some (Cast (if plainCharsAreSigned? then "" else " (signed short) "))
              | "sshortOfUChar"   -> Some (Cast " (short) ")
              | "sshortOfUshort"  -> Some (Cast " (short) ")
              | "sshortOfUint"    -> Some (Cast " (short) ")
              | "sshortOfUlong"   -> Some (Cast " (short) ")
              | "sshortOfUllong"  -> Some (Cast " (short) ")
              | "sshortOfSchar"   -> Some (Cast "")
              | "sshortOfSint"    -> Some (Cast " (short) ")
              | "sshortOfSlong"   -> Some (Cast " (short) ")
              | "sshortOfSllong"  -> Some (Cast " (short) ")

              %% cast to signed int
              | "sintOfChar"      -> Some (Cast (if plainCharsAreSigned? then "" else " (signed int) "))
              | "sintOfUChar"     -> Some (Cast " (signed int) ")
              | "sintOfUshort"    -> Some (Cast " (signed int) ")
              | "sintOfUint"      -> Some (Cast " (signed int) ")
              | "sintOfUlong"     -> Some (Cast " (signed int) ")
              | "sintOfUllong"    -> Some (Cast " (signed int) ")
              | "sintOfSchar"     -> Some (Cast "")
              | "sintOfSshort"    -> Some (Cast "")
              | "sintOfSlong"     -> Some (Cast " (signed int) ")
              | "sintOfSllong"    -> Some (Cast " (signed int) ")
 
              %% cast to signed long
              | "slongOfChar"     -> Some (Cast (if plainCharsAreSigned? then "" else " (unsigned long) "))
              | "slongOfUChar"    -> Some (Cast " (unsigned long) ")
              | "slongOfUshort"   -> Some (Cast " (unsigned long) ")
              | "slongOfUint"     -> Some (Cast " (unsigned long) ")
              | "slongOfUlong"    -> Some (Cast " (unsigned long) ")
              | "slongOfUllong"   -> Some (Cast " (unsigned long) ")
              | "slongOfSchar"    -> Some (Cast "")
              | "slongOfSshort"   -> Some (Cast "")
              | "slongOfSint"     -> Some (Cast "")
              | "slongOfSllong"   -> Some (Cast " (unsigned long) ")

              %% cast to signed long long
              | "sllongOfChar"    -> Some (Cast (if plainCharsAreSigned? then "" else " (signed long long) "))
              | "sllongOfUChar"   -> Some (Cast " (signed long long) ")
              | "sllongOfUshort"  -> Some (Cast " (signed long long) ")
              | "sllongOfUint"    -> Some (Cast " (signed long long) ")
              | "sllongOfUlong"   -> Some (Cast " (signed long long) ")
              | "sllongOfUllong"  -> Some (Cast " (signed long long) ")
              | "sllongOfSchar"   -> Some (Cast "")
              | "sllongOfSshort"  -> Some (Cast "")
              | "sllongOfSint"    -> Some (Cast "")
              | "sllongOfSlong"   -> Some (Cast "")

           (*
            * These should not appear in final spec to be printed.
            *
            * | "mathIntOfChar"   -> Some (Cast MathInt  )
            * | "mathIntOfUchar"  -> Some (Cast MathInt)
            * | "mathIntOfUshort" -> Some (Cast MathInt  )
            * | "mathIntOfUint"   -> Some (Cast MathInt  )
            * | "mathIntOfUlong"  -> Some (Cast MathInt  )
            * | "mathIntOfUllong" -> Some (Cast MathInt  )
            * | "mathIntOfSchar"  -> Some (Cast MathInt  )
            * | "mathIntOfSshort" -> Some (Cast MathInt  )
            * | "mathIntOfSint"   -> Some (Cast MathInt  )
            * | "mathIntOfSlong"  -> Some (Cast MathInt  )
            * | "mathIntOfSllong" -> Some (Cast MathInt  )
            *
            * | "charOfMathInt"   -> Some (Cast " (char) "     )
            * | "ucharOfMathInt"  -> Some (Cast " (unsigned char) "    )
            * | "ushortOfMathInt" -> Some (Cast " (unsigned short) "   )
            * | "uintOfMathInt"   -> Some (Cast " (unsigned int) "     )
            * | "ulongOfMathInt"  -> Some (Cast " (unsigned long) "    )
            * | "ullongOfMathInt" -> Some (Cast " (unsigned long long) "   )
            * | "scharOfMathInt"  -> Some (Cast " (signed char) "    )
            * | "sshortOfMathInt" -> Some (Cast " (short) "   )
            * | "sintOfMathInt"   -> Some (Cast " (signed int) "     )
            * | "slongOfMathInt"  -> Some (Cast " (unsigned long) "    )
            * | "sllongOfMathInt" -> Some (Cast " (signed long long) "   )
            *)
 
              | _  -> 
                %% TODO: look for name clashes
                if legal_C_Id? id then
                  Some (Prefix id)
                else
                  let _ = writeLine ("Error 2 in cfixity: illegal id: " ^ id) in
                  None)
         | Op (Qualified(q,id), _) ->
           %% TODO: look for name clashes
           if legal_C_Id? id then
             Some (Prefix (if q in? [UnQualified, "C"] then id else id)) % q ^ "_" ^ id
           else
             let _ = writeLine ("Error 3 in cfixity: illegal id: " ^ id) in
             None)
    | _ -> 
      Some Unknown
        

 %% ========================================================================
 %% Implicit constants (Nat, Char, String)
 %% ========================================================================

 op printFunAsC (status : CGenStatus) (fun : MSFun) : Option Pretty =
  case fun of
    | Nat     n  -> Some (string (show n))
    | Char    c  -> Some (string (show c))
    | String  s  -> Some (string s)
   %| Bool    b  -> Some (string (if b then "(0 == 0)" else "(0 != 0)")) %% Boolean TRUE and FALSE are not part of the core C language
   %| Project f  -> Some (string ("." ^ f))                              %% TODO: can this happen?
   %| Op (Qualified ("C", id), _) -> Some (string id)                    %% TODO: can this happen?
   %| Op (Qualified (q,   id), _) -> Some (string (q ^ "_" ^ id))        %% TODO: can this happen?
    | _ -> 
      let _ = writeLine ("Error in printFunAsC: unrecognized fun: " ^ anyToString fun) in
      None

 %% ========================================================================
 %% Explicit numeric constants (Hex, Oct, Dec)
 %% ========================================================================

 op printNumericConstantAsC (suffix : String) (tm : MSTerm) (radix : MSTerm) 
  : Option Pretty = 
  let

    def get_nat_value (tm : MSTerm) : Option Nat =
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
          
    def digitize prefix n base suffix =
      let
        def aux digits n =
          if n < base then
            implode ([digit n] ++ digits)
          else
            let i = n div base in
            let j = n - (base * i) in
            aux ([digit j] ++ digits) i
      in
      let suffix = 
          %% TODO: what are the correct rules for dropping suffix?
          case suffix of
            | "u" | n <= 0x7FFF -> ""
            | _ -> suffix
      in
      prefix ^ (aux [] n) ^ suffix
      
    def hex n suffix = digitize "0x" n 16 suffix
    def oct n suffix = digitize "0"  n 8  suffix
    def dec n suffix = digitize ""   n 10 suffix

  in
  case get_nat_value tm of
    | Some n ->
      % type IntConstBase = | dec | hex | oct
      Some (string (case radix of
                      | Fun (Embed ("hex", _), _, _) -> hex n suffix
                      | Fun (Embed ("oct", _), _, _) -> oct n suffix
                      | Fun (Embed ("dec", _), _, _) -> dec n suffix
                      | _                            -> dec n suffix)) % default to dec
    | _ ->
      None

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
             
 op printTermAsC (status : CGenStatus) (tm : MSTerm) : Option Pretty = 
  case tm of
    | Var       ((id,  _), _) -> 
      if legal_C_Id? id then
        %% TODO: look for name clashes
        Some (string id)
      else
        let _ = writeLine ("Error in printTermAsC: illegal var name: " ^ id) in
        None
    | Fun       (fun, _,   _) -> printFunAsC  status fun
    | TypedTerm (t1, _,    _) -> printTermAsC status t1
    | Apply     (t1, t2,   _) -> 
      (let {f, args} = uncurry (t1, [t2]) in
       let args =  flattenRecordArgs args in
       case cfixity status f of
         | Some fixity ->
           (case (fixity, args) of

              | (Prefix c_str, args) ->
                let opt_blocks =
                    foldl (fn (opt_blocks, arg) ->
                             case (opt_blocks, printTermAsC status arg) of
                               | (Some blocks, Some block) ->
                                 Some (blocks ++ [block])
                               | _ ->
                                 None)
                          (Some [])
                          args
                in
                (case opt_blocks of
                   | Some blocks ->
                     let pretty_args = 
                         AnnTermPrinter.ppList (fn block -> block)
                                               (string "(", string ", ", string ")")
                                               blocks
                     in
                     Some (blockNone (0, 
                                      [(0, string c_str),
                                       (0, pretty_args)]))
                   | _ ->
                     None)

              | (PrefixNoParens c_str, [arg]) ->
                (case printTermAsC status arg of
                   | Some pretty ->
                     Some (blockNone (0, 
                                      [(0, string c_str),
                                       (0, pretty)]))
                   | _ ->
                     None)
              | (Postfix c_str, [arg]) ->
                (case printTermAsC status arg of
                   | Some pretty ->
                     Some (blockNone (0, 
                                      [(0, pretty),
                                       (0, string c_str)]))                                      
                   | _ ->
                     None)

              | (Infix c_str, [arg1, arg2]) ->
                (case (printTermAsC status arg1, printTermAsC status arg2) of
                   | (Some p1, Some p2) ->
                     Some (blockFill (0, 
                                      [(0, p1),
                                       (0, string c_str),
                                       (0, p2)]))
                   | _ ->
                     None)

              | (Cast c_str, [arg]) ->
                (case printTermAsC status arg of
                   | Some pretty ->
                     Some (blockNone (0, 
                                      [(0, string c_str),
                                       (0, pretty)]))
                   | _ ->
                     None)

              | (Constant suffix, [tm, radix]) -> 
                printNumericConstantAsC suffix tm radix

              | (ArrayAccess, array :: indices) ->
                let opt_blocks = 
                foldl (fn (opt_blocks, index) ->
                         case (opt_blocks, printTermAsC status index) of
                           | (Some blocks, Some block) ->
                             Some (blocks ++ [block])
                           | _ ->
                             None)
                      (Some [])
                      (reverse indices)
                in
                (case (opt_blocks, printTermAsC status array) of
                   | (Some blocks, Some pretty_array_name) ->
                     let pretty_indices =
                         AnnTermPrinter.ppList (fn block -> block)
                                               (string "[", string ", ", string "]")
                                               blocks
                     in
                     Some (blockNone (0, 
                                      [(0, pretty_array_name),
                                       (0, pretty_indices)]))
                   | _ ->
                     None)
              | (Unknown, _) ->
                let _ = writeLine ("Error in printTermAsC: unknown fixity for " ^ printTerm f) in
                None)
         | _ ->
           None)
    | _ -> 
      let _ = writeLine ("Error in printTermAsC: unrecognized term: " ^ printTerm tm) in
      None

 %% ========================================================================

endspec
