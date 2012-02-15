AnnSpecPrinter qualifying spec 
 import /Languages/SpecCalculus/AbstractSyntax/SCTerm  % SCTerm
 import /Languages/MetaSlang/AbstractSyntax/PrinterSig % printTerm, printType, printPattern
 import /Languages/MetaSlang/AbstractSyntax/Printer
 import /Languages/MetaSlang/Specs/AnnSpec
 % import /Library/IO/Primitive/IO                    % getEnv
 import /Library/Legacy/DataStructures/IntSetSplay    % indicesToDisable
 import /Library/Legacy/DataStructures/NatMapSplay    % markTable's

 import /Languages/SpecCalculus/Semantics/Environment
 % op SpecCalc.getBaseSpec : () -> Spec % defined in /Languages/SpecCalculus/Semantics/Environment
 op printPragmas?: Bool = true

 %% ========================================================================

 type MSFun = AFun Position

 type CFunCall = {f : MSTerm, args : MSTerms}

 op unpackRecordArgs (args : MSTerms) : MSTerms =
  foldl (fn (args, arg) ->
           case arg of
             | Record (("1", arg1) :: pairs, _) ->
               args ++ [arg1] ++ (map (fn (_, arg) -> arg) pairs)
             | _ ->
               args ++ [arg])
        []
        args
             
 op uncurry (t1 : MSTerm, args : MSTerms) : CFunCall =
  case t1 of
    | Apply (t2, t3, _) -> uncurry (t2, [t3] ++ args)
    | _ -> {f = t1, args = args}

 type CType = | Char | SChar | UChar | Int | SInt | UInt | SShort | UShort | SLong | ULong | SLLong | ULLong | MathInt

 type CFixity = | Infix | Prefix | PrefixNoParens | Postfix | ArrayAccess | Ignore | Constant CType | Cast CType

 op plainCharsAreSigned?   : Bool = false
 op plainCharsAreUnsigned? : Bool = ~ plainCharsAreSigned?

 op cfixity (tm : MSTerm) : CFixity =
    case tm of 
      | Fun (fun, _, _) -> 
        (case fun of
           | And         -> Infix
           | Or          -> Infix
           | Equals      -> Infix
           | NotEquals   -> Infix
           | Project   _ -> Postfix
           | Op (Qualified ("C", id), _) ->
             (case id of
                | "@_sint"          -> ArrayAccess
                | "-_1_sint"        -> PrefixNoParens

                | "sintConstant"    -> Constant SInt
                | "slongConstant"   -> Constant SLong
                | "sllongConstant"  -> Constant SLLong

                | "uintConstant"    -> Constant UInt
                | "ulongConstant"   -> Constant ULong
                | "ullongConstant"  -> Constant ULLong

                | "mathIntOfChar"   -> Cast MathInt  % ??
                | "mathIntOfUchar"  -> Cast MathInt  % ??
                | "mathIntOfUshort" -> Cast MathInt  % ??
                | "mathIntOfUint"   -> Cast MathInt  % ??
                | "mathIntOfUlong"  -> Cast MathInt  % ??
                | "mathIntOfUllong" -> Cast MathInt  % ??
                | "mathIntOfSchar"  -> Cast MathInt  % ??
                | "mathIntOfSshort" -> Cast MathInt  % ??
                | "mathIntOfSint"   -> Cast MathInt  % ??
                | "mathIntOfSlong"  -> Cast MathInt  % ??
                | "mathIntOfSllong" -> Cast MathInt  % ??

                | "charOfMathInt"   -> Cast Char     % ??
                | "charOfUChar"     -> if plainCharsAreUnsigned? then Ignore else Cast Char
                | "charOfUshort"    -> Cast Char
                | "charOfUint"      -> Cast Char
                | "charOfUlong"     -> Cast Char
                | "charOfUllong"    -> Cast Char
                | "charOfSchar"     -> if plainCharsAreSigned? then Ignore else Cast Char
                | "charOfSshort"    -> Cast Char
                | "charOfSint"      -> Cast Char
                | "charOfSlong"     -> Cast Char
                | "charOfSllong"    -> Cast Char

                | "ucharOfMathInt"  -> Cast UChar     % ??
                | "ucharOfChar"     -> if plainCharsAreUnsigned? then Ignore else Cast UChar
                | "ucharOfSchar"    -> Cast UChar
                | "ucharOfUshort"   -> Cast UChar
                | "ucharOfUint"     -> Cast UChar
                | "ucharOfUlong"    -> Cast UChar
                | "ucharOfUllong"   -> Cast UChar
                | "ucharOfSshort"   -> Cast UChar
                | "ucharOfSint"     -> Cast UChar
                | "ucharOfSlong"    -> Cast UChar
                | "ucharOfSllong"   -> Cast UChar

                | "scharOfMathInt"  -> Cast SChar     % ??
                | "scharOfChar"     -> if plainCharsAreSigned? then Ignore else Cast SChar
                | "scharOfUChar"    -> Cast SChar
                | "scharOfUshort"   -> Cast SChar
                | "scharOfUint"     -> Cast SChar
                | "scharOfUlong"    -> Cast SChar
                | "scharOfUllong"   -> Cast SChar
                | "scharOfSshort"   -> Cast SChar
                | "scharOfSint"     -> Cast SChar
                | "scharOfSlong"    -> Cast SChar
                | "scharOfSllong"   -> Cast SChar

                | "ushortOfMathInt" -> Cast UShort     % ??
                | "ushortOfChar"    -> if plainCharsAreSigned? then Ignore else Cast UShort
                | "ushortOfUChar"   -> Ignore
                | "ushortOfUint"    -> Cast UShort
                | "ushortOfUlong"   -> Cast UShort
                | "ushortOfUllong"  -> Cast UShort
                | "ushortOfSchar"   -> Cast UShort
                | "ushortOfSshort"  -> Cast UShort
                | "ushortOfSint"    -> Cast UShort
                | "ushortOfSlong"   -> Cast UShort
                | "ushortOfSllong"  -> Cast UShort

                | "uintOfMathInt"   -> Cast UInt     % ??
                | "uintOfChar"      -> if plainCharsAreUnsigned? then Ignore else Cast UInt
                | "uintOfUChar"     -> Ignore
                | "uintOfUshort"    -> Ignore
                | "uintOfUlong"     -> Cast UInt
                | "uintOfUllong"    -> Cast UInt
                | "uintOfSchar"     -> Cast UInt
                | "uintOfSshort"    -> Cast UInt
                | "uintOfSint"      -> Cast UInt
                | "uintOfSlong"     -> Cast UInt
                | "uintOfSllong"    -> Cast UInt

                | "ulongOfMathInt"  -> Cast ULong     % ??
                | "ulongOfChar"     -> if plainCharsAreUnsigned? then Ignore else Cast ULong
                | "ulongOfUChar"    -> Ignore
                | "ulongOfUshort"   -> Ignore
                | "ulongOfUint"     -> Ignore
                | "ulongOfUllong"   -> Cast ULong
                | "ulongOfSchar"    -> Cast ULong
                | "ulongOfSshort"   -> Cast ULong
                | "ulongOfSint"     -> Cast ULong
                | "ulongOfSlong"    -> Cast ULong
                | "ulongOfSllong"   -> Cast ULong
 
                | "ullongOfMathInt" -> Cast ULLong     % ??
                | "ullongOfChar"    -> if plainCharsAreUnsigned? then Ignore else Cast ULLong
                | "ullongOfUChar"   -> Ignore
                | "ullongOfUshort"  -> Ignore
                | "ullongOfUint"    -> Ignore
                | "ullongOfUlong"   -> Ignore
                | "ullongOfSchar"   -> Cast ULLong
                | "ullongOfSshort"  -> Cast ULLong
                | "ullongOfSint"    -> Cast ULLong
                | "ullongOfSlong"   -> Cast ULLong
                | "ullongOfSllong"  -> Cast ULLong

                | "sshortOfMathInt" -> Cast SShort     % ??
                | "sshortOfChar"    -> if plainCharsAreSigned? then Ignore else Cast SShort
                | "sshortOfUChar"   -> Cast SShort
                | "sshortOfUshort"  -> Cast SShort
                | "sshortOfUint"    -> Cast SShort
                | "sshortOfUlong"   -> Cast SShort
                | "sshortOfUllong"  -> Cast SShort
                | "sshortOfSchar"   -> Ignore
                | "sshortOfSint"    -> Cast SShort
                | "sshortOfSlong"   -> Cast SShort
                | "sshortOfSllong"  -> Cast SShort

                | "sintOfMathInt"   -> Cast SInt     % ??
                | "sintOfChar"      -> if plainCharsAreSigned? then Ignore else Cast SInt
                | "sintOfUChar"     -> Cast SInt
                | "sintOfUshort"    -> Cast SInt
                | "sintOfUint"      -> Cast SInt
                | "sintOfUlong"     -> Cast SInt
                | "sintOfUllong"    -> Cast SInt
                | "sintOfSchar"     -> Ignore
                | "sintOfSshort"    -> Ignore
                | "sintOfSlong"     -> Cast SInt
                | "sintOfSllong"    -> Cast SInt
 
                | "slongOfMathInt"  -> Cast SLong     % ??
                | "slongOfChar"     -> if plainCharsAreSigned? then Ignore else Cast SLong
                | "slongOfUChar"    -> Cast SLong
                | "slongOfUshort"   -> Cast SLong
                | "slongOfUint"     -> Cast SLong
                | "slongOfUlong"    -> Cast SLong
                | "slongOfUllong"   -> Cast SLong
                | "slongOfSchar"    -> Ignore
                | "slongOfSshort"   -> Ignore
                | "slongOfSint"     -> Ignore
                | "slongOfSllong"   -> Cast SLong

                | "sllongOfMathInt" -> Cast SLLong     % ??
                | "sllongOfChar"    -> if plainCharsAreSigned? then Ignore else Cast SLLong
                | "sllongOfUChar"   -> Cast SLLong
                | "sllongOfUshort"  -> Cast SLLong
                | "sllongOfUint"    -> Cast SLLong
                | "sllongOfUlong"   -> Cast SLLong
                | "sllongOfUllong"  -> Cast SLLong
                | "sllongOfSchar"   -> Ignore
                | "sllongOfSshort"  -> Ignore
                | "sllongOfSint"    -> Ignore
                | "sllongOfSlong"   -> Ignore

                | _  -> Prefix)
           | _ -> Prefix)
      | _ -> Prefix
        

 op printFunAsC (fun : MSFun) : Pretty =
  string (case fun of
            | Not        -> "!"
            | And        -> "&&"
            | Or         -> "||"
            | Equals     -> "=="
            | NotEquals  -> "!="

            | Nat     n  -> show n
            | Char    c  -> show c
            | String  s  -> s
           %| Bool    b  -> if b then "(0 == 0)" else "(0 != 0)"

            | Project f  -> "." ^ f

            | Op (Qualified ("C", id), _) -> 
              (case id of
                 | "-_1_sint" -> "-"
                 | _ -> id)

            | Op (Qualified (q, id), _) -> q ^ "_" ^ id

            | _ -> "<unknown: " ^ anyToString fun ^ ">")

 op printTermAsC (trm : MSTerm) : Pretty = 
  case trm of
    | Var       ((id,  _),     _) -> string id
    | Fun       (fun, _,       _) -> printFunAsC fun
    | TypedTerm (tm, _,        _) -> printTermAsC tm
    | Lambda    ([(_, _, tm)], _) -> printTermAsC tm
    | Apply     (t1, t2,       _) -> 
      (let {f, args} = uncurry (t1, [t2]) in
       let args =  unpackRecordArgs args in
       case (cfixity f, args) of

         | (Infix, [arg1, arg2]) ->
           blockFill (0, 
                      [(0, printTermAsC arg1),
                       (0, printTermAsC f),
                       (0, printTermAsC arg2)])

         | (Postfix, [arg1]) ->
           blockFill (0, 
                      [(0, printTermAsC arg1),
                       (0, printTermAsC f)])

         | (PrefixNoParens, [arg]) ->
           blockFill (0, 
                      [(0, printTermAsC f),
                       (0, printTermAsC arg)])


         | (Prefix, args) ->
           let pretty_args = 
               AnnTermPrinter.ppListPath []
                                         (fn (_, arg) -> printTermAsC arg)
                                         (string "(", string ", ", string ")")
                                         args
           in
           blockFill (0, 
                      [(0, printTermAsC f),
                       (0, pretty_args)])

         | (ArrayAccess, array :: indices) ->
           let pretty_indices = 
               AnnTermPrinter.ppListPath []
                                         (fn (_, index) -> printTermAsC index)
                                         (string "[", string ", ", string "]")
                                         indices
           in
           blockFill (0, 
                      [(0, printTermAsC array),
                       (0, pretty_indices)])

         | (Ignore, [arg]) ->
           printTermAsC arg

         | (Constant ctype, [n, radix]) -> 
           let postfix = case ctype of
                           | SInt   -> ""
                           | SLong  -> "l"
                           | SLLong -> "ll"
                           | UInt   -> "u"
                           | ULong  -> "ul"
                           | ULLong -> "ull"
           in
           (case radix of
              | Fun (Embed ("hex", _), _, _) -> 
                blockFill (0, 
                           [(0, string "0x"),
                            (0, printTermAsC n),
                            (0, string postfix)])
              | Fun (Embed ("oct", _), _, _) -> 
                blockFill (0, 
                           [(0, string "0"),
                            (0, printTermAsC n),
                            (0, string postfix)])
              | _ -> 
                blockFill (0, 
                           [(0, printTermAsC n),
                            (0, string postfix)]))

         | (Cast ctype, [arg1]) ->
           let cast =
               case ctype of
                 | Char    -> " (char) "
                 | SChar   -> " (signed char) "
                 | UChar   -> " (unsigned char) "
                 | Int     -> " (int) "
                 | SInt    -> " (signed int) "
                 | UInt    -> " (unsigned int) "
                 | SShort  -> " (signed short) "
                 | UShort  -> " (unsigned short) "
                 | SLong   -> " (signed long) "
                 | ULong   -> " (unsigned long) "
                 | SLLong  -> " (signed long long) "
                 | ULLong  -> " (unsigned long long) "
                 | MathInt -> " (bignum) "
           in
           blockFill (0, 
                      [(0, string cast),
                       (0, printTermAsC arg1)])

         | _ ->
           fail "fixity mismatch")
      
    | _ -> string ("<term: " ^ anyToString trm ^ ">")

 %% ========================================================================


endspec
