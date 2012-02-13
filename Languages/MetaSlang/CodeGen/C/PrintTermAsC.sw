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

 type CFixity = | Infix | Prefix | PrefixNoParens | Postfix | ArrayAccess | Ignore | Literal Id

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
                | "slongOfSint"    -> Ignore
                | "sintOfSshort"   -> Ignore
                | "ushortOfUint"   -> Ignore
                | "sintConstant"   -> Literal id
                | "uintConstant"   -> Literal id
                | "ullongConstant" -> Literal id
                | "@_sint"         -> ArrayAccess
                | "-_1_sint"       -> PrefixNoParens
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
            | Bool    b  -> if b then "TRUE" else "FALSE"

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

         | (Ignore, [arg]) ->
           printTermAsC arg

         | (Literal "sintConstant", [n, radix]) -> 
           (case radix of
              | Fun (Embed ("hex", _), _, _) -> 
                blockFill (0, 
                           [(0, string "0x"),
                            (0, printTermAsC n)])
              | _ -> 
                printTermAsC n)

         | (Literal "uintConstant", [n, radix]) -> 
           (case radix of
              | Fun (Embed ("hex", _), _, _) -> 
                blockFill (0, 
                           [(0, string "0x"),
                            (0, printTermAsC n)])
              | _ -> 
                printTermAsC n)

         | (Literal "ullongConstant", [n, radix]) -> 
           (case radix of
              | Fun (Embed ("hex", _), _, _) -> 
                blockFill (0, 
                           [(0, string "0x"),
                            (0, printTermAsC n),
                            (0, string "LLU")])
              | _ -> 
                blockFill (0, 
                           [(0, printTermAsC n),
                            (0, string "LLU")]))

         | (ArrayAccess, [array, index]) ->
           blockFill (0, 
                      [(0, printTermAsC array),
                       (0, string "["),
                       (0, printTermAsC index),
                       (0, string "]")])

         | _ ->
           fail "fixity mismatch")
      
    | _ -> string ("<term: " ^ anyToString trm ^ ">")

 %% ========================================================================


endspec
