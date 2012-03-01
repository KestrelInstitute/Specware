PrintTypeAsC qualifying spec 
 import /Languages/SpecCalculus/AbstractSyntax/SCTerm  % SCTerm
 import /Languages/MetaSlang/AbstractSyntax/PrinterSig % printTerm, printType, printPattern
 import /Languages/MetaSlang/AbstractSyntax/Printer
 import /Languages/MetaSlang/Specs/Printer
 import /Languages/MetaSlang/Specs/AnnSpec
 import /Library/Legacy/DataStructures/IntSetSplay    % indicesToDisable
 import /Library/Legacy/DataStructures/NatMapSplay    % markTable's

 import /Languages/SpecCalculus/Semantics/Environment

 type CGenOptions = {plainCharsAreSigned? : Bool,
                     printPragmas?        : Bool}

 op init_cgen_options (spc : Spec) : CGenOptions = 
  let plain_chars_are_signed? =
      case findTheOp (spc, Qualified ("C", "plainCharsAreSigned")) of
        | Some opinfo ->
          let 
            def true? tm =
              case tm of
                | Fun (Bool b, _, _) -> b
                | TypedTerm (tm, _, _) -> true? tm
                | _ -> 
                  let _ = writeLine ("plainCharsAreSigned has unrecognized definition: " ^ printTerm tm 
                                       ^ ", defaulting to false") 
                  in
                  false
          in
          let signed? = true? opinfo.dfn in
          signed?
        | _ ->
          let _ = writeLine ("could not find plainCharsAreSigned, defaulting to false") in
          false
  in

  let _ = writeLine ("printPragmas? is hardwired to false for now") in
  let print_pragmas? = false in

  let _ = writeLine ("plainCharsAreSigned? = " ^ show plain_chars_are_signed?) in
  let _ = writeLine ("printPragmas?        = " ^ show print_pragmas?)          in
  let _ = writeLine ("") in
  {plainCharsAreSigned? = plain_chars_are_signed?,
   printPragmas?        = print_pragmas?}

 op legal_C_Id? (id : String) : Bool =
  %% TODO: look for name clashes
  let 
    def legal_C_char? char =
      isAlphaNum char || char = #_
  in
  case explode id of
    | hd :: tail -> (isAlpha hd || hd = #_) && (forall? legal_C_char? tail)
    | _ -> false

 op printTypeAsC (cgen_options : CGenOptions) (typ : MSType) : Option Pretty =
   case printTypeAsC_split cgen_options typ of
     | Some (pretty_type, index_lines) ->
       Some (case index_lines of
               | [] -> pretty_type
               | _ -> blockNone (0, [(0, pretty_type)] ++ index_lines))
     | _ ->
       None

 op printTypeAsC_split (cgen_options : CGenOptions) (typ : MSType) : Option (Pretty * List (Nat * Pretty)) =
  case typ of

    | Base (Qualified (q, id), [], _) -> 
      let opt_id =
          if q = "C" then
            case id of
              | "Uchar"  -> Some "unsigned char"
              | "Schar"  -> Some "signed char"
              | "Char"   -> Some "char"
              | "Ushort" -> Some "unsigned short"
              | "Uint"   -> Some "unsigned int"
              | "Ulong"  -> Some "unsigned long"
              | "Ullong" -> Some "unsigned long long"
              | "Sshort" -> Some "short"
              | "Sint"   -> Some "int"
              | "Slong"  -> Some "long"
              | "Sllong" -> Some "long long"
              | _        -> 
                let _ = writeLine ("Error in printTypeAsC: unknown C type: " ^ id) in
                None
          else 
            %% TODO: look for name clashes
            if legal_C_Id? id then
              let _ = writeLine("Type not mentioned in C: " ^ id) in
              Some id
            else
              let _ = writeLine ("Error in printTypeAsC: bad name for C type: " ^ id) in
              None
      in
      (case opt_id of
         | Some id -> 
           Some (string id, [])
         | _ -> None)

    | Product ([], _) -> 
      Some (string "{}", [])

    | Product (row, _) -> 
      let opt_blocks : Option Prettys = foldl (fn (opt_blocks, (id, typ)) ->
                               case (opt_blocks, printTypeAsC cgen_options typ) of
                                 | (Some blocks, Some pretty_field_type) ->
                                   Some (blocks ++
                                           [blockNone (0, [(0, pretty_field_type),
                                                           (0, string " "),
                                                           (0, string id),
                                                           (0, string "; ")])])
                                 | _ ->
                                   None)
                            (Some [])
                            row
      in
      (case opt_blocks of
         | Some blocks ->
           Some (blockFill (0, 
                            [(0, string "{")]
                            ++
                            (List.map (fn block -> (0, block)) blocks)
                            ++
                            [(0, string "}")]),
                 [])
         | _ ->
           None)

    | Subtype _ ->
      %% Bletch:
      %%
      %% Array limits in C have the most major (most slowly varying) index first and 
      %% the most minor (most quickly varying) index last.
      %% (I.e. 'foo[2][4]' refers to a 2-element array where each element is 'foo[4]')
      %%
      %% From our perspective, that means outer length restrictions should be printed 
      %% before inner length restrictions. 
      %%
      %% Not only that, but if we wish to make Bar a typedef for Foo[2][4] the C syntax
      %% is 'typedef Foo Bar[2][4]' (as opposed to the sensible 'typedef Foo[2][4] Bar').
      %%
      %% MetaSlang: 'type Matrix_2_4 = (Array (Array Sint | ofLength? 4) | ofLength? 2)'
      %%  =>
      %%         C: 'typedef int Matrix_2_4[2][4];'
      %% 
      let 
        def split_apart_limits (typ, limits) =          
          %% Because C typedef scatters information around
          case typ of
            | Subtype (Base (Qualified ("C", "Array"), [element_type], _), 
                       Apply (Fun (Op (Qualified ("C", "ofLength?"), _), _, _),
                              Fun (Nat n, _, _),
                              _),
                       _)
              -> 
              if n = 0 then
                let _ = writeLine ("Error in printTypeAsC: array size = 0") in
                None
              else
                let outer_limit_lines = [(0, string "["), (0, string (show n)), (0, string "]")] in
                (case split_apart_limits (element_type, limits) of
                   | Some (base_type, inner_limit_lines) ->
                     Some (base_type, outer_limit_lines ++ inner_limit_lines)
                   | _ ->
                    None)
            | _ ->
              Some (typ, limits)
      in
      (case split_apart_limits (typ, []) of
         | Some (typ, limits) ->
           (case printTypeAsC_split cgen_options typ of 
              | Some (pretty_type, []) ->
                Some (pretty_type, limits)
              | _ ->
                None)
         | _ ->
           None)
    | _ -> 
      let _ = writeLine ("Error in printTypeAsC_split: unrecognized type: " ^ printType typ) in
      None
      
endspec
