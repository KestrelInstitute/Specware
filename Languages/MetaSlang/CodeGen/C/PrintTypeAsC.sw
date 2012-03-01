PrintTypeAsC qualifying spec 
 import /Languages/SpecCalculus/AbstractSyntax/SCTerm  % SCTerm
 import /Languages/MetaSlang/AbstractSyntax/PrinterSig % printTerm, printType, printPattern
 import /Languages/MetaSlang/AbstractSyntax/Printer
 import /Languages/MetaSlang/Specs/Printer
 import /Languages/MetaSlang/Specs/AnnSpec
 import /Library/Legacy/DataStructures/IntSetSplay    % indicesToDisable
 import /Library/Legacy/DataStructures/NatMapSplay    % markTable's

 import /Languages/SpecCalculus/Semantics/Environment

 op legalId? (id : String) : Bool =
  let 
    def legal_C_char? char =
      isAlphaNum char || char = #_

  case explode id of
    | hd :: tail -> (isAlpha hd || hd = #_) && (forall? legal_C_char? tail)
    | _ -> false

 op printTypeAsC (typ : MSType) : Option Pretty =
   case printTypeAsC_split typ of
     | Some (pretty_type, index_lines) ->
       Some (case index_lines of
               | [] -> pretty_type
               | _ -> blockNone (0, [(0, pretty_type)] ++ index_lines))
     | _ ->
       None

 op printTypeAsC_split (typ : MSType) : Option (Pretty * List (Nat * Pretty)) =
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
                let _ = writeLine ("printTypeAsC: unknown C type: " ^ id) in
                None
          else if legalId? id then
            Some id % TODO: look for bad chars
          else
            let _ = writeLine ("printTypeAsC: bad name for C type: " ^ id) in
            None
      in
      (case opt_id of
         | Some id -> Some (string id, [])
         | _ -> None)

    | Product ([], _) -> 
      Some (string "{}", [])

    | Product (row, _) -> 
      let opt_blocks = foldl (fn (opt_blocks, (id, typ)) ->
                               case (opt_blocks, printTypeAsC typ) of
                                 | (Some blocks, Some line) ->
                                   Some (blocks ++
                                           [blockFill (0, [(0, line),
                                                           (0, string " "),
                                                           (0, string id)])])
                                 | _ ->
                                   None)
                            (Some [])
                            row
      in
      (case opt_blocks of
         | Some blocks ->
           Some (AnnTermPrinter.ppList (fn block -> block)
                                       (PrettyPrint.string "{", PrettyPrint.string "; ", PrettyPrint.string "}")
                                       blocks,
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
                let _ = writeLine ("printTypeAsC: array size = 0") in
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
           (case printTypeAsC_split typ of 
              | Some (pretty_type, []) ->
                Some (pretty_type, limits)
              | _ ->
                None)
         | _ ->
           None)
    | _ -> 
      let _ = writeLine ("printTypeAsC_split: unrecognized type: " ^ printType typ) in
      None
      
endspec
