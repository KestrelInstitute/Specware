PrintAsC qualifying spec 

 import PrintAsCUtils

 %% ========================================================================
 %% Main print routine for types. 
 %% 
 %% C Types and typedefs print very strangely, with component information 
 %% moved around and reordered in arbitrary ways that are inconsistent with
 %% with a simple recursive depiction.
 %% 
 %% Instead, we need to split the information about a MetaSlang type into
 %% two components (one for base type name and another for array arguments).
 %% Callers will then move those around as appropriate.
 %% 
 %% ========================================================================

 op printTypeAsC_split (status : CGenStatus) (typ : MSType) 
  : Option (Pretty * List (Nat * Pretty) * CGenStatus) =
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
           Some (string id, [], status)
         | _ -> None)

    | Product ([], _) -> 
      Some (string "{}", [], status)

    | Product (row, _) -> 
      let opt_blocks_and_status = 
          foldl (fn (opt_blocks_and_status, (id, typ)) ->
                   case opt_blocks_and_status of
                     | Some (blocks, status) ->
                       (case printTypeAsC status typ of
                          | Some (pretty_field_type, status) ->
                            Some (blocks ++
                                    [blockNone (0, [(0, pretty_field_type),
                                                    (0, string " "),
                                                    (0, string id),
                                                    (0, string "; ")])],
                                  status)
                          | _ ->
                            None)
                     | _ ->
                       None)
                (Some ([], status))
                row
      in
      (case opt_blocks_and_status of
         | Some (blocks, status) ->
           Some (blockFill (0, 
                            [(0, string "{")]
                            ++
                            (List.map (fn block -> (0, block)) blocks)
                            ++
                            [(0, string "}")]),
                 [],
                 status)
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
      %%          =>
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
           (case printTypeAsC_split status typ of 
              | Some (pretty_type, [], status) ->
                Some (pretty_type, limits, status)
              | _ ->
                None)
         | _ ->
           None)
    | _ -> 
      let _ = writeLine ("Error in printTypeAsC_split: unrecognized type: " ^ printType typ) in
      None
      
 %% ========================================================================
 %% Print routine for types when we don't need to deal with typedef nonsense.
 %% ========================================================================

 op printTypeAsC (status : CGenStatus) (typ : MSType) : Option (Pretty * CGenStatus) =
   case printTypeAsC_split status typ of
     | Some (pretty_type, index_lines, status) ->
       let pretty = 
           case index_lines of
             | [] -> pretty_type
             | _ -> blockNone (0, [(0, pretty_type)] ++ index_lines)
       in
       Some (pretty, status)
     | _ ->
       None

endspec
