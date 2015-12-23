(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

PrintAsC qualifying spec 

 import PrintAsCUtils

 %% ========================================================================
 %% Main print routine for types. 
 %% 
 %% C Types and typedefs print very strangely, with component information 
 %% moved around and reordered in arbitrary ways that are inconsistent with
 %% a simple recursive depiction.
 %% 
 %% Instead, we need to split the information about a MetaSlang type into
 %% two components (one for base type name and another for array arguments).
 %% Callers will then move those around as appropriate.
 %% 
 %% ========================================================================

 op getPartsForCType (status : CGenStatus, typ : MSType) : Pretty * List (Nat * Pretty) * CGenStatus =
  case typ of

    | Base (qid as Qualified (q, id), [], _) -> 
      (case getCTypeName (qid, status) of
         | Some c_type_name -> (string c_type_name, [], status)
         | _ ->
           (string id, [], status    % trying with this commented out: reportError ("no C type for: " ^ show qid, status)
           ))

    | Product ([], _) -> 
      (string "{}", [], status)

    | Product (row, _) -> 
      let (lines, status) =
          foldl (fn ((lines, status), (id, typ)) ->
                   let (pretty_field_type, status) = printTypeAsC (status, typ) in
                   (lines ++
                    [(0, blockNone (0, [(0, pretty_field_type),
                                        L0_space,
                                        (0, string id),
                                        (0, string "; ")]))],
                    status))
                ([], status)
                row
      in
      let lines = [L0_lbracket] ++ lines ++ [L0_rbracket] in
      (blockFill (0, lines), [], status)

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
        def split_apart_array_type_info (typ, pretty_bounds) =          
          %% Get various pieces of type information, because C typedef scatters information around.
          %% Return element type (e.g. the type XXX), suffix (e.g. string "[2][4]"), and status.
          case typ of
            | Subtype (Base (Qualified ("C", "Array"), [element_type], _), 
                       Apply (Fun (Op (Qualified ("C", "ofLength?"), _), _, _),
                              Fun (Nat n, _, _),
                              _),
                       _)
              -> 
              %% Special case for fixed length subtypes of C.Array.
              let major_pretty_bound = [(0, string "["), (0, string (show n)), (0, string "]")] in
              let (innermost_element_type, minor_pretty_bounds, status) = 
                  split_apart_array_type_info (element_type, pretty_bounds)
              in
              let status = if n = 0 then reportError ("array size = 0", status) else status in
              (innermost_element_type, major_pretty_bound ++ minor_pretty_bounds, status)

            | Subtype (parent_type, _, _) ->
              %% All other subtype predicates are ignored.
              (parent_type, [], status)

            | _ ->
              (typ, pretty_bounds, status)
      in
      let (innermost_element_type, pretty_bounds, status) = split_apart_array_type_info (typ, []) in
      let (pretty_element_type, _, status) = getPartsForCType (status, innermost_element_type) in
      (pretty_element_type, pretty_bounds, status)
          
    | _ -> 
      %% Some kind of type not handled (yet?):
      (string "", [], reportError ("unrecognized kind of type: " ^ printType typ, status))
      
 %% ========================================================================
 %% Print routine for types when we don't need to deal with typedef nonsense.
 %% ========================================================================

 op printTypeAsC (status : CGenStatus, typ : MSType) : Pretty * CGenStatus =
  let (pretty_type, index_lines, status) = getPartsForCType(status, typ) in
  let pretty = 
      case index_lines of
        | [] -> pretty_type
        | _ -> blockNone (0, [(0, pretty_type)] ++ index_lines)
  in
  (pretty, status)

endspec
