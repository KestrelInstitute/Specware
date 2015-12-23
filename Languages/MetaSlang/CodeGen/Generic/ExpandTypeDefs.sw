(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

ExpandTypeDefs qualifying spec

import /Languages/MetaSlang/Specs/Environment

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Expand defined types if they are defined as base types or subtypes.
%% For polymorphic types, substitute the provided type args into the expanded definition.
%%
%% This ensures that all resulting types are either 
%%    primitive (no definition), or
%%    a non-base type, or
%%    a base type that expands directly into one of the above (but not into a subtype)
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op SpecTransform.expandTypeDefs (spc : Spec) : Spec =
 let 
   def expand typ =
     case typ of
       | Base (qid, arg_types, _) ->
         (case findTheType (spc, qid) of
            | Some info ->
              if definedTypeInfo? info then
                let (tvs, tdef) = unpackFirstTypeDef info in

                %% Note that tdef (the defintion of the base type) could be 
                %% monomorphic, in which case tvs and arg_types will be empty.
                %%
                %% In that case, we will still use the expanded definition, 
                %% but the substitution below will be vacuous.

                let revise? = (length tvs = length arg_types)
                              &&
                              (case tdef of
                                 | Subtype _ -> true
                                 | Base    _ -> true
                                 | _ -> false)
                in
                if revise? then 
                  let new = substType (zip (tvs, arg_types), tdef) in
                  expand new
                else
                  typ
              else
                typ
            | _ -> typ)
       | _ -> typ
 in
 mapSpec (fn t -> t, expand, fn p -> p) spc

end-spec
