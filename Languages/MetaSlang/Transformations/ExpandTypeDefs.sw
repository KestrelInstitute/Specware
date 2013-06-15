ExpandTypeDefs qualifying spec

import /Languages/MetaSlang/Specs/Environment

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Remove subtype predicates, etc. that would not appear in final code.
%% Keep subtypes of Nat, later used to choose among char, short, int, long, etc.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op SpecTransform.expandTypeDefs (spc : Spec) : Spec =
 let 
   def expand typ =
     case typ of
       | Base (qid, typs, a) ->
         (case findTheType (spc, qid) of
            | Some info ->
              if definedTypeInfo? info then
                let (tvs, tdef) = unpackFirstTypeDef info in
                let recur? = (length tvs = length typs)
                             &&
                             (case tdef of
                                | Subtype _ -> true
                                | Base    _ -> true
                                | _ -> false)
                in
                if recur? then 
                  let new = substType (zip (tvs, typs), tdef) in
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
