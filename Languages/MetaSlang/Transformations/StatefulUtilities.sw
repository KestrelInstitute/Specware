Stateful qualifying spec {

%% Shared between DeconflictUpdates and StatefulUpdates

import /Languages/MetaSlang/CodeGen/DebuggingSupport

import /Languages/MetaSlang/Transformations/SliceSpec
import /Languages/MetaSlang/Transformations/Setf
import /Languages/MetaSlang/Transformations/RecordMerge

op stateful_q : Qualifier = "Stateful"
op sPos       : Position  = Internal "StatefulUtilites"

op get_stateful_types (spc        : Spec, 
                       type_names : TypeNames) 
 : Option MSTypes =
 foldl (fn (types, type_name) ->
          case types of
            | Some types ->
              (case findTheType (spc, type_name) of
                 | Some _ ->
                   let typ = Base (type_name, [], sPos) in
                   Some (typ |> types)
                 | _ -> None)
            | _ -> None)
       (Some [])
       type_names

op stateful_type? (spc            : Spec, 
                   typ            : MSType, 
                   stateful_types : MSTypes) 
 : Bool =
 exists? (fn stateful_type ->
            possiblySubtypeOf? (typ, stateful_type, spc))
         stateful_types


}