(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Stateful qualifying spec {

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% These routines are used in the production of stateful code.
%%
%% We include this file under the Transformations directory because the 
%% operations here are used (among other things) for actions that simply 
%% transform a spec in preparation for the later production of a stateful 
%% quasi-spec.
%%
%% In particular, deconflictUpdates needs to know which types are intended to 
%% be stateful.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

import /Languages/MetaSlang/CodeGen/DebuggingSupport
import /Languages/MetaSlang/CodeGen/Generic/SliceSpec
import /Languages/MetaSlang/CodeGen/Generic/RecordMerge

import /Languages/MetaSlang/CodeGen/Stateful/Setf

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
