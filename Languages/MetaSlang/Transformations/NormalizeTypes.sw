(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

NormTypes qualifying spec 

(* 
 * Replace types by their named types. 
 * Some calls to these routines could be avoided if everything (esp. typechecker) 
 * onlyexpanded types when necessary.
 *)

import /Languages/MetaSlang/Specs/Utilities

type TypeNameInfo = List (QualifiedId * TyVars * MSType)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op [a] replaceable_type? (typ : AType a) : Bool =
 case typ of
   | Quotient  _ -> true
   | CoProduct _ -> true
   | Subtype   _ -> true
   | Product   ((id1,_) :: _, _) -> id1 ~= "1"
   | _ -> false

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% topLevelTypeNameInfo is called by the Haskell and Isabelle ppSpec routines
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op topLevelTypeNameInfo (spc : Spec) : TypeNameInfo =
 foldriAQualifierMap
   (fn (q, id, info, result) ->
      if primaryTypeName? (q, id, info) then
        %% When access is via a primary alias, update the info and
        %% record that (identical) new value for all the aliases.
        if  definedTypeInfo? info then
          let (tvs, typ) = unpackFirstTypeDef info in
          if replaceable_type? typ then
            (Qualified (q, id), tvs, typ) :: result
          else 
            result
        else 
          result
      else 
        result)
   []
   spc.types

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% normalizeType is called by makeIsoMorphism:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op normalizeType (spc               : Spec, 
                  typename_info     : TypeNameInfo,
                  check_top?        : Bool,
                  ignore_subtypes?  : Bool, 
                  only_replaceable? : Bool)
                 (typ               : MSType)
 : MSType =
 % let _ = writeLine("nt: "^printType ty) in
 if (~ only_replaceable? || replaceable_type? typ) &&
    ~ (check_top? && exists? (fn (id, vs, top_type) -> typ = top_type) typename_info) % Avoid changing definition itself!
   then
     let new_name_info = 
         foldl (fn (result, (name, tvs, top_type)) ->
                  case result of
                    | None ->
                      (case typeMatch (top_type, typ, spc, ignore_subtypes?, true) of
                         | Some tyvar_sbst ->
                           if check_top? && typ = top_type then 
                             None 
                           else
                             Some (name, tvs, tyvar_sbst)
                         | _ ->
                           None)
                    | _ -> 
                      result)
               None 
               typename_info 
      in
      case new_name_info of
       | Some (name, tvs, tyvar_sbst) ->
         %let _ = writeLine("normalizeType: "^show name^"\n"^anyToString tvs^"\n"^anyToString tyvar_sbst) in
         %if length tvs = length tyvar_sbst then
           let type_args = 
               map (fn tv -> 
                      case findLeftmost (fn (tv1, _) -> tv = tv1) tyvar_sbst of
                        | Some (_, ty_i) -> ty_i
                        | None -> mkTyVar tv)
                 tvs
           in
           Base (name, type_args, typeAnn typ)
         %else typ
       | _ -> typ
 else 
   typ

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% normalizeTypes is called from the ASW_Printer ppSpec routine
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Replaces type expressions by their named types
op SpecTransform.normalizeTypes (spc : Spec, ignore_subtypes? : Bool): Spec =
 let typeNameInfo = topLevelTypeNameInfo spc in
 mapSpec (id, 
          normalizeType (spc, typeNameInfo, true, ignore_subtypes?, true), 
          id) 
         spc
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% normalizeNewTypes is called from the Haskell and Isabelle ppSpec routines
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op norm_def (name as Qualified (q,id) : QualifiedId,
             map_fns                  : TSP_Maps Position, 
             spc                      : Spec) 
 : Spec =
 case findTheOp (spc, name) of
   | Some info -> 
     let new_dfn  = mapTerm map_fns info.dfn                       in
     let new_info = info << {dfn = new_dfn}                        in
     let new_ops  = insertAQualifierMap (spc.ops, q, id, new_info) in
     spc << {ops = new_ops}
   | _ -> 
     spc

% never called?
% op norm_type_def (name as Qualified (q,id), map_fns, spc : Spec) : Spec = 
%   case findTheType(spc, name) of
%     | Some info ->
%       let new_dfn   = mapType map_fns info.dfn                         in
%       let new_info  = info << {dfn = new_dfn}                          in
%       let new_types = insertAQualifierMap (spc.types, q, id, new_info) in
%       spc << {types = new_types}
%     | _ -> 
%       spc

%% normalize without normalizing imports
op SpecTransform.normalizeNewTypes (spc : Spec, ignore_subtypes? : Bool) : Spec =
 let typename_info = topLevelTypeNameInfo spc in
 let map_fns       = (id, 
                      normalizeType (spc, typename_info, false, ignore_subtypes?, true), 
                      id)
 in
 let new_elements = map (fn elt ->
                           case elt of
                             | Property (pt, nm, tvs,                 term, a) ->
                               Property (pt, nm, tvs, mapTerm map_fns term, a)

                             | OpDef (name, n, pf, a) ->
                               % README (emw4): the proof here used to
                               % be "mapped", but there is no clear
                               % way to do this for normalizeType...
                               OpDef (name, n, pf, a)
                             | _ -> elt)
                        spc.elements
 in
 let spc = spc << {elements = new_elements} in
 foldl (fn (spc, elt) ->
          case elt of
            | OpDef   (name, _,    _, _) -> norm_def    (name, map_fns, spc)
            | Op      (name, true,    _) -> norm_def    (name, map_fns, spc)
           %| TypeDef (name,          _) -> normTypeDef (name, map_fns, spc)
            | _ -> spc)
       spc 
       spc.elements

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

end-spec
