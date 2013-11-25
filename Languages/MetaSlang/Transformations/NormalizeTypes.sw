(* Replaces types by their named types. This wouldn't be necessary if everything (esp. typechecker) only
   expanded a type when necessary *)

NormTypes qualifying spec 

import /Languages/MetaSlang/Specs/Utilities

%% called by the Haskell and Isabelle ppSpec routines:
op topLevelTypeNameInfo (spc : Spec) : List (QualifiedId * TyVars * MSType) =
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

%% called by makeIsoMorphism:
op normalizeType (spc               : Spec, 
                  typename_info     : List (QualifiedId * TyVars * MSType), 
                  checkTop?         : Bool,
                  ignore_subtypes?  : Bool, 
                  only_replaceable? : Bool)
                 (typ               : MSType)
 : MSType =
 % let _ = writeLine("nt: "^printType ty) in
 if (only_replaceable? => replaceable_type? typ)
    && ~ (checkTop? && exists? (fn (id, vs, top_type) -> typ = top_type) typename_info) % Avoid changing definition itself!
   then
     let new_name_info = 
         foldl (fn (result, (name, tvs, top_type)) ->
                  case result of
                    | None ->
                      % let _ = writeLine("name: "^printQualifiedId name^"\n"^"nt: "^printType ty^" =~= "^printType top_ty) in
                      (case typeMatch (top_type, typ, spc, ignore_subtypes?, false) of
                         | Some tyvar_sbst ->
                           if checkTop? && typ = top_type then 
                             None 
                           else
                             % let _ = toScreen("top_ty:\n"^(anyToString top_ty)^"\nty:\n"^(anyToString ty)
                             %                     ^"\ntyvar_sbst:\n"^(anyToString tyvar_sbst)
                             %                     ^"\n tvs:\n"^(anyToString tvs)) in
                             Some (name, tvs, tyvar_sbst)
                         | _ ->
                           None)
                    | _ -> 
                      result)
               None 
               typename_info 
      in
      case new_name_info of
       | Some (name, tvs, tyvar_sbst) | length tvs = length tyvar_sbst ->
         let type_args = 
             map (fn tv -> 
                    case findLeftmost (fn (tv1, _) -> tv = tv1) tyvar_sbst of
                      | Some (_, ty_i) -> ty_i)
                 tvs
         in
         Base (name, type_args, typeAnn typ)

       | _ -> typ
 else 
   typ

%% Replaces type expressions by their named types
%% called from ASW_Printer ppSpec routines
op normalizeTypes (spc : Spec, ignore_subtypes? : Bool): Spec =
 let typeNameInfo = topLevelTypeNameInfo spc in
 mapSpec (id, 
          normalizeType (spc, typeNameInfo, true, ignore_subtypes?, true), 
          id) 
         spc
 
op norm_def (name as Qualified (q,id), map_fns, spc : Spec) : Spec =
 case findTheOp (spc, name) of
   | Some info -> 
     let new_dfn  = mapTerm map_fns info.dfn                       in
     let new_info = info << {dfn = new_dfn}                        in
     let new_ops  = insertAQualifierMap (spc.ops, q, id, new_info) in
     spc << {ops = new_ops}
   | _ -> 
     spc

op norm_type_def (name as Qualified (q,id), map_fns, spc : Spec) : Spec =
  case findTheType(spc, name) of
    | Some info ->
      let new_dfn   = mapType map_fns info.dfn                         in
      let new_info  = info << {dfn = new_dfn}                          in
      let new_types = insertAQualifierMap (spc.types, q, id, new_info) in
      spc << {types = new_types}
    | _ -> 
      spc

%% normalize without normalizing imports
%% called by haskell and isabelle ppspec routines
op normalizeNewTypes (spc : Spec, ignore_subtypes? : Bool) : Spec =
 let typename_info = topLevelTypeNameInfo spc in
 let map_fns       = (id, 
                      normalizeType (spc, typename_info, false, ignore_subtypes?, true), 
                      id)
 in
 let new_elements = map (fn elt ->
                           case elt of
                             | Property (pt, nm, tvs,                 term, a) ->
                               % let _ = writeLine("msp: "^printQualifiedId(nm)^"\n"^printTerm term) in
                               Property (pt, nm, tvs, mapTerm map_fns term, a)

                             | OpDef (name, n,     opt_info, a) ->
                               let new_opt_info =
                                   case opt_info of
                                     | Some info -> Some (mapTransformInfo (mapTerm map_fns) info)
                                     | _ -> None
                               in
                               OpDef (name, n, new_opt_info, a)

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

op [a] replaceable_type? (typ : AType a) : Bool =
 case typ of
   | Quotient  _ -> true
   | CoProduct _ -> true
   | Subtype   _ -> true
   | Product   ((id1,_) :: _, _) -> id1 ~= "1"
   | _ -> false

end-spec
