(* Replaces types by their named types. This wouldn't be necessary if everything (esp. typechecker) only
   expanded a type when necessary *)

NormTypes qualifying spec

  import /Languages/MetaSlang/Specs/Utilities

  op topLevelTypes(spc: Spec): List(QualifiedId * TyVars * MSType) =
    foldriAQualifierMap
      (fn (q, id, info, result) ->
         if primaryTypeName? (q, id, info) then
           %% When access is via a primary alias, update the info and
           %% record that (identical) new value for all the aliases.
           if  definedTypeInfo? info
             then
               let (tvs,ty) = unpackFirstTypeDef info in
               if replaceableType? ty
                 then (Qualified(q, id),tvs,ty) :: result
               else result
           else result
         else result)
      [] spc.types

  op normalizeType
       (spc: Spec, typeNameInfo: List(QualifiedId * TyVars * MSType), checkTop?: Bool,
        ign_subtypes?: Bool, only_replaceable?: Bool)
       (ty: MSType): MSType =
    % let _ = writeLine("nt: "^printType ty) in
    if (only_replaceable? => replaceableType? ty)
      && ~ (checkTop? && exists? (fn (id,vs,top_ty) -> ty = top_ty) typeNameInfo) % Avoid changing definition itself!
     then
       case foldl (fn (result,(qid,tvs,top_ty)) ->
                   case result of
                     | None ->
                       % let _ = writeLine("qid: "^printQualifiedId qid^"\n"^"nt: "^printType ty^" =~= "^printType top_ty) in
                       (case typeMatch(top_ty,ty,spc,ign_subtypes?,false) of
                          | Some tyvar_sbst ->
                            if checkTop? && ty = top_ty then None else
			    % let _ = toScreen("top_ty:\n"^(anyToString top_ty)^"\nty:\n"^(anyToString ty)
                            %                     ^"\ntyvar_sbst:\n"^(anyToString tyvar_sbst)
                            %                     ^"\n tvs:\n"^(anyToString tvs)) in
                            Some(qid, tvs, tyvar_sbst)
                          | None -> None)
                     | _ -> result)
              None typeNameInfo of
         | Some (qid, tvs, tyvar_sbst) | length tvs = length tyvar_sbst ->
           Base(qid,map (fn tv -> case findLeftmost (fn (tv1,_) -> tv = tv1) tyvar_sbst of
                                   | Some(_,ty_i) -> ty_i)
                      tvs,
                 typeAnn ty)

         | _ -> ty
     else ty

  %% Replaces type expressions by their named types
  op normalizeTypes(spc: Spec, ign_subtypes?: Bool): Spec =
    let typeNameInfo = topLevelTypes spc in
    mapSpec (id, normalizeType(spc, typeNameInfo, true, ign_subtypes?, true), id) spc
 
  op normDef(qid as Qualified(q,id), map_fns, spc): Spec =
    case findTheOp(spc, qid) of
      | Some info -> spc << {ops = insertAQualifierMap (spc.ops, q, id, info << {dfn = mapTerm map_fns info.dfn})}
      | None -> spc

  op normTypeDef(qid as Qualified(q,id), map_fns, spc): Spec =
    case findTheType(spc, qid) of
      | Some info ->
        spc << {types = insertAQualifierMap (spc.types, q, id, info << {dfn = mapType map_fns info.dfn})}
      | None -> spc

  %% Normalize without normalizing imports
  op normalizeNewTypes(spc: Spec, ign_subtypes?: Bool): Spec =
    let typeNameInfo = topLevelTypes spc in
    let map_fns = (id, normalizeType(spc, typeNameInfo, false, ign_subtypes?, true), id) in
    let spc = spc << {elements = map (fn el ->
                                        case el of
                                          | Property (pt, nm, tvs, term, a) ->
                                            % let _ = writeLine("msp: "^printQualifiedId(nm)^"\n"^printTerm term) in
                                            Property (pt, nm, tvs, mapTerm map_fns term, a)
                                          | OpDef(qid,n,hist,a) ->
                                            let new_hist = map (fn (tm, rlspc) ->
                                                                  %let _ = writeLine("hist: "^printTerm tm^"\n"^printTerm(mapTerm map_fns tm)) in
                                                                  (mapTerm map_fns tm,
                                                                   rlspc))
                                                             hist
                                            in
                                            OpDef(qid,n,new_hist,a)
                                          | _ -> el)
                        spc.elements}
    in
    foldl (fn (spc,el) ->
           case el of
             | OpDef(qid,_,hist,_) -> normDef(qid, map_fns, spc)
             | Op(qid,true,_) -> normDef(qid, map_fns, spc)
             %| TypeDef(qid,_) -> normTypeDef(qid, map_fns, spc)
             | _ -> spc)
      spc spc.elements

  op  replaceableType?: [a] AType a -> Bool
  def replaceableType? ty =
    case ty of
      | Quotient _ -> true
      | CoProduct _ -> true
      | Subtype _ -> true
      | Product((id1,_)::_, a) -> id1 ~= "1"
      | _ -> false

end-spec
