NormTypes qualifying spec

  import /Languages/MetaSlang/Specs/Utilities

  op topLevelTypes(spc: Spec): List(QualifiedId * TyVars * Sort) =
    foldriAQualifierMap
      (\_lambda (q, id, info, result) ->
         if primarySortName? (q, id, info) then
           %% When access is via a primary alias, update the info and
           %% record that (identical) new value for all the aliases.
           if  definedSortInfo? info
             then
               let (tvs,ty) = unpackFirstSortDef info in
               if replaceableType? ty
                 then Cons((Qualified(q, id),tvs,ty),result)
               else result
           else result
         else result)
      [] spc.sorts

  op normalizeType (spc: Spec, typeNameInfo: List(QualifiedId * TyVars * Sort), checkTop?: Boolean) (ty: Sort): Sort =
    % let _ = writeLine("nt: "^printSort ty) in
    if replaceableType? ty
      \_and \_not (checkTop? && exists? (\_lambda (id,vs,top_ty) \_rightarrow ty = top_ty) typeNameInfo) % Avoid changing definition itself!
     then
       case foldl (\_lambda (result,(qid,tvs,top_ty)) \_rightarrow
                   case result of
                     | None \_rightarrow
                       % let _ = writeLine("qid: "^printQualifiedId qid^"\n"^"nt: "^printSort ty^" =~= "^printSort top_ty) in
                       (case typeMatch(top_ty,ty,spc,false) of
                          | Some tyvar_sbst \_rightarrow
                            if checkTop? && ty = top_ty then None else
			    % let _ = toScreen("top_ty:\n"^(anyToString top_ty)^"\nty:\n"^(anyToString ty)
                            %                     ^"\ntyvar_sbst:\n"^(anyToString tyvar_sbst)
                            %                     ^"\n tvs:\n"^(anyToString tvs)) in
                            Some(qid, tvs, tyvar_sbst)
                          | None \_rightarrow None)
                     | _ \_rightarrow result)
              None typeNameInfo of
         | Some (qid, tvs, tyvar_sbst) | length tvs = length tyvar_sbst \_rightarrow
           Base(qid,map (\_lambda tv \_rightarrow case findLeftmost (\_lambda (tv1,_) \_rightarrow tv = tv1) tyvar_sbst of
                                   | Some(_,ty_i) \_rightarrow ty_i)
                      tvs,
                 sortAnn ty)

         | _ \_rightarrow ty
     else ty

  %% Replaces type expressions by their named sorts
  op normalizeTypes(spc: Spec): Spec =
    let typeNameInfo = topLevelTypes spc in
    mapSpec (id,normalizeType(spc,typeNameInfo,true),id) spc
 
  op normDef(qid as Qualified(q,id), map_fns, spc): Spec =
    case findTheOp(spc, qid) of
      | Some info \_rightarrow spc \_guillemotleft {ops = insertAQualifierMap (spc.ops, q, id, info \_guillemotleft {dfn = mapTerm map_fns info.dfn})}
      | None \_rightarrow spc

  op normSortDef(qid as Qualified(q,id), map_fns, spc): Spec =
    case findTheSort(spc, qid) of
      | Some info \_rightarrow
        spc \_guillemotleft {sorts = insertAQualifierMap (spc.sorts, q, id, info \_guillemotleft {dfn = mapSort map_fns info.dfn})}
      | None \_rightarrow spc

  %% Normalize without normalizing imports
  op normalizeNewTypes(spc: Spec): Spec =
    let typeNameInfo = topLevelTypes spc in
    let map_fns = (id, normalizeType(spc,typeNameInfo,false),id) in
    let spc = spc \_guillemotleft {elements = map (fn el ->
                                       case el of
                                         | Property (pt, nm, tvs, term, a) ->
                                           % let _ = writeLine("msp: "^printQualifiedId(nm)^"\n"^printTerm term) in
                                           Property (pt, nm, tvs, mapTerm map_fns term, a)
                                         | _ -> el)
                                  spc.elements}
    in
    foldl (fn (spc,el) \_rightarrow
           case el of
             | OpDef(qid,_,_) \_rightarrow normDef(qid, map_fns, spc)
             | Op(qid,true,_) \_rightarrow normDef(qid, map_fns, spc)
             %| SortDef(qid,_) \_rightarrow normSortDef(qid, map_fns, spc)
             | _ \_rightarrow spc)
      spc spc.elements

  op  replaceableType?: [a] ASort a \_rightarrow Boolean
  def replaceableType? ty =
    case ty of
      | Quotient _ \_rightarrow true
      | CoProduct _ \_rightarrow true
      | Subsort _ \_rightarrow true
      | Product((id1,_)::_, a) -> id1 ~= "1"
      | _ \_rightarrow false

endspec
