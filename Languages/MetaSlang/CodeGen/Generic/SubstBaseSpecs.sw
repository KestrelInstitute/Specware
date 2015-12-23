(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

SubstBaseSpecs qualifying spec

 import /Languages/MetaSlang/Specs/StandardSpec
 import /Languages/SpecCalculus/Semantics/Value
 import /Languages/MetaSlang/Specs/Utilities

 op Specware.evaluateUnitId: String \_rightarrow Option Value   % Defined in /Languages/SpecCalculus/Semantics/Bootstrap, which imports this spec

 op SpecTransform.substBaseSpecs  (spc: Spec) : Spec = substBaseSpecs1(spc, baseExecutableSpecNames)

 %% To get an executable base
 op baseExecutableSpecNames : List String = ["/Library/Base/List_Executable", "/Library/Base/String_Executable", "/Library/Base/Integer_Executable"]
 
 op topLevelOpsAndTypesExcludingBaseSubsts (spc : Spec) : QualifiedIds * QualifiedIds =
  let (base_subst_ops, base_subst_types) = substBaseSpecOpsAndTypes () in
  let ops   = filter (fn name -> ~ (name in? base_subst_ops)) (topLevelOpNames   spc) in
  let types = filter (fn name -> ~ (name in? base_subst_ops)) (topLevelTypeNames spc) in
  (ops, types)
  
 op substBaseSpecOpsAndTypes () : QualifiedIds * QualifiedIds =
  %% used during code generation to avoid miscontruing these as "toplevel" ops and types
  foldl (fn ((ops, types), exec_spec_name) ->
           case evaluateUnitId exec_spec_name of
             | None -> (ops, types)
             | Some (Spec exec_spc) ->
               foldl (fn ((ops, types), el) ->
                        case el of
                          | Op(qid as Qualified(q,id), true, _) ->
                            (case findAQualifierMap (exec_spc.ops, q, id) of
                               | Some _ ->  (qid :: ops, types)
                               | _ -> (ops, types))
                          | OpDef(qid as Qualified(q,id), _, _, _) ->
                            (case findAQualifierMap (exec_spc.ops, q, id) of
                               | Some _ ->  (qid :: ops, types)
                               | _ -> (ops, types))
                          | Type(qid as Qualified(q,id), _) -> 
                            (case findAQualifierMap (exec_spc.types, q, id) of
                               | Some _ ->  (ops, qid :: types)
                               | _ -> (ops, types))
                          | TypeDef(qid as Qualified(q,id), _) -> 
                            (case findAQualifierMap (exec_spc.types, q, id) of
                               | Some _ ->  (ops, qid :: types)
                               | _ -> (ops, types))
                          | _ ->
                            (ops, types))
                     (ops, types)
                     exec_spc.elements)
        ([], [])
        baseExecutableSpecNames

 op substBaseSpecs1(spc: Spec, baseExecutableSpecNames: List String): Spec =
   %% Actually does an import
   let (op_map, elements) =
       foldl (fn ((op_map, elements), exec_spec_name) ->
                case evaluateUnitId exec_spec_name of
                  | None -> (op_map, elements)
                  | Some(Spec exec_spc) ->
                    foldl (fn ((op_map, elements), el) ->
                             case el of
                               | Op(qid as Qualified(q,id), true, _) ->
                                 (case findAQualifierMap(exec_spc.ops, q, id) of
                                    | Some info -> 
                                      (insertAQualifierMap(op_map, q, id, trimOldDefs info),
                                       if embed? None (AnnSpec.findTheOp(spc, qid))
                                         then % let _ = writeLine(printQualifiedId qid) in
                                              elements ++ [el]
                                         else elements)
                                    | _ -> (op_map, elements))
                               | OpDef(qid as Qualified(q,id), _, _, a) ->
                                 (case findAQualifierMap(exec_spc.ops, q, id) of
                                    | Some info | some?(AnnSpec.findTheOp(spc, qid)) ->
                                      (insertAQualifierMap(op_map, q, id, trimOldDefs info),
                                       elements)
                                    | _ -> (op_map, elements))
                               | _ -> (op_map, elements))
                      (op_map, elements) exec_spc.elements)
         (spc.ops, spc.elements) baseExecutableSpecNames
   in
   spc << {ops = op_map, elements = elements}

 op [a] firstDef(dfn: ATerm a): ATerm a =
   case dfn of
     | And(d1::_, _) -> d1
     | Pi(tvs, tm, pos) -> Pi(tvs, firstDef tm, pos)
     | TypedTerm(tm, ty, pos) -> TypedTerm(firstDef tm, ty, pos)
     | d -> d

 op [a] trimOldDefs(opinfo: AOpInfo a): AOpInfo a =
   opinfo << {dfn = firstDef opinfo.dfn}

end-spec
