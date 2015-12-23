(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* When a spec has a TypeDef for a type that has a declaration in an imported spec this is like an implicit morphism
   which systems such as Isabelle cannot handle, so sometimes it needs to be explicated *)

ExplicateMorph qualifying
spec
import ../Specs/AnalyzeRecursion
import /Languages/MetaSlang/Specs/Categories/AsRecord  % Morphism
import /Languages/SpecCalculus/Semantics/Evaluate/Spec/MergeSpecs

op needsMorphismExplication?(spc: Spec): Bool =
  exists? (fn el ->
             case el of
               | TypeDef(qid, _) ->
                 exists? (fn el1 ->
                            case el1 of
                              | Import(_, _, imp_elts, _) ->
                                existsSpecElement?
                                  (fn el2 ->
                                     case el2 of
                                       | Type(qid1, _) ->
                                         if qid = qid1
                                           then let _ = writeLine(show qid^" defined") in true else false
                                       | _ -> false)
                                  imp_elts
                              | _ -> false)
                   spc.elements
               | _ -> false)
    spc.elements

op oldTypesDefined(spc: Spec): QualifiedIds =
  foldl (fn (qids, el) ->
             case el of
               | TypeDef(qid, _)
                   | exists? (fn el1 ->
                                case el1 of
                                  | Import(_, _, imp_elts, _) ->
                                    existsSpecElement?
                                    (fn el2 ->
                                       case el2 of
                                         | Type(qid1, _) -> qid = qid1
                                         | _ -> false)
                                    imp_elts
                                         | _ -> false)
                       spc.elements ->
                 qid::qids                 
               | _ -> qids)
      []
      spc.elements

op mergeImportElt(spc: Spec, imp_el: SpecElement): Spec =
  let new_spc = appendElement(spc, imp_el) in
  let Import(_, i_spc, _, _) = imp_el in
  let new_types = foldriAQualifierMap (fn (q,id,info,new_types) -> mergeTypeInfo new_spc new_types info)
                    spc.types i_spc.types
  in
  let new_ops = foldriAQualifierMap (fn (q,id,info,new_ops) -> mergeOpInfo new_spc new_ops info false)
                    spc.ops i_spc.ops
  in
  new_spc << {types = new_types,
              ops   = new_ops}

op getImportSpec(spc: Spec): Spec =
  let imports = filter (fn el ->
                          case el of
                            | Import _ -> true
                            | _ -> false)
                  spc.elements
  in
  case imports of
    | [Import(_, i_spc, _, _)] -> i_spc
    | (i_spc_el as Import(_, i_spc, _, _)) :: r_imports ->
  % let _ = writeLine("Merging imports of\n"^printSpec spc) in
  let init_spc = setElements(i_spc, [i_spc_el]) in
  let spc = foldl mergeImportElt init_spc r_imports in
  % let _ = writeLine("merged imports:\n"^printSpec spc) in
  spc

op bringToTopOfSpec(elts: SpecElements, needed_ops: QualifiedIds, needed_types: QualifiedIds): SpecElements =
  foldr (fn (el, ret_elts) ->
           case el of
             | Import(_, _, imp_elts, _)
                 | existsSpecElement? (fn el ->
                                       case el of
                                         | Type(qid, _) -> qid in? needed_types
                                         | TypeDef(qid, _) -> qid in? needed_types
                                         | Op(qid, _, _) -> qid in? needed_ops
                                         | OpDef(qid, _, _, _) -> qid in? needed_ops
                                         | _ -> false)
                     imp_elts ->
               bringToTopOfSpec(imp_elts, needed_ops, needed_types) ++ ret_elts
            | _ -> el :: ret_elts)
    [] elts
               

op explicateMorphism(spc: Spec | needsMorphismExplication? spc): Morphism =
  let import_spc = getImportSpec spc in
  let redef_qids = oldTypesDefined spc in
  % let (needed_ops, needed_types) = used_*([], redef_qids, spc) in
  let new_spc_elements = bringToTopOfSpec(spc.elements, [], redef_qids) in
  let new_spc_elements = filter (fn el ->
                                   case el of
                                     | Type(qid, _) -> ~(qid in? redef_qids)
                                     | _ -> true)
                           new_spc_elements
  in
  let new_spc = setElements(spc, new_spc_elements) in
  % let _ = writeLine("Flattened spec:\n"^printSpec new_spc) in
  makeMorphism(import_spc, new_spc, emptyMap, emptyMap, [], None)  

end-spec
