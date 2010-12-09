SliceSpec qualifying
spec
import ../Specs/AnalyzeRecursion

type QualifierSet = AQualifierMap Bool

op emptySet: QualifierSet = emptyAQualifierMap

op in? (Qualified(q,id): QualifiedId, s: QualifierSet) infixl 20 : Bool =
  some?(findAQualifierMap(s, q, id) )

op nin?  (Qualified(q,id): QualifiedId, s: QualifierSet) infixl 20 : Bool =
  none?(findAQualifierMap(s, q, id) )

op <| (s: QualifierSet, Qualified(x, y): QualifiedId) infixl 25 : QualifierSet =
  insertAQualifierMap(s, x, y, true)

op addList(s: QualifierSet, l: QualifiedIds): QualifierSet =
  foldl (<|) s l

op haskellElement?(el: SpecElement): Bool =
   case el of
     | Pragma("#translate", prag_str, "#end", _) | haskellPragma? prag_str -> true
     | Pragma _ -> false
     | _ -> true

op haskellPragma?(s: String): Bool =
  let s = stripOuterSpaces s in
  let len = length s in
  len > 2 \_and (let pr_type = subFromTo(s, 0, 7) in
             pr_type = "Haskell" \_or pr_type = "haskell")

 op  filterSpecNonBaseElements: (SpecElement -> Boolean) -> SpecElements -> Bool -> Spec -> SpecElements
 def filterSpecNonBaseElements p elements sliceBase? base_spec =
   mapPartial
     (fn el ->
      if ~(p el) then
	None
      else
	Some(case el of
	       | Import (s_tm, i_sp, elts, a) ->
	         if (sliceBase? => i_sp ~= base_spec)
                   then Import (s_tm, i_sp, filterSpecNonBaseElements p elts sliceBase? base_spec, a)
                   else el
	       | _ ->  el))
     elements

op [a] sliceAQualifierMap(m: AQualifierMap a, s: QualifierSet, pred: QualifiedId -> Bool): AQualifierMap a =
  mapiPartialAQualifierMap (fn (q, id, v) ->
                              let qid = Qualified(q, id) in
                              if qid in? s || pred qid
                                then Some v
                              else None)
    m

op scrubSpec(spc: Spec, op_set: QualifierSet, type_set: QualifierSet, base_spec: Spec, sliceBase?: Bool): Spec =
  let def element_filter el =
        case el of
          | Sort(qid, _)     -> qid in? type_set
          | SortDef(qid, _)  -> qid in? type_set
          | Op(qid, _, _)    -> qid in? op_set && numRefinedDefs spc qid = 1
          | OpDef(qid, refine_num, _) -> qid in? op_set && numRefinedDefs spc qid = refine_num + 1
          | Property(_, _, _, formula, _) ->
            forall? (fn qid -> qid in? op_set || (sliceBase? && some?(findTheOp(base_spec, qid))))
              (opsInTerm formula)
              && forall? (fn qid -> qid in? type_set || (sliceBase? && some?(findTheSort(base_spec, qid))))
                   (typesInTerm formula)
 %          | Import(tm, im_spc, im_elts, _) ->
%             exists? (fn im_el -> if element_filter im_el
%                                    then % let _ = writeLine("filter accepts:\n"^ anyToString tm) in
%                                         true
%                                    else false) im_elts
          | Import _ -> true
          | _ -> haskellElement? el
  in
  spc <<
    {sorts = sliceAQualifierMap(spc.sorts, type_set, fn qid -> sliceBase? && some?(findTheSort(base_spec, qid))),
     ops =   sliceAQualifierMap(spc.ops,     op_set, fn qid -> sliceBase? && some?(findTheOp(base_spec, qid))),
     elements = filterSpecNonBaseElements element_filter spc.elements sliceBase? base_spec
     }


op sliceSpecInfo(spc: Spec, root_ops: QualifiedIds, root_types: QualifiedIds, ignore_subtypes?: Bool, sliceBase?: Bool)
     : QualifierSet * QualifierSet =
  let base_spec = SpecCalc.getBaseSpec() in
  let def newOpsInTerm(tm: MS.Term, newopids: QualifiedIds, op_set: QualifierSet): QualifiedIds =
        foldTerm (fn opids -> fn t ->
                    case t of
                      | Fun(Op(qid,_),_,_)
                          | qid nin? opids && qid nin? op_set && (sliceBase? => none?(findTheOp(base_spec, qid))) ->
                        qid :: opids
                      | _ -> opids,
                  fn result -> fn _ -> result,
                  fn result -> fn _ -> result)
          newopids tm
      def newOpsInType(ty: Sort, newopids: QualifiedIds, op_set: QualifierSet): QualifiedIds =
        foldSort (fn result -> fn t ->
                    case t of
                      | Fun(Op(qid,_),_,_) | qid nin? result -> qid::result
                      | _ -> result,
                  fn result -> fn _ -> result,
                  fn result -> fn _ -> result)
          newopids ty
      def newTypesInTerm(tm: MS.Term, newtypeids: QualifiedIds, type_set: QualifierSet): QualifiedIds =
        foldTerm (fn result -> fn _ -> result,
                  fn result -> fn t ->
                    case t of
                      | Base(qid,_,_)
                          | qid nin? result && qid nin? type_set && (sliceBase? => none?(findTheOp(base_spec, qid))) ->
                        qid :: result
                      | _ -> result,
                  fn result -> fn _ -> result)

          newtypeids tm
      def newTypesInType(ty: Sort, newtypeids: QualifiedIds, type_set: QualifierSet): QualifiedIds =
        foldSort (fn result -> fn _ -> result,
                  fn result -> fn t ->
                    case t of
                      | Base(qid,_,_) 
                          | qid nin? result && qid nin? type_set && (sliceBase? => none?(findTheOp(base_spec, qid))) ->
                        qid :: result
                      | _ -> result,
                  fn result -> fn _ -> result)

          newtypeids ty

      def iterateDeps(new_ops, new_types, op_set, type_set) =
        %let _ = writeLine("nts: "^anyToString new_ops) in
        if new_ops = [] && new_types = [] then (op_set, type_set)
        else
        let op_set = addList(op_set, new_ops) in
        let type_set = addList(type_set, new_types) in
        let new_ops1 = foldl (fn (newopids, qid) ->
                              case findTheOp(spc, qid) of
                                | Some opinfo -> newOpsInTerm(opinfo.dfn, newopids, op_set)
                                | None -> newopids)
                         [] new_ops
        in
        let new_ops2 = if ignore_subtypes? then new_ops1
                       else
                         foldl (fn (newopids, qid) ->
                              case findTheSort(spc, qid) of
                                | Some typeinfo -> newOpsInType(typeinfo.dfn, newopids, op_set)
                                | None -> newopids)
                           new_ops1 new_types
        in
        let new_types1 = foldl (fn (newtypeids, qid) ->
                              case findTheOp(spc, qid) of
                                | Some opinfo -> newTypesInTerm(opinfo.dfn, newtypeids, type_set)
                                | None -> newtypeids)
                         [] new_ops
        in
        let new_types2 = foldl (fn (newtypeids, qid) ->
                              case findTheSort(spc, qid) of
                                | Some typeinfo -> newTypesInType(typeinfo.dfn, newtypeids, type_set)
                                | None -> newtypeids)
                           new_types1 new_types
        in
        iterateDeps(new_ops2, new_types2, op_set, type_set)
    in
    let (op_set, type_set) = iterateDeps(root_ops, root_types, emptySet, emptySet) in
    (op_set, type_set)

op sliceSpec(spc: Spec, root_ops: QualifiedIds, root_types: QualifiedIds, ignore_subtypes?: Bool, sliceBase?: Bool): Spec =
  let (op_set, type_set) = sliceSpecInfo(spc, root_ops, root_types, ignore_subtypes?, sliceBase?) in
  let sliced_spc = scrubSpec(spc, op_set, type_set, SpecCalc.getBaseSpec(), sliceBase?) in
  sliced_spc

%% Just for debugging
op AnnSpec.subtractSpec: Spec -> Spec -> Spec

endspec
