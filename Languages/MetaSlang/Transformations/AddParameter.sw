AddParameter qualifying
spec
import ../Specs/AnalyzeRecursion

op findOpsBetween(spc: Spec, top_fn: QualifiedId, fun: QualifiedId): QualifiedIds =
  let baseSpec = getBaseSpec() in
  let def iterateRefsTo(roots: QualifiedIds, found: QualifiedIds, ref_by_map: RefMap): RefMap =
        case roots of
          | [] -> ref_by_map
          | root :: rest ->
            let refs = opsInOpDefFor(root, spc) in
            %% Ignore Base ops
            let refs = filter (fn x -> none?(findTheOp(baseSpec, x))) refs in
            let ref_by_map = foldl (fn (ref_by_map, op_id) -> addToRefMap(ref_by_map, op_id, root))
                               ref_by_map refs
            in
            let new_refs = filter (fn x -> x nin? found && x ~= fun) refs in
            iterateRefsTo(new_refs++rest, new_refs++found, ref_by_map)
      def iterateRefsBy(roots: QualifiedIds, found: QualifiedIds, ref_by_map: RefMap): QualifiedIds =
        case roots of
          | [] -> found
          | root :: rest ->
            let new_refs_by = filter (fn x -> x nin? found) (applyRefMap(ref_by_map, root)) in
            iterateRefsBy(new_refs_by ++ rest, new_refs_by ++ found, ref_by_map)
   in
   let ref_by_map = iterateRefsTo([top_fn], [top_fn], emptyAQualifierMap) in
   iterateRefsBy([fun], [fun], ref_by_map)

op addParameter(spc: Spec, fun: QualifiedId, pos: Nat, o_return_pos: Option Nat, name: Id, ty: QualifiedId,
                top_fn: QualifiedId, val: QualifiedId, o_qual: Option Qualifier): Spec =
  let fns_to_change = findOpsBetween(spc, top_fn, fun) in
  let _ = app (fn qid -> writeLine(printQualifiedId qid)) fns_to_change in
  spc

endspec
