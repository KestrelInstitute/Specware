(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* Search for types with no definition that may be empty and define them to be sutypes of an inhabited type.
  E.g. type T is replaced by 
  type T__NonEmpty 
  op T__predicate: T__NonEmpty -> Bool
  type T = (T__NonEmpty | T__predicate)

  Evidence of non emptiness is 
  op foo: T
  axiom there_is_a_T is ex(t: T) true

  For type constructors you need to consider whether the type parameter is empty
*)

EmptyTypes qualifying
spec
  import ../Specs/Utilities

  op specConstrainsTypeInhabited?(ty: MSType, spc: Spec): Bool =
     existsOpWithType?(ty, spc)
    || existsTrueExistentialAxiomForType?(ty, spc)

  op knownNonEmptyTypeQID?(qid: QualifiedId, spc: Spec): Bool =
    qid in? knownNonEmptyBaseTypes
      || (case findTheType(spc, qid) of
            | None -> false
            | Some info ->
          let (tvs, dfn) = unpackFirstTypeDef info in
          ~(tvs = [] && anyType? dfn)
            || specConstrainsTypeInhabited?(mkBase(qid,[]), spc)
            || knownNonEmptyType?(dfn, spc))

  op knownNonEmptyType?(ty: MSType, spc: Spec): Bool =
    case ty of
      | Base(qid, arg_tys, _) -> knownNonEmptyTypeQID?(qid, spc)
      | Product(id_prs, _) -> forall? (fn (_, tyi) -> knownNonEmptyType?(tyi, spc)) id_prs
      | _ -> specConstrainsTypeInhabited?(ty, spc)

  op emptyTypesToSubtypes(spc: Spec): Spec = 
    let def fixSpecElts(elts: List SpecElement, type_map: TypeMap, op_map: OpMap)
              : List SpecElement * TypeMap * OpMap =
          case elts of
            | [] -> ([], type_map, op_map)
            | elt::rest ->
          let (new_elts, new_type_map, new_op_map) = fixSpecElts(rest, type_map, op_map) in
          case elt of
            | Type(qid as Qualified(q,id),a) | ~(knownNonEmptyTypeQID?(qid, spc)) ->
              let new_type_name = id^"__NonEmpty" in
              let new_type_qid = Qualified(q, new_type_name) in
              let new_pred_name = id^"__Predicate" in
              let new_pred_qid = Qualified(q, new_pred_name) in
              let new_pred_type = mkArrow(Base(new_type_qid, [], a), boolType) in
              let qid_def = Subtype(Base(new_type_qid, [], a),
                                    mkOp(new_pred_qid, new_pred_type),
                                    a)
              in
              let new_type_map = insertAQualifierMap(new_type_map, q, new_type_name,
                                                     {names = [new_type_qid], dfn = Any a})
              in
              let new_type_map = insertAQualifierMap(new_type_map, q, id,
                                                     {names = [qid], dfn = qid_def})
              in
              let new_op_def = maybePiTerm([], TypedTerm(Any a, new_pred_type, a)) in
              let new_op_map = insertAQualifierMap(new_op_map, q, new_pred_name,
                                                   {names = [new_pred_qid], fixity = Nonfix,
                                                    fullyQualified? = false, % Conservative
                                                    dfn = new_op_def})
              in
              ([Type(new_type_qid,a),
                Op(new_pred_qid,false,a),
                TypeDef(qid, a)]
               ++ new_elts,
               new_type_map, new_op_map)
              
            | Import(s_tm, i_sp, i_elts, a) ->
              let (new_i_elts, new_type_map, new_op_map) = fixSpecElts(i_elts, new_type_map, new_op_map) in
              (Cons(Import(s_tm, i_sp, new_i_elts, a), new_elts),
               new_type_map, new_op_map)
            | _ -> (Cons(elt, new_elts), new_type_map, new_op_map) 
    in
    let (new_elts, new_type_map, new_op_map) = fixSpecElts(spc.elements, spc.types, spc.ops) in
    let result = spc << {elements = new_elts,
                         ops = new_op_map,
                         types = new_type_map}
    in
    % let _ = writeLine(printSpec result) in
    result

endspec
