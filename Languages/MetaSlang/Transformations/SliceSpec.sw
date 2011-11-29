SliceSpec qualifying spec
{
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

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


 op scrubSpec (spc : Spec, op_set : QualifierSet, type_set : QualifierSet) : Spec =
  let new_types =
      mapiPartialAQualifierMap (fn (q, id, v) ->
                                  if Qualified (q, id) in? type_set then
                                    Some v
                                  else 
                                    None)
                               spc.types
  in
  let new_ops =
      mapiPartialAQualifierMap (fn (q, id, v) ->
                                  if Qualified (q, id) in? op_set then
                                    Some v
                                  else 
                                    None)
                               spc.ops
  in
  let
    def filterElements (elements : SpecElements) : SpecElements =
      let
        def keep? el =
          case el of
            | Type     (qid,              _) -> qid in? type_set
            | TypeDef  (qid,              _) -> qid in? type_set
            | Op       (qid, _,           _) -> qid in? op_set && numRefinedDefs spc qid = 1
            | OpDef    (qid, refine_num,  _) -> qid in? op_set && numRefinedDefs spc qid = refine_num + 1
            | Property (_, _, _, formula, _) ->
              forall? (fn qid -> qid in? op_set) (opsInTerm formula)
              && 
              forall? (fn qid -> qid in? type_set) (typesInTerm formula)
              % | Import   (_, _, elts,       _) -> exists? (fn el -> element_filter el) elts
            | Import _ -> true
            | _ -> haskellElement? el
      in
      mapPartial (fn elt ->
                    if keep? elt then
                      Some (case elt of
                              | Import (s_tm, i_sp, elts,                a) ->
                                Import (s_tm, i_sp, filterElements elts, a)
                              | _ ->  elt)
                    else
                      None)
                 elements
  in
  let new_elements = filterElements spc.elements in
  spc << {
          types    = new_types,
          ops      = new_ops, 
          elements = new_elements
          }

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% Haskell generation calls this directly...
 op sliceSpecInfoForCode (spc        : Spec,
                          root_ops   : QualifiedIds, 
                          root_types : QualifiedIds) 
  : QualifierSet * QualifierSet =
  let chase_subtypes? = false in
  let chase_theorems? = false in
  let 
    def cut_op?   (qid : QualifiedId) : Bool = false
    def cut_type? (qid : QualifiedId) : Bool = false
  in
  sliceSpecInfo (spc, root_ops, root_types, cut_op?, cut_type?, chase_subtypes?, chase_theorems?)

 op sliceSpecInfo (spc             : Spec, 
                   root_ops        : QualifiedIds, 
                   root_types      : QualifiedIds, 
                   cut_op?         : QualifiedId -> Bool, % stop recursion at these, and do not include them
                   cut_type?       : QualifiedId -> Bool, % stop recursion at these, and do not include them
                   chase_subtypes? : Bool, 
                   chase_theorems? : Bool)
  : QualifierSet * QualifierSet =
  let 
    def eq_op_qid (Qualified (q, id)) = Qualified (q, "eq_" ^ id)
      
    def newOpsInTerm (tm : MSTerm, newopids : QualifiedIds, op_set : QualifierSet) : QualifiedIds =
      foldTerm (fn opids -> fn tm ->
                  case tm of
                    | Fun (Op (qid,_), funtype, _) ->
                      if qid nin? opids  && qid nin? op_set then
                        qid :: opids
                      else
                        opids
                    | Fun (Equals, Arrow (Product ([("1", Base (type_qid, _, _)), _], _), _, _), _) ->
                      let eq_qid = eq_op_qid type_qid in
                      if eq_qid nin? opids  && eq_qid nin? op_set then % avoid millions of duplicate entries
                        eq_qid :: opids
                      else
                        opids
                    | _ -> opids,
                fn result -> fn _ -> result,
                fn result -> fn _ -> result)
               newopids 
               tm

    def newOpsInType (ty : MSType, newopids : QualifiedIds, op_set : QualifierSet) : QualifiedIds =
      foldType (fn opids -> fn tm ->
                  case tm of
                    | Fun (Op (qid,_), funtype, _) ->
                      if qid nin? opids && qid nin? op_set then
                        qid :: opids
                      else
                        opids
                    | Fun (Equals, Arrow (Product ([("1", Base (type_qid, _, _)), _], _), _, _), _) ->
                      let eq_qid = eq_op_qid type_qid in
                      if eq_qid nin? opids  && eq_qid nin? op_set then % avoid millions of duplicate entries
                        eq_qid :: opids
                      else
                        opids
                    | _ -> opids,
                fn result -> fn _ -> result,
                fn result -> fn _ -> result)
               newopids 
               ty

    def newTypesInTerm (tm : MSTerm, newtypeids : QualifiedIds, type_set : QualifierSet) : QualifiedIds =
      foldTerm (fn result -> fn _ -> result,
                fn result -> fn t ->
                  case t of
                    | Base (qid,_,_) | qid nin? result && qid nin? type_set -> qid :: result
                    | _ -> result,
                fn result -> fn _ -> result)
               newtypeids 
               tm
      
    def newTypesInType (ty : MSType, newtypeids : QualifiedIds, type_set : QualifierSet) : QualifiedIds =
      foldType (fn result -> fn _ -> result,
                fn result -> fn t ->
                  case t of
                    | Base (qid,_,_) | qid nin? result && qid nin? type_set -> qid :: result
                    | _ -> result,
                fn result -> fn _ -> result)
               newtypeids 
               ty
      
    def iterateDeps (new_ops, new_types, op_set, type_set) =
      if new_ops = [] && new_types = [] then 
        (op_set, type_set)
      else
        let op_set   = addList (op_set,   new_ops)   in
        let type_set = addList (type_set, new_types) in
        let new_ops_in_ops = 
            foldl (fn (newopids, qid) ->
                     case findTheOp (spc, qid) of
                       | Some opinfo -> newOpsInTerm (opinfo.dfn, newopids, op_set)
                       | None -> newopids)
                  [] 
                  new_ops
        in
        let new_ops_in_ops_or_types = 
            if chase_subtypes? then 
              foldl (fn (newopids, qid) ->
                       case findTheType (spc, qid) of
                         | Some typeinfo -> newOpsInType(typeinfo.dfn, newopids, op_set)
                         | None -> newopids)
                    new_ops_in_ops
                    new_types
            else
              new_ops_in_ops
        in
        let new_types_in_ops = 
            foldl (fn (newtypeids, qid) ->
                     case findTheOp (spc, qid) of
                       | Some opinfo -> newTypesInTerm (opinfo.dfn, newtypeids, type_set)
                       | None -> newtypeids)
                  [] 
                  new_ops
        in
        let new_types_in_ops_or_types = 
            foldl (fn (newtypeids, qid) ->
                     case findTheType (spc, qid) of
                       | Some typeinfo -> newTypesInType (typeinfo.dfn, newtypeids, type_set)
                       | None -> newtypeids)
                  new_types_in_ops
                  new_types
        in
        iterateDeps (new_ops_in_ops_or_types, new_types_in_ops_or_types, op_set, type_set)
  in
  let (op_set, type_set) = iterateDeps(root_ops, root_types, emptySet, emptySet) in
  (op_set, type_set)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op sliceSpec (spc             : Spec, 
               root_ops        : QualifiedIds,        % include these and things they recursively mention
               root_types      : QualifiedIds,        % include these and things they recursively mention
               cut_op?         : QualifiedId -> Bool, % stop recursion at these, and do not include them
               cut_type?       : QualifiedId -> Bool, % stop recursion at these, and do not include them
               chase_subtypes? : Bool,                % recur through subtype predicates and quotient relations
               chase_theorems? : Bool)                % recur through axioms and theorems that mention included types and ops
  : Spec =
  let (op_set, type_set) = sliceSpecInfo (spc, root_ops, root_types, cut_op?, cut_type?, chase_subtypes?, chase_theorems?) in
  let sliced_spc         = scrubSpec     (spc, op_set,   type_set)                                                         in
  sliced_spc

 op sliceSpecForCode (spc             : Spec, 
                      root_ops        : QualifiedIds,        % include these and things they recursively mention
                      root_types      : QualifiedIds,        % include these and things they recursively mention
                      cut_op?         : QualifiedId -> Bool, % stop recursion at these, and do not include them
                      cut_type?       : QualifiedId -> Bool) % stop recursion at these, and do not include them
  : Spec =
  let chase_subtypes? = false in  % do not recur through subtype predicates and quotient relations
  let chase_theorems? = false in  % do not recur through axioms and theorems that mention included types and ops
  sliceSpec (spc, root_ops, root_types, cut_op?, cut_type?, chase_subtypes?, chase_theorems?)
  
}
