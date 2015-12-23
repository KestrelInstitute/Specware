(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

TypeAllTerms qualifying spec

import /Languages/MetaSlang/Specs/Environment

op fullyType (term : MSTerm, expected_type : MSType, spc : Spec) : MSTerm =
 let unfolded_type = stripSubtypes (spc, unfoldBase (spc, expected_type)) in
 let
   def typeApply (t1, t2) = 
     let t1_type          = inferType (spc, t1)                            in
     let unfolded_t1_type = stripSubtypes (spc, unfoldBase (spc, t1_type)) in
     case unfolded_t1_type of
       | Arrow (dom, rng, _) ->
         let new_t1 = fullyType (t1, t1_type, spc) in
         let new_t2 = fullyType (t2, dom, spc)     in
         Apply (new_t1, new_t2, noPos)
       | _ ->
         let t2_type          = inferType  (spc, t2)      in
         let unfolded_t2_type = unfoldBase (spc, t2_type) in
         let _ = writeLine ("") in
         let _ = writeLine ("Internal confusion: Type for applied term is not an Arrow") in
         let _ = writeLine (" Application : " ^ printTerm term)           in
         let _ = writeLine (anyToString term)                             in
         let _ = writeLine ("          t1 : " ^ printTerm t1)             in
         let _ = writeLine ("  Type of t1 : " ^ printType t1_type)        in
         let _ = writeLine ("          => " ^ printType unfolded_t1_type) in
         let _ = writeLine ("          t2 : " ^ printTerm t2)             in
         let _ = writeLine ("  Type of t2 : " ^ printType t2_type)        in
         let _ = writeLine ("          => " ^ printType unfolded_t2_type) in
         let _ = writeLine ("") in
         term

   def typeRecord record_fields =
     case unfolded_type of
       | Product (product_fields, _) ->
         if length record_fields = length product_fields then
           let typed_record_fields = 
               map2 (fn ((record_id, record_term), (product_id, product_type)) ->
                       if record_id = product_id then
                         (record_id, fullyType (record_term, product_type, spc))
                       else
                         let _ = writeLine ("") in
                         let _ = writeLine ("Internal confusion: Product field " ^ product_id ^ " doesn't match record field " ^ record_id) in
                         let _ = writeLine (" Record : " ^ printTerm term)          in
                         let _ = writeLine ("   type : " ^ printType expected_type) in
                         let _ = writeLine ("       => " ^ printType unfolded_type) in
                         let _ = writeLine ("") in
                         (record_id, record_term))
                    (record_fields,
                     product_fields)
           in
           Record (typed_record_fields, noPos)
         else
           let _ = writeLine ("") in
           let _ = writeLine ("Internal confusion: Record term inconsistent with Product type") in
           let _ = writeLine (" Record  : " ^ printTerm term)          in
           let _ = writeLine (" Product : " ^ printType unfolded_type) in
           let _ = writeLine ("") in
           Record (record_fields, noPos)
      | _ ->
        let _ = writeLine ("") in
        let _ = writeLine ("Internal confusion: Type for record is not a Product")      in
        let _ = writeLine (" Record : " ^ printTerm term)          in
        let _ = writeLine ("   Type : " ^ printType expected_type) in
        let _ = writeLine ("       => " ^ printType unfolded_type) in
        let _ = writeLine ("") in
        term

   def typeBind (binder, vars, body) = 
     let new_body = fullyType (body, Boolean noPos, spc) in
     Bind (binder, vars, new_body, noPos)

   def typeThe (var, body) = 
     let new_body = fullyType (body, Boolean noPos, spc) in
     The (var, new_body, noPos)

   def typeLet (bindings, body) = 
     let new_bindings = 
         map (fn (pat, value) -> 
                let pat_type  = patternType pat in
                let new_value = fullyType (value, pat_type, spc) in
                (pat, new_value))
             bindings 
     in
     let new_body = fullyType (body, expected_type, spc) in
     Let (new_bindings, new_body, noPos)

   def typeLetRec (bindings, body) = 
     let new_bindings = 
         map (fn (var as (_, var_type), value) -> 
                let new_value = fullyType (value, var_type, spc) in
                (var, new_value))
             bindings 
     in
     let new_body = fullyType (body, expected_type, spc) in
     LetRec (new_bindings, new_body, noPos)

   def typeVar var = 
     var

   def typeFun (fun, ftype) = 
     Fun (fun, ftype, noPos)

   def typeRule ((pat, cond, body), rng) =
     let new_body = fullyType (body, rng, spc) in
     (pat, cond, new_body)

   def typeLambda (rules : MSRules) =
     case unfolded_type of
       | Arrow (dom, rng, _) ->
         let rules = map (fn rule -> typeRule (rule, rng)) rules in
         Lambda (rules, noPos)
       | _ ->
         let _ = writeLine ("") in
         let _ = writeLine ("Internal confusion: Type for lambda is not an Arrow")  in
         let _ = writeLine (" Lambda : " ^ printTerm term)          in
         let _ = writeLine ("   Type : " ^ printType expected_type) in
         let _ = writeLine ("       => " ^ printType unfolded_type) in
         let _ = writeLine ("") in
         term

   def typeIfThenElse (pred, t1, t2) = 
     let new_pred = fullyType (pred, Boolean noPos, spc) in
     let new_t1   = fullyType (t1,   expected_type, spc) in
     let new_t2   = fullyType (t2,   expected_type, spc) in
     IfThenElse (new_pred, new_t1, new_t2, noPos)

   def typeSeq terms = 
     let last_term :: rev_prefix = reverse terms in
     let new_last_term = fullyType (last_term, expected_type, spc) in
     Seq (reverse (new_last_term :: rev_prefix), noPos)

   def typeTypedTerm (trm, explicit_type, expected_type) = 
     fullyType (trm, explicit_type, spc) 
     
   def typePi (tvs, trm) = 
     let new_trm = fullyType (trm, expected_type, spc) in
     Pi (tvs, new_trm, noPos)

   def typeAnd terms = 
     And (map (fn tm -> fullyType (tm, expected_type, spc)) terms, noPos)

 in

 let new =
     case term of
       | Apply      (t1, t2,             _) -> typeApply      (t1, t2)
       | Record     (fields,             _) -> typeRecord     fields
       | Bind       (binder, vars, body, _) -> typeBind       (binder, vars, body)
       | The        (var, body,          _) -> typeThe        (var, body)
       | Let        (bindings, body,     _) -> typeLet        (bindings, body)
       | LetRec     (bindings, body,     _) -> typeLetRec     (bindings, body)
       | Var        (var,                _) -> term
       | Fun        (fun, ftype,         _) -> typeFun        (fun, ftype)
       | Lambda     (match,              _) -> typeLambda     match
       | IfThenElse (pred, t1, t2,       _) -> typeIfThenElse (pred, t1, t2)
       | Seq        (terms,              _) -> typeSeq        terms
       | TypedTerm  (trm, explicit_type, _) -> typeTypedTerm  (trm, explicit_type, expected_type)
       | Pi         (tvs, trm,           _) -> typePi         (tvs, trm)
       | And        (terms,              _) -> typeAnd        terms
       | _ -> 
         term 
 in
 let
   def matches? (t1, t2) =
     (possiblySubtypeOf? (t1, t2, spc))
     ||
     (case (t1, t2) of
        | (Product (fields1, _), Product (fields2, _)) 
          | (length fields1 = length fields2)
          ->
          forall? (fn ((id1, t1), (id2, t2)) -> 
                     id1 = id2 &&
                     matches? (t1, t2))
                  (zip (fields2, fields2))
        | _ ->
          false)
 in
 case maybeInferType (spc, new) of
   | Some inferred_type ->
     if matches? (inferred_type, expected_type) then
       new
     else
       % let _ = writeLine ("") in
       % let _ = writeLine ("Adding type for " ^ printTerm new) in
       % let _ = writeLine ("inferred type = " ^ printType inferred_type) in
       % let _ = writeLine ("     new type = " ^ printType expected_type) in
       % let _ = writeLine ("") in
       TypedTerm (new, expected_type, noPos)
   | _ ->
     %% This should not be possible once the type checker has run
     let _ = writeLine ("") in
     let _ = writeLine ("Could not infer type for " ^ printTerm new) in
     let _ = writeLine ("using expected type instead: " ^ printType expected_type) in
     let _ = writeLine ("") in
     TypedTerm (new, expected_type, noPos)

%% ================================================================================
%% SpecTransform.typeAllTerms is a user-invocable transformation that explicitly
%% types every sub-term with the type imposed by its context.
%% This allows later transformations to process every sub-term in the context of
%% seeing it directly within a TypedTerm.
%% ================================================================================

op SpecTransform.typeAllTerms (spc : Spec) : Spec =
 let used_names = StringSet.fromList (qualifierIds spc.ops) in
 let 
   def revise dfn =
     let (tvs, typ, term) = unpackFirstTerm dfn        in
     let term1            = fullyType (term, typ, spc) in
     maybePiTerm (tvs, TypedTerm (term1, typ, noPos))
 in
 let new_ops = 
     mapOpInfos (fn info -> 
                   let (old_decls, old_defs) = opInfoDeclsAndDefs info                     in
                   let new_defs              = map revise old_defs                         in
                   let new_dfn               = maybeAndTerm (old_decls ++ new_defs, noPos) in
                   info << {dfn = new_dfn})
                spc.ops
 in
 setOps (spc, new_ops)

end-spec
