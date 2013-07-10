TypeAllTerms qualifying spec

import /Languages/MetaSlang/Specs/Environment

op fullyType (term : MSTerm, typ : MSType, spc  : Spec) : MSTerm =
 let unfolded_type = unfoldBase (spc, typ) in
 let
   def typeApply (t1, t2) = 
     let t1_type          = termType t1               in
     let unfolded_t1_type = unfoldBase (spc, t1_type) in
     case unfolded_t1_type of
       | Arrow (dom, rng, _) ->
         let new_t1 = fullyType (t1, t1_type, spc) in
         let new_t2 = fullyType (t2, dom, spc)     in
         Apply (new_t1, new_t2, noPos)
       | _ ->
         let _ = writeLine ("Internal confusion: Type for applied term is not an Arrow")       in
         let _ = writeLine (" Apply      : " ^ printTerm term)             in
         let _ = writeLine (" Type of t1 : " ^ printType t1_type)          in
         let _ = writeLine ("         => : " ^ printType unfolded_t1_type) in
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
                         let _ = writeLine ("Internal confusion: Product field " ^ product_id ^ " doesn't match record field " ^ record_id) in
                         let _ = writeLine (" Record  : " ^ printTerm term)          in
                         let _ = writeLine (" Product : " ^ printType unfolded_type) in
                         (record_id, record_term))
                    (record_fields,
                     product_fields)
           in
           Record (typed_record_fields, noPos)
         else
           let _ = writeLine ("Internal confusion: Record term inconsistent with Product type") in
           let _ = writeLine (" Record  : " ^ printTerm term)          in
           let _ = writeLine (" Product : " ^ printType unfolded_type) in
           Record (record_fields, noPos)
      | _ ->
        let _ = writeLine ("Internal confusion: Type for record is not a Product")      in
        let _ = writeLine (" Record : " ^ printTerm term)          in
        let _ = writeLine ("   Type : " ^ printType typ)           in
        let _ = writeLine ("     => : " ^ printType unfolded_type) in
        term

   def typeBind (binder, vars, body) = 
     let new_body = fullyType (body, Boolean noPos, spc) in
     Bind (binder, vars, new_body, noPos)

   def typeThe (var, body) = 
     let new_body = fullyType (body, typ, spc) in
     The (var, new_body, noPos)

   def typeLet (bindings, body) = 
     let new_bindings = 
         map (fn (pat, value) -> 
                let pat_type  = patternType pat in
                let new_value = fullyType (value, pat_type, spc) in
                (pat, new_value))
             bindings 
     in
     let new_body = fullyType (body, typ, spc) in
     Let (new_bindings, new_body, noPos)

   def typeLetRec (bindings, body) = 
     let new_bindings = 
         map (fn (var as (_, var_type), value) -> 
                let new_value = fullyType (value, var_type, spc) in
                (var, new_value))
             bindings 
     in
     let new_body = fullyType (body, typ, spc) in
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
         let _ = writeLine ("Internal confusion: Type for lambda is not an Arrow")  in
         let _ = writeLine (" Lambda : " ^ printTerm term)          in
         let _ = writeLine ("   Type : " ^ printType typ)           in
         let _ = writeLine ("     => : " ^ printType unfolded_type) in
         term

   def typeIfThenElse (pred, t1, t2) = 
     let new_pred = fullyType (pred, Boolean noPos, spc) in
     let new_t1   = fullyType (t1,   typ,           spc) in
     let new_t2   = fullyType (t2,   typ,           spc) in
     IfThenElse (new_pred, new_t1, new_t2, noPos)

   def typeSeq terms = 
     let last_term :: rev_prefix = reverse terms in
     let new_last_term = fullyType (last_term, typ, spc) in
     Seq (reverse (new_last_term :: rev_prefix), noPos)

   def typeTypedTerm (trm, explicit_type) = 
     fullyType (trm, explicit_type, spc) 
     
   def typePi (tvs, trm) = 
     let new_trm = fullyType (trm, typ, spc) in
     Pi (tvs, new_trm, noPos)

   def typeAnd terms = 
     And (map (fn tm -> fullyType (tm, typ, spc)) terms, noPos)

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
       | TypedTerm  (trm, typ,           _) -> typeTypedTerm  (trm, typ)
       | Pi         (tvs, trm,           _) -> typePi         (tvs, trm)
       | And        (terms,              _) -> typeAnd        terms
       | _ -> 
         term 
 in
 TypedTerm (new, typ, noPos)


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
