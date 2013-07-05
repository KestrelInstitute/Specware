AddTypeConstructors qualifying spec

import /Languages/MetaSlang/CodeGen/CodeGenUtilities

%% from Prove.sw :
%%    let (spc,constrOps) = addTypeConstructorsForSnark spc in
%%    let (spc,constrOps) = addProductTypeConstructors spc in
%%    let (spc,constrOps) = addProductAccessors spc in

(*
 * SpecTransform.addTypeConstructors is a transform that adds the constructor ops 
 * for each element of each co-product type, 
 * 
 * For example, for Lists, the following ops are added:
 *  op [a] List__Cons (x1 : a, x2 : List a) : List a = (embed cons) (x1, x2)
 *  op [a] List_nil ()                      : List a = embed nil
 *)

op true_cond : MSTerm = mkTrue ()

op SpecTransform.addTypeConstructors (spc : Spec) : Spec =
 let (spc, _) = addTypeConstructorsInternal (spc, false) in 
 % ignore names of constrOps
 spc

op addTypeConstructorsForSnark (spc : Spec) : Spec * OpNames =
 addTypeConstructorsInternal (spc, true)

op addTypeConstructorsInternal (spc : Spec, snark? : Bool) : Spec * OpNames =
 foldriAQualifierMap (fn (q, id, typeinfo, (spc, op_names)) ->
                        let (spc, constructor_names) = 
                            addTypeConstructorsFromType (spc, 
                                                         snark?, 
                                                         Qualified (q, id),
                                                         typeinfo) 
                        in
                        (spc, op_names ++ constructor_names))
                     (spc, []) 
                     spc.types

op addTypeConstructorsFromType (spc       : Spec, 
                                snark?    : Bool, 
                                type_name : TypeName,
                                type_info : TypeInfo)
 : Spec * OpNames =
 if ~ (definedTypeInfo? type_info) then
   (spc, [])
 else
   let (tvs, typ)  = unpackFirstTypeDef type_info         in
   let type_vars   = map (fn tv -> TyVar (tv, noPos)) tvs in
   let parent_type = Base (type_name, type_vars, noPos)   in
   case typ of
     | CoProduct (alternatives, _) -> 
       foldl (fn ((spc, op_names), (alt_id, opt_alt_type)) ->

                %% A coproduct alternative (opt_alt_type) might be None, for an atomic constructor,
                %% or Some MSType, for a constructor from arguments.

                let op_name as Qualified (op_q, alt_id) = getConstructorOpName (type_name, alt_id, snark?) in
                let alt_type         = case opt_alt_type of
                                         | Some alt_type -> alt_type
                                         | _  -> Product ([], noPos)
                in
                let has_arg?         = case opt_alt_type of
                                         | Some _ -> true
                                         | _ -> false
                in
                let op_type          = Arrow (alt_type, parent_type, noPos)                     in
                let (op_pat, op_tm)  = getPatternAndTermFromType alt_type                       in
                let op_fn            = Fun (Embed (alt_id, has_arg?), op_type, noPos)           in
                let op_body          = if has_arg? then
                                         Apply (op_fn, op_tm, noPos)
                                       else
                                         op_fn
                in
                let op_lambda        = Lambda ([(op_pat, true_cond, op_body)], noPos)           in
                let op_dfn           = maybePiTerm (tvs, TypedTerm (op_lambda, op_type, noPos)) in
                let op_info          = {names           = [op_name], 
                                        fixity          = Nonfix, 
                                        dfn             = op_dfn,
                                        fullyQualified? = false}
                in
                let new_ops          = insertAQualifierMap (spc.ops, op_q, alt_id, op_info)     in
                let new_spec         = setOps (spc, new_ops)                                    in
                let op_names         = op_name :: op_names                                      in
                (new_spec, op_names))
             (spc, []) 
             alternatives
     | _ -> (spc, [])

op getConstructorOpName (Qualified (type_q, type_id) : TypeName,
                         alt_id                      : String,
                         snark?                      : Bool)
 : OpName =
 % the two _'s are important: that how the constructor op names are
 % distinguished from other opnames (hack)
 let constructor_id = 
      if snark? then 
        "embed__" ^ alt_id
      else
        type_id ^ "__" ^ alt_id
 in
 Qualified (type_q, constructor_id)

(*
 * addProductTypeConstructors adds a Constructor op for each product type.
 * E.g. for type P = {a: A, b: B}, the following op is added:
 * op mk_Record_P (a : A, b : B) : P = (a, b)
 *)

op addProductTypeConstructors (spc : Spec) : Spec * OpNames =
 foldriAQualifierMap (fn (type_q, type_id, type_info, (spc, op_names)) ->
                        let type_name = Qualified (type_q, type_id) in
                        let (spc, constructor_names) =
                            addProductTypeConstructorsFromType (spc, 
                                                                type_name,
                                                                type_info) 
                        in
                        (spc, op_names ++ constructor_names))
                     (spc, []) 
                     spc.types

op addProductTypeConstructorsFromType (spc       : Spec,
                                       type_name : TypeName,
                                       type_info : TypeInfo)
 : Spec * OpNames =
 %% TODO: THIS IS NONSENSE
 if ~ (definedTypeInfo? type_info) then
   (spc, [])
 else
   let (tvs, type_dfn) = unpackFirstTypeDef type_info in
   case type_dfn of
     | Product (fields, _) -> 
       (let op_name as Qualified (op_q, op_id) = getRecordConstructorOpName type_name  in
	let type_vars       = map (fn tv -> TyVar (tv, noPos)) tvs                     in
        let parent_type     = Base (type_name, type_vars, noPos)                       in
        let op_type         = Arrow (type_dfn, parent_type, noPos)                     in
        let (op_pat, op_tm) = getPatternAndTermFromType type_dfn                       in
        let op_lambda       = Lambda ([(op_pat, true_cond, op_tm)], noPos)             in
        let op_dfn          = maybePiTerm (tvs, TypedTerm (op_lambda, op_type, noPos)) in
        let op_info         = {names          = [op_name], 
                               fixity          = Nonfix, 
                               dfn             = op_dfn,
                               fullyQualified? = false}
        in
        let new_ops         = insertAQualifierMap (spc.ops, op_q, op_id, op_info)      in
        let new_spec        = setOps (spc, new_ops)                                    in
        let op_names        = [op_name]                                                in
        (addElementAfter (new_spec,
                          % TODO: maybe change "OpDef opqid" to "OpDecl (opqid, true)"
                          OpDef (op_name, 0, [], noPos),
                          TypeDef (type_name, noPos)), 
         op_names)) 
     | _ -> (spc, [])

(*
 * addProductAccessors adds the accessor op for each element of each product type.
 * E.g. for type P = {a: A, b: B}, the following ops are added:
 *  op project_P_a (p : P) : A = project (a) p
 *  op project_P_b (p : P) : B = project (b) p
 *)

op addProductAccessors (spc : Spec) : Spec * OpNames =
 foldriAQualifierMap (fn (type_q, type_id, type_info, (spc, op_names)) ->
                        let type_name = Qualified (type_q, type_id) in
                        let (spc, accessor_names) =
                            addProductAccessorsFromType (spc, 
                                                         type_name,
                                                         type_info) 
                        in
                        (spc, op_names ++ accessor_names))
                     (spc, []) 
                     spc.types

op addProductAccessorsFromType (spc                                 : Spec,
                                type_name as Qualified (_, type_id) : TypeName,
                                type_info                           : TypeInfo)
 : Spec * OpNames =
 if ~ (definedTypeInfo? type_info) then
   (spc, [])
 else
   let (tvs, type_dfn) = unpackFirstTypeDef       type_info    in
   let type_vars       = map (fn tv -> TyVar (tv, noPos)) tvs  in
   let parent_type     = Base (type_name, type_vars, noPos)    in
   let simplified_dfn  = stripSubtypesAndBaseDefs spc type_dfn in
   case simplified_dfn of
     | Product (fields, _) ->
       (foldl (fn ((spc, op_names), (field_id, field_type)) ->
                 let op_name as Qualified (op_q, op_id) = getAccessorOpName (type_id, type_name, field_id) in
                 let op_type         = Arrow (parent_type, field_type, noPos)                   in
                 let (op_pat, op_tm) = getPatternAndTermFromType field_type                     in
                 let op_fn           = Fun    (Project (field_id), op_type,             noPos)  in
                 let op_body         = Apply  (op_fn, op_tm,                            noPos)  in
                 let op_lambda       = Lambda ([(op_pat, true_cond, op_body)],          noPos)  in
                 let op_dfn          = maybePiTerm (tvs, TypedTerm (op_lambda, op_type, noPos)) in
                 let op_info         = {names           = [op_name], 
                                        fixity          = Nonfix, 
                                        dfn             = op_dfn,
                                        fullyQualified? = false}
                 in
                 let new_ops         = insertAQualifierMap (spc.ops, op_q, op_id, op_info)      in
                 let op_names        = op_name :: op_names                                      in
                 (addElementAfter (setOps (spc, new_ops), 
                                   OpDef (op_name, 0, [], noPos), 
                                   TypeDef (type_name,noPos)), 
                  op_names))  % TODO: maybe change "OpDef opqid" to "OpDecl (opqid, true)"
              (spc, [])
              fields)
     | _ -> (spc, [])

end-spec
