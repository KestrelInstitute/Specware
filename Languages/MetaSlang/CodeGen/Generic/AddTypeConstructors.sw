(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

AddTypeConstructors qualifying spec

import /Languages/MetaSlang/CodeGen/CodeGenUtilities

(*
 * SpecTransform.addTypeConstructors is a transform that adds the constructor ops 
 * for each element of each co-product type, 
 * 
 * For example, for Lists, the following ops are added:
 *  op [a] List__Cons (x1 : a, x2 : List a) : List a = (embed cons) (x1, x2)
 *  op [a] List_nil ()                      : List a = embed nil
 *)

op atPos : Position = Internal "AddTypeConstructors"

op getConstructorId (type_id : Id,  Qualified(_,alt_id) : QualifiedId, snark? : Bool) : Id =
 % the two _'s are important: that how the constructor op names are
 % distinguished from other opnames (hack)
 if snark? then 
   "embed__" ^ alt_id
 else
   type_id ^ "__" ^ alt_id

op newCoProductOpInfos (spc          : Spec, 
                        type_name    : TypeName,
                        tvs          : TyVars,
                        type_dfn     : MSType,
                        type_ref     : MSType,
                        alternatives : List (QualifiedId * Option MSType),
                        snark?       : Bool)
  : List OpInfo =
  %% e.g., type X = | A | B Nat
  let Qualified (type_q, type_id) = type_name in
  map (fn (alt_id, opt_alt_type) ->
         %% A coproduct alternative (opt_alt_type) might be None, for an atomic constructor,
         %% or Some MSType, for a constructor from arguments.

         let op_q    = type_q                                     in    
         let op_id   = getConstructorId (type_id, alt_id, snark?) in
         let op_name = Qualified (op_q, op_id)                    in

         let (op_body, op_type) =
             case opt_alt_type of
               | Some alt_type -> 
                 %% e.g.  | B Nat
                 let (op_pat, op_tm)  = getPatternAndTermFromType alt_type                in
                 let op_type          = Arrow  (alt_type, type_ref,                atPos) in
                 let op_fn            = Fun    (Embed (alt_id, true), op_type,     atPos) in
                 let lambda_body      = Apply  (op_fn, op_tm,                      atPos) in
                 let op_lambda        = Lambda ([(op_pat, trueTerm, lambda_body)], atPos) in
                 (op_lambda, op_type)
               | _  -> 
                 %% e.g.  | A
                 let op_type     = type_ref                                    in
                 let op_constant = Fun (Embed (alt_id, false), op_type, atPos) in
                 (op_constant, op_type)
         in

         let op_dfn  = maybePiTerm (tvs, TypedTerm (op_body, op_type, atPos)) in
         let op_info = {names           = [op_name], 
                        fixity          = if some? opt_alt_type then Constructor1 else Constructor0, 
                        dfn             = op_dfn,
                        fullyQualified? = false}
         in
         op_info)
     alternatives
 
(*
 * addProductTypeConstructors adds a Constructor op for each product type.
 * E.g. for type P = {a: A, b: B}, the following op is added:
 * op mk_Record_P (a : A, b : B) : P = (a, b)
 *)

op newProductConstructor (spc       : Spec, 
                          type_name : TypeName,
                          tvs       : TyVars,
                          type_dfn  : MSType,
                          type_ref  : MSType,
                          fields    : List (Id * MSType),
                          snark?    : Bool)
 : OpInfo =
 %% TODO: FIX THIS NONSENSE
 let op_name as Qualified (op_q, op_id) = getRecordConstructorOpName type_name  in
 let (op_pat, op_tm) = getPatternAndTermFromType type_dfn                       in
 let op_type         = Arrow       (type_dfn, type_ref,                 atPos)  in
 let op_lambda       = Lambda      ([(op_pat, trueTerm, op_tm)],        atPos)  in
 let op_dfn          = maybePiTerm (tvs, TypedTerm (op_lambda, op_type, atPos)) in
 let op_info         = {names          = [op_name], 
                        fixity          = Nonfix, 
                        dfn             = op_dfn,
                        fullyQualified? = false}
 in
 op_info

(*
 * addProductAccessors adds the accessor op for each element of each product type.
 * E.g. for type P = {a: A, b: B}, the following ops are added:
 *  op project_P_a (p : P) : A = project (a) p
 *  op project_P_b (p : P) : B = project (b) p
 *)

op newProductAccessors (spc       : Spec, 
                        type_name : TypeName,
                        tvs       : TyVars,
                        type_dfn  : MSType,
                        type_ref  : MSType,
                        fields    : List (Id * MSType),
                        snark?    : Bool)
 : List OpInfo =
 let Qualified (type_q, type_id) = type_name in
 let simplified_dfn  = stripSubtypesAndBaseDefs spc type_dfn in
 List.map (fn (field_id, field_type) ->
        let op_name as Qualified (op_q, op_id) = getAccessorOpName (type_id, type_name, field_id) in
        let (op_pat, op_tm) = getPatternAndTermFromType type_ref                       in
        let op_type         = Arrow  (type_ref, field_type,                    atPos)  in
        let op_fn           = Fun    (Project (field_id), op_type,             atPos)  in
        let op_body         = Apply  (op_fn, op_tm,                            atPos)  in
        let op_lambda       = Lambda ([(op_pat, trueTerm, op_body)],           atPos)  in
        let op_dfn          = maybePiTerm (tvs, TypedTerm (op_lambda, op_type, atPos)) in
        let op_info         = {names           = [op_name], 
                               fixity          = Nonfix, 
                               dfn             = op_dfn,
                               fullyQualified? = false}
        in
        op_info)
     fields

op newProductOpInfos (spc       : Spec, 
                      type_name : TypeName,
                      tvs       : TyVars,
                      type_dfn  : MSType,
                      type_ref  : MSType,
                      fields    : List (Id * MSType),
                      snark?    : Bool)
 : List OpInfo =
 let constructor = newProductConstructor (spc,
                                          type_name,
                                          tvs,
                                          type_dfn,
                                          type_ref,
                                          fields,
                                          snark?)
 in
 let accessors = newProductAccessors (spc,
                                      type_name,
                                      tvs,
                                      type_dfn,
                                      type_ref,
                                      fields,
                                      snark?)
 in
 constructor :: accessors

op newOpInfosForType (spc       : Spec, 
                      type_name : TypeName,
                      type_info : TypeInfo,
                      snark?    : Bool)
 : List OpInfo =
 if ~ (definedTypeInfo? type_info) then
   []
 else
   let (tvs, type_dfn) = unpackFirstTypeDef type_info         in
   let type_vars       = map (fn tv -> TyVar (tv, atPos)) tvs in
   let type_ref        = Base (type_name, type_vars, atPos)   in
   case type_dfn of

     | CoProduct (alternatives, _) -> 
       newCoProductOpInfos (spc,
                            type_name,
                            tvs,
                            type_dfn,
                            type_ref,
                            alternatives,
                            snark?)

     | Product (fields, _) -> 
       newProductOpInfos (spc,
                          type_name,
                          tvs,
                          type_dfn,
                          type_ref,
                          fields,
                          snark?)

     | _ -> []

op addTypeConstructorsInternal (spc : Spec, snark? : Bool) : Spec =
 let new_op_infos =
     foldriAQualifierMap (fn (type_q, type_id, type_info, op_infos) ->
                            let type_name = Qualified (type_q, type_id) in
                            op_infos ++
                            newOpInfosForType (spc, 
                                               type_name, 
                                               type_info, 
                                               snark?))
                        []
                        spc.types
 in
 let (new_ops, reversed_new_elements) = 
     foldl (fn ((ops, reversed_elements), op_info) ->
              let op_name as Qualified (op_q, op_id) = primaryOpName op_info in
              let ops               = insertAQualifierMap (ops, op_q, op_id, op_info) in
              let element           = Op (op_name, true, atPos)                       in
              let reversed_elements = element :: reversed_elements                    in
              (ops, reversed_elements))
           (spc.ops, reverse spc.elements)
           new_op_infos
 in
 let spc = setOps      (spc, new_ops)                       in
 let spc = setElements (spc, reverse reversed_new_elements) in
 spc

op SpecTransform.addTypeConstructors (spc : Spec) : Spec =
 addTypeConstructorsInternal (spc, false)

end-spec
