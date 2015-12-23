(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

AddEqOps qualifying spec

import /Languages/MetaSlang/Specs/StandardSpec
import /Languages/MetaSlang/Specs/Environment

(*
 * add an equality op for each user type
 *)

op aePos : Position = Internal "AddEqOps"

op SpecTransform.addEqOps (spc : Spec) : Spec =
  foldTypeInfos (fn (info, spc) ->
                   let name = primaryTypeName info               in
                   let spc  = addEqOpsFromType (spc, name, info) in
                   spc)
                spc 
                spc.types

op addEqOpsFromType (spc       : Spec, 
                     type_name : QualifiedId, 
                     type_info : TypeInfo) 
 : Spec =
 let

   def get_lambda_term (typ, body) =
     let pat  = RecordPat ([("1", VarPat (("x", typ), aePos)), 
                            ("2", VarPat (("y", typ), aePos))],
                           aePos)
     in
     Lambda ([(pat, trueTerm, body)], aePos)

   def get_equality_type typ =
     Arrow (Product ([("1", typ), ("2", typ)], aePos),
            Boolean aePos,
            aePos)

   def add_eq_op (spc, eq_name as Qualified (eq_q, eq_id), arg_type, body) =
     let arg_type = case arg_type of
                      | Base (name, args, _) ->
                        let tvs = tabulate (length args,
                                            fn i -> TyVar ("tv" ^ show i, aePos))
                        in
                        Base (name, tvs, aePos)
                      | _ ->
                        arg_type
     in
     let eq_lambda = get_lambda_term (arg_type, body)      in
     let eq_type   = get_equality_type arg_type            in
     let eq_dfn    = TypedTerm (eq_lambda, eq_type, aePos) in
     case findTheOp (spc, eq_name) of
       | Some info -> 
         if equalTermAlpha? (info.dfn, eq_dfn) then
           spc
         else
           let _ = writeLine("Warning: attempt to redefine " ^ show eq_name) in
           let _ = writeLine("from: " ^ printTerm info.dfn)                  in
           let _ = writeLine("  to: " ^ printTerm eq_dfn)                    in
           let _ = writeLine("No change made.")                              in
           spc
       | _ ->
         let eq_info   = {names           = [eq_name],
                          fixity          = Nonfix,
                          dfn             = eq_dfn,
                          fullyQualified? = false}
         in
         let ops = insertAQualifierMap (spc.ops, eq_q, eq_id, eq_info) in
         let elt = Op (eq_name, true, aePos)                           in
         let spc = setOps        (spc, ops)                            in
         let spc = appendElement (spc, elt)                            in
         spc

   def get_eq_term_from_product_fields (fields, product_type, varx, vary) =
     let and_op   = mkAndOp aePos in
     foldr (fn ((field_id, field_type), body) ->
              let projtyp = Arrow (product_type, field_type, aePos) in
              let eq_type = Arrow (Product ([("1", field_type), ("2", field_type)], aePos),
                                   Boolean aePos, 
                                   aePos) 
              in
              let projection    = Fun (Project (field_id), projtyp, aePos) in
              let x_field       = Apply (projection, varx, aePos) in
              let y_field       = Apply (projection, vary, aePos) in
              let field_eq_test = Apply (Fun (Equals, eq_type, aePos),
                                         Record ([("1", x_field), 
                                                  ("2", y_field)], 
                                                 aePos), 
                                         aePos)
              in
              if equalTermAlpha? (body, trueTerm) then % first case
                field_eq_test
              else
                Apply (and_op,
                       Record ([("1", field_eq_test), ("2", body)], aePos), 
                       aePos))
           trueTerm 
           fields
 in
 if ~ (definedTypeInfo? type_info) then
   spc
 else
   let (tvs, typ) = unpackFirstTypeDef type_info in
   %% Was unfoldStripType which is unnecessary and dangerous because of recursive types
   let simplified_type = stripSubtypesAndBaseDefs spc typ in
   case simplified_type of
     | Boolean _ -> spc
     | Base (Qualified ("Nat",       "Nat"),     [], _) -> spc
     | Base (Qualified ("Integer",   "Int"),     [], _) -> spc
     | Base (Qualified ("Character", "Char"),    [], _) -> spc
     | Base (Qualified ("String",    "String"),  [], _) -> spc
    %| Base (Qualified ("??",        "Float"),   [], _) -> spc
     | _ ->
       let eq_arg_type = Base (type_name, 
                            map (fn tv -> TyVar (tv, aePos)) tvs,
                            aePos)
       in
       let varx    = Var (("x", eq_arg_type), aePos) in
       let vary    = Var (("y", eq_arg_type), aePos) in
       let eq_name = get_equality_name type_name     in
       % check for aliases first
       case typ of
         | Base (alias_type_name, _, _) ->
           % define the equality op in terms of the aliased type
           let alias_eq_name = get_equality_name alias_type_name                         in
           let alias_eq_type = get_equality_type eq_arg_type                             in

           %% Although the alias equality op is defined on the alias type,
           %% the type of the Fun here uses the types of the original args.
           let alias_eq_fun  = Fun    (Op (alias_eq_name, Nonfix), alias_eq_type, aePos) in
           let alias_eq_args = Record ([("1", varx), ("2", vary)],                aePos) in
           let eq_body       = Apply  (alias_eq_fun, alias_eq_args,               aePos) in

           %% Add an equality op for the aliased type.
           let spc           = add_eq_op (spc, alias_eq_name, typ, Any aePos)            in
           %% Add an equality op for the original type, invoking the equality op above.
           let spc           = add_eq_op (spc, eq_name, eq_arg_type, eq_body)            in
           spc

         | _ ->
           case typ of
             | Product (fields, _) -> 
               let eq_body = get_eq_term_from_product_fields (fields, eq_arg_type, varx, vary) in
               add_eq_op (spc, eq_name, eq_arg_type, eq_body)
             | CoProduct (fields, _) ->
               (let match =
                    foldr (fn ((field_id, opt_field_type), match) ->
                             let xpat = EmbedPat (field_id, 
                                                  case opt_field_type of 
                                                    | None -> None 
                                                    | Some field_type -> 
                                                      Some (VarPat (("x0", field_type), aePos)), 
                                                  eq_arg_type, 
                                                  aePos) 
                             in
                             let ypat = EmbedPat (field_id, 
                                                  case opt_field_type of 
                                                    | None -> None 
                                                    | Some field_type -> 
                                                      Some (VarPat (("y0", field_type), aePos)), 
                                                  eq_arg_type, 
                                                  aePos) 
                             in
                             let eq_field_type =
                                 let 
                                   def nonproduct_eq_test field_type =
                                     let eq_type = get_equality_type field_type in
                                     Apply (Fun (Equals, eq_type, aePos), 
                                            Record ([("1", Var (("x0", field_type), aePos)), 
                                                     ("2", Var (("y0", field_type), aePos))],
                                                    aePos), 
                                            aePos)
                                 in
                                 case opt_field_type of
                                   | None -> trueTerm
                                   | Some (field_type as Base _) -> nonproduct_eq_test field_type
                                   | Some field_type ->
                                     %% Was unfoldStripType which is unnecessary and dangerous because of recursive types
                                     let simplified_field_type = stripSubtypesAndBaseDefs spc field_type in
                                     case simplified_field_type of
                                       | Product (fields, _) -> 
                                         get_eq_term_from_product_fields (fields, 
                                                                          field_type, 
                                                                          Var (("x0", field_type), aePos), 
                                                                          Var (("y0", field_type), aePos))
                                       | _ -> nonproduct_eq_test field_type
                             in
                             let rule_1    = (ypat,                         trueTerm, eq_field_type) in
                             let rule_2    = (WildPat (eq_arg_type, aePos), trueTerm, falseTerm)     in
                             let ymatch    = [rule_1, rule_2] in
                             let case_term = Apply (Lambda (ymatch, aePos), vary, aePos) in
                             Cons ((xpat, trueTerm, case_term), match))
                          []
                          fields
                in
                let eq_body = Apply (Lambda (match, aePos), varx, aePos) in
                add_eq_op (spc, eq_name, eq_arg_type, eq_body))
             | _ -> spc

op get_equality_name (Qualified (q, id) : QualifiedId) : QualifiedId =
 Qualified (q, "eq_" ^ id)


end-spec
