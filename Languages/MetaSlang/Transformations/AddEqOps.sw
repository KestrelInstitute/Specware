AddEqOps qualifying spec

import /Languages/MetaSlang/Specs/StandardSpec
import /Languages/MetaSlang/Specs/Environment

(*
 * add an equality op for each user type
 *)

op SpecTransform.addEqOps (spc : Spec) : Spec =
 foldriAQualifierMap (fn (q, id, typeinfo, spc) ->
                        addEqOpsFromType (spc, Qualified (q, id), typeinfo))
                     spc 
                     spc.types

op addEqOpsFromType (spc       : Spec, 
                     type_name : QualifiedId, 
                     type_info : TypeInfo) 
 : Spec =
 let

   def getLambdaTerm (typ, body) =
     let cond = mkTrue () in
     let pat  = RecordPat ([("1", VarPat (("x", typ), noPos)), 
                            ("2", VarPat (("y", typ), noPos))],
                           noPos)
     in
     Lambda ([(pat, cond, body)], noPos)

   def getEqOpType typ =
     Arrow (Product ([("1", typ), ("2", typ)], noPos),
            Boolean noPos,
            noPos)

   def addEqOp (eq_name as Qualified (eq_q, eq_id), old_type, body) =
     let eq_lambda = getLambdaTerm (old_type, body)        in
     let eq_type   = getEqOpType old_type                  in
     let eq_dfn    = TypedTerm (eq_lambda, eq_type, noPos) in
     let eq_info   = {names           = [eq_name],
                      fixity          = Nonfix,
                      dfn             = eq_dfn,
                      fullyQualified? = false}
     in
     let ops = insertAQualifierMap (spc.ops, eq_q, eq_id, eq_info) in
     let spc = setOps (spc, ops)         in
     let elt = Op (eq_name, true, noPos) in
     let spc = appendElement (spc, elt)  in
     spc

   def getEqTermFromProductFields (fields, old_type, varx, vary) =
     let mytrue   = mkTrue ()     in
     let and_op   = mkAndOp noPos in
     foldr (fn ((field_id, field_type), body) ->
              let projtyp = Arrow (old_type, field_type, noPos) in
              let eq_type = Arrow (Product ([("1", field_type), ("2", field_type)], noPos),
                                   Boolean noPos, 
                                   noPos) 
              in
              let projection    = Fun (Project (field_id), projtyp, noPos) in
              let x_field       = Apply (projection, varx, noPos) in
              let y_field       = Apply (projection, vary, noPos) in
              let field_eq_test = Apply (Fun (Equals, eq_type, noPos),
                                         Record ([("1", x_field), 
                                                  ("2", y_field)], 
                                                 noPos), 
                                         noPos)
              in
              if body = mytrue then % first case
                field_eq_test
              else
                Apply (and_op,
                       Record ([("1", field_eq_test), ("2", body)], noPos), 
                       noPos))
           (mkTrue ()) 
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
       let old_type = Base (type_name, 
                            map (fn tv -> TyVar (tv, noPos)) tvs,
                            noPos)
       in
       let varx    = Var (("x", old_type), noPos) in
       let vary    = Var (("y", old_type), noPos) in
       let eq_name = getEqOpQid type_name         in
       % check for aliases first
       case typ of
         | Base (alias_type_name, _, _) ->
           % define the equality op in terms of the aliased type
           let aeqqid = getEqOpQid alias_type_name                             in
           let fun    = Fun (Op (aeqqid, Nonfix), getEqOpType old_type, noPos) in
           let args   = Record ([("1", varx), ("2", vary)], noPos)             in
           let body   = Apply (fun, args, noPos)                               in
           addEqOp (eq_name, old_type, body)
           %% Boolean is same as default case
         | _ ->
           case typ of
             | Product (fields, _) -> 
               let body = getEqTermFromProductFields (fields, old_type, varx, vary) in
               addEqOp (eq_name, old_type, body)
             | CoProduct (fields, _) ->
               (let match =
                    foldr (fn ((field_id, opt_field_type), match) ->
                             let xpat = EmbedPat (field_id, 
                                                  case opt_field_type of 
                                                    | None -> None 
                                                    | Some field_type -> 
                                                      Some (VarPat (("x0", field_type), noPos)), old_type, noPos) 
                             in
                             let ypat = EmbedPat (field_id, 
                                                  case opt_field_type of 
                                                    | None -> None 
                                                    | Some field_type -> 
                                                      Some (VarPat (("y0", field_type), noPos)), old_type, noPos) 
                             in
                             let eq_field_type =
                                 let 
                                   def nonproduct_eq_test field_type =
                                     let eq_type = getEqOpType field_type in
                                     Apply (Fun (Equals, eq_type, noPos), 
                                            Record ([("1", Var (("x0", field_type), noPos)), 
                                                     ("2", Var (("y0", field_type), noPos))],
                                                    noPos), 
                                            noPos)
                                 in
                                 case opt_field_type of
                                   | None -> mkTrue ()
                                   | Some (field_type as Base _) -> nonproduct_eq_test field_type
                                   | Some field_type ->
                                     %% Was unfoldStripType which is unnecessary and dangerous because of recursive types
                                     let simplified_field_type = stripSubtypesAndBaseDefs spc field_type in
                                     case simplified_field_type of
                                       | Product (fields, _) -> 
                                         getEqTermFromProductFields (fields, 
                                                                     field_type, 
                                                                     Var (("x0", field_type), noPos), 
                                                                     Var (("y0", field_type), noPos))
                                       | _ -> nonproduct_eq_test field_type
                             in
                             let rule_1    = (ypat,                      mkTrue (), eq_field_type) in
                             let rule_2    = (WildPat (old_type, noPos), mkTrue (), mkFalse ())    in
                             let ymatch    = [rule_1, rule_2] in
                             let case_term = Apply (Lambda (ymatch, noPos), vary, noPos) in
                             Cons ((xpat, mkTrue (), case_term), match))
                          []
                          fields
                in
                let body = Apply (Lambda (match, noPos), varx, noPos) in
                addEqOp (eq_name, old_type, body))
             | _ -> spc

op getEqOpQid (Qualified (q, id) : QualifiedId) : QualifiedId =
 Qualified (q, "eq_" ^ id)


end-spec
