(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

CodeGen qualifying spec

import /Languages/MetaSlang/CodeGen/CodeGenUtilities


(*
 * getExpandedProductDomain returns the expansion of the domain type of an op 
 * if that expansion is a (non-record) product type.
 *
 * E.g., given:
 *
 *   type A = X * Y * Z
 *   op foo: A -> B
 *
 * it returns:
 *
 *   Some (X * Y * Z)
 *)

op getExpandedProductDomain (spc : Spec, qid : QualifiedId) : Option MSType =
 case findTheOp (spc, qid) of
   | Some info ->
     let typ = firstOpDefInnerType info in 
     let typ = unfoldToArrow (spc, typ) in
     (case typ of
        | Arrow (domain as (Base _), _, _) ->
          (case unfoldToProduct (spc, domain) of
             %% note: unfoldToProduct returns None for records with named fields
             | Product (fields, _) -> Some domain
             | _ -> None)
        | _ -> None)
   | _ -> None


(*
 * encapsulateProductArgs modifies applications of ops to tuples, for ops that
 * have a single argument with a product type (after type expansion).
 *
 * In such cases, a let variable (_arg) is introduced to bind the product and 
 * this variable is then used as the single argument to the op.
 *
 * E.g., given:
 *
 *   type X = A * B * C
 *   op foo: X -> Y
 *
 * Transform:
 *
 *   foo (a, b, c) 
 *
 * to:
 *
 *   foo (let _arg = (a, b, c) in _arg)
 *
 * Note: This is done for products, but not for records with named fields.
 *)

op SpecTransform.encapsulateProductArgs (spc : Spec) : Spec =
 let
   def adjustApplTerm term =
     case term of
       | Apply (f as Fun (Op (qid, _), _, _), 
                args as Record _, 
                _) 
         ->
         (case getExpandedProductDomain (spc, qid) of
            | Some domain ->
              %% domain is a product type (but not a record with named fields)
              let vname = "_arg" in
              let vpat  = VarPat ((vname, domain), noPos) in
              let vref  = Var    ((vname, domain), noPos) in
              let varg  = Let ([(vpat, args)], vref, noPos) in
              Apply (f, varg, noPos)
            | _ -> term)
      | _ -> term
 in
 mapSpec (adjustApplTerm, id, id) spc

end-spec
