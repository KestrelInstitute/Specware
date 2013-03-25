AdjustAppl qualifying spec

 import CodeGenUtilities

 (*
  * returns whether the domain A of an op if it is declared as
  *
  * op foo: A -> B
  *
  * and A is a type defined as a product type.
  *)
 op getFoldedDomain (spc : Spec, qid : QualifiedId) : Option MSType =
  case findTheOp (spc, qid) of
    | None -> None
    | Some info ->
      let typ = firstOpDefInnerType info in 
      let typ = unfoldToArrow (spc, typ) in
      case typ of
        | Arrow (domain as (Base _), _, _) ->
          let domain = unfoldToProduct (spc, domain) in
          (case domain of
             | Product (fields, _) -> Some domain
             | _ -> None)
        | _ -> None


 (*
  * adjustAppl checks for application terms to ops with a folded domain (see
  * above check). If the argument of the application term is a product, then
  * a let variable is introduced and used as argument, e.g.:
  *
  * type A = B * C
  * op foo: A -> D
  *
  * foo (b, c) would then be transformed into foo (let arg= (b, c) in arg)
  *)

 op SpecTransform.adjustAppl (spc : Spec) : Spec =
  let
    def adjustApplTerm tm =
      case tm of
        | Apply (funterm as Fun (Op (qid, _), typ, _), argterm as Record _, b) ->
          (case getFoldedDomain (spc, qid) of
             | None -> tm
             | Some optyp ->
               let vname = "_arg" in
               let pat = VarPat ((vname, optyp), b) in
               Apply (funterm, Let ([(pat, argterm)], Var ((vname, optyp), b), b), b))
        | _ -> tm
  in
  mapSpec (adjustApplTerm, id, id) spc

end-spec
