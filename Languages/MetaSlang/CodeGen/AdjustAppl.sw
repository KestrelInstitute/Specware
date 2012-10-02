AdjustAppl qualifying spec

 import CodeGenUtilities

 (*
  * returns whether the domain A of an op if it is declared as
  *
  * op foo: A -> B
  *
  * and A is a type defined as a product type.
  *)
 op getFoldedDomain: Spec * QualifiedId -> Option MSType
 def getFoldedDomain (spc, qid) =
   case findTheOp (spc, qid) of
     | None -> None
     | Some info ->
       let srt = firstOpDefInnerType info in 
       let srt = unfoldToArrow (spc, srt) in
       case srt of
	 | Arrow (domsrt as (Base _), ransrt, _) ->
	   let usrt = unfoldToProduct (spc, domsrt) in
	   (case usrt of
	      | Product (fields, _) -> Some (domsrt)
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

  op adjustAppl: Spec -> Spec
  def adjustAppl spc =
    let
      def adjustApplTerm (t) =
	case t of
	  | Apply (funterm as Fun (Op (qid, _), srt, _), argterm as Record _, b) ->
	    (case getFoldedDomain (spc, qid) of
	       | None -> t
	       | Some opsrt ->
	         let vname = "_arg" in
	         let pat = VarPat ((vname, opsrt), b) in
		 Apply (funterm, Let ([(pat, argterm)], Var ((vname, opsrt), b), b), b)
		)
	  | _ -> t
    in
    mapSpec (adjustApplTerm, id, id) spc

end-spec
