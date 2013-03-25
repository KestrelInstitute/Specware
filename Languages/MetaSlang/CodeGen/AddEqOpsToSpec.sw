AddEqOpsToSpec qualifying spec

 import /Languages/MetaSlang/Specs/StandardSpec
 import /Languages/MetaSlang/Specs/Environment

 (**
  * adds for each user type the corresponding
  * equality op
  *)

 op SpecTransform.addEqOpsToSpec (spc : Spec) : Spec =
  foldriAQualifierMap (fn (q, id, typeinfo, spc) ->
                         addEqOpsFromType (spc, Qualified (q, id), typeinfo))
                      spc 
                      spc.types

 op addEqOpsFromType (spc : Spec, qid :QualifiedId, info : TypeInfo) : Spec =
  let
    def getLambdaTerm (srt, body, b) =
      let cond = mkTrue () in
      let pat = RecordPat ([("1", VarPat (("x", srt), b)), ("2", VarPat (("y", srt), b))], b) in
      Lambda ([(pat, cond, body)], b)

    def getEqOpType (srt, b) =
      Arrow (Product ([("1", srt), ("2", srt)], b), Boolean b, b)

    def addEqOp (eqqid as Qualified (eq, eid), osrt, body, b) =
      let term = getLambdaTerm (osrt, body, b) in
      let info = {names  = [eqqid],
		  fixity = Nonfix,
		  dfn    = TypedTerm (term, getEqOpType (osrt, b), b),
		  fullyQualified? = false}
      in
      let ops = insertAQualifierMap (spc.ops, eq, eid, info) in
      let spc = setOps (spc, ops) in
      let elt = Op (eqqid, true, noPos) in
      let spc = appendElement (spc, elt) in
      spc
  in
  if ~ (definedTypeInfo? info) then
    spc
  else
    let (tvs, srt) = unpackFirstTypeDef info in
    %% Was unfoldStripType which is unnecessary and dangerous because of recursive types
    let usrt = stripSubtypesAndBaseDefs spc srt in
    case usrt of
      | Boolean _ -> spc
      | Base (Qualified ("Nat",       "Nat"),     [], _) -> spc
      | Base (Qualified ("Integer",   "Int"),     [], _) -> spc
      | Base (Qualified ("Character", "Char"),    [], _) -> spc
      | Base (Qualified ("String",    "String"),  [], _) -> spc
     %| Base (Qualified ("??",        "Float"),   [], _) -> spc
      | _ ->
        let b = typeAnn srt in
	let osrt = Base (qid, map (fn tv -> TyVar (tv, b)) tvs, b) in
	let varx = Var (("x", osrt), b) in
	let vary = Var (("y", osrt), b) in
	let eqqid as Qualified (eq, eid) = getEqOpQid qid in
	let
          def getEqTermFromProductFields (fields, osrt, varx, vary) =
	    foldr (fn ((fid, fsrt), body) ->
		   let projsrt = Arrow (osrt, fsrt, b) in
		   let eqtype = Arrow (Product ([("1", fsrt), ("2", fsrt)], b), Boolean b, b) in
		   let proj = Fun (Project (fid), projsrt, b) in
		   let t1 = Apply (proj, varx, b) in
		   let t2 = Apply (proj, vary, b) in
		   let t = Apply (Fun (Equals, eqtype, b), Record ([("1", t1), ("2", t2)], b), b) in
		   if body = mkTrue () then 
		     t
		   else
		     let andSrt = Arrow (Product ([("1", Boolean b), ("2", Boolean b)], b), Boolean b, b) in
		     let andTerm = mkAndOp b in
		     Apply (andTerm, Record ([("1", t), ("2", body)], b), b)
		     %IfThenElse (t, body, mkFalse (), b)
		    )
	          (mkTrue ()) 
		  fields
	in
	% check for aliases first
	case srt of
	  | Base (aqid, _, b) ->
	    % define the eq-op in terms of the aliased type
	    let aeqqid = getEqOpQid (aqid) in
	    let fun = Fun (Op (aeqqid, Nonfix), getEqOpType (osrt, b), b) in
	    let args = Record ([("1", varx), ("2", vary)], b) in
	    let body = Apply (fun, args, b) in
	    addEqOp (eqqid, osrt, body, b)
          %% Boolean is same as default case
	  | _ ->
	    case srt of
	      | Product (fields, _) -> 
	        let body = getEqTermFromProductFields (fields, osrt, varx, vary) in
		addEqOp (eqqid, osrt, body, b)
	      | CoProduct (fields, _) ->
		(let applysrt = Arrow (osrt, Boolean b, b) in
		 let match =
		     foldr (fn ((fid, optfsrt), match) ->
			    let xpat = EmbedPat (fid, 
						 case optfsrt of 
						   | None -> None 
						   | Some fsrt -> Some (VarPat (("x0", fsrt), b)), osrt, b) 
			    in
			    let ypat = EmbedPat (fid, 
						 case optfsrt of 
						   | None -> None 
						   | Some fsrt -> Some (VarPat (("y0", fsrt), b)), osrt, b) 
			    in
			    let eqFsrt =
			        let 
                                  def bcase fsrt =
				    let eqsrt = getEqOpType (fsrt, b) in
				    Apply (Fun (Equals, eqsrt, b), 
					   Record ([("1", Var (("x0", fsrt), b)), 
						    ("2", Var (("y0", fsrt), b))],
						   b), 
					   b)
				in
				  case optfsrt of
				    | None -> mkTrue ()
				    | Some (fsrt as Base _) -> bcase fsrt
				    | Some fsrt ->
				    %% Was unfoldStripType which is unnecessary and dangerous because of recursive types
				    let ufsrt = stripSubtypesAndBaseDefs spc fsrt in
				      case fsrt of
					| Product (fields, _) -> 
					  getEqTermFromProductFields (fields, fsrt, 
								      Var (("x0", fsrt), b), 
								      Var (("y0", fsrt), b))
					| _ -> bcase (fsrt)
			    in
			    let ymatch = [(ypat, mkTrue (), eqFsrt), (WildPat (osrt, b), mkTrue (), mkFalse ())] in
			    let caseTerm = Apply (Lambda (ymatch, b), vary, b) in
			    Cons ((xpat, mkTrue (), caseTerm), match))
		           []
			   fields
		 in
		 let body = Apply (Lambda (match, b), varx, b) in
		 addEqOp (eqqid, osrt, body, b))
	      | _ -> spc

 op getEqOpQid (Qualified (q, id) : QualifiedId) : QualifiedId =
  Qualified (q, "eq_" ^ id)


end-spec
