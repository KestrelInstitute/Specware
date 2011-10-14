ConformOpDecls qualifying spec 

import CodeGenUtilities

 (*
 * conformOpDecls checks whether we have an opdef of the form
 *
 * type P = A * B
 * op foo: P -> Q
 * def foo (a, b) = ...
 *
 * i.e. the declaration contains the user type name, but the arguments refer to its definition term.
 * ops are transformed to something like
 * 
 * def foo (arg) = 
 *   let a = arg^1 in
 *   let b - arg^2 in
 *   ...
 *)

op conformOpDecls: Spec -> Spec
def conformOpDecls spc =
  %let _ = writeLine ("lambdaToInner...") in
  let ops = foldriAQualifierMap
            (fn (q, id, info, newops) ->
	     let (old_decls, old_defs) = opInfoDeclsAndDefs info in
	     let new_defs = 
	         List.map (fn dfn ->
			   let (tvs, srt, term) = unpackFirstTerm dfn in
			   let new_tm = conformOpDeclsTerm (spc, srt, term, id) in
			   maybePiTerm (tvs, TypedTerm (new_tm, srt, termAnn term)))
		          old_defs
	     in
	     let new_dfn = maybeAndTerm (old_decls ++ new_defs, termAnn info.dfn) in
	     let new_info = info << {dfn = new_dfn} in
	     insertAQualifierMap (newops, q, id, new_info))
	    emptyAQualifierMap spc.ops
  in
  setOps (spc, ops)

op conformOpDeclsTerm: Spec * MSType * MSTerm * Id -> MSTerm
def conformOpDeclsTerm (spc, srt, term, _) =
  let srt = unfoldToArrow (spc, srt) in
  case srt of
    | Arrow (domsrt as (Base _), ransrt, _) ->
    let usrt = unfoldToProduct (spc, domsrt) in
    (case usrt of
       | Product (fields, _) ->
       let termtype = inferType (spc, term) in
       (case termtype of
	  | Arrow (Product (fields0, _), _, _) ->
	  if productfieldsAreNumbered (fields0) then
	    case term of
	      | Lambda ([(pat, _, bodyterm)], b) ->
		let optplist =
		 (case pat of
		   | VarPat ((id, _), _) -> Some[id]
		   | RecordPat (plist, _) -> 
		     if forall? (fn | (_, VarPat _) -> true | (_, _) -> false) plist then
		       Some (List.map (fn (_, VarPat ((id, _), _)) -> id) plist)
		     else
		       None
		   | _ -> None
		)
		in
		 (case optplist of
		   | None -> term
		   | Some plist -> 
		   if length (fields0) = length (plist) then
		     %let _ = writeLine ("checking "^id^"...") in
		     let argname = "_arg" in
		     let pnamessrts = zip (plist, fields0) in
		     let bodyterm = foldr (fn ((variable, (id, fsrt)), bodyterm) ->
					   let proj = Fun (Project (id), Arrow (srt, fsrt, b), b) in
					   let pterm = Apply (proj, Var ((argname, srt), b), b) in
					   Let ([(VarPat ((variable, fsrt), b), pterm)], bodyterm, b))
		                           bodyterm pnamessrts
		     in
		     let cond = mkTrue () in
		     let newpat = VarPat ((argname, srt), b) in
		     Lambda ([(newpat, cond, bodyterm)], b)
		   else
		     term
		  )
	      | _ ->term
	  else term
	  | _ -> term)
     | _ -> term
      )
    | _ -> term
       


end-spec
