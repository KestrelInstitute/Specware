RemoveQuoitent qualifying spec
  import Simplify
  
  op  removeQuotient: Spec -> Spec
  def removeQuotient spc =
    let newOps = mapOpInfos (fn old_info ->
			     if definedOpInfo? old_info then
			       %% TODO: Handle multiple defs??
			       let (old_tvs, old_srt, old_tm) = unpackFirstOpDef old_info in
			       let new_tm = remQuotientTerm (old_tm, spc) in
			       let new_dfn = maybePiTerm (old_tvs, 
							  SortedTerm (new_tm, 
								      old_srt,
								      termAnn old_info.dfn))
			       in
				 old_info << {dfn = new_dfn}
			     else
			       old_info)
                            spc.ops
    in
    setOps(spc, newOps)

  op  remQuotientTerm: MS.Term * Spec -> MS.Term
  def remQuotientTerm(term, spc) =
    mapTerm (fn (tm) -> remQuotientTerm1(tm, spc),
	     (fn (s) -> s),
	     (fn (p) -> p)) term
  
  op  remQuotientTerm1: MS.Term * Spec -> MS.Term
  def remQuotientTerm1(term, spc) =
    case term of
      | Apply (Fun (Choose, cSrt, _), Record([(_,f), (_, a)], _), b) -> 
        let srt = inferType(spc, term) in
	let res = SortedTerm(simplifiedApply(f, a, spc), srt, b) in
	%let _ = writeLine("remQ: "^ printTerm(term)^" -> " ^ printTerm(res)) in
	  res
      | _ -> term

endspec