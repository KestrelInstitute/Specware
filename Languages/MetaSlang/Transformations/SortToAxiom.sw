spec
 import ../Specs/Environment

  op axiomFromSubSortDefTop: Spec * Qualifier * Id * OpInfo -> Properties
  
  def axiomFromSubSortDefTop(spc,qname,name,decl) =
    case decl:OpInfo of
      | (op_names, fixity, (srtTyVars,srt), [(termTyVars, term)]) ->
        let localOps = spc.importInfo.localOps in
	if memberQualifiedId(qname, name, localOps) then
	  let pos = termAnn(term) in
	  let opName = mkQualifiedId(qname, name) in
	  let ax:Property = (Axiom, name^"_def", [], hd (unLambdaDef(spc, srt, opName, term))) in
	  %	let _ = writeLine(name^": in axiomFromOpDef Def part") in
            [ax]
	else []
      | _ -> %let _ = writeLine(name^": in axiomFromOpDef NOT def part") in
	       []
	

  op explicateHiddenAxioms: PosSpec -> Spec
  def explicateHiddenAxioms spc =
    let def axiomFromOpDef(qname,name,decl,defs) = defs ++ axiomFromOpDefTop(spc,qname,name,decl) in
    let norm_spc = spc in
    %%let norm_spc = translateMatch(norm_spc) in
    %%let norm_spc = arityNormalize(norm_spc) in
    let def mergeAxiomsByPos(oas, nas) =
      let def cmpGt(oax as (_, _, _, oat), nax as (_, _, _, nat)) =
        let old_pos:Position = termAnn(oat) in
	let new_pos = termAnn(nat) in
	case compare(old_pos, new_pos) of
	  | Greater -> false
	  | _ -> true in
      case (oas,nas) of
        | ([],nas) -> nas
        | (oas,[]) -> oas
        | (oa::oas,na::nas) ->
            if cmpGt(oa, na) then
              Cons(na, mergeAxiomsByPos(Cons(oa,oas),nas))
            else Cons(oa, mergeAxiomsByPos(oas,Cons(na,nas))) in
    let newAxioms = foldriAQualifierMap axiomFromOpDef [] norm_spc.ops in
    let newProperties = mergeAxiomsByPos(spc.properties, newAxioms) in
    %%let _ = debug("explicateHidden") in 
    setProperties(spc, newProperties)

endspec