Prover qualifying spec
 import DefToAxiom
 import OpToAxiom

  op explicateHiddenAxioms: Spec -> Spec
  def explicateHiddenAxioms spc =
%    let def axiomFromOpDecl(qname,name, decl,defs) = axiomFromOpDeclTop(spc,qname,name,
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
    let newDefAxioms = foldriAQualifierMap axiomFromOpDef [] norm_spc.ops in
    let newProperties = mergeAxiomsByPos(spc.properties, newDefAxioms) in
    %%let _ = debug("explicateHidden") in 
    setProperties(spc, newProperties)

endspec
