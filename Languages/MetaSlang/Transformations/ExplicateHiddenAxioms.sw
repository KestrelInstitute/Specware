Prover qualifying spec
 import DefToAxiom
 import SortToAxiom
% import OpToAxiom

  op explicateHiddenAxioms: Spec -> Spec
  def explicateHiddenAxioms spc =
    let def axiomFromSortDef(qname,name,sortDecl,sortAxioms) = sortAxioms ++ axiomFromSortDefTop(spc,qname,name,sortDecl) in
    let def axiomFromOpDef(qname,name,decl,defAxioms) = defAxioms ++ axiomFromOpDefTop(spc,qname,name,decl) in
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
    let newSortAxioms = foldriAQualifierMap axiomFromSortDef [] norm_spc.sorts in
    let newDefAxioms = foldriAQualifierMap axiomFromOpDef [] norm_spc.ops in
    let newProperties = mergeAxiomsByPos(spc.properties, newSortAxioms) in
    let newProperties = mergeAxiomsByPos(newProperties, newDefAxioms) in
    %%let _ = debug("explicateHidden") in 
    simplifySpec((setProperties(spc, newProperties)))

endspec
