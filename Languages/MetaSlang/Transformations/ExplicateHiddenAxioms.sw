Prover qualifying spec
 import DefToAxiom
 import SortToAxiom
% import OpToAxiom

  op explicateHiddenAxioms: Spec -> Spec
  def explicateHiddenAxioms spc =
%    let def axiomFromSortDef(qname,name,sortDecl,sortAxioms) = sortAxioms ++ axiomFromSortDefTop(spc,qname,name,sortDecl) in
%    let def axiomFromOp(qname,name,decl,defAxioms) = defAxioms ++ axiomFromOpTop(spc,qname,name,decl) in
%    %let def axiomFromProp(prop,props) = props ++ axiomFromPropTop(spc,prop) in

%    let newSortAxioms = foldriAQualifierMap axiomFromSortDef [] spc.sorts in
%    let newDefAxioms = foldriAQualifierMap axiomFromOp [] spc.ops in
%    %let newPropAxioms = foldr axiomFromProp [] spc.elements in
%    let newElements = mergeAxiomsByPos(spc.elements, newSortAxioms) in
%    let newElements = mergeAxiomsByPos(newElements, newDefAxioms) in
%    %let newElements = mergeAxiomsByPos(newElements, newPropAxioms) in
    %%let _ = debug("explicateHidden") in 
    %simplifySpec((setElements(spc, newElements)))
    let def expandElts(elts,result) =
	  foldr
	    (fn (el,r_elts) ->
	     case el of
	      | Import (s_tm,i_sp,s_elts) ->
		let newElts = expandElts(s_elts,[]) in
		Cons(Import(s_tm,i_sp,newElts),r_elts)
	      | SortDef qid ->
	        (case AnnSpec.findTheSort(spc,qid) of
		   | Some sortinfo ->
		     Cons(el,axiomFromSortDefTop(spc,qid,sortinfo) ++ r_elts))
	      | Op qid ->
	        (case AnnSpec.findTheOp(spc,qid) of
		   | Some opinfo -> Cons(el,axiomFromOpSrtTop(spc,qid,opinfo) ++ r_elts))
	      | OpDef qid ->
	        (case AnnSpec.findTheOp(spc,qid) of
		   | Some opinfo -> Cons(el,axiomFromOpDefTop(spc,qid,opinfo) ++ r_elts))
	      | _ -> Cons(el,r_elts) )
	    result
	    elts
    in
    setElements(spc, expandElts(spc.elements,[]))

endspec
