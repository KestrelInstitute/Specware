(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Prover qualifying spec
 import DefToAxiom
 import TypeToAxiom
% import OpToAxiom

  op explicateHiddenAxioms: Spec -> Spec
  def explicateHiddenAxioms spc =
%    let def axiomFromTypeDef(qname,name,typeDecl,typeAxioms) = typeAxioms ++ axiomFromTypeDefTop(spc,qname,name,typeDecl) in
%    let def axiomFromOp(qname,name,decl,defAxioms) = defAxioms ++ axiomFromOpTop(spc,qname,name,decl) in
%    %let def axiomFromProp(prop,props) = props ++ axiomFromPropTop(spc,prop) in

%    let newTypeAxioms = foldriAQualifierMap axiomFromTypeDef [] spc.types in
%    let newDefAxioms = foldriAQualifierMap axiomFromOp [] spc.ops in
%    %let newPropAxioms = foldr axiomFromProp [] spc.elements in
%    let newElements = mergeAxiomsByPos(spc.elements, newTypeAxioms) in
%    let newElements = mergeAxiomsByPos(newElements, newDefAxioms) in
%    %let newElements = mergeAxiomsByPos(newElements, newPropAxioms) in
    %%let _ = debug("explicateHidden") in 
    %simplifySpec((setElements(spc, newElements)))
    let def expandElts(elts,result) =
	  foldr
	    (fn (el,r_elts) ->
	     case el of
	      | Import (s_tm,i_sp,s_elts,a) ->
		let newElts = expandElts(s_elts,[]) in
		Cons(Import(s_tm,i_sp,newElts,a),r_elts)
	      | TypeDef (qid, _) ->
	        (case AnnSpec.findTheType(spc,qid) of
		   | Some typeinfo ->
		     Cons(el,axiomFromTypeDefTop(spc,qid,typeinfo) ++ r_elts))
	      | Op (qid,def?,_) ->
	        (case AnnSpec.findTheOp(spc,qid) of
		   | Some opinfo -> Cons (el,
                                          axiomFromOpSrtTop(spc,qid,opinfo) 
                                            ++ (if def? then axiomFromOpDefTop(spc,qid,opinfo) else [])
                                            ++ r_elts))
	      | OpDef (qid, _, _, _) ->
	        (case AnnSpec.findTheOp(spc,qid) of
		   | Some opinfo -> Cons(el,
                                         axiomFromOpDefTop(spc,qid,opinfo) 
                                           ++ r_elts))
	      | _ -> Cons(el,r_elts) )
	    result
	    elts
    in
    setElements(spc, expandElts(spc.elements,[]))

endspec
