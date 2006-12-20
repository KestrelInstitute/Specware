PosSpecToSpec qualifying spec
 %%  convert pos terms to standard terms

 import ../StandardSpec
 import /Library/Legacy/DataStructures/NatMapSplay  % for metaTyVars

 op  convertPosSpecToSpec: Spec -> Spec
 def convertPosSpecToSpec spc =
   let context = initializeMetaTyVars() in
   let
     def convertPTerm term =
           case term of
	     | ApplyN([t1,t2],pos) -> Apply(t1,t2,pos)
	     | ApplyN (t1::t2::terms,pos) -> 
	       convertPTerm (ApplyN([t1,ApplyN(cons(t2,terms),pos)],pos))
	     | Fun (f,s,pos) -> Fun(convertPFun f,s,pos)
	     | _ -> term
     def convertPSort srt =
           case srt of
	     | MetaTyVar(tv,pos) -> 
	       let {name,uniqueId,link} = ! tv in
	       (case link
		  of None -> TyVar (findTyVar(context,uniqueId),pos)
		   | Some ssrt -> convertPSort ssrt)
	     | _ -> srt
     def convertPFun (f) = 
           case f of
	     | PQuotient qid -> Quotient qid
             | PChoose   qid -> Choose   qid
             | OneName(n,fxty)  -> Op(Qualified(UnQualified,n), fxty)
             | TwoNames(qn,n,fxty) -> Op(Qualified(qn,n), fxty)
             | _ -> f
   in
%% mapSpec is correct but unnecessarily maps non-locals
%   mapSpec (convertPTerm, convertPSort, fn x -> x)
%     spc
 
  let {sorts, ops, elements, qualifier} = spc in
%  let {imports = _, localOps, localSorts, localProperties} = importInfo in
  let tsp = (convertPTerm, convertPSort, fn x -> x) in
  spc << { ops = if ~(hasLocalOp? spc) then 
                   ops
		 else
                   mapOpInfosUnqualified (fn info ->
					  if someOpAliasIsLocal? (info.names, spc) then
					    info << {dfn = mapTerm tsp info.dfn}
					  else 
					    info)
			      ops,

          sorts = if ~(hasLocalSort? spc) then 
                   sorts
                  else
		   mapSortInfos (fn info ->
				 if someSortAliasIsLocal? (info.names, spc) then
				   info << {dfn = mapSort tsp info.dfn}
				 else 
				   info)
				sorts,

          elements =  map (fn el ->
                             case el of
                               | Property (pt, qid, tvs, term) -> 
                                 Property(pt, qid, tvs, 
                                          mapTerm tsp term)
                               | _ -> el)
                           elements
         }


 op  convertPosTermToTerm : MS.Term -> MS.Term
 def convertPosTermToTerm tm =
   let context = initializeMetaTyVars() in
   let
     def convertPTerm term =
           case term of
	     | ApplyN([t1,t2],pos) -> Apply(t1,t2,pos)
	     | ApplyN (t1::t2::terms,pos) -> 
	       convertPTerm (ApplyN([t1,ApplyN(cons(t2,terms),pos)],pos))
	     | Fun (f,s,pos) -> Fun(convertPFun f,s,pos)
	     | _ -> term
     def convertPSort srt =
           case srt of
	     | MetaTyVar(tv,pos) -> 
	       let {name,uniqueId,link} = ! tv in
	       (case link
		  of None -> TyVar (findTyVar(context,uniqueId),pos)
		   | Some ssrt -> convertPSort ssrt)
	     | _ -> srt
     def convertPFun (f) = 
           case f of
	     | PQuotient qid -> Quotient qid
             | PChoose   qid -> Choose   qid
             | OneName(n,fxty)  -> Op(Qualified(UnQualified,n), fxty)
             | TwoNames(qn,n,fxty) -> Op(Qualified(qn,n), fxty)
             | _ -> f
   in
   let tsp = (convertPTerm, convertPSort, fn x -> x) in
   mapTerm tsp tm

endspec

