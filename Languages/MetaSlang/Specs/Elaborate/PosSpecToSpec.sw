PosSpecToSpec qualifying spec {
 %%  convert pos terms to standard terms

 import ../StandardSpec
 import /Library/Legacy/DataStructures/NatMapSplay  % for metaTyVars

 op convertPosSpecToSpec: Spec -> Spec

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
           case f
	     of PQuotient equiv  -> Quotient 
	      | PChoose equiv    -> Choose
	      | PRestrict pred   -> Restrict
	      | PRelax pred      -> Relax
	      | OneName(n,fxty)  -> Op(Qualified(UnQualified,n), fxty)
	      | TwoNames(qn,n,fxty) -> Op(Qualified(qn,n), fxty)
	      | _ -> f
   in
%% mapSpec is correct but unnecessarily maps non-locals
%   mapSpec (convertPTerm, convertPSort, fn x -> x)
%     spc
  let {importInfo, sorts, ops, properties} = spc in
  let {imports = _, localOps, localSorts, localProperties} = importInfo in
  let tsp_maps = (convertPTerm, convertPSort, fn x -> x) in
  { importInfo       = importInfo,

    ops              = mapAQualifierMap 
			(fn opinfo as (aliases, fixity, (tvs, srt), defs) ->
			 let nm = hd aliases in
			 if member(nm,localOps)
			   then
			    (aliases, fixity, (tvs, mapSort tsp_maps srt), 
			     mapTermSchemes tsp_maps defs)
			   else opinfo)
			ops,

    sorts            = mapAQualifierMap 
			 (fn sortinfo as (aliases, tvs, defs) ->
			  let nm = hd aliases in
			  if member(nm,localSorts)
			   then (aliases, tvs, mapSortSchemes tsp_maps defs)
			   else sortinfo)
			 sorts,

    properties       = map (fn prop as (pt, nm, tvs, term) -> 
			       (pt, nm, tvs, if member(nm,localProperties)
				               then mapTerm tsp_maps term
					       else term))
			   properties
   }
}
