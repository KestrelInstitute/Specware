% synchronized with version 1.4 of SW4/Languages/MetaSlang/TypeChecker/PosSpecToSpec.sl

PosSpecToSpec qualifying
spec {
 %%  convert pos terms to standard terms

 import ../PosSpec
 import ../StandardSpec

 op convertPosSpecToSpec: PosSpec -> Spec

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
  let {imports = _, importedSpec = _, localOps, localSorts} = importInfo in
  let tsp_maps = (convertPTerm, convertPSort, fn x -> x) in
  { importInfo       = importInfo,

    ops              = mapAQualifierMap 
			(fn opinfo as (aliases, fixity, (tvs, srt), opt_def) ->
			 let nm = hd aliases in
			 if member(nm,localOps)
			   then
			    (aliases, fixity, (tvs, mapSort tsp_maps srt), 
			     mapTermOpt tsp_maps opt_def)
			   else opinfo)
			ops,

    sorts            = mapAQualifierMap 
			 (fn sortinfo as (aliases, tvs, opt_def) ->
			  let nm = hd aliases in
			 if member(nm,localSorts)
			   then (aliases, tvs, mapSortOpt tsp_maps opt_def)
			   else sortinfo)
			 sorts,

    properties       = map (fn (pt, nm, tvs, term) -> 
			       (pt, nm, tvs, mapTerm tsp_maps term))
			   properties
   }
}
