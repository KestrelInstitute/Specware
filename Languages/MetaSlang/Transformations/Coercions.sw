%%% Adds coercion functions between subtype and supertype so they can have
%%% different implementations

Coercions qualifying
spec 
  import /Languages/MetaSlang/Specs/Environment

  type TypeCoercionInfo = {subtype: QualifiedId,
			   supertype: QualifiedId,
			   coerceToSuper: MS.Term,
			   coerceToSub: MS.Term}
  type TypeCoercionTable = List TypeCoercionInfo

  op  addCoercions: TypeCoercionTable \_rightarrow Spec \_rightarrow Spec
  def addCoercions coercions spc =
%    let _ = toScreen(printSpec spc) in
    let
      def mapTermTop info =
	let (tvs,ty,tm) = unpackFirstOpDef info in
	maybePiTerm(tvs,SortedTerm(mapTerm(tm,ty),ty,termAnn tm))
	
      def mapTerm(tm,ty) =
	let rm_ty = inferType(spc,tm) in
%	let _ = toScreen(printTerm tm^": "^printSort rm_ty ^"\n-> "
%			 ^ printSort ty^"\n\n") in
	let delayCoercion? =
	    case tm of
	      | Lambda _ \_rightarrow true
	      | Let _ \_rightarrow true
	      | LetRec _ \_rightarrow true
	      | IfThenElse _ \_rightarrow true
	      | Record _ \_rightarrow true
	      | _ \_rightarrow false
	in
	let n_tm = mapSubTerms(tm,if delayCoercion? then ty else rm_ty) in
	if delayCoercion? \_or overloadedTerm? n_tm then n_tm
	else
	case find (fn tb \_rightarrow subsortOf?(rm_ty,tb.subtype,spc)) coercions of
	  | Some tb \_rightarrow
	    if subsortOf?(ty,tb.supertype,spc)
	      \_and \_not(subsortOf?(ty,tb.subtype,spc))
	      then mkApply(tb.coerceToSuper,n_tm)
	      else n_tm
	  | None \_rightarrow
	case find (fn tb \_rightarrow subsortOf?(rm_ty,tb.supertype,spc)
		            \_and \_not(subsortOf?(rm_ty,tb.subtype,spc)))
	       coercions of
	  | Some tb \_rightarrow
	    if subsortOf?(ty,tb.subtype,spc)
	      then mkApply(tb.coerceToSub,n_tm)
	      else n_tm
	  | None \_rightarrow n_tm

      def mapSubTerms(tm,ty) =
	case tm of
	  | Apply (t1, t2, a) ->
	    let fn_ty = inferType(spc,t1) in
	    Apply (mapTerm(t1,fn_ty), mapTerm(t2,domain (spc,fn_ty)), a)
	  | Record (row, a) ->
	    let srts = productSorts (spc,ty) in
	    Record(map (fn ((idi,tmi),tyi) \_rightarrow (idi, mapTerm(tmi,tyi))) (zip(row,srts)), a)
	  | Bind (bnd, vars, trm, a) ->
	    Bind (bnd, vars, mapTerm(trm,ty), a)
	  | The (var, trm, a) ->
	    The (var, mapTerm(trm,boolSort), a)
	  | Let (decls, bdy, a) ->
	    Let (map (fn (pat,trm) \_rightarrow (pat,mapTerm(trm,ty)))   % Assumes no coercions in pattern
		   decls,
		 mapTerm(bdy,ty), a)
	  | LetRec (decls, bdy, a) ->
	    LetRec (map (fn ((id,srt), trm) \_rightarrow ((id,srt), mapTerm(trm,srt)))decls,
		    mapTerm(bdy,ty), a)
	  | Lambda (match, a) ->
	    Lambda (map (fn (pat,condn,trm) \_rightarrow
			 (pat, mapTerm(condn,boolSort),mapTerm(trm,range (spc,ty))))
			 match,
		    a)
	  | IfThenElse (t1, t2, t3, a) ->
	    IfThenElse (mapTerm(t1,boolSort), mapTerm(t2,ty), mapTerm(t3,ty), a)
	  | Seq (terms, a) ->
	    Seq (terms, a)		% Fix !!!
	  | SortedTerm (trm, srt, a) ->
	    SortedTerm (mapTerm(trm,srt), srt, a)
	  | _ \_rightarrow tm
    in
    spc << {ops = foldl (fn (el,ops) \_rightarrow
			 case el of
			   | OpDef (qid as Qualified(q,id)) \_rightarrow
			     (case AnnSpec.findTheOp(spc,qid) of
			       | Some info \_rightarrow
				 insertAQualifierMap (ops, q, id,
						      info << {dfn = mapTermTop info})
			       | None \_rightarrow ops)
			   | _ \_rightarrow ops)
	            spc.ops
		    spc.elements,
	    %% mapOpInfos (fn info \_rightarrow info << {dfn = mapTermTop info}) spc.ops,
	    elements = map (fn el \_rightarrow
			      case el of
				| Property(pt,nm,tvs,term) \_rightarrow
				  Property(pt,nm,tvs,mapTerm(term,boolSort))
				| _ \_rightarrow el)
	                 spc.elements}
    
  op  subsortOf?: Sort * QualifiedId * Spec \_rightarrow Boolean
  def subsortOf?(ty,qid,spc) =
    %let _ = toScreen(printQualifiedId qid^": "^printSort ty^"\n") in
    case ty of
      | Base(qid1,srts,_) \_rightarrow
        qid1 = qid
	 \_or (case findTheSort (spc, qid1) of
	      | None -> false
	      | Some info ->
		if definedSortInfo? info then
		  let (tvs, srt) = unpackFirstSortDef info in
		  let ssrt = substSort (zip (tvs, srts), srt) in
		  subsortOf?(ssrt,qid,spc)
		else
		  false)
      | _ \_rightarrow false

  op  overloadedTerm?: MS.Term \_rightarrow Boolean
  def overloadedTerm? tm =
    case tm of
      | Fun(Nat _,_,_) \_rightarrow true
      | _ \_rightarrow false

endspec
