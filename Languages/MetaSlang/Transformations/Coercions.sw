%%% Adds coercion functions between subtype and supertype so they can have
%%% different implementations

Coercions qualifying
spec 
  import /Languages/MetaSlang/Specs/Environment

  type TypeCoercionInfo = {subtype: QualifiedId,
			   supertype: QualifiedId,
			   coerceToSuper: MS.Term,
			   coerceToSub: MS.Term,
                           overloadedOps: List String}
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
        let n_tm = liftCoercion(n_tm,rm_ty,ty) in
	if delayCoercion? \_or overloadedTerm? n_tm then n_tm
	else
	case find (fn tb \_rightarrow subsortOf?(rm_ty,tb.subtype,spc)) coercions of
	  | Some tb \_rightarrow
	    if subsortOf?(ty,tb.supertype,spc)
	      \_and \_not(subsortOf?(ty,tb.subtype,spc))
	      then coerceToSuper(n_tm,tb)
	      else n_tm
	  | None \_rightarrow
	case find (fn tb \_rightarrow subsortOf?(rm_ty,tb.supertype,spc)
		            \_and \_not(subsortOf?(rm_ty,tb.subtype,spc)))
	       coercions of
	  | Some tb \_rightarrow
	    if subsortOf?(ty,tb.subtype,spc)
	      then coerceToSub(n_tm,tb)
	      else n_tm
	  | None \_rightarrow n_tm

      def mapSubTerms(tm,ty) =
	case tm of
	  | Apply (t1, t2, a) ->
	    let fn_ty = inferType(spc,t1) in
	    Apply (mapTerm(t1,fn_ty), mapTerm(t2,domain (spc,fn_ty)), a)
	  | Record (row, a) ->
	    let srts = map (fn (_,x) -> x) (product (spc,ty)) in
	    Record(map (fn ((idi,tmi),tyi) \_rightarrow (idi, mapTerm(tmi,tyi))) (zip(row,srts)), a)
	  | Bind (bnd, vars, trm, a) ->
	    Bind (bnd, vars, mapTerm(trm,ty), a)
	  | The (var, trm, a) ->
	    The (var, mapTerm(trm,boolSort), a)
	  | Let (decls, bdy, a) ->
	    %Let (map (fn (pat,trm) \_rightarrow (pat,mapTerm(trm,ty)))   % Assumes no coercions in pattern
	    Let (map (fn (pat,trm) \_rightarrow (pat,mapTerm(trm,patternSort pat)))   % Assumes no coercions in pattern
		   decls,
		 mapTerm(bdy,ty), a)
	  | LetRec (decls, bdy, a) ->
	    LetRec (map (fn ((id,srt), trm) \_rightarrow ((id,srt), mapTerm(trm,srt))) decls,
		    mapTerm(bdy,ty), a)
	  | Lambda (match, a) ->
	    Lambda (map (fn (pat,condn,trm) \_rightarrow
			 (pat, mapTerm(condn,boolSort),mapTerm(trm, range(spc,ty))))
			 match,
		    a)
	  | IfThenElse (t1, t2, t3, a) ->
	    IfThenElse (mapTerm(t1,boolSort), mapTerm(t2,ty), mapTerm(t3,ty), a)
	  | Seq (terms, a) ->
	    Seq (terms, a)		% Fix !!!
	  | SortedTerm (trm, srt, a) ->
	    SortedTerm (mapTerm(trm,srt), srt, a)
	  | _ \_rightarrow tm
      def liftCoercion (tm,ty,target_ty) =
        %let _ = toScreen("lc "^ printTerm tm ^": "^ printSort ty ^" ->"^ printSort target_ty ^"\n ") in
        case tm of
          | Apply(f as Fun(Op(Qualified(qual,idn),_),_,_),x,a) \_rightarrow
            (case checkCoercions x of
               | Some(tb,coerce_fn)
                   | member(idn,tb.overloadedOps)
                     \_or %% Special case for minus (probably not worth generalizing)
                       %% minus on nats is equal to minus on integers if we know result is a nat
                     (qual = "Integer" \_and idn = "-" %\_and coerce_fn = int
                        \_and (case target_ty of
                             | Base(Qualified("Nat","Nat"),[],_) \_rightarrow true
                             | _ \_rightarrow false))
                 \_rightarrow
                 let new_x = removeCoercions(x,coerce_fn) in
                 let new_tm = Apply(f,new_x,a) in
                 (if subsortOf?(ty,tb.supertype,spc)
                   then Apply(coerce_fn,new_tm,a)
                   else new_tm) 
               | _ \_rightarrow tm)
          | _ \_rightarrow tm
      def checkCoercions tm =
        (case tm of
           | Record(row, _) \_rightarrow
             foldl (\_lambda ((_,x),result) \_rightarrow
                    case checkCoercions1 x of
                      | (false,_) -> (false,None)
                      | new_result ->
                    case result of
                      | (false,_) -> result
                      | (true,Some _) -> result
                      | (true,None) -> new_result)
               (true, None) row 
           | _ \_rightarrow checkCoercions1 tm).2
      def checkCoercions1 tm =
        case tm of
          | Apply(f,_,_) \_rightarrow
            (case find (fn tb \_rightarrow f = tb.coerceToSuper \_or f = tb.coerceToSub) coercions of
               | Some tb \_rightarrow (true, Some(tb,f))
               | None \_rightarrow (false,None))
          | _ \_rightarrow (overloadedTerm? tm,None)
      def removeCoercions(tm,f) =
        case tm of
          | Record(row, a) ->
            Record(map (\_lambda(id,x) -> (id,removeCoercion(x,f))) row, a)
          | _ -> removeCoercion(tm,f)
      def removeCoercion(tm,f) =
        case tm of
          | Apply(f1,x,_) | f = f1 \_rightarrow x
          | _ -> tm
      def coerceToSuper(tm,tb) =
        case tm of
          | Apply(f,x,_) | f = tb.coerceToSub \_rightarrow x
          | _ \_rightarrow mkApply(tb.coerceToSuper,tm)
      def coerceToSub(tm,tb) =
        case tm of
          | Apply(f,x,_) | f = tb.coerceToSuper \_rightarrow x
          | _ \_rightarrow mkApply(tb.coerceToSub,tm)
    in
    spc << {ops = foldl (fn (el,ops) \_rightarrow
			 case el of
			   | Op (qid as Qualified(q,id), true) \_rightarrow % true means decl includes def
			     (case AnnSpec.findTheOp(spc,qid) of
			       | Some info \_rightarrow
				 insertAQualifierMap (ops, q, id,
						      info << {dfn = mapTermTop info})
			       | None \_rightarrow ops)
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

  op directlyImplementedSubsort?(ty: Sort, coercions: TypeCoercionTable): Boolean =
    case ty of
      | Base(qid,_,_) \_rightarrow exists (\_lambda tb \_rightarrow tb.subtype = qid) coercions
      | _ -> false

endspec
