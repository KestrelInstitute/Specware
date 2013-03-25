(* Replace all curried functions by functions that take products
 op f: A -> B -> C
-->
 op f_1_1: A * B -> C

Calls f x y --> f_1_1(x,y), f x --> (fn y -> f_1_1(x,y))

 op f: A * (B -> C -> D) -> E
-->
 op f_2: A * (B * C -> D) -> E

 fn x -> (fn y -> e(x,y))
-->
 fn (x,y) -> e(x,y)

 fn x -> (e: (A -> B))
-->
 fn (x,y) e y

Assume that pattern matching has been transformed away
*)

RemoveCurrying qualifying spec
  import CurryUtils
  
  op SpecTransform.removeCurrying (spc : Spec) : Spec =
    let spc = addUnCurriedOps spc in
    let newOps = mapOpInfos (fn old_info ->
			     if definedOpInfo? old_info then
			       %% TODO: Handle multiple defs??
			       let (old_tvs, old_srt, old_tm) = unpackFirstOpDef old_info in
			       let new_tm = unCurryTerm (old_tm, spc) in
			       let new_dfn = maybePiTerm (old_tvs, 
							  TypedTerm (new_tm, 
								      old_srt,
								      termAnn old_info.dfn))
			       in
				 old_info << {dfn = new_dfn}
			     else
			       old_info)
                            spc.ops
    in
    let newTypes = mapTypeInfos (fn old_info ->
				 if definedTypeInfo? old_info then
				   %% TODO: Handle multiple defs??
				   let (old_tvs, old_srt) = unpackFirstTypeDef old_info in
				   let new_srt = (unCurryType(old_srt,spc)).2 in
				   let new_dfn = maybePiType (old_tvs, new_srt) in
				   old_info << {dfn = new_dfn}
				 else
				   old_info)
                                spc.types
    in
    setOps (setTypes (spc, newTypes), newOps)

   op addUnCurriedOps: Spec -> Spec
  def addUnCurriedOps spc =
    let def doOp (old_el, q, id, info, r_elts, r_ops) =
	  let pos = termAnn info.dfn in
	  let (old_decls, old_defs) = opInfoDeclsAndDefs info in
	  case old_defs of
	    | old_def :: _ ->
	      (let (old_tvs, old_srt, old_tm) = unpackFirstTerm old_def in
	       case newUncurriedOp (spc, id, old_srt) of
		 | Some (new_id, new_srt) ->
		   let new_ops = 
		       (%% remove old defs, but insure at least one real decl
			let decls_but_no_defs = 
			    case old_decls of
			      | [] -> [maybePiTerm (old_tvs, TypedTerm (Any pos, old_srt, pos))]
			      | _ -> old_decls
			in
			let new_dfn = maybeAndTerm (decls_but_no_defs, pos) in 
			insertAQualifierMap (r_ops, q, id, info << {dfn = new_dfn}))
		   in
		   %% Add definition of replacement (only bother with first def)
		   %% TODO: Handle multiple defs??
		   let new_dfn = maybePiTerm (old_tvs, TypedTerm (old_tm, new_srt, pos)) in
		   let new_ops = insertAQualifierMap (new_ops, q, new_id,
						      info << {names = [Qualified (q, new_id)],
							       dfn   = new_dfn})
		   in
		   let new_qid = Qualified (q, new_id) in
		   (Cons (Op (new_qid, false, pos), % false means def is not printed as part of decl
                          Cons (OpDef (new_qid, 0, [], noPos),
                                r_elts)),
                    new_ops)
		 | None -> (Cons(old_el,r_elts),r_ops))
	    | _ -> (Cons(old_el,r_elts),r_ops)
	def addUnCurried(elts,result) =
          foldr
	    (fn (el,(r_elts,r_ops)) ->
	     case el of
	      | Import (s_tm,i_sp,s_elts,a) ->
		let (newElts,newOps) = addUnCurried(s_elts,([],r_ops)) in
		(Cons(Import(s_tm,i_sp,newElts,a),r_elts),
		 newOps)
	      | Op (Qualified(q,id), true,a) ->  % true means decl includes def
		(case findAQualifierMap(r_ops,q,id) of
		   | Some info ->  doOp(el,q,id,info,r_elts,r_ops)
		   | _ -> 
                     let _ = writeLine (q ^ "." ^ id ^ " is an Op element not in the qualifier map") in
                     (Cons (el,r_elts), r_ops))
	      | OpDef(Qualified(q,id),_,_,a) ->
		(case findAQualifierMap(r_ops,q,id) of
		   | Some info ->  doOp(el,q,id,info,r_elts,r_ops)
		   | _ -> 
                     let _ = writeLine (q ^ "." ^ id ^ " is an OpDef element not in the qualifier map") in
                     (Cons (el,r_elts), r_ops))
	      | _ -> (Cons(el,r_elts),r_ops))
	    result
	    elts
    in
    let (newElts,newOps) = addUnCurried(spc.elements, ([],spc.ops)) in
    spc << {ops        = newOps, 
	    elements   = newElts}

  op  newUncurriedOp: Spec * Id * MSType -> Option (Id * MSType)
  def newUncurriedOp (spc, nm, srt) =
    let (hasCurried?, unCurriedSrt) = unCurryType (srt, spc) in
    if ~hasCurried? then 
      None
    else 
      let curryshape = curryShapeNum (spc, srt) in
      Some(unCurryName (nm, curryshape),
	   unCurriedSrt)

 %op  unCurryDef: MSTerm * Nat -> MSTerm
 %def unCurryDef(tm,curryshape) =

  op  getCurryFnArgs: MSTerm -> Option (MSTerm * MSTerms)
  def getCurryFnArgs t =
    let def aux (term, i, args) =
      case term of
	| Fun _ -> Some (term, args)
	| Var _ -> Some (term, args)
	| Apply (t1, t2,_) -> aux (t1, i + 1,  t2::args)
	| _ -> None
    in 
      aux (t, 0, [])

  op  unCurryTerm: MSTerm * Spec -> MSTerm
  def unCurryTerm (tm, spc) =
    let def unCurryTermRec t = unCurryTerm(t,spc)
        def unCurryApply(f,args,spc) =
	  let fsrt = termTypeEnv(spc,f) in
	  let curryShape = curryShapeNum(spc,fsrt) in
	  if curryShape = length args then
            mkApply(convertFun(f,curryShape,spc),
                    mkTuple(map unCurryTermRec args))
	  else
            %% TODO: Specware miscompiles this if 'freevars f' is used inline
            let free_vars = freeVars f in
	    let newVars = mkNewVars(removePrefix(curryArgTypes(spc,fsrt), 
                                                 length args),
                                    map (fn (id,_) -> id) free_vars,
                                    spc)
            in
	    mkLambda(mkTuplePat(map mkVarPat newVars),
		     mkApply(convertFun(f,curryShape,spc),
			     mkTuple(map unCurryTermRec args
				     ++ map mkVar (newVars))))
    in
    case tm of
      | Apply(t1,t2,a) ->
        (case getCurryFnArgs tm  of
	   | None -> unCurryApply(unCurryTermRec t1,[t2],spc)
	   | Some(f,args) -> unCurryApply(f,args,spc))
      | Record(row,a) ->
	let newRow = map (fn (id,trm) -> (id, unCurryTermRec trm)) row in
	if row = newRow then tm
	  else Record(newRow,a)
      | Var((id,srt),a) ->
	let (hasCurried?,nSrt) = unCurryType(srt,spc) in
	if ~hasCurried?
	  then tm
	  else Var((id,nSrt),a)
      | Fun (Op(qid as Qualified(q1,nm1),fixity),srt,a) ->
	(case newUncurriedOp(spc,nm1,srt) of
	  | Some(nNm,nSrt) -> Fun(Op(Qualified(q1,nNm),fixity),nSrt,a)
	  | _ -> tm)
	
      %% Assume multiple rules have been transformed away and predicate is true
      | Lambda([(pat,_,body)],_)  ->
	let bodyType = termTypeEnv(spc,body) in
	if arrow? (spc,bodyType)
	  then flattenLambda([pat],body,bodyType,spc)
	else
	let newBody = unCurryTermRec body in
	if newBody = body
	  then tm
	else mkLambda(pat,newBody)

      | Lambda(rls,a) ->
	let newrls = map (fn (pat,pred,body) -> (pat,unCurryTermRec pred,unCurryTermRec body))
	               rls
	in Lambda(newrls,a)
	  
      | Let(decls,M,a)  ->
	let newDecls = map (fn (pat,tm) -> (pat,unCurryTermRec tm))
	                 decls
	in
	let newM = unCurryTermRec M in
	if newM = M && newDecls = decls
	  then tm
	 else Let(newDecls,newM,a)
      | LetRec(decls,M,a) ->
	let newDecls = map (fn (pat,tm) -> (pat,unCurryTermRec tm))
	                 decls
	in
	let newM = unCurryTermRec M in
	if newM = M && newDecls = decls
	  then tm
	 else LetRec(newDecls,newM,a)
      | The (var,term,a) ->
	let newTerm = unCurryTermRec term in
          if newTerm = term then
            tm
          else
            The (var,newTerm,a)
      | IfThenElse(t1,t2,t3,a) ->
	let newT1 = unCurryTermRec t1 in
	let newT2 = unCurryTermRec t2 in
	let newT3 = unCurryTermRec t3 in
	if newT1 = t1 && newT2 = t2 && newT3 = t3 then tm
	  else IfThenElse (newT1, newT2, newT3, a)
      | Seq(terms,a) -> Seq(map unCurryTermRec terms,a)
%      | Bind(b,vars,M,_)  -> 
      | _ -> tm

  op  unCurryType: MSType * Spec -> Bool * MSType
  %% Returns transformed type and whether any change was made
  %% Don't look inside type definitions except to follow arrows
  %% (otherwise infinitely recursive)
  def unCurryType(srt,spc) =
    let def unCurryRec s = unCurryType(s,spc)
        def unCurryArrowAux(rng,accumDomSrts) =
	  (case stripSubtypes(spc,rng) of
	    | Arrow(dom, restRng, _) ->
	      let expandedDomSrts = accumDomSrts
%                  foldl (fn (dom_srt, dom_srts) ->
%			 case productOpt (spc, dom_srt) of
%			   | Some fields -> dom_srts ++ (map (fn (_,s) -> s) fields)
%			   | _ -> dom_srts ++ [dom_srt])
%		        []
%		        accumDomSrts
	      in
	      (true,(unCurryArrowAux(restRng,expandedDomSrts ++ [dom])).2)
	    | _ ->
	      let (changed?,nRng) = unCurryRec rng in
	      let (changed?,nDomSrts) = foldrPred unCurryRec changed? accumDomSrts
	      in (changed?,mkArrow(mkProduct nDomSrts, nRng)))
    in
    case srt of
      | Subtype(srt, p, a) -> 
        let (changed?, ns) = unCurryRec srt in
	let np = unCurryTerm(p, spc) in
	(changed?, Subtype(ns, np, a))
      | Arrow(dom, rng, _) ->
        unCurryArrowAux(rng,[dom])
      | Product(xs,a) ->
        let (changed?,nxs)
	   = foldrPred (fn (id,t) ->
			let (changed?,nt) = unCurryRec t in
		        (changed?,(id,nt)))
	       false xs
	in (changed?,Product(nxs,a))
      | CoProduct(xs,a) ->
	let (changed?,nxs)
	   = foldrPred (fn (id,Some t) ->
			   let (changed?,nt) = unCurryRec t in
		           (changed?,(id,Some nt))
			  | pr -> (false,pr))
	       false xs
	in (changed?,CoProduct(nxs,a))
      | Quotient(s,t,a) ->
        let (changed?,ns) = unCurryRec s in
	let nt = unCurryTerm(t, spc) in
	(changed?, Quotient (ns,nt,a))
      | s -> (false,s)

  op  flattenLambda: MSPatterns * MSTerm * MSType * Spec -> MSTerm
  def flattenLambda(vs,body,bodyType,spc) =
    case body of
      | Lambda([(sPat,_,sBody)],_) ->
        flattenLambda(vs ++ [sPat],sBody,termTypeEnv(spc,sBody),spc)
      | _ ->
	case arrowOpt(spc,bodyType) of
	  | Some (dom,_) ->
	    %% !!? If dom is a product should we flatten it? No, for the moment.
	    let newVars = mkNewVars([dom],
				    map (fn (id,_)-> id) (freeVars body),
				    spc)
	    in
	      mkLambda(mkTuplePat(vs ++ map mkVarPat newVars),
		       unCurryTerm(mkApply(body,mkTuple(map mkVar newVars)),spc))
	  | None -> mkLambda(mkTuplePat vs,unCurryTerm(body,spc))

  def varNamePool = ["x","y","z","w","l","m","n","o","p","q","r","s"]

  op  mkNewVars: MSTypes * List Id * Spec -> List Var
  def mkNewVars(srts,usedNames,spc) =
    let def findUnused(srts,usedNames,pool) =
          case srts of
	    | [] -> []
	    | srt::rSrts ->
	      if head pool in? usedNames
		then findUnused(srts,usedNames,tail pool)
		else Cons((head pool,(unCurryType(srt,spc)).2),
			  findUnused(rSrts,usedNames,tail pool))
    in findUnused(srts,usedNames,varNamePool)

  op  convertFun: MSTerm * Nat * Spec -> MSTerm
  def convertFun(tm,curryshape,spc) =
    case tm of
      | Fun (Op (Qualified(q,id),_),srt,_) ->
        mkOp(Qualified(q,unCurryName(id,curryshape)),
	     (unCurryType(srt,spc)).2)
      | Var((id,srt),a) -> Var((id,(unCurryType(srt,spc)).2),a)
      | _ -> tm
endspec
