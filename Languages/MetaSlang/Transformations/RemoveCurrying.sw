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
  
  op  removeCurrying: Spec -> Spec
  def removeCurrying spc =
    let spc = addUnCurriedOps spc in
    let newOps = mapOpInfos (fn old_info ->
			     if definedOpInfo? old_info then
			       %% TODO: Handle multiple defs??
			       let (old_tvs, old_srt, old_tm) = unpackFirstOpDef old_info in
			       let new_tm = unCurryTerm (old_tm, spc) in
			       let new_dfn = maybePiTerm (old_tvs, 
							  SortedTerm (new_tm, 
								      old_srt,
								      termAnn old_info.dfn))
			       in
				 old_info << {dfn = new_dfn}
			     else
			       old_info)
                            spc.ops
    in
    let newSorts = mapSortInfos (fn old_info ->
				 if definedSortInfo? old_info then
				   %% TODO: Handle multiple defs??
				   let (old_tvs, old_srt) = unpackFirstSortDef old_info in
				   let new_srt = (unCurrySort(old_srt,spc)).2 in
				   let new_dfn = maybePiSort (old_tvs, new_srt) in
				   old_info << {dfn = new_dfn}
				 else
				   old_info)
                                spc.sorts
    in
    setOps (setSorts (spc, newSorts), newOps)

   op addUnCurriedOps: Spec -> Spec
  def addUnCurriedOps spc =
    let newOps =
        foldriAQualifierMap
	  (fn (q, id, info, new_ops) ->
	   let pos = termAnn info.dfn in
	   let (old_decls, old_defs) = opInfoDeclsAndDefs info in
	   case old_defs of
	     | old_def :: _ ->
	       (let (old_tvs, old_srt, old_tm) = unpackTerm old_def in
		case newUncurriedOp (spc, id, old_srt) of
		  | Some (new_id, new_srt) ->
		    let new_ops = 
		        (%% remove old defs, but insure at least one real decl
			 let decls_but_no_defs = 
                             case old_decls of
			       | [] -> [maybePiTerm (old_tvs, SortedTerm (Any pos, old_srt, pos))]
			       | _ -> old_decls
			 in
			 let new_dfn = maybeAndTerm (decls_but_no_defs, pos) in 
			 insertAQualifierMap (new_ops, q, id, info << {dfn = new_dfn}))
		    in
		    %% Add definition of replacement (only bother with first def)
		    %% TODO: Handle multiple defs??
		    let new_dfn = maybePiTerm (old_tvs, SortedTerm (old_tm, new_srt, pos)) in
		    insertAQualifierMap (new_ops, q, new_id,
					 info << {names = [Qualified (q, new_id)],
						  dfn   = new_dfn})
		  | None -> new_ops)
	     | _ ->
	       (debug (q, id, info.fixity); 
		new_ops))
	  spc.ops
	  spc.ops
    in
      setOps (spc, newOps)

  def debug tp = tp

  op  newUncurriedOp: Spec * Id * Sort -> Option (Id * Sort)
  def newUncurriedOp (spc, nm, srt) =
    let (hasCurried?, unCurriedSrt) = unCurrySort (srt, spc) in
    if ~hasCurried? then 
      None
    else 
      let curryshape = curryShapeNum (spc, srt) in
      Some(unCurryName (nm, curryshape),
	   unCurriedSrt)

 %op  unCurryDef: MS.Term * Nat -> MS.Term
 %def unCurryDef(tm,curryshape) =

  op  getCurryFnArgs: MS.Term -> Option(MS.Term * List MS.Term)
  def getCurryFnArgs t =
    let def aux (term, i, args) =
      case term of
	| Fun _ -> Some (term, args)
	| Var _ -> Some (term, args)
	| Apply (t1, t2,_) -> aux (t1, i + 1, cons (t2, args))
	| _ -> None
    in 
      aux (t, 0, [])

  op  unCurryTerm: MS.Term * Spec -> MS.Term
  def unCurryTerm (tm, spc) =
    let def unCurryTermRec t = unCurryTerm(t,spc)
        def unCurryApply(f,args,spc) =
	  let fsrt = termSortEnv(spc,f) in
	  let curryShape = curryShapeNum(spc,fsrt) in
	  if curryShape = length args
	    then mkApply(convertFun(f,curryShape,spc),
			 mkTuple(map unCurryTermRec args))
	  else
	    let newVars = mkNewVars(nthTail(curryArgSorts(spc,fsrt),
					    length args - 1),
				    map (fn (id,_) -> id) (freeVars f),
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
	let (hasCurried?,nSrt) = unCurrySort(srt,spc) in
	if ~hasCurried?
	  then tm
	  else Var((id,nSrt),a)
      | Fun (Op(qid as Qualified(q1,nm1),fixity),srt,a) ->
	(case newUncurriedOp(spc,nm1,srt) of
	  | Some(nNm,nSrt) -> Fun(Op(Qualified(q1,nNm),fixity),nSrt,a)
	  | _ -> tm)
	
      %% Assume multiple rules have been transformed away and predicate is true
      | Lambda([(pat,_,body)],_)  ->
	let bodySort = termSortEnv(spc,body) in
	if arrow? (spc,bodySort)
	  then flattenLambda([pat],body,bodySort,spc)
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
	if newM = M & newDecls = decls
	  then tm
	 else Let(newDecls,newM,a)
      | LetRec(decls,M,a) ->
	let newDecls = map (fn (pat,tm) -> (pat,unCurryTermRec tm))
	                 decls
	in
	let newM = unCurryTermRec M in
	if newM = M & newDecls = decls
	  then tm
	 else LetRec(newDecls,newM,a)
      | IfThenElse(t1,t2,t3,a) ->
	let newT1 = unCurryTermRec t1 in
	let newT2 = unCurryTermRec t2 in
	let newT3 = unCurryTermRec t3 in
	if newT1 = t1 & newT2 = t2 & newT3 = t3 then tm
	  else IfThenElse (newT1, newT2, newT3, a)
      | Seq(terms,a) -> Seq(map unCurryTermRec terms,a)
%      | Bind(b,vars,M,_)  -> 
      | _ -> tm

  op  unCurrySort: Sort * Spec -> Boolean * Sort
  %% Returns transformed sort and whether any change was made
  %% Don't look inside sort definitions except to follow arrows
  %% (otherwise infinitely recursive)
  def unCurrySort(srt,spc) =
    let def unCurryRec s = unCurrySort(s,spc)
        def unCurryArrowAux(rng,accumDomSrts) =
	  (case stripSubsorts(spc,rng) of
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
      | Subsort(srt, p, a) ->  unCurryRec srt
        %let (changed?, ns) = unCurryRec srt in
	%let np = unCurryTerm(p, spc) in
	%(changed?, Subsort(ns, p, a))
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

  op  flattenLambda: List Pattern * MS.Term * Sort * Spec -> MS.Term
  def flattenLambda(vs,body,bodySort,spc) =
    case body of
      | Lambda([(sPat,_,sBody)],_) ->
        flattenLambda(vs ++ [sPat],sBody,termSortEnv(spc,sBody),spc)
      | _ ->
	case arrowOpt(spc,bodySort) of
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

  op  mkNewVars: List Sort * List Id * Spec -> List Var
  def mkNewVars(srts,usedNames,spc) =
    let def findUnused(srts,usedNames,pool) =
          case srts of
	    | [] -> []
	    | srt::rSrts ->
	      if List.member(hd pool,usedNames)
		then findUnused(srts,usedNames,tl pool)
		else cons((hd pool,(unCurrySort(srt,spc)).2),
			  findUnused(rSrts,usedNames,tl pool))
    in findUnused(srts,usedNames,varNamePool)

  op  convertFun: MS.Term * Nat * Spec -> MS.Term
  def convertFun(tm,curryshape,spc) =
    case tm of
      | Fun (Op (Qualified(q,id),_),srt,_) ->
        mkOp(Qualified(q,unCurryName(id,curryshape)),
	     (unCurrySort(srt,spc)).2)
      | Var((id,srt),a) -> Var((id,(unCurrySort(srt,spc)).2),a)
      | _ -> tm
endspec
