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
    let newOps = mapAQualifierMap
                   (fn (nms,fixity,srtScheme,(dtvs,def1)::_) ->
		     (nms,fixity,srtScheme,[(dtvs,unCurryTerm(def1,spc))])
		     | x -> x)
		   spc.ops
    in
    let newSorts = mapAQualifierMap
                     (fn (aliases,tvs,(tvs1,srt)::_) ->
		       (aliases,tvs,[(tvs1,(unCurrySort(srt,spc)).2)])
		       | x -> x)
		     spc.sorts
    in
    setOps(setSorts(spc,newSorts),newOps)

  op  addUnCurriedOps: Spec -> Spec
  def addUnCurriedOps spc =
    let newOps =
        foldriAQualifierMap
	  (fn (qualifier,id,(nms,fixity,(stvs,srt),
			     ((dtvs,def1)::_)),
	       new_ops) ->
	     (case newUncurriedOp(spc,id,srt) of
	        | Some(nNm,nSrt) ->
		  % Remove definition of old op
		  let new_ops =
		      insertAQualifierMap(new_ops,qualifier,id,
					  (nms,fixity,(stvs,srt),[]))
		  in
		  % Add definition of replacement (only bother with first def)
		  insertAQualifierMap(new_ops,qualifier,nNm,
				      ([Qualified(qualifier,nNm)],fixity,
				       (stvs,nSrt),
				       [(dtvs,def1)]))
	        | None -> new_ops)
	    | (qualifier,id,inf,new_ops) -> (debug(qualifier,id,inf);new_ops))
	  spc.ops
	  spc.ops
    in
      setOps(spc,newOps)

  def debug tp = tp

  op  newUncurriedOp: Spec * Id * Sort -> Option(Id * Sort)
  def newUncurriedOp(spc,nm,srt) =
    let (hasCurried?,unCurriedSrt) = unCurrySort(srt,spc) in
    if ~hasCurried? then None
     else let curryshape = curryShapeNum(spc,srt) in
          Some(unCurryName(nm,curryshape),
	       unCurriedSrt)

%  op  unCurryDef: MS.Term * Nat -> MS.Term
%  def unCurryDef(tm,curryshape) =
  op  getCurryFnArgs: MS.Term -> Option(MS.Term * List MS.Term)
  def getCurryFnArgs t =
    let def aux(term,i,args) =
        case term
          of Fun _ -> Some(term,args)
	   | Var _ -> Some(term,args)
           | Apply(t1,t2,_) -> aux(t1,i+1,cons(t2,args))
           | _ -> None
  in aux(t,0,[])

  op  unCurryTerm: MS.Term * Spec -> MS.Term
  def unCurryTerm(tm,spc) =
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
	  then flattenLambda(getParams pat,body,bodySort,spc)
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
