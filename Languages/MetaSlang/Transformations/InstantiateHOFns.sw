InstantiateHO qualifying
spec
  import ../Specs/Environment
  import ../Specs/Utilities
  sort Term = MS.Term

  op instantiateHOFns: Spec -> Spec
  def instantiateHOFns spc =
    let m = makeUnfoldMap spc in
    unFoldTerms(spc,m)

  op unFoldTerms: Spec * AQualifierMap DefInfo -> Spec
  def unFoldTerms(spc,m) =
    mapSpec (fn t -> maybeUnfoldTerm(t,m),id,id)
      spc

  %% (params,defn body,indices of applied fn args,curried?,recursive?)
  sort DefInfo = List Var * Term * List Nat * Boolean * Boolean

  op makeUnfoldMap: Spec -> AQualifierMap DefInfo
  def makeUnfoldMap(spc) =
    mapiPartialAQualifierMap
      (fn (q,id,(op_names, _, (_,srt), defs)) ->
        case defs of
	  | [] -> None
	  | (defSch1 as (tvs,def1)):: _ ->
	    if (~(tvs = [])) & hoFnSort?(spc,srt)
	         & unfoldable?(Qualified(q,id), def1)
             then let numCurryArgs = curryShapeNum(spc,srt) in
	          if numCurryArgs > 1
	           then analyzeCurriedDefn(Qualified(q,id), def1, numCurryArgs)
		   else analyzeUnCurriedDefn(Qualified(q,id), def1)
	     else None)
      spc.ops

  op analyzeCurriedDefn: QualifiedId * Term * Nat -> Option DefInfo
  def analyzeCurriedDefn(qid,defn,numCurryArgs) =
    let (params,body) = curriedParams(defn) in
    if ~(length params = numCurryArgs) then None
    else
    let def normalizeCurriedAppl t =
	  case getCurryArgs t of
	    | Some(f as Fun(Op(nqid,_),_,_),args) ->
	      if nqid = qid & length args = numCurryArgs
		then mkAppl(f,args)
		else t
	    | _ -> t
    in
    let normalizedBody = mapTerm(normalizeCurriedAppl,id,id) body in
    analyzeDefn(qid,params,normalizedBody,true)

  op analyzeUnCurriedDefn: QualifiedId * Term -> Option DefInfo
  def analyzeUnCurriedDefn(qid,defn) =
    case defn of
      | Lambda([(pat,_,body)],_) -> analyzeDefn(qid,lambdaVars pat,body,false)
      | _ -> None

  def analyzeDefn(qid,params,body,curried?) =
    let patinds = tabulate(length params,id) in
    let appliedParamVector = findAppliedParams(params,body,patinds) in
    Some(params,body,
	 filter (fn i -> nth(appliedParamVector,i)) patinds,
	 curried?,
	 %% Recursive?
	 existsSubTerm
	   (fn t -> case t of
		      | Apply(Fun(Op(nqid,_),_,_),_,_) -> nqid = qid
		      | _ -> false)
	   body)
    
  %% Find parameters which are applied
  def findAppliedParams(params,body,patinds) =
    foldSubTerms (fn (t,r) ->
		  case t of
		   | Apply(Var(v,_),_,_) ->
		     map (fn i -> if v = nth(params,i)
				   then true
				   else nth(r,i))
		       patinds
		   | _ -> r)
      (map (fn _ -> false) patinds)
      body

  %% has an argument that is HO. Arguments are either curried or product
  op hoFnSort?: Spec * Sort -> Boolean
  def hoFnSort? (spc,srt) =
    case arrowOpt(spc,srt) of
      | None -> false
      | Some (dom,rng) ->
        arrow?(spc,dom)
	  or (case arrowOpt(spc,rng) of
		| Some _ -> hoFnSort? (spc,rng)
		| None ->
	      case productOpt(spc,dom) of
		| None -> false
		| Some fields ->
		  exists (fn (_,s) -> arrow? (spc,s)) fields)

  def unfoldSizeThreshold = 40
  
  op unfoldable?: QualifiedId * Term -> Boolean
  def unfoldable?(qid,defn) =
    sizeTerm defn < unfoldSizeThreshold

  def sizeTerm t = foldSubTerms (fn (_,sum) -> sum + 1) 0 t

  op maybeUnfoldTerm: Term * AQualifierMap DefInfo -> Term
  def maybeUnfoldTerm(t,m) =
   case t of
     | Apply (f,a,_) ->
       (case f of
	  %% Uncurried case
	  | Fun(Op(qid as Qualified(q,id),_),srt,_) ->
	    (case findAQualifierMap(m,q,id) of
	       | None -> t
	       | Some(vs,defn,fnIndices,curried?,recursive?) ->
		 if ~curried?
		      & exists (fn i -> constantTerm?(getTupleArg(a,i)))
		          fnIndices
		  then makeUnfoldedTerm
		         (f,termToList a,srt,vs,defn,fnIndices,recursive?,qid,id)
		  else t)
	  %% Curried case
	  | Apply _ ->
	    (case getCurryArgs t of
	       | None -> t
	       | Some(f,args) ->
		 (case f of
		    | Fun(Op(qid as Qualified(q,id),_),srt,_) ->
		      (case findAQualifierMap(m,q,id) of
			 | None -> t
			 | Some(vs,defn,fnIndices,curried?,recursive?) ->
			   if curried? & (length args = length vs)
			     & exists (fn i -> constantTerm?(nth(args,i)))
			         fnIndices
			    then makeUnfoldedTerm
			           (f,args,srt,vs,defn,fnIndices,recursive?,qid,id)
			    else t)
		    | _ -> t))
	  | _ -> t)
     | _ -> t

  op makeUnfoldedTerm: Term * List Term * Sort * List Var * Term * List Nat
                         * Boolean * QualifiedId * String
                      -> Term
  def makeUnfoldedTerm(f,args,instantiatedFnSort,vs,defbody,fnIndices,
		       recursive?,qid,nm) =
    let replaceIndices = filter (fn i -> constantTerm?(nth(args,i))
				        & member(i,fnIndices))
                           (tabulate (length args, id))
    in
    let vSubst = map (fn i -> (nth(vs,i),nth(args,i))) replaceIndices in
    let remainingIndices =  filter (fn i -> ~(member(i,replaceIndices)))
                              (tabulate (length args, id))
    in
    let remainingParams = map (fn i -> nth(  vs,i)) remainingIndices in
    let remainingArgs   = map (fn i -> nth(args,i)) remainingIndices in
    if recursive?
      then makeRecursiveLocalDef(qid,nm,defbody,instantiatedFnSort,remainingParams,
				 remainingArgs,remainingIndices,vSubst)
      else makeLet(remainingParams,remainingArgs,substitute(defbody,vSubst))

  %% Returns nm if it is not referenced in t, otherwise adds -i to
  %% to make it unique
  op locallyUniqueName: Id * Term -> Id
  def locallyUniqueName(baseName,t) =
    let def aux (baseName,t,i) =
          let indName = baseName^"-"^(Nat.toString i) in
	  if idReferenced?(indName,t)
	    then aux(baseName,t,i+1)
	    else indName
    in aux(baseName,t,0)

  op idReferenced?: Id * Term -> Boolean
  def idReferenced?(id,t) =
    existsSubTerm
      (fn st -> case st of
                 | Var((id1,_),_) -> id = id1
                 | _ -> false)
      t

  def makeRecursiveLocalDef(qid,nm,defbody,instantiatedFnSort,remainingParams,
			    remainingArgs,remainingIndices,vSubst) =
    %% check name conflict with args and defbody. defbody should be safe
    %% because user can't put "--" in identifier, but to be safe
    let localFnName = locallyUniqueName(nm^"--local",
					mkTuple(cons(defbody,remainingArgs)))
    in
    let localFn = (localFnName,instantiatedFnSort) in
    let tyVarSubst = [] in		% !!?
    let def foldRecursiveCall t =
          case t of
	    | Apply(Fun(Op(nqid,_),_,_),arg,a) ->
	      if ~(qid = nqid) then t
	      else
	      let args = termToList arg in
	      Apply(mkVar localFn,
		    mkTuple(map (fn i -> nth(args,i)) remainingIndices),
		    a)
	    | _ -> t
	def instantiateTyVars s =
	  case s of
	    | TyVar (name, _) ->
	      (case find (fn (nm,_) -> nm = name) tyVarSubst of
		 | Some(_,ss) -> ss
		 | _ -> s)
	    | _ -> s
    in
    let localDefbody = mapTerm (foldRecursiveCall,instantiateTyVars,id) defbody in
    let localDef = mkLambda(mkTuplePat(map mkVarPat remainingParams),
			    substitute(localDefbody,vSubst))
    in
    mkLetRec([(localFn,localDef)],
	     mkApply(mkVar localFn,mkTuple remainingArgs))

  op getCurryArgs: Term -> Option(Term * List Term)
  def getCurryArgs t =
    let def aux(term,i,args) =
        case term
          of Fun(_,srt,_) ->
             if i > 1
               then Some(term,args)
              else None
           | Apply(t1,t2,_) -> aux(t1,i+1,cons(t2,args))
           | _ -> None
  in aux(t,0,[])

  op getTupleArg: Term * Nat -> Term
  def getTupleArg(t,i) =
    case t of
      | Record (tms,_) -> (nth(tms,i)).2
      | tm -> (if i = 0 then tm else fail("Illegal getTupleArg call"))

  def constantTerm? t =
    case t of
      | Lambda _ -> true
      | Fun _ -> true
      | _ -> false

  op lambda?: Term -> Boolean
  def lambda? t =
    case t of
      | Lambda _ -> true
      | _ -> false

  op makeLet: List Var * List Term * Term -> Term
  def makeLet(params,args,body) =
    if params = [] then body
    else
    mkLet(tabulate (length params,fn i -> (mkVarPat(nth(params,i)),nth(args,i))),
	  body)

  op termToList: Term -> List Term
  def termToList t =
    case t of
      | Record (fields,_) -> map (fn (_,x) -> x) fields
      | _ -> [t]

  op mkTuplePat  : List Pattern  -> Pattern
  def mkTuplePat pats =
    case pats of
      | [pat] -> pat
      | _ -> RecordPat (tagTuple(pats), noPos)

  op lambdaVars: Pattern -> List Var
  def lambdaVars(pat:Pattern) = 
    case pat
      of VarPat(v,_)-> [v]
       | RecordPat(fields,_) ->
	 if all (fn (_,VarPat _) -> true | _ -> false) fields
	   then map (fn (_,VarPat(v,_)) -> v) fields
	   else []
       | _ -> []

  def curriedSort?(sp,srt) = curryShapeNum(sp,srt) > 1

  def curryShapeNum(sp,srt) =
    case arrowOpt(sp,srt)
      of Some (dom,rng) -> 1 + curryShapeNum(sp,rng)
       | _ -> 0

  def curriedParams defn =
    let def aux(t,vs) =
          case t of
	    | Lambda([(VarPat(v,_),_,body)],_) ->
	      aux(body,vs ++ [v])
	    | _ -> (vs,t)
    in
    aux(defn,[])

endspec
