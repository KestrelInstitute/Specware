InstantiateHO qualifying
spec
  import Simplify
  import CurryUtils
  import ../Specs/Utilities
  sort Term = MS.Term

  op  instantiateHOFns: Spec -> Spec
  def instantiateHOFns spc =
    %let spc = renameInSpec spc in
    let spc = normalizeCurriedDefinitions spc in
    let spc = simplifySpec spc in
    let m = makeUnfoldMap spc in
    %let m = mapAQualifierMap (renameDefInfo (emptyContext())) m in
    unFoldTerms(spc,m)

%  def renameDefInfo c (vs,defn,defsrt,fnIndices,curried?,recursive?) =
%    let vs = map (renamePattern c) vs in
%    let defn = renameTerm c defn in
%    (vs,defn,defsrt,fnIndices,curried?,recursive?)

  op  unFoldTerms: Spec * AQualifierMap DefInfo -> Spec
  def unFoldTerms(spc,m) =
    let simplifyTerm = simplify spc in
    mapSpec (fn t -> maybeUnfoldTerm(t,m,simplifyTerm,spc),id,id)
      spc

  op  unfoldInTerm: Term * AQualifierMap DefInfo * (Term -> Term) * Spec -> Term
  def unfoldInTerm(tm,m,simplifyTerm,spc) =
    mapSubTerms (fn t -> maybeUnfoldTerm(t,m,simplifyTerm,spc))
      tm

  %% (params,defn body,indices of applied fn args,curried?,recursive?)
  sort DefInfo = List Pattern * Term * Sort * List Nat * Boolean * Boolean

  op  makeUnfoldMap: Spec -> AQualifierMap DefInfo
  def makeUnfoldMap(spc) =
    mapiPartialAQualifierMap
      (fn (q,id,(op_names, _, (_,srt), defs)) ->
        case defs of
	  | [] -> None
	  | (defSch1 as (tvs,def1)):: _ ->
	    if (~(tvs = [])) & hoFnSort?(spc,srt)
	         & unfoldable?(Qualified(q,id), def1)
             then let numCurryArgs = curryShapeNum(spc,srt) in
	          let argSorts = if numCurryArgs > 1
				   then curryArgSorts(spc,srt)
				   else noncurryArgSorts(spc,srt)
		  in
		  let HOArgs = map (fn s -> hoSort?(spc,s)) argSorts in
	          if numCurryArgs > 1
	           then analyzeCurriedDefn  (Qualified(q,id),def1,numCurryArgs,HOArgs,srt)
		   else analyzeUnCurriedDefn(Qualified(q,id),def1,HOArgs,srt)
	     else None)
      spc.ops

  op  analyzeCurriedDefn: QualifiedId * Term * Nat * List Boolean * Sort -> Option DefInfo
  def analyzeCurriedDefn(qid,defn,numCurryArgs,HOArgs,srt) =
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
    let normalizedBody = mapSubTerms normalizeCurriedAppl body in
    analyzeDefn(qid,params,normalizedBody,HOArgs,true,srt)

  op  analyzeUnCurriedDefn: QualifiedId * Term * List Boolean * Sort -> Option DefInfo
  def analyzeUnCurriedDefn(qid,defn,argSorts,srt) =
    case defn of
      | Lambda([(pat,_,body)],_) -> analyzeDefn(qid,getParams pat,body,argSorts,false,srt)
      | _ -> None

  op  analyzeDefn: QualifiedId * List Pattern * Term * List Boolean * Boolean * Sort
                    -> Option DefInfo
  def analyzeDefn(qid,params,body,HOArgs,curried?,srt) =
    if ~(recursiveCallsPreserveHOParameters?(body,qid,params,HOArgs))
      then None
    else
    let patinds = tabulate(length params,id) in
    Some(params,body,srt,
	 filter (fn i -> nth(HOArgs,i)) patinds,
	 curried?,
	 %% Recursive?
	 existsSubTerm
	   (fn t -> case t of
		      | Apply(Fun(Op(nqid,_),_,_),_,_) -> nqid = qid
		      | _ -> false)
	   body)

  op  recursiveCallsPreserveHOParameters?: Term * QualifiedId * List Pattern * List Boolean
                                          -> Boolean
  def recursiveCallsPreserveHOParameters? (body,qid,params,HOArgs) =
    ~(existsSubTerm
        (fn t ->
	  case t of
	   | Apply(Fun(Op(nqid,_),_,_),args,_) ->
	     if nqid = qid
	       then ~(hoParamsSame?(params,termList args,HOArgs))
	       else false
	   | _ -> false)
        body)

  op  hoParamsSame?: List Pattern * List Term * List Boolean -> Boolean
  def hoParamsSame?(params,args,HOArgs) =
    length params = length args
      & all (fn i -> if nth(HOArgs,i)
	              then patternMatchesTerm?(nth(params,i),nth(args,i))
		      else true)
          (tabulate(length params,id))

  op  patternMatchesTerm?: Pattern * Term -> Boolean
  def patternMatchesTerm?(p,t) =
    case (p,t) of
      | (VarPat((vp,_),_),Var((v,_),_)) -> v = vp
      | (RecordPat(pfields,_),Record(tfields,_)) ->
        all (fn (id,pi) -> patternMatchesTerm?(pi,lookupId(id,tfields))) pfields
      | _ -> false
    
(*
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
*)

  %% has an argument that is HO. Arguments are either curried or product
  op  hoFnSort?: Spec * Sort -> Boolean
  def hoFnSort? (spc,srt) =
    case arrowOpt(spc,srt) of
      | None -> false
      | Some (dom,rng) ->
        hoSort?(spc,dom)
	  or (case arrowOpt(spc,rng) of
		| Some _ -> hoFnSort? (spc,rng)
		| None ->
	      case productOpt(spc,dom) of
		| None -> false
		| Some fields ->
		  exists (fn (_,s) -> arrow? (spc,s)) fields)

  op  hoSort?: Spec * Sort -> Boolean
  def hoSort? (spc,srt) =
    case stripSubsorts(spc, srt) of
      | Arrow _ -> true
      | Product(fields,_) ->
        exists (fn(_,s) -> hoSort?(spc,s)) fields
      | _ -> false

  def unfoldSizeThreshold = 80
  
  op  unfoldable?: QualifiedId * Term -> Boolean
  def unfoldable? (_ (* qid *), defn) =
    sizeTerm defn < unfoldSizeThreshold

  def sizeTerm t = foldSubTerms (fn (_,sum) -> sum + 1) 0 t

  op  maybeUnfoldTerm: Term * AQualifierMap DefInfo * (Term -> Term) * Spec -> Term
  def maybeUnfoldTerm(t,unfoldMap,simplifyTerm,spc) =
   case t of
     | Apply (f,a,_) ->
       (case f of
	  %% Uncurried case
	  | Fun(Op(qid as Qualified(q,id),_),srt,_) ->
	    (case findAQualifierMap(unfoldMap,q,id) of
	       | None -> t
	       | Some(vs,defn,defsrt,fnIndices,curried?,recursive?) ->
		 if ~curried?
		      & length(termList a) > foldr max 0 fnIndices
		      & exists (fn i -> constantTerm?(getTupleArg(a,i)))
		          fnIndices
		  then makeUnfoldedTerm
		         (f,termToList a,inferType(spc,t),
			  sortMatch(defsrt,srt,spc),
			  vs,defn,fnIndices,recursive?,qid,id,
			  unfoldMap,simplifyTerm,spc)
		  else t)
	  %% Curried case
	  | Apply _ ->
	    (case getCurryArgs t of
	       | None -> t
	       | Some(f,args) ->
		 (case f of
		    | Fun(Op(qid as Qualified(q,id),_),srt,_) ->
		      (case findAQualifierMap(unfoldMap,q,id) of
			 | None -> t
			 | Some(vs,defn,defsrt,fnIndices,curried?,recursive?) ->
			   if curried? & (length args = length vs)
			     & exists (fn i -> constantTerm?(nth(args,i)))
			         fnIndices
			    then makeUnfoldedTerm(f,args,inferType(spc,t),
						  sortMatch(defsrt,srt,spc),
						  vs,defn,fnIndices,recursive?,
						  qid,id,unfoldMap,simplifyTerm,spc)
			    else t)
		    | _ -> t))
	  | _ -> t)
     | _ -> t

  op  makeUnfoldedTerm: Term * List Term * Sort * TyVarSubst * List Pattern * Term
                         * List Nat * Boolean * QualifiedId * String
                         * AQualifierMap DefInfo * (Term -> Term) * Spec
                      -> Term
  def makeUnfoldedTerm(_ (* f *), args, resultSort, tyVarSbst, vs, defbody, fnIndices,
		       recursive?, qid, nm, unfoldMap, simplifyTerm, spc) =
    let replaceIndices = filter (fn i -> constantTerm?(nth(args,i))
				        & member(i,fnIndices))
                           (tabulate (length args, id))
    in
    let vSubst = foldl (fn (i,r) -> r ++ matchPairs(nth(vs,i),nth(args,i)))
                   [] replaceIndices
    in
    let remainingIndices =  filter (fn i -> ~(member(i,replaceIndices)))
                              (tabulate (length args, id))
    in
    let remainingParams = map (fn i -> nth(  vs,i)) remainingIndices in
    let remainingArgs   = map (fn i -> nth(args,i)) remainingIndices in
    if recursive?
      then makeRecursiveLocalDef(qid,nm,defbody,resultSort,tyVarSbst,
				 remainingParams, remainingArgs,remainingIndices,
				 vSubst,simplifyTerm)
      else
      let instantiateTyVars = fn s -> instantiateTyVars(s,tyVarSbst) in
      let defbody = mapTerm(id,instantiateTyVars,id) defbody in
      let remainingParams = map (fn p -> mapPattern(id,instantiateTyVars,id) p)
                              remainingParams in
      let newTm = makeLet(remainingParams,remainingArgs,defbody) in
      let newTm = substitute(newTm,vSubst) in
      unfoldInTerm(simplifyTerm(newTm),unfoldMap,simplifyTerm,spc)

  %% Returns nm if it is not referenced in t, otherwise adds -i to
  %% to make it unique
  op  locallyUniqueName: Id * Term -> Id
  def locallyUniqueName(baseName,t) =
    let def aux (baseName,t,i) =
          let indName = baseName^"-"^(Nat.toString i) in
	  if idReferenced?(indName,t)
	    then aux(baseName,t,i+1)
	    else indName
    in aux(baseName,t,0)

  op  idReferenced?: Id * Term -> Boolean
  def idReferenced?(id,t) =
    existsSubTerm
      (fn st -> case st of
                 | Var((id1,_),_) -> id = id1
                 | _ -> false)
      t

  def makeRecursiveLocalDef(qid,nm,defbody,resultSort,tyVarSubst,remainingParams,
			    remainingArgs,remainingIndices,vSubst,simplifyTerm) =
    %% check name conflict with args and defbody. defbody should be safe
    %% because user can't put "--" in identifier, but to be safe
    let localFnName = locallyUniqueName(nm^"--local",
					%% Just to give context of var names to avoid
					mkTuple(cons(defbody,remainingArgs)))
    in
    let newArgTerm = mkTuple remainingArgs in
    let instantiatedFnSort = mkArrow(termSort newArgTerm,resultSort) in
    let localFn = (localFnName,instantiatedFnSort) in
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
    in
    let instantiateTyVars = fn s -> instantiateTyVars(s,tyVarSubst) in
    let defbody = mapTerm (id,instantiateTyVars,id) defbody in
    let localDefbody = mapSubTerms foldRecursiveCall defbody in
    let localDef = substitute(mkLambda(mapPattern (id,instantiateTyVars,id)
				         (mkTuplePat(remainingParams)),
				       localDefbody),
			      vSubst)
    in
    simplifyTerm(mkLetRec([(localFn,localDef)],
			  mkApply(mkVar localFn,newArgTerm)))

  sort TyVarSubst = List(Id * Sort)
  def instantiateTyVars(s,tyVarSubst) =
    case s of
      | TyVar (name, _) ->
	(case find (fn (nm,_) -> nm = name) tyVarSubst of
	   | Some(_,ss) -> ss
	   | _ -> s)
      | _ -> s

  op  sortMatch: Sort * Sort * Spec -> TyVarSubst
  def sortMatch(s1,s2,spc) =
   let def match(srt1,srt2,pairs) =
        case (srt1,srt2) of
	  | (TyVar(id1,_), srt2) -> 
	    if some?(find (fn (id,_) -> id = id1) pairs)
	      then pairs
	      else cons((id1,srt2),pairs)
	  | (Arrow(t1,t2,_),Arrow(s1,s2,_)) -> 
	    match(t2,s2,match(t1,s1,pairs))
	  | (Product(r1,_),Product(r2,_)) -> 
	    matchL(r1,r2,pairs,fn((_,s1),(_,s2),pairs) -> match(s1,s2,pairs)) 
	  | (CoProduct(r1,_),CoProduct(r2,_)) -> 
	    matchL(r1,r2,pairs,
		   fn((id1,s1),(id2,s2),pairs) ->
		    if id1 = id2 then
		      (case (s1,s2) of
			 | (None,None) -> pairs 
			 | ((Some ss1),(Some ss2)) -> match(ss1,ss2,pairs))
		   else pairs)
	  | (Quotient(ty,trm,_),Quotient(ty_,trm_,_)) -> 
	    match(ty,ty_,pairs)
	  | (Subsort(ty,_,_),ty2) -> match(ty,ty2,pairs)
	  | (ty,Subsort(ty2,_,_)) -> match(ty,ty2,pairs)
	  | (Base(id,ts,pos1),Base(id_,ts_,pos2)) ->
	    if id = id_
	      then matchL(ts,ts_,pairs,match)
	      else
		let s2_ = unfoldBase(spc,srt2) in
		if equalSort?(srt2,s2_)
		  then pairs
		else match(srt1,s2_,pairs)
	  | (_,Base _) ->
	    let s2_ = unfoldBase(spc,srt2) in
	    if equalSort?(srt2,s2_)
	     then pairs
	     else match(srt1,s2_,pairs)
	  | _ -> pairs
  in match(s1,s2,[])

  op matchL: fa(a) List a * List a * TyVarSubst * (a * a * TyVarSubst -> TyVarSubst)
                 -> TyVarSubst
  def matchL(l1,l2,pairs,matchElt) =
    case (l1,l2)
     of (e1::l1,e2::l2) -> matchL(l1,l2,matchElt(e1,e2,pairs),matchElt)
      | _ -> pairs

  op normalizeCurriedDefinitions: Spec -> Spec
  def normalizeCurriedDefinitions spc =
    let normOps =
        mapiAQualifierMap
	  (fn (q,id,opinfo as (op_names, inf, (svs,srt), defs)) ->
	     case defs of
	       | [] -> opinfo
	       | (tvs,def1) :: rDefs ->		% Currently additional defs ignored
	         let numCurryArgs = curryShapeNum(spc,srt) in
	         let argSorts = curryArgSorts(spc,srt) in
		 let normDef1 = normalizeCurriedDefn(def1,argSorts) in
		 (op_names, inf, (svs,srt), cons((tvs,normDef1),rDefs)))
          spc.ops
    in setOps(spc,normOps)

  op  normalizeCurriedDefn: Term * List Sort -> Term
  def normalizeCurriedDefn(defn,curryArgSorts) =
    let def aux(defn,curryArgSorts,argNum) = 
	  case curryArgSorts of
	    | [] -> defn
	    | argSort::rSorts ->
	      case defn of
		| Lambda([(pat,pred,body)],a) ->
		  Lambda([(pat,pred,aux(body,rSorts,argNum+1))],a)
		| Lambda _ -> defn
		| _ ->
		  if argNum = 0 & rSorts = [] & product? argSort
		    then			% Uncurried
		    (case argSort of
		      | Product(fields,_) ->
		        let vars = (foldl (fn ((label,srt),(result,i)) ->
					    (result ++ [(label,("x-"^Nat.toString i,srt))],
					     i+1))
				      ([],0) fields).1
			in mkLambda(mkRecordPat(map (fn(l,v) -> (l,mkVarPat(v))) vars),
				    mkApply(defn,
					    mkRecord(map (fn (l,v) -> (l,mkVar(v))) vars))))
		  else 
		  let nv = ("x-"^Nat.toString argNum,argSort) in
		  mkLambda(mkVarPat(nv),aux(mkApply(defn,mkVar(nv)),rSorts,argNum+1))
    in aux(defn,curryArgSorts,0)

  op  transparentRenaming: Qualifier * Id * Term * Spec -> Qualifier * Id * Term
  %% If definition is just a renaming then "unfold"
  def transparentRenaming(q,id,def1,spc) =
    case def1 of
      | Fun(Op(Qualified(q2,id2),_),_,_) ->
        (case findAQualifierMap(spc.ops,q2,id2) of
	  | Some (_, _, _, [(_,def2)]) -> (q2,id2,def2)
	  | _ -> (q,id,def1))
      | _ -> (q,id,def1)


  op  getCurryArgs: Term -> Option(Term * List Term)
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

  op  getTupleArg: Term * Nat -> Term
  def getTupleArg(t,i) =
    case t of
      | Record (tms,_) -> (nth(tms,i)).2
      | tm -> (if i = 0 then tm else fail("Illegal getTupleArg call"))

  op  termList: Term -> List Term
  def termList t =
    case t of
      | Record(fields,_ ) -> foldr (fn ((_,st),r) -> cons(st,r)) [] fields
      | _ -> [t]

  op  makeLet: List Pattern * List Term * Term -> Term
  def makeLet(params,args,body) =
    if params = [] then body
    else
    mkLet(tabulate (length params,fn i -> (nth(params,i),nth(args,i))),
	  body)

  op  termToList: Term -> List Term
  def termToList t =
    case t of
      | Record (fields,_) -> map (fn (_,x) -> x) fields
      | _ -> [t]

  op  mkTuplePat  : List Pattern  -> Pattern
  def mkTuplePat pats =
    case pats of
      | [pat] -> pat
      | _ -> RecordPat (tagTuple(pats), noPos)

  op  matchPairs: Pattern * Term -> List (Var * Term)
  def matchPairs(p,t) =
    case (p,t) of
      | (VarPat(pv,_),t) -> [(pv,t)]
      | (RecordPat(pfields,_),Record(tfields,_)) ->
        foldl (fn ((id,p1),r) -> r ++ matchPairs(p1,lookupId(id,tfields)))
	  [] pfields
      | _ -> fail "matchPairs: Shouldn't happen"

  op  lookupId: Id *  List (Id * Term)  -> Term  
  def lookupId(id,fields) =
    case find (fn (id1,t1) -> id = id1) fields of
      | Some (_,t) -> t
      | _ -> fail "lookupId: Shouldn't happen"

%%% inCurryUtils
%  op  curriedSort?: Spec * Sort -> Boolean
%  def curriedSort?(sp,srt) = curryShapeNum(sp,srt) > 1

%  op  curryShapeNum: Spec * Sort -> Nat
%  def curryShapeNum(sp,srt) =
%    case arrowOpt(sp,srt)
%      of Some (_,rng) -> 1 + curryShapeNum(sp,rng)
%       | _ -> 0

%  op  curryArgSorts: Spec * Sort -> List Sort
%  def curryArgSorts(sp,srt) =
%    case arrowOpt(sp,srt)
%      of Some (dom,rng) -> cons(stripSubsorts(sp,dom),curryArgSorts(sp,rng))
%       | _ -> []

%  op  curriedParams: Term -> List Pattern * Term
%  def curriedParams defn =
%    let def aux(t,vs) =
%          case t of
%	    | Lambda([(p,_,body)],_) ->
%	      if (case p of
%		    | VarPat _ -> true
%		    | RecordPat _ -> true
%		    | _ -> false)
%		then aux(body,vs ++ [p])
%		else (vs,t)
%	    | _ -> (vs,t)
%    in
%    aux(defn,[])

%  op  noncurryArgSorts: Spec * Sort -> List Sort
%  def noncurryArgSorts(sp,srt) =
%    case arrowOpt(sp,srt)
%      of Some (dom,_) ->
%	 (case productOpt(sp,dom) of
%	   | Some fields -> map (fn(_,s) -> s) fields
%	   | _ -> [dom])
%       | _ -> []


endspec
