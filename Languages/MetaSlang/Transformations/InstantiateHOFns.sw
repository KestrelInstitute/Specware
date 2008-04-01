InstantiateHO qualifying
spec
  import Simplify
  import CurryUtils
  import ../Specs/Utilities
  type Term = MS.Term

  op  instantiateHOFns: Spec -> Spec
  def instantiateHOFns spc =
    %let _ = writeLine("Before HO Instantiation:\n"^printSpec spc) in
    let result = aux_instantiateHOFns spc false in
    %let _ = writeLine("After HO Instantiation:\n"^printSpec result) in
    result

  %% snark interface can call this directly to set flag to true
  op  aux_instantiateHOFns: Spec -> Boolean -> Spec
  def aux_instantiateHOFns spc snark_hack? =
    %let spc = renameInSpec spc in
    let spc = normalizeCurriedDefinitions spc in
    let spc = simplifySpec spc in
    let m = makeUnfoldMap spc snark_hack? in
    %let m = mapAQualifierMap (renameDefInfo (emptyContext())) m in
    let spc = unFoldTerms(spc,m) in
    spc

%  def renameDefInfo c (vs,defn,defsrt,fnIndices,curried?,recursive?) =
%    let vs = map (renamePattern c) vs in
%    let defn = renameTerm c defn in
%    (vs,defn,defsrt,fnIndices,curried?,recursive?)


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% mapSpecNotingOpNames is a variant of mapSpec that allows us to use the name
 %% of an op in the tranformations being done on terms within it.
 %% If necessary, it could be generalized to do something similar for types.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op  mapSpecNotingOpNames : (QualifiedId -> (ATerm Position -> ATerm Position)) *
			    (ASort    Position -> ASort    Position) *
    		            (APattern Position -> APattern Position)
			     -> Spec -> Spec

 def mapSpecNotingOpNames (op_fn, sort_fn, pat_fn) spc =
   let outer_tsp = (op_fn (mkUnQualifiedId "outside_of_any_op"), sort_fn, pat_fn) in
   spc << {
	   sorts        = mapSpecSorts          outer_tsp spc.sorts,
	   ops          = mapSpecOpsNotingName  op_fn sort_fn pat_fn spc.ops,
	   elements     = mapSpecProperties     outer_tsp spc.elements
	  }

 op  mapSpecOpsNotingName : (QualifiedId -> (ATerm Position -> ATerm Position)) -> 
			    (ASort    Position -> ASort    Position) ->
			    (APattern Position -> APattern Position) ->
			    AOpMap Position -> AOpMap Position

 def mapSpecOpsNotingName op_fn sort_fn pat_fn ops =
   mapOpInfos (fn info -> 
	       let inner_tsp = (op_fn (primaryOpName info), sort_fn, pat_fn) in
	       %% now the the tsp knows the name of the op
	       info << {dfn = mapTerm inner_tsp info.dfn})
              ops

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op  unFoldTerms: Spec * AQualifierMap DefInfo -> Spec
  def unFoldTerms(spc,m) =
    let simplifyTerm = simplify spc in
    mapSpecNotingOpNames (fn outer_qid -> (fn t -> maybeUnfoldTerm(outer_qid,t,m,simplifyTerm,spc)),
			  id,
			  id)
                         spc

  op  unfoldInTerm: QualifiedId * Term * AQualifierMap DefInfo * (Term -> Term) * Spec -> Term
  def unfoldInTerm(outer_qid,tm,m,simplifyTerm,spc) =
    mapSubTerms (fn t -> maybeUnfoldTerm(outer_qid, t,m,simplifyTerm,spc))
      tm

  %% (params,defn body,indices of applied fn args,curried?,recursive?)
  type DefInfo = List Pattern * Term * Sort * List Nat * Boolean * Boolean

  op  makeUnfoldMap: Spec -> Boolean -> AQualifierMap DefInfo
  def makeUnfoldMap spc snark_hack? =
    mapiPartialAQualifierMap
      (fn (q, id, info) -> 
       let (decls, defs) = opInfoDeclsAndDefs info in
       case defs of
	 | [] -> None
	 | dfn :: _ ->
	   let (tvs, srt, def1) = unpackTerm dfn in
	   %% would like to remove tvs ~= [] condition but currently causes problem in Snark translation
	   if (if snark_hack? then tvs ~= [] else true) && hoFnSort? (spc, srt)  && unfoldable? (Qualified (q, id), def1) then
	     let numCurryArgs = curryShapeNum(spc,srt) in
             % see note below about debugging indexing error
             % let _ = toScreen ("\n numCurryArgs = " ^ (toString numCurryArgs) ^ " for " ^ (anyToString srt) ^ "\n") in
	     let argSorts = (if numCurryArgs > 1 then
			       curryArgSorts    (spc, srt)
			     else 
			       noncurryArgSorts (spc, srt))
	     in
	     let HOArgs = map (fn s -> hoSort?(spc,s)) argSorts in
	     if numCurryArgs > 1 then
	       analyzeCurriedDefn(Qualified(q,id), def1, numCurryArgs, HOArgs, srt)
	     else 
	       analyzeUnCurriedDefn(Qualified(q,id), def1, HOArgs, srt)
	   else 
	     None)
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
    % possibly useful to help debug current indexing error that happens with:  proc MatchingProofs
    % Confusion with Functions.o  (possibly because it it typed using Function(a,b) instead of a -> b)
    % let _ = toScreen ("\n:Params  [" ^ (Nat.toString (List.length params))  ^ "]= " ^ (anyToString params) ^ "\n") in
    % let _ = toScreen ("\n:Patinds [" ^ (Nat.toString (List.length patinds)) ^ "]= " ^ (anyToString patinds) ^ "\n") in
    % let _ = toScreen ("\n:HOARgs  [" ^ (Nat.toString (List.length HOArgs))  ^ "]= " ^ (anyToString HOArgs)  ^ "\n") in
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

  op  maybeUnfoldTerm: QualifiedId * Term * AQualifierMap DefInfo * (Term -> Term) * Spec -> Term
  def maybeUnfoldTerm(outer_qid, t,unfoldMap,simplifyTerm,spc) =
   case t of
     | Apply (f,a,_) ->
       (case f of
	  %% Uncurried case
	  | Fun(Op(qid as Qualified(q,id),_),srt,_) ->
	    (case findAQualifierMap(unfoldMap,q,id) of
	       | None -> t
	       | Some (vs, defn, defsrt, fnIndices, curried?, recursive?) ->
		 if ~curried?
		      & length(termList a) > foldr max 0 fnIndices
		      & exists (fn i -> constantTerm?(getTupleArg(a,i)))
		          fnIndices
		  then makeUnfoldedTerm
		         (outer_qid, f,termToList a,inferType(spc,t),
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
			    then makeUnfoldedTerm(outer_qid, f,args,inferType(spc,t),
						  sortMatch(defsrt,srt,spc),
						  vs,defn,fnIndices,recursive?,
						  qid,id,unfoldMap,simplifyTerm,spc)
			    else t)
		    | _ -> t))
	  | _ -> t)
     | _ -> t

  op  makeUnfoldedTerm: QualifiedId * Term * List Term * Sort * TyVarSubst * List Pattern * Term
                         * List Nat * Boolean * QualifiedId * String
                         * AQualifierMap DefInfo * (Term -> Term) * Spec
                      -> Term
  def makeUnfoldedTerm(outer_qid, _(* f *), args, resultSort, tyVarSbst, vs, defbody, fnIndices,
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
      then makeRecursiveLocalDef(outer_qid,qid,nm,defbody,resultSort,tyVarSbst,
				 remainingParams, remainingArgs,remainingIndices,
				 vSubst,simplifyTerm)
      else
      let defbody = instantiateTyVarsInTerm(defbody, tyVarSbst) in
      let remainingParams = map (fn p -> instantiateTyVarsInPattern(p,tyVarSbst))
                              remainingParams in

      let (remainingParams, remainingArgs) = 
          adjustBindingsToAvoidCapture (remainingParams, remainingArgs, (* vs, *) args, defbody)
      in

      let newTm = makeLet(remainingParams,remainingArgs,defbody) in
      let newTm = substitute(newTm,vSubst) in
      unfoldInTerm(outer_qid, simplifyTerm(newTm),unfoldMap,simplifyTerm,spc)


  def adjustBindingsToAvoidCapture (remainingParams, remainingArgs, (* params, *) args, defbody) =

    %% If a parameter var could capture a free var in an arg, introduce temp vars to 
    %% avoid the capture:
    %%   First bind the new temp vars to all the args (no capture possible).
    %%   Then bind the parameter vars to the new temp vars (no capture possible).

    let 
      def similar? (param, arg) =
	    case (param, arg) of
	      | (VarPat ((param_id,_),_), Var ((arg_id,_),_)) -> 
	        param_id = arg_id
	      | (RecordPat (p_fields, _), Record (a_fields, _)) ->
	        all (fn (p,a) -> similar? (p,a)) 
		    (zip ((map (fn field -> field.2) p_fields), 
			  (map (fn field -> field.2) a_fields)))
	      | _ -> false
    in
    let (remainingParams, remainingArgs) = 
        unzip (filter (fn (param, arg) -> ~ (similar?(param, arg)))
	              (zip (remainingParams, remainingArgs)))
    in
    let pattern_vars  : List (List Var) = map patVars  remainingParams in
    let arg_free_vars : List (List Var) = map freeVars remainingArgs   in
    let possible_capture? =
        case rev pattern_vars of
	  | [] -> false
	  | _ :: outer_pattern_vars ->
	    (let (capture?, _) =
	     foldl (fn (arg_vars, (capture?, outer_pattern_vars_list)) ->
		    if capture? then
		      (true, [])
		    else if exists (fn av -> 
				    exists (fn outer_pat_vars -> 
					    exists (fn pv -> av.1 = pv.1) 
					           outer_pat_vars)
				           outer_pattern_vars_list)
		                   arg_vars 
		      then
			(true, [])
		    else
		      (false,
		       case outer_pattern_vars_list of
			 | [] -> []
			 | _ :: outer_list -> outer_list))
	           (false, outer_pattern_vars)
		   (rev arg_free_vars)
	     in
	       capture?)
    in
    if possible_capture? then
      %% Note: This is a rare occurence.  It seems to happen once(!) in the Forges PSL
      %% sources, and never in Specware, Accord, Planware, JFlaws, JavaCard, ...
      let 
        def find_unused_id index =
	  let new_id = "temp-" ^ (toString index) ^ "-" in
	  if idReferenced? (new_id, defbody) || (exists (fn arg -> idReferenced? (new_id, arg)) args) then
	    find_unused_id (index + 1)
	  else
	    (index + 1, new_id)
      in
      let (_, temp_vars) = 
	  foldl (fn (arg, (index, new_vars)) ->
		 let (index, new_id) = find_unused_id index in
		 let new_var = ((new_id, termSort arg), noPos) in
		 (index,  new_vars ++ [new_var]))
	        (0, [])
		remainingArgs
      in
      let revisedParams = (map (fn v -> VarPat v) temp_vars) ++ remainingParams               in
      let revisedArgs   = remainingArgs                      ++ map (fn v -> Var v) temp_vars in
      (revisedParams, revisedArgs)
    else	
      (remainingParams, remainingArgs)

  op  my_x_counter : () -> Nat

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

  def makeRecursiveLocalDef(outer_qid,qid,nm,defbody,resultSort,tyVarSubst,remainingParams,
			    remainingArgs,remainingIndices,vSubst,simplifyTerm) =
    %% check name conflict with args and defbody. defbody should be safe
    %% because user can't put "--" in identifier, but to be safe
    %% We ignore provided "nm" (its probably equal to the id part of qid),
    %% and compute a new "nm" using the entire qualified id.
    let prefix = (let Qualified(q,xid) = outer_qid in 
		  if q = UnQualified then xid else q ^ "_" ^ xid)
    in
    let localFnName = locallyUniqueName(prefix^"_"^nm^"--local",
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
	  | (Quotient(ty,_,_),Quotient(ty2,_,_)) -> 
	    match(ty,ty2,pairs)
	  | (Subsort(ty,_,_),ty2) -> match(ty,ty2,pairs)
	  | (ty,Subsort(ty2,_,_)) -> match(ty,ty2,pairs)
	  | (Base(id,ts,pos1),Base(id2,ts2,pos2)) ->
	    if id = id2
	      then matchL(ts,ts2,pairs,match)
	      else
		let s2x = unfoldBase(spc,srt2) in
		if equalType? (srt2,s2x) % also reasonable: equivType? spc (srt2,s2x)
		  then pairs
		else match(srt1,s2x,pairs)
	  | (_,Base _) ->
	    let s2x = unfoldBase(spc,srt2) in
	    if equalType? (srt2,s2x)  % also reasonable: equivType? spc (srt2,s2x)
	     then pairs
	     else match(srt1,s2x,pairs)
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
	  (fn (q, id, info) ->
	   let pos = termAnn info.dfn in
	   let (old_decls, old_defs) = opInfoDeclsAndDefs info in
	   case old_defs of
	     | [] -> info
	     | _ ->
	       let new_defs =
	           map (fn dfn ->
			let pos = termAnn dfn in
			let (tvs, srt, def1) = unpackTerm dfn in
			let numCurryArgs = curryShapeNum (spc, srt) in
			let argSorts     = curryArgSorts (spc, srt) in
			let normDef1 = normalizeCurriedDefn (def1, argSorts) in
			maybePiTerm (tvs, SortedTerm (normDef1, srt, pos)))
	               old_defs
	       in
		 info << {dfn = maybeAndTerm (old_decls ++ new_defs, pos)})
          spc.ops
    in 
      setOps (spc, normOps)

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
					    (result ++ [(label,("xxx-"^Nat.toString i,srt))],
					     i+1))
				      ([],0) fields).1
			in mkLambda(mkRecordPat(map (fn(l,v) -> (l,mkVarPat(v))) vars),
				    mkApply(defn,
					    mkRecord(map (fn (l,v) -> (l,mkVar(v))) vars))))
		  else 
		  let nv = ("yyy-"^Nat.toString argNum,argSort) in
		  mkLambda(mkVarPat(nv),aux(mkApply(defn,mkVar(nv)),rSorts,argNum+1))
    in aux(defn,curryArgSorts,0)

  op  transparentRenaming: Qualifier * Id * Term * Spec -> Qualifier * Id * Term
  %% If definition is just a renaming then "unfold"
  def transparentRenaming (q, id, def1, spc) =
    case def1 of
      | Fun (Op (Qualified (q2, id2),_), _, _) ->
        (case findAQualifierMap (spc.ops, q2, id2) of
	  | Some info -> 
	    (let (decls, defs) = opInfoDeclsAndDefs info in
	     case defs of
	       | [def2] -> (q2, id2, def2)
	       | _ -> (q, id, def1))
	  | _ -> (q, id, def1))
      | _ -> (q, id, def1)


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
