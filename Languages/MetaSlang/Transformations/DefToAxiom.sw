Prover qualifying spec
 import ../Specs/Environment
 import ProverPattern

  sort Term = MS.Term
  op unCurry: MS.Term * Nat -> Option ((List Id) * MS.Term)

  op unCurrySort: Sort * Nat -> Sort

  op mkUncurryEquality: Spec * Sort * QualifiedId * MS.Term -> MS.Term

  def mkUncurryEquality(sp, srt, qid, trm) =
    let funOp = mkOp(qid, srt) in
      mkUncurryEqualityRec(sp, srt, trm, funOp, srt, trm, [])

  op mkUncurryEqualityRec: Spec * Sort * MS.Term * MS.Term *
                           Sort * MS.Term * List MS.Term -> MS.Term

  def mkUncurryEqualityRec(sp, topSrt, topTrm, topFunOp, srt, trm, prevArgs) =
    case srt of
      | Arrow (dom, rng, _) ->
        (case trm of
	  | Lambda ([(pat, cond, body)],_) ->
	    let argNames = patternNamesOpt(pat) in
	    (case argNames of
	      | Some argNames ->
	      let numargs = length argNames in
	      let argSorts = case productOpt(sp, dom) of
			       | Some fields -> map (fn (_,srt) -> srt) fields
			       | None -> [dom] in
	      let arity = length(argSorts) in
	      if arity = numargs
		then 
		  let newArgs = map (fn(id, srt) -> mkVar (id,srt)) (argNames, argSorts) in
		  mkUncurryEqualityRec(sp, topSrt, topTrm, topFunOp, rng, body, prevArgs ++ newArgs)
	      else
		mkEquality(topSrt, topFunOp, topTrm)
	      | _-> mkEquality(topSrt, topFunOp, topTrm))
	  | _ -> mkEquality(topSrt, topFunOp, topTrm))
       | _ ->
	   (case trm of
	      | Lambda ([(pat, cond, body)],_) ->  mkEquality(topSrt, topFunOp, topTrm)
	      | _ -> mkEquality(srt, mkAppl(topFunOp, prevArgs), trm))
      
(*  op mkUncurryEqualityRec: Spec * Sort * MS.Term *
                           Sort * QualifiedId * Pattern *
			   Sort * MS.Term * Nat -> MS.Term

  def mkUncurryEqualityRec(sp, srt, trm, dom, qid, pat, rng, body, curryN) =
    let argNames = patternNames(pat) in
    let numargs = length argNames in
    let argSorts = case productOpt(sp, dom) of
		     | Some fields -> map (fn (_,srt) -> srt) fields
		     | None -> [dom] in
    let arity = length(argSorts) in
    let funOp = mkOp(qid, srt) in
    if arity = numargs
      then 
	let args = map (fn(id, srt) -> mkVar (id,srt)) (argNames, argSorts) in
	let lhs = mkAppl(funOp, args) in
	mkEquality(rng, lhs, body)
    else
      mkEquality(srt, funOp, trm)
*)

  op mkDefEquality: Sort * QualifiedId * MS.Term -> MS.Term

  def mkDefEquality(srt, qid, trm) =
    mkEquality(srt, mkOp(qid, srt), trm)

  def productLength(sp:Spec, srt:Sort) = 
    case productOpt(sp,srt)
      of Some fields -> length fields
       | None -> 1

  def functionSort?(sp,srt) = 
      case unfoldBase(sp,srt)
        of Arrow _ -> true
         | Subsort(s,_,_) -> functionSort?(sp,s)
         | _ -> false
(*
 op patternNameOpt : Pattern       -> Option Id
 op patternNamesOpt: Pattern       -> Option (List Id)

 def patternNameOpt (pattern) = 
   case pattern of
     | VarPat((id,_),_) -> Some id 
     | _ -> None

 def patternNamesOpt (pattern) = 
   case pattern of
     | VarPat((id,_),_) -> Some [id]
     | RecordPat(fields,_) ->
         List.foldl (fn ((_,p), namesOpt) ->
		     case namesOpt of
		       | Some names ->
		       (case patternNameOpt(p) of
			  | Some name -> Some (names ++ [name])
			  | _ -> None)
		       | _-> None)
	            (Some ([])) fields
     | _ -> None
*)
  op curryShapeNum: Spec * Sort -> Nat
  def curryShapeNum(sp,srt) =
    case arrowOpt(sp,srt)
      of Some (dom,rng) -> 1 + curryShapeNum(sp,rng)
       | _ -> 0

  op unLambdaDef: Spec * Sort * QualifiedId * MS.Term -> List MS.Term

  def unLambdaDef(spc, srt, name, term) =
    let new_equality = mkUncurryEquality(spc, srt, name, term) in
    let faVars = freeVars(new_equality) in
    let new_equality = mkBind(Forall, faVars, new_equality) in
    let eqltyWithPos = withAnnT(new_equality, termAnn(term)) in
      [eqltyWithPos]

(*    if functionSort?(spc,srt)
      then
	(case (curryShapeNum(spc,srt),sortArity(spc,srt))
	   of (1,None) ->
	     (case term of 
		| Lambda ([(pat, cond, body)], _)
		    -> [mkUncurryEquality(spc, srt, name, body)]
		| _ -> [mkDefEquality(srt, name, term)] %fail("unCurryDef?")
		     )
	    | (1,Some (_,arity)) ->
		(case term of
		   | Lambda ([(pat, cond, body)],_) ->
		     let formals = patternNames(pat) in
		     let n = length formals in
		       [mkUncurryEquality(spc, srt, name, term)]
		   | _ ->  % fail("Not sure that arity normalization hasn't precluded this case")
		     [mkDefEquality(srt, name, term)])
	    | (curryN,None) ->
		 (case unCurry(term,curryN) of
		    | Some (uCArgs, uCBody) ->  % fn x -> fn y -> fn z -> f-1-1-1(x,y,z)
		       [mkUncurryEquality(spc, srt, name, term)]
		    | _ -> [mkDefEquality(srt, name, term)])
	    | (curryN,Some (_,arity)) ->
		 (case unCurry(term,curryN) of
		    | Some (uCArgs, uCBody) ->
		       [mkUncurryEquality(spc, srt, name, term)]
		    | _ -> [mkDefEquality(srt, name, term)]))
    else [mkDefEquality(srt, name, term)]
*)

  op axiomFromOpDefTop: Spec * Qualifier * Id * OpInfo -> Properties
  
  def axiomFromOpDefTop(spc,qname,name,decl) =
    case decl:OpInfo of
      | (op_names, fixity, (srtTyVars,srt), [(termTyVars, term)]) ->
        let localOps = spc.importInfo.localOps in
	if memberQualifiedId(qname, name, localOps) then
	  let pos = termAnn(term) in
	  let opName = mkQualifiedId(qname, name) in
	  let initialFmla = hd (unLambdaDef(spc, srt, opName, term)) in
	  let liftedFmlas = proverPattern(initialFmla) in
	  let axioms = map (fn(fmla:Term) -> (Axiom, name^"_def", [], withAnnT(fmla, pos))) liftedFmlas in
	  %%let ax:Property = (Axiom, name^"_def", [], hd (unLambdaDef(spc, srt, opName, term))) in
	  	%let _ = writeLine(name^": in axiomFromOpDef Def part") in
            axioms
	else %let _ = writeLine(name^": in axiomFromOpDef Def part is not local") in
	  %let _ = debug("not local op") in
	     []
      | _ -> %let _ = writeLine(name^": in axiomFromOpDef NOT def part") in
	       []
	

  op explicateHiddenAxioms: Spec -> Spec
  def explicateHiddenAxioms spc =
    let def axiomFromOpDef(qname,name,decl,defs) = defs ++ axiomFromOpDefTop(spc,qname,name,decl) in
    let norm_spc = spc in
    %%let norm_spc = translateMatch(norm_spc) in
    %%let norm_spc = arityNormalize(norm_spc) in
    let def mergeAxiomsByPos(oas, nas) =
      let def cmpGt(oax as (_, _, _, oat), nax as (_, _, _, nat)) =
        let old_pos:Position = termAnn(oat) in
	let new_pos = termAnn(nat) in
	case compare(old_pos, new_pos) of
	  | Greater -> false
	  | _ -> true in
      case (oas,nas) of
        | ([],nas) -> nas
        | (oas,[]) -> oas
        | (oa::oas,na::nas) ->
            if cmpGt(oa, na) then
              Cons(na, mergeAxiomsByPos(Cons(oa,oas),nas))
            else Cons(oa, mergeAxiomsByPos(oas,Cons(na,nas))) in
    let newAxioms = foldriAQualifierMap axiomFromOpDef [] norm_spc.ops in
    let newProperties = mergeAxiomsByPos(spc.properties, newAxioms) in
    %%let _ = debug("explicateHidden") in 
    setProperties(spc, newProperties)

endspec
