Prover qualifying spec
 import ../Specs/Environment
 import ProverPattern
 import OpToAxiom
 import Simplify
 import ../CodeGen/CodeGenTransforms

  % sort Term = MS.Term
  op unCurry: MS.Term * Nat -> Option ((List Id) * MS.Term)

  op unCurrySort: Sort * Nat -> Sort

  op mkUncurryEquality: Spec * Sort * QualifiedId * MS.Term -> MS.Term

  def mkUncurryEquality (sp, srt, qid, trm) =
    let funOp = mkOp (qid, srt) in
    mkUncurryEqualityRec (sp, srt, trm, funOp, srt, trm, [])

  op mkUncurryEqualityRec: Spec * Sort * MS.Term * MS.Term *
                           Sort * MS.Term * List MS.Term -> MS.Term

  def mkUncurryEqualityRec (sp, topSrt, topTrm, topFunOp, srt, trm, prevArgs) =
    % case arrowOpt(sp, srt) of
    %  | Some(dom, rng) ->
    case srt of
      | Arrow (dom, rng, _) ->
        (case trm of
	  | Lambda ([(pat, cond, body)], _) ->
	    let argNames = patternNamesOpt pat in
	    (case argNames of
	      | Some argNames ->
	        let numargs = length argNames in
		let argSorts = case productOpt (sp, dom) of
				 | Some fields -> map (fn (_, srt) -> srt) fields
				 | None -> [dom] in
		let arity = length argSorts in
		if arity = numargs then
		  let newArgs = map (fn (id, srt) -> mkVar (id, srt)) (argNames, argSorts) in
		  mkUncurryEqualityRec (sp, topSrt, topTrm, topFunOp, rng, body, prevArgs ++ newArgs)
		else 
		  let argSorts = case dom of
				   | Product (fields, _) -> map (fn (_, srt) -> srt) fields
				   | None -> [dom] in
		  let arity = length argSorts in
		  if arity = numargs then
		    let newArgs = map (fn (id, srt) -> mkVar (id, srt)) (argNames, argSorts) in
		    mkUncurryEqualityRec (sp, topSrt, topTrm, topFunOp, rng, body, prevArgs ++ newArgs)
		  else
		    %let _ = if topFunOp = mkOp (mkUnQualifiedId "switch", topSrt) then debug "topUnc" else () in 
		    mkEquality (topSrt, topFunOp, topTrm)
	      | _-> 
		%let _ = if topFunOp = mkOp (mkUnQualifiedId "switch", topSrt) then debug "topUnc" else () in
		mkEquality (topSrt, topFunOp, topTrm))
	  | _ -> 
	    %let _ = if topFunOp = mkOp (mkUnQualifiedId "switch", topSrt) then debug "topUnc" else () in
	    mkEquality (topSrt, topFunOp, topTrm))
       | _ ->
	 case trm of
	   | Lambda ([(pat, cond, body)], _) -> 
	     %let _ = if topFunOp = mkOp (mkUnQualifiedId "switch", topSrt) then debug "topUnc" else () in
	     mkEquality (topSrt, topFunOp, topTrm)
	   | _ -> 
	     mkEquality (srt, mkAppl (topFunOp, prevArgs), trm)
      
(*  op mkUncurryEqualityRec: Spec * Sort * MS.Term *
                           Sort * QualifiedId * Pattern *
			   Sort * MS.Term * Nat -> MS.Term

  def mkUncurryEqualityRec (sp, srt, trm, dom, qid, pat, rng, body, curryN) =
    let argNames = patternNames pat in
    let numargs = length argNames in
    let argSorts = case productOpt (sp, dom) of
		     | Some fields -> map (fn (_, srt) -> srt) fields
		     | None -> [dom] in
    let arity = length argSorts in
    let funOp = mkOp (qid, srt) in
    if arity = numargs
      then 
	let args = map (fn (id, srt) -> mkVar (id, srt)) (argNames, argSorts) in
	let lhs = mkAppl (funOp, args) in
	mkEquality (rng, lhs, body)
    else
      mkEquality (srt, funOp, trm)
*)

  op mkDefEquality: Sort * QualifiedId * MS.Term -> MS.Term

  def mkDefEquality (srt, qid, trm) =
    mkEquality (srt, mkOp (qid, srt), trm)

  def productLength (sp:Spec, srt:Sort) = 
    case productOpt (sp, srt)
      of Some fields -> length fields
       | None -> 1

  def functionSort? (sp, srt) = 
      case unfoldBase (sp, srt)
        of Arrow _ -> true
         | Subsort (s, _, _) -> functionSort? (sp, s)
         | _ -> false
(*
 op patternNameOpt : Pattern       -> Option Id
 op patternNamesOpt: Pattern       -> Option (List Id)

 def patternNameOpt pattern = 
   case pattern of
     | VarPat ((id, _), _) -> Some id 
     | _ -> None

 def patternNamesOpt pattern = 
   case pattern of
     | VarPat ((id, _), _) -> Some [id]
     | RecordPat (fields, _) ->
         List.foldl (fn ((_, p), namesOpt) ->
		     case namesOpt of
		       | Some names ->
		        (case patternNameOpt p of
			  | Some name -> Some (names ++ [name])
			  | _ -> None)
		       | _-> None)
	            (Some ([])) fields
     | _ -> None
*)
  op curryShapeNum: Spec * Sort -> Nat
  def curryShapeNum (sp, srt) =
    case arrowOpt (sp, srt)
      of Some (dom, rng) -> 1 + curryShapeNum (sp, rng)
       | _ -> 0

  op unLambdaDef: Spec * Sort * QualifiedId * MS.Term -> List MS.Term

  def unLambdaDef (spc, srt, name, term) =
    let new_equality = mkUncurryEquality (spc, srt, name, term) in
    let faVars       = freeVars new_equality in
    let new_equality = mkBind (Forall, faVars, new_equality) in
    let eqltyWithPos = withAnnT (new_equality, termAnn term) in
    [eqltyWithPos]

(*    if functionSort? (spc, srt)
      then
	(case (curryShapeNum (spc, srt), sortArity (spc, srt))
	   of (1, None) ->
	     (case term of 
		| Lambda ([(pat, cond, body)], _)
		    -> [mkUncurryEquality (spc, srt, name, body)]
		| _ -> [mkDefEquality (srt, name, term)] %fail "unCurryDef?"
		     )
	    | (1, Some (_, arity)) ->
		(case term of
		   | Lambda ([(pat, cond, body)], _) ->
		     let formals = patternNames pat in
		     let n = length formals in
		       [mkUncurryEquality (spc, srt, name, term)]
		   | _ ->  % fail "Not sure that arity normalization hasn't precluded this case"
		     [mkDefEquality (srt, name, term)])
	    | (curryN, None) ->
		 (case unCurry (term, curryN) of
		    | Some (uCArgs, uCBody) ->  % fn x -> fn y -> fn z -> f-1-1-1 (x, y, z)
		       [mkUncurryEquality (spc, srt, name, term)]
		    | _ -> [mkDefEquality (srt, name, term)])
	    | (curryN, Some (_, arity)) ->
		 (case unCurry (term, curryN) of
		    | Some (uCArgs, uCBody) ->
		       [mkUncurryEquality (spc, srt, name, term)]
		    | _ -> [mkDefEquality (srt, name, term)]))
    else [mkDefEquality (srt, name, term)]
*)

  op axiomFromOpTop: Spec * Qualifier * Id * OpInfo -> Properties
  def axiomFromOpTop (spc, q, id, info) =
    axiomFromOpDefTop (spc, q, id, info) ++ 
    axiomFromOpSrtTop (spc, q, id, info)

  op axiomFromOpDefTop: Spec * Qualifier * Id * OpInfo -> Properties
  def axiomFromOpDefTop (spc, q, id, info) =
    case opInfoDefs info of
      | [] -> []
      | defs ->
        %% new: fold over all defs (but presumably just one for now)
        foldl (fn (dfn, props) ->
	       let (tvs, srt, term) = unpackTerm dfn in
	       let localOps = spc.importInfo.localOps in
	       if memberQualifiedId (q, id, localOps) then
		 let pos = termAnn term in
		 let qid = Qualified (q, id) in
		 let initialFmla = hd (unLambdaDef (spc, srt, qid, term)) in
		 %let unTupledFmlas = foldRecordFmla (spc, srt, initialFmla) in
		 %let unTupleAxioms = map (fn (fmla:MS.Term) -> (Axiom, mkQualifiedId (q, id^"_def"), [], withAnnT (fmla, pos))) unTupledFmlas in
		 let unTupleAxioms = [] in
		 %let _ = if true or id = "queens_gs_aux_1" then writeLine ("initialFmla: "^printTerm initialFmla) else () in
		 let liftedFmlas = proverPattern initialFmla in
		 %let simplifiedLiftedFmlas = map (fn fmla -> simplify (spc, fmla)) liftedFmlas in
		 %let _ = if id = "queens_gs_aux_1" then map (fn lf -> writeLine ("LiftedAxioms: " ^ printTerm lf)) liftedFmlas else [] in
		 let defAxioms = map (fn (fmla:MS.Term) -> (Axiom, mkQualifiedId (q, id^"_def"), [], withAnnT (fmla, pos))) liftedFmlas in
		 %%let ax:Property = (Axiom, id^"_def", [], hd (unLambdaDef (spc, srt, qid, term))) in
		 %let _ = writeLine (id^": in axiomFromOpDef Def part") in
		 props ++ defAxioms ++ unTupleAxioms
	       else 
		 %let _ = writeLine (id^": in axiomFromOpDef Def part is not local") in
		 %let _ = debug "not local op" in
		 props)
	      []
	      defs

   op axiomFromOpSrtTop: Spec * Qualifier * Id * OpInfo -> Properties
  def axiomFromOpSrtTop (spc, q, id, info) =
    let srt = firstOpDefInnerSort info in
    let localOps = spc.importInfo.localOps in
    if memberQualifiedId (q, id, localOps) then
      let pos = sortAnn srt in
      let qid = Qualified (q, id) in
      let subTypeFmla = opSubsortAxiom (spc, qid, srt) in
      let liftedFmlas = proverPattern subTypeFmla in
      let subTypeAxioms =
          map (fn (fmla : MS.Term) -> 
	       (Axiom, 
		mkQualifiedId (q, id^"_def"), 
		[], 
		withAnnT (fmla, pos))) 
	      liftedFmlas 
      in
	%(Axiom, mkQualifiedId (q, id^"_def"), [], withAnnT (subTypeFmla, pos)) in
	subTypeAxioms
    else 
      %let _ = writeLine (id^": in axiomFromOpDef Def part is not local") in
      %let _ = debug "not local op" in
      []

  op foldRecordFmla: Spec * Sort * MS.Term -> List MS.Term
  def foldRecordFmla (spc, srt, fmla) =
    case srt of
      | Arrow (dom, range, _) ->
        (case productOpt (spc, dom) of
	   | Some fields ->
	     (case findMatchingUserTypeOption (spc, dom) of
		| Some (usrt as Base (srtId, _, _)) ->
		  (case fmla of
		     | Bind (Forall, vars, body, b) ->
		       let recVar  = (mkRecVarId srtId, usrt) in
		       let subst   = mkSubstProjForVar (vars, fields, usrt, recVar) in
		       let newBody = substituteInRHSEqualityBody (body, subst) in
		       [mkBind (Forall, [recVar], newBody)]
		     | _ -> [])
		| _ -> [])
	   | _ -> [])
      | _ -> []

  op substituteInRHSEquality: MS.Term * List (Var * MS.Term) -> MS.Term
  def substituteInRHSEqualityBody (term, subst) =
    case term of
      | Apply (Fun (Equals, eSrt, _), 
	       Record ([(_, LHS), (_, RHS)], _), 
	       _) 
        -> 
        let newRHS = substitute (RHS, subst) in
	mkEquality (eSrt, LHS, newRHS)
      | _ -> substitute (term, subst)
  
  op mkRecVarId: QualifiedId -> String
  def mkRecVarId (Qualified (_, id)) = id ^ "RecVar"

  op mkSubstProjForVar: List Var * List (FieldName * Sort) * Sort * Var -> List (Var * MS.Term)
  def mkSubstProjForVar (vars, fields, recSrt as Base (sort_qid as Qualified (_, sort_id), _,  _), recVar) =
    let
      def mkSubstProjForVarRec (vars, fields) =
	case (vars, fields) of
	  | ([], []) -> []
          | (hdVar::restVars, (field_id, fieldSrt) :: restFields) ->
	    let restSubst = mkSubstProjForVarRec (restVars, restFields) in
            let proj_id   = getAccessorOpName (sort_id, sort_qid, field_id) in
	    let funTerm   = Fun (Op (proj_id, Nonfix), 
				 Arrow (recSrt, fieldSrt, noPos), 
				 noPos) 
	    in
	    let term = Apply (funTerm, Var (recVar, noPos), noPos) in
	    Cons ((hdVar, term), restSubst) 
    in
      mkSubstProjForVarRec (vars, fields)


endspec
