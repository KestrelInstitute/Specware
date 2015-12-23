(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Prover qualifying spec
 import ../Specs/Environment
 import ProverPattern
 import OpToAxiom
 import Simplify
 import ../CodeGen/CodeGenUtilities

  % type Term = MS.Term

  op unCurry: MSTerm * Nat -> Option ((List Id) * MSTerm)

  op unCurryType: MSType * Nat -> MSType

% This stuff is in progress. --Eric
%   %Extracts the range of an arrow type.  Skips over subtypes, and
%   %looked up named types (wrapped in Base) as necessary.  Gives an
%   %error if the type is not an arrow type.  Ex: x -> y becomes just y.
%   op rangeOfArrowType (ty : MSType, spc : Spec) : MSType =
%     case ty of
%     | Arrow(dom, ran, _) -> ran
%     | Subtype(ty, tm, _) -> rangeOfArrowType(ty, spc) %just ignore the subtype
%     | Base(_, _, _) -> rangeOfArrowType(unfoldBase(spc, ty), spc) %pass the whole type into unfoldBase (will substitute the actuals in the type instantiation for the formals).
%     | _ -> let _ = writeLine "ERROR: rangeOfArrowType called on a non-arrow type." in ty %what should we return here?

%   % better way to handle this?
%   op errorTerm : MSTerm = Fun(String("ERROR"), Base(mkQualifiedId("String","String"),[], noPos), noPos)

%   % Added by Eric (10/31/2012).  Based on mkUncurryEqualityRec, which
%   % seemed to not treat currying correctly and was causing crashes
%   % later in the process of generating Isabelle obligationss.  This op
%   % makes an equality of a function call and its body (this equality
%   % is essentially the axiom represented by the op definition). TODO
%   % handle other cases (e.g., other patterns in the lambdas).  tm is
%   % the body of the op.  ty is the type of the op.  topFun is a Fun
%   % term corresponding to the op (suitable to be applied to argument
%   % terms).  paramsFound is in reverse order from the order
%   % of the params in the call. Each param is a variable or tuple.
%   op equateFunCallToBody_aux (tm:MSTerm, ty:MSType, topFun : MSTerm, topTy : MSType, spc:Spec, paramsFound : MSTerms) : MSTerm =
%     case tm of
%       %% TODO Should we preserve the type somehow?
%       | TypedTerm(tm,_,_) -> equateFunCallToBody_aux(tm, ty, topFun, topTy, spc, paramsFound)
%         %% I am leaving the Pi, because that's what mkUncurryEqualityRec does.
%       | Pi(tyvars,tm,_) -> Pi(tyvars, equateFunCallToBody_aux(tm, ty, topFun, topTy, spc, paramsFound), noPos)
%       % TODO handle a lambda with more than one branch in its match.
%       | Lambda([(pat, _, lambdabody)], _) -> 
%         (case pat of
%            | VarPat(var, _) -> equateFunCallToBody_aux(lambdabody, rangeOfArrowType(ty, spc), topFun, topTy, spc, Var(var, noPos)::paramsFound)
%            | RecordPat(pairs, _) ->
%              (if (forall? (fn (x,y) -> (case y of | VarPat(var, _) -> true | _ -> false)) pairs) then  %TTODO check that the field names are 1,2,3,... or maybe the handling of true (non-tuple) records here is okay.
%                 let tuplecomponents = (map (fn (x,VarPat(var, ann)) -> (x,Var(var, ann))) pairs) in
%                 let newparam = Record(tuplecomponents, noPos) in
%                 equateFunCallToBody_aux(lambdabody, rangeOfArrowType(ty, spc), topFun, topTy, spc, newparam::paramsFound)
%               else
%                 let _ = writeLine "ERROR: In equateFunCallToBody_aux, we don't yet handle tuples containing anything other than variables." in errorTerm)
%              % Trying the idea of stopping when we hit this.  The old version also added the type, like in this example:
% % conjecture Map.TMApply_def is 
% %   Map.TMApply 
% %    = fn (m: Map.Map(a, b), x: a | x in? Map.domain m) -> the (z: b) Map.apply m x = Some z
% %      : {(m, x): (Map.Map(a, b) * a) | x in? Map.domain m} -> b
%            | RestrictedPat(_, _, _) -> mkEquality(ty,mkCurriedApply(topFun, reverse (paramsFound)),tm)
%            | _ -> let _ = writeLine "ERROR: In equateFunCallToBody_aux, we don't yet handle this kind of pattern." in errorTerm)
%       % It's not a lambda, so we've stripped off all the lambdas and can now form the function call:
%       | _ -> mkEquality(ty,mkCurriedApply(topFun, reverse (paramsFound)),tm)
                                   
  op equateFunCallToBody (tm:MSTerm, ty:MSType, opqid: QualifiedId, spc:Spec) : MSTerm =
    %% Commenting out this new version for now, because I am not sure it is right:
    %%equateFunCallToBody_aux(tm, ty, mkOp(opqid, ty), ty, spc, [])
    %% Very simple version (does not attempt to gather function parameters and quantify over them).
    %% TODO: This may not result in nice rewrite rules.  One
    %% strategy could be to use this simple translation and then prove
    %% any desired rewrite rules from it.
    mkEquality(ty, mkOp(opqid, ty), tm)




  % Is this still called in one place?  Should we replace that use with equateFunCallToBody also?
  op mkUncurryEquality: Spec * MSType * QualifiedId * MSTerm -> MSTerm

  def mkUncurryEquality (sp, srt, qid, trm) =
    let funOp = mkOp (qid, srt) in
    mkUncurryEqualityRec (sp, srt, trm, funOp, srt, trm, [])

  op mkUncurryEqualityRec: Spec * MSType * MSTerm * MSTerm *
                           MSType * MSTerm * MSTerms -> MSTerm

  def mkUncurryEqualityRec (sp, topSrt, topTrm, topFunOp, srt, trm, prevArgs) =
    %let _ = writeLine("mkUncurryEqualityRec: "^printTerm trm) in
    %let _ = writeLine("mkUncurryEqualityRec srt: "^printType srt) in
    %let _ = writeLine("mkUncurryEqualityRec unfolded srt: "^printType (unfoldBase(sp,srt))) in
    case trm of
      | TypedTerm(t,_,_) ->
        mkUncurryEqualityRec(sp, topSrt, topTrm, topFunOp, srt, t, prevArgs)
      | Pi(srts,t,a) ->
	Pi(srts,mkUncurryEqualityRec(sp, topSrt, topTrm, topFunOp, srt, t, prevArgs),a)
      | _ ->
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
		let argTypes = case productOpt (sp, dom) of
				 | Some fields -> map (fn (_, srt) -> srt) fields
				 | None -> [dom] in
		let arity = length argTypes in
		if arity = numargs then
		  let newArgs = map (fn (id, srt) -> mkVar (id, srt)) (argNames, argTypes) in
		  mkUncurryEqualityRec (sp, topSrt, topTrm, topFunOp, rng, body, prevArgs ++ newArgs)
		else 
		  let argTypes = case dom of
				   | Product (fields, _) -> map (fn (_, srt) -> srt) fields
				   | None -> [dom] in
		  let arity = length argTypes in
		  if arity = numargs then
		    let newArgs = map (fn (id, srt) -> mkVar (id, srt)) (argNames, argTypes) in
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
      
(*  op mkUncurryEqualityRec: Spec * MSType * MSTerm *
                           MSType * QualifiedId * Pattern *
			   MSType * MSTerm * Nat -> MSTerm

  def mkUncurryEqualityRec (sp, srt, trm, dom, qid, pat, rng, body, curryN) =
    let argNames = patternNames pat in
    let numargs = length argNames in
    let argTypes = case productOpt (sp, dom) of
		     | Some fields -> map (fn (_, srt) -> srt) fields
		     | None -> [dom] in
    let arity = length argTypes in
    let funOp = mkOp (qid, srt) in
    if arity = numargs
      then 
	let args = map (fn (id, srt) -> mkVar (id, srt)) (argNames, argTypes) in
	let lhs = mkAppl (funOp, args) in
	mkEquality (rng, lhs, body)
    else
      mkEquality (srt, funOp, trm)
*)

  op mkDefEquality: MSType * QualifiedId * MSTerm -> MSTerm

  def mkDefEquality (srt, qid, trm) =
    mkEquality (srt, mkOp (qid, srt), trm)

  def functionType? (sp, srt) = 
      case unfoldBase (sp, srt)
        of Arrow _ -> true
         | Subtype (s, _, _) -> functionType? (sp, s)
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
         List.foldl (fn (namesOpt, (_, p)) ->
		     case namesOpt of
		       | Some names ->
		        (case patternNameOpt p of
			  | Some name -> Some (names ++ [name])
			  | _ -> None)
		       | _-> None)
	            (Some ([])) fields
     | _ -> None
*)

  op unLambdaDef (spc:Spec, srt:MSType, name:QualifiedId, term:MSTerm) : MSTerms =
    % let _ = writeLine("unLambdaDef: "^printTerm term) in
    let new_equality = equateFunCallToBody(term, srt, name, spc) in %% mkUncurryEquality (spc, srt, name, term) in
    % let _ = writeLine("new_eq: "^printTerm new_equality) in
    let (srt_vars,new_equality,piPos) =
        case new_equality of
	  | Pi tp -> tp
	  | _ -> ([],new_equality,noPos)
    in
    let faVars       = freeVars new_equality in
    let new_equality = mkBind (Forall, faVars, new_equality) in
    let eqltyWithPos = withAnnT (new_equality, termAnn term) in
    [if srt_vars = [] then eqltyWithPos
      else Pi(srt_vars,eqltyWithPos,piPos)]

(*    if functionType? (spc, srt)
      then
	(case (curryShapeNum (spc, srt), typeArity (spc, srt))
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


  op axiomFromOpTop: Spec * QualifiedId * OpInfo -> SpecElements
  def axiomFromOpTop (spc, qid, info) =
    axiomFromOpDefTop (spc, qid, info) ++ 
    axiomFromOpSrtTop (spc, qid, info)

  op axiomFromOpDefTop: Spec * QualifiedId * OpInfo -> SpecElements
  def axiomFromOpDefTop (spc, qid as Qualified(q,id), info) =
    case opInfoDefs info of
      | [] -> []
      | defs ->
        %% new: fold over all defs (but presumably just one for now)
        foldl (fn (props, dfn) ->
	       let (tvs, srt, term) = unpackFirstTerm dfn in
	       let pos = termAnn term in
	       let initialFmla = head (unLambdaDef (spc, srt, qid, term)) in
	       %let unTupledFmlas = foldRecordFmla (spc, srt, initialFmla) in
	       %let unTupleAxioms = map (fn fmla -> (Axiom, mkQualifiedId (q, id^"_def"), [], withAnnT (fmla, pos))) unTupledFmlas in
	       let unTupleAxioms = [] in
	       %let _ = if true && id = "p" then writeLine ("initialFmla: "^printTerm initialFmla) else () in
	       %let _ = if true && id = "length_Object$1$_$Object$2" then debug ("initialFmla: "^printTerm initialFmla) else () in
	       let liftedFmlas = removePatternTop(spc, initialFmla) in
	       %let simplifiedLiftedFmlas = map (fn fmla -> simplify spc fmla) liftedFmlas in
	       %let _ = if id = "p" then map (fn lf -> writeLine ("LiftedAxioms: " ^ printTerm lf)) liftedFmlas else [] in
	       let defAxioms = map (fn (fmla:MSTerm) ->
				    Property(Axiom, mkQualifiedId (q, id^"_def"), [], withAnnT (fmla, pos), pos))
	                         liftedFmlas
	       in
	       %%let ax:Property = (Axiom, id^"_def", [], hd (unLambdaDef (spc, srt, qid, term))) in
	       %let _ = writeLine (id^": in axiomFromOpDef Def part") in
	       props ++ defAxioms ++ unTupleAxioms)
	      []
	      defs

   op axiomFromOpSrtTop: Spec * QualifiedId * OpInfo -> SpecElements
  def axiomFromOpSrtTop (spc, qid as Qualified(q,id), info) =
    let srt = firstOpDefInnerType info in
    if true then   %localOp? (qid, spc) then
      let pos = typeAnn srt in
      let subTypeFmla = opSubtypeAxiom (spc, qid, srt) in
      let liftedFmlas = removePatternTop(spc, subTypeFmla) in
      let subTypeAxioms =
          map (fn (fmla : MSTerm) -> 
	       Property(Axiom, 
			mkQualifiedId (q, id^"_def_subtype"), 
			[], 
			withAnnT (fmla, pos), pos)) 
	      liftedFmlas 
      in
	%(Axiom, mkQualifiedId (q, id^"_def"), [], withAnnT (subTypeFmla, pos)) in
	subTypeAxioms
    else 
      %let _ = writeLine (id^": in axiomFromOpDef Def part is not local") in
      %let _ = debug "not local op" in
      []


  op foldRecordFmla: Spec * MSType * MSTerm -> MSTerms
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

  op substituteInRHSEquality: MSTerm * MSVarSubst -> MSTerm
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

  op mkSubstProjForVar: MSVars * MSProductFields * MSType * MSVar -> MSVarSubst
  def mkSubstProjForVar (vars, fields, recSrt as Base (type_qid as Qualified (_, type_id), _,  _), recVar) =
    let
      def mkSubstProjForVarRec (vars, fields) =
	case (vars, fields) of
	  | ([], []) -> []
          | (hdVar::restVars, (field_id, fieldSrt) :: restFields) ->
	    let restSubst = mkSubstProjForVarRec (restVars, restFields) in
            let proj_id   = getAccessorOpName (type_id, type_qid, field_id) in
	    let funTerm   = Fun (Op (proj_id, Nonfix), 
				 Arrow (recSrt, fieldSrt, noPos), 
				 noPos) 
	    in
	    let term = Apply (funTerm, Var (recVar, noPos), noPos) in
	    Cons ((hdVar, term), restSubst) 
    in
      mkSubstProjForVarRec (vars, fields)

  op axiomFromPropTop: Spec * Property -> SpecElements
  def axiomFromPropTop(spc, prop) =
    let (pt, pn, tv, fmla,pos) = prop in
    let pos = termAnn(fmla) in
    let newFmlas = removePatternTop(spc, fmla) in
    let newProps = map (fn f -> Property(pt, pn, tv, f, pos)) newFmlas in
    newProps

endspec
