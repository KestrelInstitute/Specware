% synchronized with version 1.4 of SW4/Languages/MetaSlang/TypeChecker/PosSpecToSpec.sl

PosSpecToSpec qualifying
spec {
 %%  convert pos terms to standard terms

 import ../PosSpec
 import ../StandardSpec

 %   . deletes position information
 %   . TODO: inserts default branches in patterns

 op convertPosSpecToSpec: PosSpec -> Spec
% op convertPTermToTerm                       : MetaTyVarsContext -> PTerm           -> Term
% op convertPVarToVar                         : MetaTyVarsContext -> PVar            -> Var
% op convertPSortToSort                       : MetaTyVarsContext -> PSort           -> Sort 
% op convertOptionalPSortToOptionalSort       : MetaTyVarsContext -> Option PSort    -> Option Sort
% op convertPPatternToPattern                 : MetaTyVarsContext -> PPattern        -> Pattern 
% op convertOptionalPPatternToOptionalPattern : MetaTyVarsContext -> Option PPattern -> Option Pattern
% op convertPFunToFun                         :                      PFun            -> Fun 
% op convertMetaTyVarToTyVar                  : MetaTyVarsContext -> PMetaTyVar      -> TyVar 
% op convertMetaTyVarsToTyVars                : MetaTyVarsContext -> PMetaTyVars     -> TyVars 
% op convertPSortSchemeToSortScheme           :                      PSortScheme     -> SortScheme

 def convertPosSpecToSpec spc =
   let context = initializeMetaTyVars() in
   let
     def convertPTerm term =
           case term of
	     | ApplyN([t1,t2],pos) -> Apply(t1,t2,pos)
	     | ApplyN (t1::t2::terms,pos) -> 
	       convertPTerm (ApplyN([t1,ApplyN(cons(t2,terms),pos)],pos))
	     | Fun (f,s,pos) -> Fun(convertPFun f,s,pos)
	     | _ -> term
     def convertPSort srt =
           case srt of
	     | MetaTyVar(tv,pos) -> 
	       let {name,uniqueId,link} = ! tv in
	       (case link
		  of None -> TyVar (findTyVar(context,uniqueId),pos)
		   | Some ssrt -> convertPSort ssrt)
	     | _ -> srt
     def convertPFun (f) = 
           case f
	     of PQuotient equiv  -> Quotient 
	      | PChoose equiv    -> Choose
	      | PRestrict pred   -> Restrict
	      | PRelax pred      -> Relax
	      | OneName(n,fxty)  -> Op(Qualified(UnQualified,n), fxty)
	      | TwoNames(qn,n,fxty) -> Op(Qualified(qn,n), fxty)
	      | _ -> f
   in
%% mapSpec is correct but unnecessarily maps non-locals
%   mapSpec (convertPTerm, convertPSort, fn x -> x)
%     spc
  let {importInfo, sorts, ops, properties} = spc in
  let {imports = _, importedSpec = _, localOps, localSorts} = importInfo in
  let tsp_maps = (convertPTerm, convertPSort, fn x -> x) in
  { importInfo       = importInfo,

    ops              = mapAQualifierMap 
			(fn opinfo as (aliases, fixity, (tvs, srt), opt_def) ->
			 let nm = hd aliases in
			 if member(nm,localOps)
			   then
			    (aliases, fixity, (tvs, mapSort tsp_maps srt), 
			     mapTermOpt tsp_maps opt_def)
			   else opinfo)
			ops,

    sorts            = mapAQualifierMap 
			 (fn sortinfo as (aliases, tvs, opt_def) ->
			  let nm = hd aliases in
			 if member(nm,localSorts)
			   then (aliases, tvs, mapSortOpt tsp_maps opt_def)
			   else sortinfo)
			 sorts,

    properties       = map (fn (pt, nm, tvs, term) -> 
			       (pt, nm, tvs, mapTerm tsp_maps term))
			   properties
   }

% def convertPosSpecToSpec {importInfo, sorts, ops, properties} =
%    let new_ops  = 
%        StringMap.map
%	  (fn m ->
%	   StringMap.map
%	     (fn (old_op_names, 
%		  old_fixity, 
%		  (old_tyVars, old_srt), 
%		  old_opt_def : Option(PTerm))
%	      ->
%		let context = initializeMetaTyVars() in
%		%let tyVars = convertMetaTyVarsToTyVars context (tyVars) in
%		let new_srt = convertPSortToSort context  old_srt in
%		let new_opt_def : Option(Term) = 
%		(case old_opt_def
%		   of None      -> None
%		    | Some term -> Some(convertPTermToTerm context term))
%		in
%		  (old_op_names, old_fixity, (old_tyVars, new_srt), new_opt_def))
%	   m)
%	  ops
%    in
%    let new_sorts = 
%        StringMap.map
%	  (fn m ->
%	   StringMap.map
%	     (fn (old_sort_names, 
%		  old_tyVars, 
%		  old_opt_def : Option(PSort))
%	      ->
%		let context = initializeMetaTyVars() in
%		%let tyVars = convertMetaTyVarsToTyVars context tyVars in
%		let new_opt_def : Option(Sort) = 
%		(case old_opt_def 
%		   of None     -> None 
%		    | Some srt -> Some(convertPSortToSort context srt))
%		in
%		  (old_sort_names, old_tyVars, new_opt_def)) 
%	   m)
%	  sorts
%    in
%    let new_properties = 
%        List.map (fn (pt, name, tyVars, term) -> 
%		  let context = initializeMetaTyVars() in
%		  (pt, name, tyVars, convertPTermToTerm context term)) 
%	         properties 
%    in
%    {importInfo       = importInfo,
%     sorts            = new_sorts,
%     ops              = new_ops,
%     properties       = new_properties}

% def deleteTerm(term:PTerm) : Term = 
%     convertPTermToTerm (initializeMetaTyVars()) term

% def deleteSort(srt:PSort) : Sort = 
%     convertPSortToSort (initializeMetaTyVars()) srt

% def convertPSortSchemeToSortScheme (tyVars, srt : PSort) : List(TyVar) * Sort = 
%  % Not sure if this can do anything useful other than translate to MetaSlang 
%  let context = initializeMetaTyVars() in
%  % let tyVars = convertMetaTyVarsToTyVars context mTyVars in
%  let srt = convertPSortToSort context srt in
%  (tyVars,srt)

% def deletePattern(pat:PPattern) : Pattern = 
%     convertPPatternToPattern (initializeMetaTyVars()) pat

% def convertPTermToTerm context (term:PTerm) : Term = 
%     case term	
%       of ApplyN([t1,t2],_) -> 
%	  Apply(convertPTermToTerm context t1,convertPTermToTerm context t2,noPos)
%	| Record(fields,_) -> 
%	  Record(List.map (fn(id,t)-> (id,convertPTermToTerm context t)) fields,noPos)
%	| Bind(bd,vars,term,_) -> 
%	  Bind(bd,List.map (convertPVarToVar context) vars,
%	       convertPTermToTerm context term,noPos)
%	| Let(decls,body,_) -> 
%	  Let(List.map (fn (p,t) -> (convertPPatternToPattern context  p,
%				     convertPTermToTerm context t))
%	      decls,convertPTermToTerm context body,noPos)  
%	| LetRec(decls,body,_) -> 
%	  LetRec(List.map (fn(v,t)-> (convertPVarToVar context v,
%				      convertPTermToTerm context t)) decls,
%		 convertPTermToTerm context body,noPos)
%	| Var(v,_) -> Var(convertPVarToVar context v,noPos)
%	| SortedTerm(term,_,_) -> convertPTermToTerm context(term)
%	| Fun (f,s,_) -> Fun(convertPFunToFun f,convertPSortToSort context s,noPos)
%  % Insert default branches here.
%	| Lambda(match,_) -> 
%	  let match = 
%	      List.map 
%	      (fn(p,t1,t2)-> (convertPPatternToPattern context  p,
%			      convertPTermToTerm context t1,
%			      convertPTermToTerm context t2)) 
%	      match
%	  in
%	  Lambda(match,noPos)
%	| IfThenElse(t1,t2,t3,_) -> 
%	  IfThenElse(convertPTermToTerm context t1,convertPTermToTerm context t2,
%		     convertPTermToTerm context t3,noPos)
%	| Seq(terms,_) -> 
%	  Seq(List.map (convertPTermToTerm context) terms,noPos)
%	| ApplyN (t1::t2::terms,pos) -> 
%	  convertPTermToTerm context (ApplyN([t1,ApplyN(cons(t2,terms),pos)],pos))
%	| x -> x  %System.fail (System.toString x)

% def convertPVarToVar context (id,srt) = (id,convertPSortToSort context srt)
% def convertPSortToSort (context: MetaTyVarsContext) (srt:PSort):Sort = 
%     case srt
%       of Arrow(s1,s2,_) -> Arrow(convertPSortToSort context s1,
%				  convertPSortToSort context s2, noPos)
%	| Product(fields,_) -> 
%	  Product (List.map (fn(id,s) -> (id,convertPSortToSort context  s)) fields,
%		   noPos)
%	| CoProduct(fields,_) -> 
%	  CoProduct(List.map (fn(id,s) ->
%			       (id,convertOptionalPSortToOptionalSort context s))
%		    fields,noPos)
%	| Quotient(s,t,_) -> 
%	  Quotient(convertPSortToSort context s,convertPTermToTerm context t,noPos)
%	| Subsort(s,t,_) -> 
%	  Subsort(convertPSortToSort context s,convertPTermToTerm context t,noPos)
%	| Base(qid,srts,_) -> 
%	  Base(qid,List.map (convertPSortToSort context) srts,noPos)
%	| TyVar(tv,_) -> TyVar(tv,noPos)
%	| MetaTyVar(tv,_) -> 
%	  let {name,uniqueId,link} = ! tv in
%	  (case link
%	     of None -> TyVar (findTyVar(context,uniqueId),noPos)
%	      | Some srt -> convertPSortToSort context (srt))

% def convertOptionalPSortToOptionalSort context srt = 
%     case srt
%       of None -> None
%	| Some s -> Some(convertPSortToSort context  s)

% def convertPPatternToPattern (context: MetaTyVarsContext) (pat:PPattern):Pattern = 
%     case pat of
%	| StringPat   (s,               _) -> StringPat   (s,  noPos)
%	| BoolPat     (b,               _) -> BoolPat     (b,  noPos)
%	| CharPat     (c,               _) -> CharPat     (c,  noPos)
%	| NatPat      (c,               _) -> NatPat      (c,  noPos)

%	| VarPat      (v,               _) -> VarPat      (convertPVarToVar context v,          noPos)
%	| WildPat     (srt,             _) -> WildPat     (convertPSortToSort context srt,  noPos)

%        | AliasPat    (p1, p2,          _) -> AliasPat    (convertPPatternToPattern context p1,
%                                                           convertPPatternToPattern context p2, 
%                                                           noPos)
%	| EmbedPat    (id, patopt, srt, _) -> EmbedPat    (id,    
%                                                           convertOptionalPPatternToOptionalPattern context patopt,
%                                                           convertPSortToSort context  srt,
%                                                          noPos)
%	| RecordPat   (fields,          _) -> RecordPat   (List.map (fn(id,p)-> (id,convertPPatternToPattern context  p)) fields,
%                                                           noPos)
%	| RelaxPat    (p, t,            _) -> RelaxPat    (convertPPatternToPattern context p,
%	                                                   convertPTermToTerm context t,
%							   noPos)
%	| QuotientPat (p, t,            _) -> QuotientPat (convertPPatternToPattern context  p,
%                                                           convertPTermToTerm context t,
%							   noPos)
%	| SortedPat   (p, _,            _) -> convertPPatternToPattern context p

% def convertOptionalPPatternToOptionalPattern (context: MetaTyVarsContext)
%		  (popt:Option(PPattern)):Option(Pattern) = 
%     case popt
%       of None -> None
%	| Some p -> Some(convertPPatternToPattern context p)

% def convertPFunToFun (f : PFun): Fun = 
%     case f
%       of Equals           -> Equals
%	| PQuotient equiv  -> Quotient 
%	| PChoose equiv    -> Choose
%	| PRestrict pred   -> Restrict
%	| PRelax pred      -> Relax
%	| Project id       -> Project id
%	| Embed x          -> Embed x
%	| Embedded x       -> Embedded x
%	| Nat x            -> Nat x
%	| String x         -> String x
%	| Char x           -> Char x
%	| Bool x           -> Bool x
%	| OneName(n,fxty)  -> Op(Qualified(UnQualified,n), fxty)
%	| TwoNames(qn,n,fxty) -> Op(Qualified(qn,n), fxty)
%	| Op x             -> Op x
%	%% Not sure about these cases, but have to do something
%	| Quotient         -> Quotient 
%	| Choose           -> Choose
%	| Restrict         -> Restrict
%	| Relax            -> Relax


% def convertMetaTyVarToTyVar (context: MetaTyVarsContext) (mTyVar : PMetaTyVar) : TyVar = 
%  let {name,uniqueId,link} = ! mTyVar in 
%  case link of
%   | Some (MetaTyVar (mtv,_)) -> convertMetaTyVarToTyVar context mtv
%   | Some srt                 -> findTyVar (context, uniqueId) %System.fail "Unexpected sort linked to type variable"
%   | None                     -> findTyVar (context, uniqueId)

% def convertMetaTyVarsToTyVars context (mTyVars: PMetaTyVars) : TyVars = 
%     List.map (convertMetaTyVarToTyVar context) mTyVars
}
