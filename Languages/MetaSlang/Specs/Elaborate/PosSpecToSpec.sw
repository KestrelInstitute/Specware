% synchronized with version 1.4 of SW4/Languages/MetaSlang/TypeChecker/PosSpecToSpec.sl

% PosSpecToSpec qualifying
spec {
 %%  convert pos terms to standard terms

 import ../PosSpec
 import ../StandardSpec

 %   . deletes position information
 %   . TODO: inserts default branches in patterns

 op convertPosSpecToSpec                     :                      PosSpec         -> Spec
 op convertPTermToTerm                       : MetaTyVarsContext -> PTerm           -> Term
 op convertPVarToVar                         : MetaTyVarsContext -> PVar            -> Var
 op convertPSortToSort                       : MetaTyVarsContext -> PSort           -> Sort 
 op convertOptionalPSortToOptionalSort       : MetaTyVarsContext -> Option PSort    -> Option Sort
 op convertPPatternToPattern                 : MetaTyVarsContext -> PPattern        -> Pattern 
 op convertOptionalPPatternToOptionalPattern : MetaTyVarsContext -> Option PPattern -> Option Pattern
 op convertPFunToFun                         :                      PFun            -> Fun 
 op convertMetaTyVarToTyVar                  : MetaTyVarsContext -> PMetaTyVar      -> TyVar 
 op convertMetaTyVarsToTyVars                : MetaTyVarsContext -> PMetaTyVars     -> TyVars 
 op convertPSortSchemeToSortScheme           :                      PSortScheme     -> SortScheme

 def convertPosSpecToSpec {importInfo, sorts, ops, properties} =
    let new_ops  = 
        StringMap.map
	  (fn m ->
	   StringMap.map
	     (fn (old_op_names, 
		  old_fixity, 
		  (old_tyVars, old_srt), 
		  old_opt_def : Option(PTerm))
	      ->
		let context = initializeMetaTyVars() in
		%let tyVars = convertMetaTyVarsToTyVars context (tyVars) in
		let new_srt = convertPSortToSort context  old_srt in
		let new_opt_def : Option(Term) = 
		(case old_opt_def
		   of None      -> None
		    | Some term -> Some(convertPTermToTerm context term))
		in
		  (old_op_names, old_fixity, (old_tyVars, new_srt), new_opt_def))
	   m)
	  ops
    in
    let new_sorts = 
        StringMap.map
	  (fn m ->
	   StringMap.map
	     (fn (old_sort_names, 
		  old_tyVars, 
		  old_opt_def : Option(PSort))
	      ->
		let context = initializeMetaTyVars() in
		%let tyVars = convertMetaTyVarsToTyVars context tyVars in
		let new_opt_def : Option(Sort) = 
		(case old_opt_def 
		   of None     -> None 
		    | Some srt -> Some(convertPSortToSort context srt))
		in
		  (old_sort_names, old_tyVars, new_opt_def)) 
	   m)
	  sorts
    in
    let new_properties = 
        List.map (fn (pt, name, tyVars, term) -> 
		  let context = initializeMetaTyVars() in
		  (pt, name, tyVars, convertPTermToTerm context term)) 
	         properties 
    in
    {importInfo       = importInfo,
     sorts            = new_sorts,
     ops              = new_ops,
     properties       = new_properties}

 def deleteTerm(term:PTerm) : Term = 
     convertPTermToTerm (initializeMetaTyVars()) term

 def deleteSort(srt:PSort) : Sort = 
     convertPSortToSort (initializeMetaTyVars()) srt

 def convertPSortSchemeToSortScheme (tyVars, srt : PSort) : List(TyVar) * Sort = 
  % Not sure if this can do anything useful other than translate to MetaSlang 
  let context = initializeMetaTyVars() in
  % let tyVars = convertMetaTyVarsToTyVars context mTyVars in
  let srt = convertPSortToSort context srt in
  (tyVars,srt)

 def deletePattern(pat:PPattern) : Pattern = 
     convertPPatternToPattern (initializeMetaTyVars()) pat

 def convertPTermToTerm context (term:PTerm) : Term = 
     case term	
       of ApplyN([t1,t2],_) -> 
	  Apply(convertPTermToTerm context t1,convertPTermToTerm context t2,())
	| Record(fields,_) -> 
	  Record(List.map (fn(id,t)-> (id,convertPTermToTerm context t)) fields,())
	| Bind(bd,vars,term,_) -> 
	  Bind(bd,List.map (convertPVarToVar context) vars,
	       convertPTermToTerm context term,())
	| Let(decls,body,_) -> 
	  Let(List.map (fn (p,t) -> (convertPPatternToPattern context  p,
				     convertPTermToTerm context t))
	      decls,convertPTermToTerm context body,())  
	| LetRec(decls,body,_) -> 
	  LetRec(List.map (fn(v,t)-> (convertPVarToVar context v,
				      convertPTermToTerm context t)) decls,
		 convertPTermToTerm context body,())
	| Var(v,_) -> Var(convertPVarToVar context v,())
	| SortedTerm(term,_,_) -> convertPTermToTerm context(term)
	| Fun (f,s,_) -> Fun(convertPFunToFun f,convertPSortToSort context s,())
  % Insert default branches here.
	| Lambda(match,_) -> 
	  let match = 
	      List.map 
	      (fn(p,t1,t2)-> (convertPPatternToPattern context  p,
			      convertPTermToTerm context t1,
			      convertPTermToTerm context t2)) 
	      match
	  in
	  Lambda(match,())
	| IfThenElse(t1,t2,t3,_) -> 
	  IfThenElse(convertPTermToTerm context t1,convertPTermToTerm context t2,
		     convertPTermToTerm context t3,())
	| Seq(terms,_) -> 
	  Seq(List.map (convertPTermToTerm context) terms,())
	| ApplyN (t1::t2::terms,pos) -> 
	  convertPTermToTerm context (ApplyN([t1,ApplyN(cons(t2,terms),pos)],pos))
	| x -> System.fail (System.toString x)

 def convertPVarToVar context (id,srt) = (id,convertPSortToSort context srt)
 def convertPSortToSort (context: MetaTyVarsContext) (srt:PSort):Sort = 
     case srt
       of Arrow(s1,s2,_) -> Arrow(convertPSortToSort context s1,
				  convertPSortToSort context s2, ())
	| Product(fields,_) -> 
	  Product (List.map (fn(id,s) -> (id,convertPSortToSort context  s)) fields,
		   ())
	| CoProduct(fields,_) -> 
	  CoProduct(List.map (fn(id,s) ->
			       (id,convertOptionalPSortToOptionalSort context s))
		    fields,())
	| Quotient(s,t,_) -> 
	  Quotient(convertPSortToSort context s,convertPTermToTerm context t,())
	| Subsort(s,t,_) -> 
	  Subsort(convertPSortToSort context s,convertPTermToTerm context t,())
	| PBase(qid,srts,_) -> 
	  Base(qid,List.map (convertPSortToSort context) srts,())
	| TyVar(tv,_) -> TyVar(tv,())
	| MetaTyVar(tv,_) -> 
	  let {name,uniqueId,link} = ! tv in
	  (case link
	     of None -> TyVar (findTyVar(context,uniqueId),())
	      | Some srt -> convertPSortToSort context (srt))

 def convertOptionalPSortToOptionalSort context srt = 
     case srt
       of None -> None
	| Some s -> Some(convertPSortToSort context  s)

 def convertPPatternToPattern (context: MetaTyVarsContext) (pat:PPattern):Pattern = 
     case pat of
	| StringPat   (s,               _) -> StringPat   (s,  ())
	| BoolPat     (b,               _) -> BoolPat     (b,  ())
	| CharPat     (c,               _) -> CharPat     (c,  ())
	| NatPat      (c,               _) -> NatPat      (c,  ())

	| VarPat      (v,               _) -> VarPat      (convertPVarToVar context v,          ())
	| WildPat     (srt,             _) -> WildPat     (convertPSortToSort context srt,  ())

        | AliasPat    (p1, p2,          _) -> AliasPat    (convertPPatternToPattern context p1,
                                                           convertPPatternToPattern context p2, 
                                                           ())
	| EmbedPat    (id, patopt, srt, _) -> EmbedPat    (id,    
                                                           convertOptionalPPatternToOptionalPattern context patopt,
                                                           convertPSortToSort context  srt,
                                                          ())
	| RecordPat   (fields,          _) -> RecordPat   (List.map (fn(id,p)-> (id,convertPPatternToPattern context  p)) fields,
                                                           ())
	| RelaxPat    (p, t,            _) -> RelaxPat    (convertPPatternToPattern context p,
	                                                   convertPTermToTerm context t,
							   ())
	| QuotientPat (p, t,            _) -> QuotientPat (convertPPatternToPattern context  p,
                                                           convertPTermToTerm context t,
							   ())
	| SortedPat   (p, _,            _) -> convertPPatternToPattern context p

 def convertOptionalPPatternToOptionalPattern (context: MetaTyVarsContext)
		  (popt:Option(PPattern)):Option(Pattern) = 
     case popt
       of None -> None
	| Some p -> Some(convertPPatternToPattern context p)

 def convertPFunToFun (f : PFun): Fun = 
     case f
       of Equals           -> Equals
	| PQuotient equiv  -> Quotient 
	| PChoose equiv    -> Choose
	| PRestrict pred   -> Restrict
	| PRelax pred      -> Relax
	| Project id       -> Project id
	| Embed x          -> Embed x
	| Embedded x       -> Embedded x
	| Nat x            -> Nat x
	| String x         -> String x
	| Char x           -> Char x
	| Bool x           -> Bool x
	| OneName(n,fxty)  -> Op(Qualified(UnQualified,n), fxty)
	| TwoNames(qn,n,fxty) -> Op(Qualified(qn,n), fxty)
	| Op x             -> Op x


 def convertMetaTyVarToTyVar (context: MetaTyVarsContext) (mTyVar : PMetaTyVar) : TyVar = 
  let {name,uniqueId,link} = ! mTyVar in 
  case link of
   | Some (MetaTyVar (mtv,_)) -> convertMetaTyVarToTyVar context mtv
   | Some srt                 -> findTyVar (context, uniqueId) %System.fail "Unexpected sort linked to type variable"
   | None                     -> findTyVar (context, uniqueId)

 def convertMetaTyVarsToTyVars context (mTyVars: PMetaTyVars) : TyVars = 
     List.map (convertMetaTyVarToTyVar context) mTyVars
}
