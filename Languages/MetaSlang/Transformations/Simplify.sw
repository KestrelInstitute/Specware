%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

(*
 *  Simplify term with respect to simple optimizations.
 *  Assume that all variables occur uniquely, that is, 
 *  they have unique names.

    These are very ad hoc simplifications and should be accomodated more systematically.


    Var to var definitions:
	let x = y in e 			

		is simplified to e[y/x]

    Restrict(var) to var definitions:

	let x = restrict(y) in e 	

		is simplified to e[restrict(y)/x]

----------- New ---------------------

    Dead code elimination:

	let x = e in e'			

		is simplified to e' if x is not free in e' and e does not have effects.

    Tuple instantiation:

	let z = (x,y) in [... e[project(1)z,project(2)(z)] ...]		
					

		is simplified to 

	let x_1 = x in 
	let y_1 = y in 
	let z = (x_1,y_1) in [ ... e[x_1,y_1] ...]


    Single threaded in-lining

	let x = e in e'[x]		

		is simplified to e'[e] if x occurs only once and does not have side effects.



  rewrite1: rewrite(`let ^(Varpat x) = ^(Var y) in z`, mapTerm(replace,Id,Id) `z`)
  rewrite2: rewrite(`let ....`)  



 *)

Simplify qualifying
spec
 import ../Specs/Environment
 import ../Specs/Utilities
 sort Term = MS.Term

 op  sideEffectFree: MS.Term -> Boolean
 def sideEffectFree(term) = 
     case term
       of Var _ -> true
	| Record(fields,_) -> List.all (fn(_,t)-> sideEffectFree t) fields
	| Apply(Fun(Embed _,_,_),t,_) -> sideEffectFree t
	| Fun _ -> true
	| IfThenElse(t1,t2,t3,_) -> 
		(sideEffectFree t1) 
	      & (sideEffectFree t2) 
	      & (sideEffectFree t3)
	| _ -> false 

 op  countVarRefs: MS.Term * Var -> Nat
 def countVarRefs(term,id) =
   let occ = Ref 0 : Ref Nat in
   let
     def occurs(term) = 
       case term
	 of Var (id2,_) -> 
	   (occ := (! occ) + (if id = id2 then 1 else 0); term)
	  | _ -> term
   in
     let _ = mapSubTerms occurs term in
     ! occ

 op  removeUnnecessaryVariable: Spec -> MS.Term -> MS.Term
 def removeUnnecessaryVariable spc term =
     case term
       of Let([(VarPat (id,_),e)],body,_) ->
	  let noSideEffects =  sideEffectFree(e) in
	  (case countVarRefs(body,id)
	     of 0 -> if noSideEffects then body else term
	      | 1 -> if noSideEffects
	                 or noInterveningSideEffectsBefore?
			      (body,fn (Var (id2,_)) -> id = id2
			             | _ -> false)
	               then simplifyOne spc (substitute(body,[(id,e)]))
		       else term
	      | _ -> term)
	| _ -> term

  op noInterveningSideEffectsBefore?: MS.Term * (MS.Term -> Boolean) -> Boolean 
  def noInterveningSideEffectsBefore?(tm,p) =
    %% examine terms in execution order until either p is true or a possibly side-effection
    %% term is encountered
    let result =
        foldSubTermsEvalOrder
          (fn (t,result as (noSideEffectsYet?,done?)) ->
	     if done? then result
	     else if p t then (true,true)
	     else
	     case t of
	       | Apply(Fun(Embed _,_,_),_,_) -> result
	       % case
	       | Apply(Lambda _,_,_) -> result
	       %% We don't know in general when an application can cause a side-effect 
	       | Apply(Fun (f,_,_),_,_) ->
	         if knownSideEffectFreeFn? f then result else (false,true)
	       %% We don't know when the body of a lambda will be evaluated
	       | Lambda _ -> (false,true)
	       | _ -> result)
	  (true,false)
	  tm
    in result.1

  op  knownSideEffectFreeQIds: List(Qualifier * Id)
  def knownSideEffectFreeQIds =
    [("Integer", "~"),  % TODO: deprecate
     ("Integer_","-"),
     ("Integer","+"),
     ("Integer","<"),
     ("Integer",">"),
     ("Integer","<="),
     ("Integer",">="),
     ("Integer","-"),
     ("Integer","div"),
     ("Integer","rem"),
     ("Integer","abs"),
     ("Integer","min"),
     ("Integer","max"),
     ("Integer","compare"),
     ("List","length")]

  op  knownSideEffectFreeFn?: Fun -> Boolean
  def knownSideEffectFreeFn? f =
    case f of
      | Op(Qualified(qid),_) ->
        member(qid,knownSideEffectFreeQIds)
      % Not, And, Or, Implies, Iff, Equals, NotEquals -> true
      | _ -> true
      

% We implement a version of tuple instantiation that works on terms after pattern 
% matching compilation such that all references to let (u,v) = z in .. are of the
% form let u = project(1) z, v = project(2) z in ..
%
 op  tupleInstantiate: Spec -> MS.Term -> MS.Term
 def tupleInstantiate spc (term) = 
     let
	def elimTuple(zId,srt,fields,body) =
	  let
	      def mkField(id,srt) = 
		  let name = zId^"_field"^id in
	 	  let v = (name,srt) in
		  (v,mkVar v)
	  in
	  let varFields = 
	      case productOpt(spc,srt)
		of Some fields -> map mkField fields 
		 | _ -> fail ("Product sort expected for let bound variable. Found "^printSort srt)
	  in
	  let allFields = ListPair.zip(fields,varFields) in
	  let
	     def findField(id,fields) = 
		 case fields
		   of [] -> System.fail ("Field identifier "^id^" was not found")
		    | ((id2,_),(v,vTerm))::fields -> 
		      if id = id2 then vTerm else findField(id,fields)
	  in
	  let
	     def substField(term) = 
		 case term
		   of Apply(Fun(Project id,_,_),Var((zzId,_),_),_) -> 
		      if zId = zzId
			 then findField(id,allFields)
		      else term
		    | _ -> term
	  in
	  let varDecls = List.map (fn((id,t),(v,vTerm))-> (mkVarPat v,t)) allFields in
	  let zDecl    = (mkVarPat(zId,srt),
			  mkRecord(List.map (fn((id,_),(_,vTerm))-> (id,vTerm)) allFields)) 
	  in
	  let newBody = mapSubTerms substField body in
	  let newTerm = removeUnnecessaryVariable spc (mkLet([zDecl],newBody))  in
	  mkLet(varDecls,newTerm)
     in
     case term
       of Let([((VarPat((zId,srt),_)),Record(fields,_))],body,_) -> 
	  elimTuple(zId,srt,fields,body)
	| Let([(VarPat((zId,srt),_),
		Apply(Fun(Op(Qualified("TranslationBuiltIn","mkTuple"),_),_,_),
		      Record(fields,_),_))],body,_) -> 
	  elimTuple(zId,srt,fields,body)
	| _ -> removeUnnecessaryVariable spc (term)

 op  simplifyOne: Spec -> MS.Term -> MS.Term
 def simplifyOne spc term =
     case tryEvalOne term of
       | Some cterm -> cterm
       | _ ->
     case term
       of Let(decl1::decl2::decls,body,_) -> 
	  simplifyOne spc (mkLet([decl1],simplifyOne spc (mkLet(List.cons(decl2,decls),body))))
	%% let y = x in f y  --> f x
	| Let([(VarPat(v,_),wVar as (Var(w,_)))],body,_) ->
	  substitute(body,[(v,wVar)])
	%% Do equivalent for apply lambda
	%% case y of x -> f x  -->  f y
	| Apply(Lambda([(VarPat(v,_),_,body)],_),wVar as (Var(w,_)),_) ->
	  substitute(body,[(v,wVar)])
	%% case y of _ -> z  -->  z if y side-effect free
	| Apply(Lambda([(WildPat(_,_),_,body)],_),tm,_) ->
	  if sideEffectFree tm then body else term
	| Let([(VarPat(v,_),letTerm as (Apply(Fun(Restrict,_,_),(Var _),_)))],
	      body,_) ->
	  substitute(body,[(v,letTerm)]) 
	%% Distribution of terms over application
	%% (if p then x else y) z --> if p then x z else y z
	| Apply(IfThenElse(t1,t2,t3,a),tm,_) ->
	  if simpleTerm? tm
	    then IfThenElse(t1,simplifiedApply(t2,tm,spc),simplifiedApply(t3,tm,spc),a)
	    else term
	%% (let x = y in f) z --> let x = y in f z
	| Apply(Let(binds,body,a),tm,_) ->
	  if simpleTerm? tm
	    then Let(binds,simplifiedApply(body,tm,spc),a)
	    else term
	%% (letrec x = y in f) z --> let x = y in f z
	| Apply(LetRec(binds,body,a),tm,_) ->
	  if simpleTerm? tm
	    then LetRec(binds,simplifiedApply(body,tm,spc),a)
	    else term
	%% (case x of p1 -> e1 p2 -> e2 ...) z  --> case x of p1 -> e1 z p2 -> e2 .z ..
	| Apply(Apply(Lambda(cases,a1),x,a2),tm,_) ->
	  if simpleTerm? tm
	    then Apply(Lambda(map (fn (p,pred,ei) -> (p,pred,simplifiedApply(ei,tm,spc))) cases,a1),
		       x,a2)
	    else term	%% let y = <exp> in f y  --> f <exp> where y occurs once in f and no side-effects
%	| Let([(VarPat((id,_),_),tm)],body,_) -> 
%	  let
%	     def replace(term) = 
%		 case term
%		   of (Var((id2,_),_)) -> if id = id2 then wVar else term 
%		    | _ -> term
%	  in
%	     mapTerm(replace,fn x -> x,fn p -> p) body
	%% Quantification simplification
	%% fa(x,y) x = a & p(x,y) => q(x,y) --> fa(x,y) p(a,y) => q(a,y)
	| Bind(Forall,_,_,_) -> simplifyForall spc (forallComponents term)
        | Bind(Exists,_,_,_) -> simplifyExists(existsComponents term)
	| Apply(Fun(Project i,_,_),Record(m,_),_) ->
	  (case getField(m,i) of
	    | Some fld -> fld
	    | None -> term)
	| _ -> case simplifyCase spc term of
	        | Some tm -> tm
	        | None -> tupleInstantiate spc term

  op  simplifyForall: Spec -> List Var * List MS.Term * MS.Term -> MS.Term
  def simplifyForall spc (vs,cjs,bod) =
    case normForallBody (bod,varNamesSet(vs,Cons(bod,cjs)),spc) of
      | Some(new_vs,new_cjs,new_bod) ->
        simplifyForall spc (vs++new_vs,cjs++new_cjs,new_bod)
      | _ ->
    case find (fn cj ->
	        case bindEquality cj of
		 | None -> false
		 | Some(v,e) ->
		   (simpleTerm? e)
		   & (member(v,vs))
		   & ~(isFree(v,e)))
           cjs
      of Some cj ->
	 (case  bindEquality cj of
	    | Some (pr as (sv,_)) ->
	      let sbst = [pr] in
	      simplifyForall spc
	        (filter (fn v -> ~(v = sv)) vs,
		 mapPartial (fn c -> if cj = c then None
				     else Some(simpSubstitute(spc,c,sbst)))
		 cjs,
		 simpSubstitute(spc,bod,sbst)))
       | _ -> if exists (fn cj -> equalTerm?(cj,bod)) cjs
	       then mkTrue()
	       else
		 let simplCJs = foldr (fn (cj,new_cjs) -> simplifyConjunct(cj,spc) ++ new_cjs) [] cjs in
		 if simplCJs = cjs
		   then mkSimpBind(Forall,vs,mkSimpImplies(mkSimpConj cjs,bod))
		   else simplifyForall spc (vs,simplCJs,bod)

  op  simplifyConjunct: MS.Term * Spec -> List MS.Term 
  def simplifyConjunct (cj,spc) =
    case cj of
      | Apply(Fun(Equals,_,_),Record([("1",Record(lhs_flds,_)),("2",Record(rhs_flds,_))],_),_) ->
        map (fn ((_,lhs_e),(_,rhs_e)) -> mkEquality(inferType(spc,lhs_e),lhs_e,rhs_e))
	  (zip(lhs_flds,rhs_flds))
      | _ -> [cj]

  op  varNamesSet: List Var * List MS.Term -> StringSet.Set
  def varNamesSet(vs,tms) =
    foldl (fn ((nm,_),nm_set) -> StringSet.add(nm_set,nm))
      StringSet.empty
      (vs ++ foldl (fn (t,fvs) -> freeVars t ++ fvs) [] tms)
    

  op  normForallBody: MS.Term * StringSet.Set * Spec -> Option(List Var * List MS.Term * MS.Term)
  %% fa(x) p => let y = m in n --> fa(x,y) p & y = m => n
  def normForallBody(body,used_names,spc) =
    case body of
      | Let([(pat,val)],let_body,_) ->	% fa(x) p => let y = m in n --> fa(x,y) p & y = m => n
        (case patternToTerm pat of
	   | Some pat_tm ->
	     let new_vs = freeVars pat_tm in
	     let (unique_vs,sb) = getRenamingSubst(new_vs,used_names) in
	     if sb = []
	       then Some(unique_vs,[mkEquality(inferType(spc,pat_tm),pat_tm,val)],let_body)
	       else Some(unique_vs,[mkEquality(inferType(spc,pat_tm),substitute(pat_tm,sb),val)],
			 simpSubstitute(spc,let_body,sb))
	   | _ -> None)
      | _ -> None

  op  getRenamingSubst: List Var * StringSet.Set -> List Var * List (Var * MS.Term)
  def getRenamingSubst(vs,used_names) =
    foldr (fn (v as (nm,ty),(vs,sb)) ->
	   let new_nm = StringUtilities.freshName(nm,used_names) in
	   if nm = new_nm
	    then (Cons(v,vs),sb)
	    else let new_v = (new_nm,ty) in
	         (Cons(new_v,vs),Cons((v,mkVar new_v),sb)))
      ([],[]) vs

  op  simpSubstitute: Spec * MS.Term *  List (Var * MS.Term) -> MS.Term
  def simpSubstitute(spc,t,sbst) =
    let stm = substitute(t,sbst) in
    simplify spc stm

  op  bindEquality: MS.Term -> Option(Var * MS.Term)
  def bindEquality t =
    case t of
      | Apply(Fun(Equals,_,_),Record([(_,e1),(_,e2)], _),_) ->
        (case e1 of
	  | Var(v,_) -> Some(v,e2)
	  | _ ->
	 case e2 of
	  | Var(v,_) -> Some(v,e1)
	  | _ -> None)
      | _ -> None

  op  simplifyExists: List Var * List MS.Term -> MS.Term
  def simplifyExists(vs,cjs) =
    mkSimpBind(Exists,vs,mkSimpConj cjs)    

  def simplifyCase spc term =
    case term of
      %% case (a,b,c) of (x,y,z) -> g(x,y,z) -> g(a,b,c)
      | Apply(Lambda([(RecordPat(pats,_),_,body)],_),Record(acts,_),_) ->
        if all (fn(_,VarPat _) -> true |_ -> false) pats 
	  then (if all (fn(_,Var _) -> true |_ -> false) acts
		  then Some(substitute(body,makeSubstFromRecord(pats,acts)))
		  else Some(List.foldr (fn (((_,v),(_,val)),body) ->
					 simplifyOne spc (mkLet([(v,val)],body)))
			      body (zip(pats,acts))))
	  else None
      | _ -> None

  op  makeSubstFromRecord: List(Id * Pattern) * List(Id * MS.Term) -> List(Var * MS.Term)
  def makeSubstFromRecord(pats,acts) =
    foldl (fn ((id,VarPat(v,_)),result) -> Cons((v,findField(id,acts)),result))
      []
      pats

  def simplifiedApply(t1,t2,spc) =
    simplifyOne spc (mkApply(t1,t2))

  op  simpleTerm?: MS.Term -> Boolean
  def simpleTerm?(term) = 
    case term of 
      | Record(fields,_) ->
        all (fn (_,t) -> simpleTerm t) fields
      | _ -> simpleTerm term

 def simplify spc term = mapSubTerms(simplifyOne spc) term


 op  simplifySpec: Spec -> Spec
 def simplifySpec(spc) = 
     mapSpec (simplify spc,fn s -> s,fn p -> p) spc
    
endspec

