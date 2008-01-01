TypeObligations qualifying
spec 
 import /Languages/MetaSlang/Transformations/CurryUtils
 import /Languages/MetaSlang/Transformations/PatternMatch
 import /Languages/MetaSlang/Transformations/Simplify
 import /Languages/MetaSlang/Transformations/LambdaLift
 import /Languages/MetaSlang/Transformations/ProverPattern
 import /Languages/MetaSlang/Transformations/InstantiateHOFns
 import /Languages/MetaSlang/Transformations/RenameBound
 import /Languages/SpecCalculus/Semantics/Evaluate/Signature
 import /Languages/SpecCalculus/Semantics/Evaluate/Spec/MergeSpecs

 %type SpecElement  = QualifiedId * TyVars * MS.Term 
 type TypeCheckConditions = SpecElements * StringSet.Set

 op makeTypeCheckObligationSpec: Spec -> Spec
 op checkSpec : Spec -> TypeCheckConditions

 def simplifyObligations? = true
 %% These two should be false for Isabelle conversion
 def generateTerminationConditions? = true
 def generateExhaustivityConditions? = true


% Auxiliary variable environment.
% Gamma maps local variables to their types, 
% and also accumulates local context assertions.

 type Decl  = 
   | Var Var 
   | Cond MS.Term                 
   | LetRec List (Var * MS.Term) 
   | Let List (Pattern * MS.Term)

 type Gamma = List Decl * TyVars * Spec * Option (QualifiedId * List Pattern) * QualifiedId
                * Option Sort * NameSupply

 op  insert       : Var * Gamma -> Gamma
 op  assertCond   : MS.Term * Gamma -> Gamma
 op  insertLet    : List (Pattern * MS.Term) * Gamma -> Gamma
 op  insertLetRec : List (Var * MS.Term) * Gamma -> Gamma

 op  assertSubtypeCond: MS.Term * MS.Sort * Gamma -> Gamma
 def assertSubtypeCond(term,srt,gamma) = 
     case srt
       of Subsort(srt,pred,_) ->
          let (ds,tvs,spc,qid,name,ty,names) = gamma in
          assertSubtypeCond(term,srt,(cons(Cond(mkLetOrApply(pred,term,gamma)),ds),
				      tvs,spc,qid,name,ty,names))
        | _ -> gamma

 op  mkLetOrApply: MS.Term * MS.Term * Gamma -> MS.Term
 def mkLetOrApply(fntm,arg,(ds,tvs,spc,qid,name,ty,names)) =
   let fntm = renameTerm (names,emptyEnv()) fntm in
   case fntm of
     | Lambda ([(VarPat(v as (vn,srt),_),Fun(Bool true, _,_),bod)],_) ->
       % mkLet([(VarPat(v,a),arg)],bod)
       if countVarRefs(bod,v) <= 1
	 then
	   mapTerm (fn (tm) -> case tm of
				| Var(v1,_) -> if v1 = v then arg else tm
				| _ -> tm,
		    id, id)
	     bod
         else
	   mkBind(Forall,[v],mkImplies(mkEquality(srt,mkVar v,arg),bod))
     | Lambda ([(RecordPat([("1",VarPat(v1 as (vn1,srt1),_)),("2",VarPat(v2 as (vn2,srt2),_))],_),
		 Fun(Bool true, _,_),bod)],_)
       ->
       if (embed? Record arg) && countVarRefs(bod,v1) <= 1 && countVarRefs(bod,v2) <= 1 
	 then
	   let Record([("1",arg1),("2",arg2)],_) = arg in
	   mapTerm (fn (tm) -> case tm of
				| Var(vr,_) -> if vr = v1 then arg1
					       else if vr = v2 then arg2
					       else tm
				| _ -> tm,
		    id, id)
	     bod
         else
	   mkBind(Forall,[v1,v2],mkImplies(mkEquality(mkProduct[srt1,srt2],
						      mkTuple[mkVar v1,mkVar v2],
						      arg),
					   bod))
       
     | _ -> mkApply(fntm,arg)

 def assertCond(cond,gamma as (ds,tvs,spc,qid,name,ty,names)) = 
   case cond of
     | Fun((Bool true,_,_)) -> gamma
     | _ -> (cons(Cond cond,ds),tvs,spc,qid,name,ty,names)
 def insert((x,srt),gamma as (ds,tvs,spc,qid,name,ty,names))  = 
     let ds = Cons(Var(x,srt),ds) in
     let i = case StringMap.find (!names, x)
	      of None   -> 0
	       | Some n -> n
     in
     let _ = names := StringMap.insert(!names,x,i) in
     let gamma = (ds,tvs,spc,qid,name,ty,names) in
     let gamma = assertSubtypeCond(mkVar(x,srt),srt,gamma) in
     gamma
% Subsort conditions:
 def insertLet(decls,(ds,tvs,spc,qid,name,ty,names)) = 
     (cons(Let decls,ds),tvs,spc,qid,name,ty,names)
 def insertLetRec(decls,(ds,tvs,spc,qid,name,ty,names)) =
   let _ = app (fn((x,_),_)-> names := StringMap.insert(!names,x,0)) decls in
   (cons(LetRec decls,ds),tvs,spc,qid,name,ty,names)

 def printDecl(d:Decl) = 
     case d
       of Var (x,srt) -> x^":"^printSort srt
	| Cond term -> "assert "^printTerm term
	| LetRec (decls) -> printTerm (LetRec(decls,mkRecord([]),noPos))
	| Let decls -> printTerm (Let(decls,mkRecord([]),noPos))

 op printGamma: Gamma -> ()
 def printGamma(decls,_,_,_,_,_,_) = 
     let _ = app (fn decl -> 
		(String.toScreen (printDecl decl);
 		 String.toScreen "; "))
		(rev decls)
     in
     let _ = writeLine "" in
     ()
 

 op addCondition : TypeCheckConditions * Gamma * MS.Term * String -> 
		   TypeCheckConditions
 op addFailure :   TypeCheckConditions * Gamma * String -> 
		   TypeCheckConditions

 op freshName : Gamma * String -> String

 op  ?? infixl 9 : fa(a,b) a * b -> a * b
 def ??(x) = x


 op |- infixl 7 : (TypeCheckConditions * Gamma) * (MS.Term * Sort) -> TypeCheckConditions

 op <= : TypeCheckConditions * Gamma * MS.Term * Sort * Sort -> TypeCheckConditions

 op getSpec    : Gamma -> Spec
 op unfoldBase : Gamma * Sort -> Sort

 def getSpec (_,_,e,_,_,_,_) = e

 def unfoldBase((_,_,spc,_,_,_,_),tau) = 
     Utilities.unfoldBase(spc,tau)

 op  mkConjecture: QualifiedId * TyVars * MS.Term -> SpecElement
 def mkConjecture(qid,tvs,fm) =
   Property(Conjecture,qid,tvs,fm,noPos)

 def addFailure((tcc,claimNames),(_,_,_,_,name as Qualified(qid, id),_,_),description) = 
     let descName = id^" :"^description in
     let name = mkQualifiedId(qid, descName) in
     (Cons(mkConjecture(name,[],mkFalse()),tcc),StringSet.add(claimNames,descName))

 op  makeVerificationCondition: Gamma * MS.Term * String * StringSet.Set -> Option(QualifiedId * TyVars * MS.Term)
 def makeVerificationCondition((decls,tvs,spc,qid,name as Qualified(qual, id),_,_),term,id_tag,claimNames) = 
     let
	def insert(decl,formula) = 
	    case decl
	      of Var v ->        
		 if isFree(v,formula)
		    then mkBind(Forall,[v],formula)
		 else formula
	       | Cond (Fun(Bool true,_,_)) -> formula
	       | Cond c ->       mkImplies(c,formula)
	       | Let decls ->    Let(decls,formula,noPos)
	       | LetRec decls -> LetRec(decls,formula,noPos)
     in
     let term = foldl insert term decls in
     % let _ = writeLine("Simplifying "^printTerm term) in
     case if simplifyObligations? then simplify spc term else term of
       | Fun(Bool true,_,_) -> None
       %% In general simplify doesn't change e -> true because of strictness, but that should not be
       %% issue here
       | Apply(Fun (Implies, _, _), Record([("1",t1),("2",t2)],_),_) | trueTerm? t2 || t1 = t2 ->
         None
       | claim -> Some(mkQualifiedId(qual, StringUtilities.freshName(id^id_tag,claimNames)),tvs,claim)

 def addCondition(tcc as (tccs,claimNames),gamma,term,id_tag) =
   case makeVerificationCondition(gamma,term,id_tag,claimNames) of
     | Some condn -> let Qualified(_, cname) = condn.1 in
                     (Cons(mkConjecture condn,tccs),StringSet.add(claimNames,cname))
     | None       -> tcc

% Generate a fresh name with respect to all the
% names previously used in spec (as ops) and
% for the bound variables.
%
 def freshName((_,_,_,_,_,_,names),name) =
   fresh names name

 op  freshVar: Id * Sort * Gamma -> MS.Term * Gamma
 def freshVar(name0,sigma1,gamma) =
   let x = freshName(gamma,name0) in
   let xVar   = mkVar(x,sigma1) in
   let gamma1 = insert((x,sigma1),gamma) in
   (xVar,gamma1)

 %%% If sigma1 is a product produce a product of new vars
 op  freshVars: Id * Sort * Gamma -> MS.Term * Gamma
 def freshVars(name0,sigma1,gamma) =
   case sigma1 of
     | Product(prs,_) ->
       let (vsprs,rgamma)
          = foldl (fn ((id,s),(vs,gamma)) ->
		   let (nv,ngamma) = freshVar(name0,s,gamma) in
		   (cons((id,nv),vs),ngamma))
              ([],gamma) prs
       in
       (mkRecord(rev vsprs),rgamma)
     | _ -> freshVar(name0,sigma1,gamma)

% check type well formedness as well...

 def |-((tcc,gamma),(M,tau)) = 
     case M
       of Apply(N1,N2,_) ->
	  let spc = getSpec gamma in
          let sigma1 = inferType(spc,N1) 		           in
	  (case N1 of 
	     | Lambda(rules,_) ->
	       let tcc  = (tcc,gamma) |- N2 ?? domain(spc,sigma1)  in
	       let tau2 = range(spc,sigma1) 		    	   in
	       let tcc  = <= (tcc,gamma,M,tau2,tau) 		   in
	       checkLambda(tcc,gamma,rules,sigma1,Some N2)
	     | Fun(Restrict,s,_) ->
	       let (dom,ran) = arrow(spc,s)			   in
	       let tcc  = (tcc,gamma) |- N2 ?? ran		   in
	       let tcc  = <= (tcc,gamma,N2,ran,tau) 		   in
	       tcc
	     | _ ->
	   let tcc  = (tcc,gamma) |- N1 ?? sigma1 	           in
	   case nonStrictAppl(N1,N2) of
	     | Some (p1,p2,polarity) ->
	       let tcc1   = (tcc,gamma)   |- p1 ?? boolSort 	   in
	       let gamma1 = assertCond(if polarity then p1 else negateTerm p1,gamma) in
	       let tcc2   = (tcc1,gamma1) |- p2 ?? tau 		   in
	       tcc2
	     | _ ->
	       let tcc  = (tcc,gamma) |- N2 ?? domain(spc,sigma1)  in
	       let tau2 = range(spc,sigma1) 		    	   in
	       let tcc  = <= (tcc,gamma,M,tau2,tau) 		   in
	       let tcc  = if generateTerminationConditions?
	                   then checkRecursiveCall(tcc,gamma,M,N1,N2)
	                   else tcc
	       in tcc)
        | Record(fields,_) -> 
	  let spc = getSpec gamma in
 	  let types = product(spc,tau) in
          let
 	      def checkField((id,term),(id2,tau),tcc) = 
 		  (tcc,gamma) |- term ?? tau
 	  in
 	  % Check recursively that every element is well typed 
          let tcc = ListPair.foldl checkField tcc (fields,types) in
 	  % Check possible subsort constraints in tau 
          let tcc = <= (tcc,gamma,M,Product(types,noPos),tau) in
          tcc

        | Bind(binder,vars,body,_) -> 
	  let gamma = foldl insert gamma vars        in
          let tcc = (tcc,gamma) |- body ?? boolSort  in
          let tcc = <= (tcc,gamma,M,boolSort,tau)    in
	  tcc
	| The(v as (_,srt),body,_) ->
	  let gamma = insert (v,gamma) in
	  let tcc = (tcc,gamma) |- body ?? boolSort  in
          let tcc = <= (tcc,gamma,M,srt,tau)         in
	  let tcc = addCondition(tcc,gamma,mkBind(Exists1,[v],body),"_the") in
	  tcc
        | Let(decls,body,_)    ->
	  let (tcc,gamma) =
	       foldl (fn ((pat,trm),(tcc,ngamma)) ->
		      let sigma1 = patternSort pat                         in
		      let (ngamma,tp) = bindPattern(ngamma,pat,sigma1)     in
		      %% This is alternative to insertLet below
		      let ngamma = assertCond(mkEquality(inferType(getSpec gamma,trm),
                                                         trm,
                                                         tp),
					      ngamma)
		      in
		      let spc = getSpec gamma 				   in
		      let tcc = (tcc,gamma) |- trm ?? sigma1               in
		      let tcc = addQuotientCondition(tcc,gamma,pat,body,Some trm) in
		      (tcc,ngamma))
	          (tcc,gamma)
		  decls
	  in
	  %let gamma = insertLet(decls,gamma)         in
	  let tcc = (tcc,gamma) |- body ?? tau       in
	  tcc
	  
        | LetRec(decls,body,_) ->
	  let gamma = foldl (fn ((v,_),gamma) -> insert(v,gamma))
	                gamma decls
	  in
	  let tcc =
	      foldl (fn (((_,srt),t),tcc) ->
		     let spc = getSpec gamma in
		     let tcc = (tcc,gamma) |- t ?? srt in
		     tcc)
	        tcc
		decls
	  in
	  let gamma = insertLetRec(decls,gamma)      in
	  let tcc = (tcc,gamma) |- body ?? tau       in
	  tcc
        | Var((id,srt),_) -> 
          let tcc = <= (tcc,gamma,M,srt,tau)         in
          tcc
        | Fun(f,s,_) -> 
	  let tcc = <= (tcc,gamma,M,s,tau)	     in
%
% List subcases explicitly to leave place for 
% special treatment.
%
	  (case f of
	     | Not        -> tcc 
	     | And        -> tcc 
	     | Or         -> tcc 
	     | Implies    -> tcc 
	     | Iff        -> tcc 
	     | Equals     -> tcc 
	     | NotEquals  -> tcc 
	     | Quotient   qid -> tcc  % TODO: anything? (or is this subsumed by treatment of s in Fun(f,s,_)?
	     | Choose     qid -> tcc  % TODO: anything? (or is this subsumed by treatment of s in Fun(f,s,_)?
	     | Restrict   -> tcc 
	     | Relax      -> tcc 
	     | Op(id,fx)  -> tcc 
	     | Project n  -> tcc
	     | Embed(n,b) -> tcc
	     | Embedded n -> tcc
	     | Select   n -> tcc
	     | Nat      i -> tcc 
	     | Char     c -> tcc
	     | String   s -> tcc
	     | Bool     b -> tcc
          )
%%
%% This checks that pattern matching is exhaustive.
%%
        | Lambda(rules,_) | length rules <= 1 ->
	  let tau2 = inferType(getSpec gamma,M) in
	  let tcc  = <= (tcc,gamma,M,tau2,tau)  in
	  checkLambda(tcc,gamma,rules,tau,None)
	
        | Lambda(rules as (pat,_,body)::_,a) ->	% eta-normalize to simple pattern & case
	  let (v,gamma) = freshVar("eV",patternSort pat,gamma) in
	  let Var v_t = v in
	  |-((tcc,gamma),(Lambda([(VarPat v_t,mkTrue(),mkApply(M,v))],a),tau))

        | IfThenElse(t1,t2,t3,_) -> 
	  let tcc1   = (tcc,gamma)   |- t1 ?? boolSort 		in
	  let gamma1 = assertCond(t1,gamma) 			in
          let tcc2   = (tcc1,gamma1) |- t2 ?? tau 		in
	  let gamma2 = assertCond(negateTerm t1,gamma) 		in
          let tcc3   = (tcc2,gamma2) |- t3 ?? tau 		in
	  tcc3
        | Seq([],_)    -> tcc
	| Seq([M],_)   -> (tcc,gamma) |- (M,tau)	
	| Seq(M::Ms,_) -> 
	  let sigma = inferType(getSpec gamma,M) 		in
	  let tcc   = (tcc,gamma) |- M ?? sigma			in
	  let tcc   = (tcc,gamma) |- Seq(Ms,noPos) ?? tau	in
	  tcc

 op  nonStrictAppl: MS.Term * MS.Term -> Option (MS.Term * MS.Term * Boolean)
 def nonStrictAppl(rator,args) =
   case (rator, args) of
     | (Fun(And,     _, _), Record([("1",p),("2",q)],_)) -> Some (p,q,true)   % p && q  -- can assume  p in q
     | (Fun(Or,      _, _), Record([("1",p),("2",q)],_)) -> Some (p,q,false)  % p or q -- can assume ~p in q
     | (Fun(Implies, _, _), Record([("1",p),("2",q)],_)) -> Some (p,q,true)   % p => q -- can assume  p in q
     | _ -> None

 op  checkLambda: TypeCheckConditions * Gamma * Match * Sort * Option MS.Term
                 -> TypeCheckConditions
 def checkLambda(tcc,gamma,rules,tau,optArg) =
   let dom = domain(getSpec gamma,tau) 			 in
   let rng = range(getSpec gamma,tau)  		 	 in
   let casesDisjoint? = disjointMatches rules            in
   let (tcc,_) = foldl (checkRule(dom,rng,optArg,casesDisjoint?)) (tcc,gamma) rules  in
   let rules = map (fn(p,c,b) -> ([p],c,mkTrue())) rules in
   let x  = useNameFrom(gamma,optArg,"D")		 in
   let vs = [mkVar(x,dom)] 	        	         in
   let (_,_,spc,_,Qualified(_, name),_,_) = gamma        in
   let context = {counter    = Ref 0,
		  spc        = spc,
		  funName    = name,
		  errorIndex = Ref 0,
		  term       = None}
   in
   let trm = match(context,vs,rules,mkFalse(),mkFalse()) in
   (case simplifyMatch(trm)
      of Fun(Bool true,_,_) -> tcc
       | trm -> if generateExhaustivityConditions?
	          then addCondition(tcc,gamma,mkBind(Forall,[(x,dom)],trm),"_exhaustive")
                 else tcc)

 op  useNameFrom: Gamma * Option MS.Term * String -> String
 def useNameFrom(gamma,optTm,default) =
   let base_name = case optTm of
		    | Some(Var((nm,_),_)) -> nm
                    | _ -> default
   in
   freshName(gamma,base_name)

 op  checkRule: Sort * Sort * Option MS.Term * Boolean
               -> (Pattern * MS.Term * MS.Term) * (TypeCheckConditions * Gamma)
               -> TypeCheckConditions * Gamma
 def checkRule(dom,rng,optArg,casesDisjoint?) ((pat,cond,body),(tcc,gamma)) = 
     let (gamma0,tp) = bindPattern(gamma,pat,dom) 	  in
     let (condn,gamma1)
        = case optArg of
	    | Some arg ->
	      let condn = mkEquality(inferType(getSpec gamma,arg),arg,tp) in
	      let gamma0 = assertCond(condn,gamma0) in
	      (condn,gamma0)
	    | _ -> (mkTrue(),gamma0)
     in
     let tcc = (tcc,gamma1) |- cond ?? boolSort 	  in
     let gamma2 = assertCond(cond,gamma1)		  in
     let tcc = (tcc,gamma2) |- body ?? rng 		  in
     let tcc = addQuotientCondition(tcc,gamma,pat,body,optArg) in
     let nextGamma =
         if casesDisjoint? || trueTerm? condn
	   then gamma
	   else assertCond(negateExistTerm(condn,gamma2,gamma),gamma)
     in
     (tcc,nextGamma)

 op  negateExistTerm: MS.Term * Gamma * Gamma -> MS.Term
 def negateExistTerm(c,(decls_new,_,_,_,_,_,_),(decls_old,_,_,_,_,_,_)) =
   let vs = mapPartial (fn decl -> case decl of
			             | Var v | isFree(v,c) ->
			               Some v
				     | _ -> None)

              (sublist(decls_new,0,length decls_new - length decls_old))
   in
   negateTerm(mkSimpBind(Exists,vs,c))

 op  addQuotientCondition: TypeCheckConditions * Gamma * Pattern * MS.Term * Option MS.Term
                          -> TypeCheckConditions
 def addQuotientCondition(tcc,gamma,pat,body,optArg) =
   case optArg of
     | Some arg ->
       (case foldSubPatterns (fn (p,result) -> 
                                case p of 
                                  | QuotientPat (VarPat pv, super_type_name, _) -> 
                                    %% If the spec has type-checked, there must be an info for the super_type.
                                    let Some info = findTheSort (gamma.3, super_type_name) in
                                    let Quotient (base_type, _, _) = info.dfn in
                                    Some (pv, base_type)
                                  | _ -> result)
                             None 
                             pat 
        of
	 | Some ((v as (vn,_),vpos), base_type) ->
	   %% fa(v1,v2) pat(v1) && pat(v2) => arg(v1) = arg(v2)
	   let v1n = (vn^"__1",base_type) in % was type of v, but should be base type of Q
	   let v1 = Var(v1n,vpos) in
	   let v2n = (vn^"__2",base_type) in % was type of v, but should be base type of Q
	   let v2 = Var(v2n,vpos) in
	   let (o_tm,conds) = patternToTermPlusConds pat in
	   let mainCond = case o_tm of
	                    | None -> []
	                    | Some tm -> [mkEquality(termSort arg,arg,tm)]
	   in
	   let all_conds = mainCond ++ conds in
	   let v1Conds = map (fn c -> substitute(c,[(v,v1)])) all_conds in
	   let v2Conds = map (fn c -> substitute(c,[(v,v2)])) all_conds in
                      let body_type = termSort body in
	   let quotCond = mkBind(Forall,[v1n,v2n],
				 mkImplies(mkConj(v1Conds ++ v2Conds),
                                           mkEquality(body_type, % was type of v, but should be type of body
                                                      substitute(body,[(v,v1)]),
                                                      substitute(body,[(v,v2)]))))
           in
	   addCondition(tcc,gamma,quotCond,"_quotient")
	 | _ -> tcc)
     | _ -> tcc

 op  returnPattern: Gamma * MS.Term * Sort * Sort  -> Gamma * MS.Term
 def returnPattern(gamma,t,tau1,tau2) = 
     returnPatternRec([],gamma,t,tau1,tau2)

 def returnPatternRec(pairs,gamma,M,tau,sigma) =
     let spc = gamma.3 in
     if equivType? spc (tau,sigma) ||
	exists (fn p -> p = (tau,sigma)) pairs
	then (gamma,M)
     else
     let pairs  = Cons((tau,sigma),pairs) 	in 
     let tau1   = unfoldBase(gamma,tau)    	in
     let sigma1 = unfoldBase(gamma,sigma)  	in
     if tau1 = sigma1
	then (gamma,M)
     else
     case tau1 
       of Subsort(tau2,pred,_) -> 
	  let gamma = assertCond(mkLetOrApply(pred,M,gamma),gamma) in
          returnPatternRec(pairs,gamma,M,tau2,sigma1)
	| _ -> 
     case sigma1 
       of Subsort(sigma2,pred,_) -> 
	  let gamma = assertCond(mkLetOrApply(pred,M,gamma),gamma) in
	  returnPatternRec(pairs,gamma,M,tau1,sigma2)
	| _ -> (gamma,M)

 op  bindPattern : Gamma * Pattern * Sort  -> Gamma * MS.Term
 def bindPattern(gamma,pat,tau) = 
   case pat
     of AliasPat(p1,p2,_) -> 
	let (gamma,t1) = bindPattern(gamma,p1,tau) in
	let (gamma,t2) = bindPattern(gamma,p2,tau) in
	let gamma = assertCond(mkEquality(tau,t1,t2),gamma) in
	(gamma,t1)
      | VarPat(v as (_,srt),_) -> 
	let gamma1 = insert(v,gamma) in
	returnPattern(gamma1,mkVar(v),srt,tau)
      | EmbedPat(constr,Some p,tau2,_) -> 
	let tau1 = patternSort p in
	let (gamma1,t1) = bindPattern(gamma,p,tau1) in
	let t2 = mkApply(mkFun(Embed(constr,true),
			       mkArrow(tau1,tau2)),
			 t1) in
	returnPattern(gamma1,t2,tau2,tau)
      | EmbedPat(constr,None,tau2,_) -> 
	returnPattern(gamma,mkFun(Embed(constr,false),tau2),tau2,tau)
      | RecordPat(fields,_) -> 
	let fs     = product(getSpec gamma,tau) in
	let fields = ListPair.zip(fs,fields)    in
	let (gamma,terms) = 
	    List.foldr
	      (fn (((_,tau),(id,p)),(g,terms))-> 
	       let (gamma,trm) = bindPattern(g,p,tau) in 
	       (gamma,cons((id,trm),terms)))
	      (gamma,[]) fields
	in
	let trm = mkRecord(terms) in
	returnPattern(gamma, trm, patternSort pat,tau)
      | WildPat(sigma,_)	->
	let (v,gamma1) = freshVar("P",sigma,gamma)in
	(gamma1,v)
     | StringPat(s,_) 	->      
       returnPattern(gamma,mkFun(String s,stringSort),stringSort,tau)
     | BoolPat(b,_) 		->      
       returnPattern(gamma,mkFun(Bool b,boolSort),boolSort,tau)
     | CharPat(ch,_) 	->      
       returnPattern(gamma,mkFun(Char ch,charSort),charSort,tau)
     | NatPat(i,_) 		->      
       returnPattern(gamma,mkFun(Nat i,natSort),natSort,tau)
     | QuotientPat(p,qid,_) 	-> 
       let Quotient(tau1,_,_) = unfoldBase(gamma,tau) in
       let (gamma,trm) = bindPattern(gamma,p,tau1)
       in
       (gamma,mkApply(mkFun(Quotient qid,mkArrow(tau1,tau)),trm))
     | RestrictedPat(p,pred,_) 	-> 
       let (gamma,trm) = bindPattern(gamma,p,tau) in
       let gamma = assertCond(pred,gamma) in
       (gamma,trm)

%% Well-foundedness condition

 op  checkRecursiveCall: TypeCheckConditions * Gamma * MS.Term * MS.Term * MS.Term -> TypeCheckConditions
 (* Don't need to generate obligation if arguments of call are independent of parameters. Normally, if an 
    obligation is generated, it should be trivial to find a WFO because the "recursive" call is made with 
    constant arguments, but if type of call is different from type of def then don't generate condition
    because it would give a type error. *)
 def checkRecursiveCall(tcc,gamma,term,n1,n2) =
   case CurryUtils.getCurryArgs term of
     | Some(f,args) ->
       (case f of
	  | Fun(Op(lqid,_),oty,_) ->
	    (case gamma of
	       | (_,_,spc,Some(qid,vs),_,Some ty,_) ->
		 if qid = lqid && length args = length vs
		   %% Should be able to deal with length args < length vs
		   then
		     %let vs = map (fn (VarPat(v,_)) -> v) vs in
		     (if vs = []
			then tcc
			else if similarType? spc (oty,ty) % TODO: A and A|p are similar -- is this desired here?
			then add_WFO_Condition(tcc,gamma,mkTuple(map (fn (pat) ->
								      let tm::_ = patternToTerms(pat) in tm) vs),
					       mkTuple args)
			else addErrorCondition(tcc,gamma,"IllegalRecursion"))
		   else tcc
	       | _ -> tcc)
	  | _ -> tcc)
     | _ ->
   case n1 of
     | Fun(Op(lqid,_),oty,_) ->
       (case gamma of
	 | (_,_,spc,Some(qid,[p]),_,Some ty,_) ->
	   if qid = lqid
	    then
	    %let vs = map (fn (VarPat(v,_)) -> v) (getParams p) in
	    (let vs = (getParams p) in
	     if vs = []
	       then tcc
	     else if similarType? spc (oty,ty) % TODO: A and A|p are similar -- is this desired here?
	     then add_WFO_Condition(tcc,gamma,mkTuple(map (fn (pat) -> let tm::_ = patternToTerms(pat) in tm) vs),
				    n2)
	     else addErrorCondition(tcc,gamma,"IllegalRecursion"))
	   else tcc
	 | _ -> tcc)
     | _ -> tcc

 op  add_WFO_Condition: TypeCheckConditions * Gamma * MS.Term * MS.Term
                       -> TypeCheckConditions
 def add_WFO_Condition((tccs,claimNames),(decls,tvs,spc,qid,name as Qualified(qual, id),_,_),param,recParam) =
   %% ex(pred) (wfo(pred) && fa(params) context(params) => pred(recParams,params))
   let paramSort = inferType(spc,recParam) in
   let predSort = mkArrow(mkProduct [paramSort,paramSort],boolSort) in
   let pred = ("pred",predSort) in
   let rhs = mkAppl(mkVar pred,[recParam,param]) in
   let def insert(decl,formula) = 
	 case decl
	   of Var v ->        
	      if isFree(v,formula)
		 then mkBind(Forall,[v],formula)
	      else formula
	    | Cond (Fun(Bool true,_,_)) -> formula
	    | Cond c ->       mkImplies(c,formula)
	    | Let decls ->    Let(decls,formula,noPos)
	    | LetRec decls -> LetRec(decls,formula,noPos)
   in
   let form = foldl insert rhs decls in
   let form = simplify spc form in
   let form = mkBind(Exists,[pred],mkConj[mkApply(mkOp(Qualified("Functions","wfo"),
						       mkArrow(predSort,boolSort)),
						  mkVar pred),
					  form])
   in
   let sname = StringUtilities.freshName(id^"_termination",claimNames) in
   let name = mkQualifiedId(qual, sname) in
   let condn = (name,tvs,form) in
   (Cons(mkConjecture condn,tccs),StringSet.add(claimNames,sname))

 op  addErrorCondition: TypeCheckConditions * Gamma * String -> TypeCheckConditions
 %% Impossible obligation str is an indication of the error
 def addErrorCondition((tccs,claimNames),(_,_,_,_,Qualified(qual, id),_,_),str) =
   let sname = StringUtilities.freshName(id^"_"^str,claimNames) in
   let condn = (mkQualifiedId(qual, sname),[],mkFalse()) in
   (Cons(mkConjecture condn,tccs),StringSet.add(claimNames,sname))

%
% Simplify term obtained from pattern matching compilation
% by replacing TranslationBuiltIn.failWith by "or"
%

 op simplifyMatch: MS.Term -> MS.Term
 def simplifyMatch(trm) = 
     case trm
       of IfThenElse(t1,t2,t3,_) -> 
	  let t2 = simplifyMatch(t2) in
	  let t3 = simplifyMatch(t3) in
	  Utilities.mkIfThenElse(t1,t2,t3)
	| Apply(Fun(Op(Qualified("TranslationBuiltIn","failWith"),_),_,_),
		Record([(_,t1),(_,t2)],_),_) -> 
	  let t1 = simplifyMatch(t1) in
	  let t2 = simplifyMatch(t2) in
	  Utilities.mkOr(t1,t2)
	| Apply(Fun(And,_,_),
		Record([(_,t1),(_,t2)],_),_) -> 
	  let t1 = simplifyMatch(t1) in
	  let t2 = simplifyMatch(t2) in
	  Utilities.mkAnd(t1,t2)
	| Let(decls,body,_) -> 
	  let trm = simplifyMatch(body) in
	  (case trm
	     of Fun(Bool _,_,_) -> trm
	      | _ -> Let(decls,trm,noPos))
	| _ -> trm

 def <=	 (tcc,gamma,M,tau,sigma) = 
     (%String.writeLine
      %	   (printTerm M^ " : "^
      %         printSort tau^" <= "^
      %	        printSort sigma); 
     subtypeRec([],tcc,gamma,M,tau,sigma))

 def subtypeRec(pairs,tcc,gamma,M,tau,sigma) =
     let spc = gamma.3 in
     if equivType? spc (tau,sigma) || 
	exists (fn p -> p = (tau,sigma)) pairs
	then tcc
     else
%      let _ = String.writeLine
%       	   (printTerm M^ " : "^
%                printSort tau^" <= "^
%       	        printSort sigma)
%      in
     let pairs  = cons((tau,sigma),pairs) 	in 
     let tau1   = unfoldBase(gamma,tau)    	in
     let sigma1 = unfoldBase(gamma,sigma)  	in
     if tau1 = sigma1
	then tcc
     else
     case tau1 
       of Subsort(tau2,pred,_) -> 
%	  let _ = String.writeLine("Asserting "^printTerm pred) in
	  let gamma = assertCond(mkLetOrApply(pred,M,gamma),gamma) in
          subtypeRec(pairs,tcc,gamma,M,tau2,sigma)
	| _ -> 
     case sigma1 
       of Subsort(sigma2,pred,_) -> 
%	  let _ = String.writeLine("Verifying "^printTerm pred) in
	  let tcc = subtypeRec(pairs,tcc,gamma,M,tau,sigma2) in
	  let tcc = addCondition(tcc,gamma,mkLetOrApply(pred,M,gamma),"_subsort") in
	  tcc
	| _ ->
     case (tau1,sigma1)
       of (Arrow(tau1,tau2,_),Arrow(sigma1,sigma2,_)) ->
	  let sigma1 = unfoldBase(gamma,sigma1) in
          let (xVarTm,gamma1) = freshVars("X",sigma1,gamma) in
          let tcc    = subtypeRec(pairs,tcc,gamma1,xVarTm,sigma1,tau1) in
          let tcc    = case M of
	                 | Lambda _ -> tcc % In this case the extra test would be redundant
	                 | _ -> subtypeRec(pairs,tcc,gamma1,
					   mkApply(M,xVarTm),tau2,sigma2)
	  in
	  tcc
        | (Product(fields1,_),Product(fields2,_)) -> 
	  let tcc = ListPair.foldl 
		      (fn((_,t1),(id,t2),tcc) -> 
		       subtypeRec(pairs,tcc,gamma,
				  mkApply(mkFun(Project id,mkArrow(sigma1,t1)),
					  M),
				  t1,t2))
		      tcc (fields1,fields2)
          in
          tcc
        | (CoProduct(fields1,_),CoProduct(fields2,_)) ->
	  let tcc = ListPair.foldl 
		(fn((_,t1),(id,t2),tcc) -> 
		   (case (t1,t2)
	              of (Some t1,Some t2) -> 
			 let gamma = assertCond(mkApply(mkFun(Embedded id, mkArrow(sigma,boolSort)),
							M),
						gamma) in
		         subtypeRec(pairs,tcc,gamma,
				    mkApply(mkFun(Select id, mkArrow(sigma,t1)), M),
				    t1,t2)
	               | (None,None) -> tcc
	               | _ -> System.fail "CoProduct mismatch"))
		 tcc (fields1,fields2)
          in
          tcc
        | (Quotient(tau1,pred1,_),Quotient(sigma2,pred2,_)) -> tcc 
	  %%%%%%%%%%%%% FIXME
        | (TyVar(tv1,_),TyVar(tv2,_)) -> tcc
        | (Base(id1,srts1,_),Base(id2,srts2,_)) ->
	  if id1 = id2
	      then
	      %%  let ps1 = ListPair.zip(srts1,srts2) in % unused
	      let tcc = ListPair.foldl
			   (fn (s1,s2,tcc) -> 
			       let x = freshName(gamma,"B") in
			       let gamma1 = insert((x,s1),gamma) in
			       %let gamma2 = insert((x,s2),gamma) in
			       let tcc = subtypeRec(pairs,tcc,gamma1,
						    mkVar(x,s1),s1,s2) in
                               %% Don't think this is necessary e.g. List Nat < List Integer
			       %let tcc = subtypeRec(pairs,tcc,gamma2,
			       %		    mkVar(x,s2),s2,s1) in
			       tcc)
			 tcc (srts1,srts2)
 	      in
	      tcc
	   else
           addFailure(tcc,
		      gamma,
		      printSort tau^
		      " could not be made subsort of "^
		      printSort sigma)
        | (Boolean(_), Boolean(_)) -> tcc
	| (Boolean(_), _) ->
           addFailure(tcc,
		      gamma,
		      printSort tau^
		      " could not be made subsort of "^
		      printSort sigma)
	| (_, Boolean(_)) ->
           addFailure(tcc,
		      gamma,
		      printSort tau^
		      " could not be made subsort of "^
		      printSort sigma)
        | _ -> (writeLine("subtypeRec: type error in "^printTerm M^"\nat "
                          ^print(termAnn M)^"\n"^printSort tau^" <=? "^printSort sigma);
                tcc)

 op  equivalenceConjectures: MS.Term * Spec -> SpecElements
 def equivalenceConjectures (r,spc) =
   let name = nameFromTerm r in
   let qual = qualifierFromTerm r in
   let domty = domain(spc,inferType(spc,r)) in
   let elty = hd(productSorts(spc,domty)) in
   let tyVars = freeTyVars elty in
   let x = ("x",elty) in
   let y = ("y",elty) in
   let z = ("z",elty) in
   [%% fa(x,y,z) r(x,y) && r(y,z) => r(x,z)
    mkConjecture(mkQualifiedId(qual, name^"_transitive"),tyVars,
		 mkBind(Forall,[x,y,z],
			mkImplies(MS.mkAnd(mkAppl(r,[mkVar x,mkVar y]),
					   mkAppl(r,[mkVar y,mkVar z])),
				  mkAppl(r,[mkVar x,mkVar z])))),
    %% fa(x,y) r(x,y) => r(y,x)
    mkConjecture(mkQualifiedId(qual, name^"_symmetric"),tyVars,
		 mkBind(Forall,[x,y],mkImplies(mkAppl(r,[mkVar x,mkVar y]),
					       mkAppl(r,[mkVar y,mkVar x])))),
    %% fa(x) r(x,x)
    mkConjecture(mkQualifiedId(qual, name^"_reflexive"),tyVars,
		 mkBind(Forall,[x],mkAppl(r,[mkVar x,mkVar x])))]

 op  nameFromTerm: MS.Term -> String
 def nameFromTerm t =
   case t of
     | Fun(Op(Qualified(q,id),_),_,_) -> id
     | _ -> "UnnamedRelation"

 op  qualifierFromTerm: MS.Term -> String
 def qualifierFromTerm t =
   case t of
     | Fun(Op(Qualified(q,id),_),_,_) -> q
     | _ -> UnQualified

 op  insertQID: QualifiedId * StringMap Nat -> StringMap Nat
 def insertQID(Qualified(q,id), m) =
   if q = UnQualified
     then m
     else StringMap.insert (m, id, 0)

 def checkSpec spc = 
   %let localOps = spc.importInfo.localOps in
   let names = foldl (fn (el,m) ->
		      case el of
			| Op    (qid,def?,_) -> insertQID(qid, m)
			| OpDef (qid,_)      -> insertQID(qid, m)
			| _ -> m)
                     empty 
		     spc.elements
   in
   let gamma0 = fn tvs -> fn tau -> fn qid -> fn nm -> ([], tvs, spc, qid, nm, tau, Ref names) in
   let tcc = ([],empty) in
   let (tccs,claimNames) =
       foldl (fn (el,tcc as (tccs,claimNames)) ->
	      let (tccs,claimNames) =
                case el of
                 | Op (qid as Qualified(q, id), true, pos) -> % true means decl includes def
                   (case findTheOp(spc,qid) of
                      | Some opinfo ->
                        let (new_tccs,claimNames) = 
                            foldr (fn (dfn, tcc) ->
                                   let (tvs, tau, term) = unpackTerm dfn in
                                   let usedNames = addLocalVars (term, StringSet.empty) in
                                   %let term = etaExpand (spc, usedNames, tau, term) in
                                   let term = renameTerm (emptyContext ()) term in 
                                   let taus = case tau of
                                                | And (srts, _) -> srts
                                                | _ -> [tau]
                                   in
                                     foldr (fn (tau, tcc) ->
                                            (tcc, gamma0 tvs
                                                  %% Was unfoldStripSort but that cause infinite recursion.
                                                  %% Is stripSubsorts sufficient (or necessary)?
                                                    (Some (stripSubsorts(spc, tau)))
                                                    (Some (qid, (curriedParams term).1))
                                                    (Qualified (q, id ^ "_Obligation")))
                                            |- term ?? tau)
                                       tcc taus)
                              ([],claimNames) 
                              (opInfoDefs opinfo)
                         in
                         if new_tccs = [] then tcc
                           else       % Split Op into decl and def
                             ([OpDef(qid,pos)] ++ new_tccs ++ [Op(qid,false,pos)] ++ tcc.1, claimNames))
                 | OpDef (qid as Qualified(q, id), _) ->
                   (case findTheOp(spc,qid) of
                      | Some opinfo ->
                        foldr (fn (dfn, tcc) ->
                               let (tvs, tau, term) = unpackTerm dfn in
                               let usedNames = addLocalVars (term, StringSet.empty) in
                               %let term = etaExpand (spc, usedNames, tau, term) in
                               let term = renameTerm (emptyContext ()) term in 
                               let taus = case tau of
                                            | And (srts, _) -> srts
                                            | _ -> [tau]
                               in
                                 foldr (fn (tau, tcc) ->
                                        (tcc, gamma0 tvs
                                              %% Was unfoldStripSort but that cause infinite recursion.
                                              %% Is stripSubsorts sufficient (or necessary)?
                                                (Some (stripSubsorts(spc, tau)))
                                                (Some (qid, (curriedParams term).1))
                                                (Qualified (q, id ^ "_Obligation")))
                                        |- term ?? tau)
                                   tcc taus)
                          tcc 
                          (opInfoDefs opinfo))
                 | SortDef (qid, _) ->
                   (case findTheSort(spc,qid) of
                      | Some sortinfo ->
                        let quotientRelations: Ref(List MS.Term) = Ref [] in
                        let _ = app (fn srt ->
                                     appSort (fn _ -> (), 
                                              fn s ->
                                              case s of
                                                | Quotient(_,r,_) ->
                                                  if List.exists (fn rx -> equivTerm? spc (r,rx))
                                                       (!quotientRelations) then ()
                                                  else 
                                                  let _ = (quotientRelations := Cons(r,!quotientRelations)) in 
                                                  ()
                                                | _ -> (),
                                              fn _ -> ())
                                       srt)
                                  (sortInfoDefs sortinfo)
                        in
                        foldr (fn (r,(tccs,names)) -> (equivalenceConjectures(r,spc) ++ tccs,names))
                          tcc 
                          (!quotientRelations))
                 | Property(_,pname as Qualified (q, id),tvs,fm, _) ->
                   let fm = renameTerm (emptyContext()) fm in
                   (tcc, gamma0 tvs None None (mkQualifiedId (q, (id^"_Obligation"))))
                   |- fm ?? boolSort
                 | _ -> tcc
	      in
              case (el,tccs) of
                | (Op(qid1,true, _),(OpDef(qid2, _)):: _) | qid1 = qid2 ->   % Split Op(qid,true)
                  (tccs, claimNames)
                | _ -> (Cons(el,tccs), claimNames))
         tcc spc.elements
     in			       
       (rev tccs,claimNames)

% op  wfoSpecTerm: SpecCalc.Term Position
% def wfoSpecTerm = (UnitId (SpecPath_Relative {path       = ["Library","Base","WFO"], 
%					       hashSuffix = None}),
%		    noPos)

 def makeTypeCheckObligationSpec (spc) =
   %let spc = lambdaLift(instantiateHOFns(spc),false) in
%   case getOptSpec (Some "/Library/Base/WFO") of
%     | None -> fail "Error in processing /Library/Base/WFO"
%     | Some wfoSpec ->
   %% if you only do an addImport to the emptyspec you miss all the substance of the
   %% original spec, thus we do an setImports to spc.
   let (new_elements,_) = checkSpec spc in
   removeDuplicateImports		% could be done more efficiently for special case
     (spc << {elements = new_elements})

% op  boundVars   : Gamma -> List Var
% op  boundTyVars : Gamma -> TyVars
% def boundTyVars(_,tyVars,_,_,_) = tyVars

% def boundVars(decls: List Decl,_,_,_,_) = 
%     let
%	def loopP(p,vs) = patternVars(p) @ vs
%	def loop(decls : List Decl,vars) = 
%	    case decls
%	      of [] -> vars
%	       | (Var v)::decls -> loop(decls,cons(v,vars))
%	       | (Cond _)::decls -> loop(decls,vars)
%	       | (LetRec(ds))::decls -> loop(decls,(List.map (fn (v,_)-> v) ds) @ vars)
%	       | (Let(ds))::decls ->
%		 loop(decls,List.foldr (fn ((p,_),vs) -> loopP(p,vs)) vars ds)
%     in
%	loop(decls,[])

end
