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

 op makeTypeCheckObligationSpec: Spec * (SpecCalc.Term Position) -> Spec
 op checkSpec : Spec -> TypeCheckConditions

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
     | _ -> mkApply(fntm,arg)

 def assertCond(cond,gamma as (ds,tvs,spc,qid,name,ty,names)) = 
   case cond of
     | Fun((Bool true,_,_)) -> gamma
     | _ -> (cons(Cond cond,ds),tvs,spc,qid,name,ty,names)
 def insert((x,srt),gamma as (ds,tvs,spc,qid,name,ty,names))  = 
     let ds = cons(Var(x,srt),ds) in
     let _ = names := StringMap.insert(!names,x,0) in
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
 

 sort TypeCheckCondition  = QualifiedId * TyVars * MS.Term 
 sort TypeCheckConditions = List(TypeCheckCondition) * StringSet.Set

 op addCondition : TypeCheckConditions * Gamma * MS.Term -> 
		   TypeCheckConditions
 op addFailure :   TypeCheckConditions * Gamma * String -> 
		   TypeCheckConditions

 op freshName : Gamma * String -> String

 op  ?? infixl 9 : fa(a,b) a * b -> a * b
 def ??(x) = x


 op |- infixl 7 :    
      (TypeCheckConditions * Gamma) * 
       (MS.Term * Sort) -> TypeCheckConditions

 op <= : TypeCheckConditions * Gamma * MS.Term * Sort * Sort -> 
	 TypeCheckConditions

 op getSpec        : Gamma -> Spec
% op inferType  : Spec * MS.Term -> Sort
% op domain     : Spec * Sort -> Sort
% op range      : Spec * Sort -> Sort
 op unfoldBase : Gamma * Sort -> Sort

 def getSpec (_,_,e,_,_,_,_) = e

 def unfoldBase((_,_,spc,_,_,_,_),tau) = 
     SpecEnvironment.unfoldBase(spc,tau)

% def arrow = SpecEnvironment.arrow
% def domain = SpecEnvironment.domain
% def range = SpecEnvironment.range
% def inferType = SpecEnvironment.inferType


 def addFailure((tcc,claimNames),(_,_,_,_,name as Qualified(qid, id),_,_),description) = 
     let descName = id^" :"^description in
     let name = mkQualifiedId(qid, descName) in
     (Cons((name,[],mkFalse()),tcc),StringSet.add(claimNames,descName))

 def makeVerificationCondition((decls,tvs,spc,qid,name as Qualified(qual, id),_,_),term,claimNames) = 
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
     case simplify spc term of
       | Fun(Bool true,_,_) -> None
       | claim -> Some(mkQualifiedId(qual, StringUtilities.freshName(id,claimNames)),tvs,claim)

 def addCondition(tcc as (tccs,claimNames),gamma,term) =
   case makeVerificationCondition(gamma,term,claimNames) of
     | Some condn -> let Qualified(_, cname) = condn.1 in (Cons(condn,tccs),StringSet.add(claimNames,cname))
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
	       let tcc  = checkRecursiveCall(tcc,gamma,M,N1,N2)    in
	       tcc)
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
        | Let(decls,body,_)    ->
	  let (tcc,gamma) =
	       foldl (fn ((pat,t),(tcc,ngamma)) ->
		      let sigma1 = patternSort pat                         in
		      let (ngamma,tp) = bindPattern(ngamma,pat,sigma1)     in
		      %% This is alternative to insertLet below
		      let ngamma = assertCond(mkEquality(inferType(getSpec gamma,t),t,tp),
					      ngamma)
		      in
		      let spc = getSpec gamma 				   in
		      let tcc = (tcc,gamma) |- t ?? sigma1                 in
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
	     | Quotient   -> tcc
	     | Choose     -> tcc 
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
        | Lambda(rules,_) ->
%	  let spc = getSpec gamma	       in
%	  let tau2 = inferType(spc,M)  	       in
%% This is redundant because infertype gets type from components and checkLambda passes tau down to components
%	  let tcc  = <= (tcc,gamma,M,tau2,tau) in
	  checkLambda(tcc,gamma,rules,tau,None)
	
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
   let tcc = foldl (checkRule(gamma,dom,rng,optArg)) tcc rules  in
   let rules = 
       (List.map (fn(p,c,b) -> ([p],c,mkTrue())) rules)	 in
   let x  = useNameFrom(gamma,optArg,"D")		 in
   let vs = [mkVar(x,dom)] 	        	         in
   let (_,_,spc,_,Qualified(_, name),_,_) = gamma        in
   let context:PatternMatch.Context = {counter    = Ref 0,
				       spc        = spc,
				       funName    = name,
				       errorIndex = Ref 0,
				       term       = None}
   in
   let trm = match(context,vs,rules,mkFalse(),mkFalse()) in
   (case simplifyMatch(trm)
      of Fun(Bool true,_,_) -> tcc
       | trm -> addCondition(tcc,gamma,mkBind(Forall,[(x,dom)],trm)))

 op  useNameFrom: Gamma * Option MS.Term * String -> String
 def useNameFrom(gamma,optTm,default) =
   let base_name = case optTm of
		    | Some(Var((nm,_),_)) -> nm
                    | _ -> default
   in
   freshName(gamma,base_name)

% 
% This should also capture that the previous patterns failed.
%
 op  checkRule: Gamma * Sort * Sort * Option MS.Term-> (Pattern * MS.Term * MS.Term) * TypeCheckConditions
               -> TypeCheckConditions
 def checkRule(gamma,dom,rng,optArg) ((pat,cond,body),tcc) = 
     let (gamma0,tp) = bindPattern(gamma,pat,dom) 		in
     let gamma1 = case optArg of
                    | Some arg ->
                      assertCond(mkEquality(inferType(getSpec gamma,arg),arg,tp),gamma0)
                    | _ -> gamma0
     in
     let tcc = (tcc,gamma1) |- cond ?? boolSort 		in
     let gamma2 = assertCond(cond,gamma1)			in
     let tcc = (tcc,gamma2) |- body ?? rng 			in
     tcc

 op  returnPattern: Gamma * MS.Term * Sort * Sort  -> Gamma * MS.Term
 def returnPattern(gamma,t,tau1,tau2) = 
     returnPatternRec([],gamma,t,tau1,tau2)

 def returnPatternRec(pairs,gamma,M,tau,sigma) =
     if equalSort?(tau,sigma) or 
	exists (fn p -> p = (tau,sigma)) pairs
	then (gamma,M)
     else
     let pairs  = cons((tau,sigma),pairs) 	in 
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
      | EmbedPat(constr,Some p,tau_,_) -> 
	let tau1 = patternSort p in
	let (gamma1,t1) = bindPattern(gamma,p,tau1) in
	let t2 = mkApply(mkFun(Embed(constr,true),
			       mkArrow(tau1,tau_)),
			 t1) in
	returnPattern(gamma1,t2,tau_,tau)
      | EmbedPat(constr,None,tau_,_) -> 
	returnPattern(gamma,mkFun(Embed(constr,false),tau_),tau_,tau)
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
	let v = freshName(gamma,"P") in
	let v = (v,sigma)            in
	let gamma1 = insert(v,gamma) in
	(gamma1,mkVar(v))
     | StringPat(s,_) 	->      
       returnPattern(gamma,mkFun(String s,stringSort),stringSort,tau)
     | BoolPat(b,_) 		->      
       returnPattern(gamma,mkFun(Bool b,boolSort),boolSort,tau)
     | CharPat(ch,_) 	->      
       returnPattern(gamma,mkFun(Char ch,charSort),charSort,tau)
     | NatPat(i,_) 		->      
       returnPattern(gamma,mkFun(Nat i,natSort),natSort,tau)
     | RelaxPat(p,pred,_) 	-> 
       let tau1 = mkSubsort(tau,pred) in
       let (gamma,trm) = bindPattern(gamma,p,tau1) in
       (gamma,mkApply(mkFun(Relax,mkArrow(tau1,tau)),trm))
     | QuotientPat(p,pred,_) 	-> 
       let Quotient(tau1,_,_) = unfoldBase(gamma,tau) in
       let (gamma,trm) = bindPattern(gamma,p,tau1)
       in
       (gamma,mkApply(mkFun(Quotient,mkArrow(tau1,tau)),trm))

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
			else if equalSort?(unfoldStripSort(spc,oty,false),ty)
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
	     else if (equalSort?(unfoldStripSort(spc,oty,false),ty))
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
   let form = mkBind(Exists,[pred],mkConj[mkApply(mkOp(Qualified("WFO","wfo"),
						       mkArrow(predSort,boolSort)),
						  mkVar pred),
					  form])
   in
   let sname = StringUtilities.freshName(id,claimNames) in
   let name = mkQualifiedId(qual, sname) in
   let condn = (name,tvs,form) in
   (Cons(condn,tccs),StringSet.add(claimNames,sname))

 op  addErrorCondition: TypeCheckConditions * Gamma * String -> TypeCheckConditions
 %% Impossible obligation str is an indication of the error
 def addErrorCondition((tccs,claimNames),(_,_,_,_,Qualified(qual, id),_,_),str) =
   let sname = StringUtilities.freshName(id^"_"^str,claimNames) in
   let condn = (mkQualifiedId(qual, sname),[],mkFalse()) in
   (Cons(condn,tccs),StringSet.add(claimNames,sname))

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
     if equalSort?(tau,sigma) or 
	exists (fn p -> p = (tau,sigma)) pairs
	then tcc
     else
%     let _ = String.writeLine
%      	   (printTerm M^ " : "^
%               printSort tau^" <= "^
%      	        printSort sigma)
%     in
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
	  let tcc = addCondition(tcc,gamma,mkLetOrApply(pred,M,gamma)) in
	  tcc
	| _ ->
     case (tau1,sigma1)
       of (Arrow(tau1,tau2,_),Arrow(sigma1,sigma2,_)) -> 
          let (xVarTm,gamma1) = freshVars("X",sigma1,gamma) in
          let tcc    = subtypeRec(pairs,tcc,gamma1,xVarTm,sigma1,tau1) in
          let tcc    = subtypeRec(pairs,tcc,gamma1,
				  mkLetOrApply(M,xVarTm,gamma1),tau2,sigma2) in
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
	  %%% FIXME?
        | (Base(id1,srts1,_),Base(id2,srts2,_)) ->
	  if id1 = id2
	      then
	      %%  let ps1 = ListPair.zip(srts1,srts2) in % unused
	      let tcc = ListPair.foldl
			   (fn (s1,s2,tcc) -> 
			       let x = freshName(gamma,"B") in
			       let gamma1 = insert((x,s1),gamma) in
			       let gamma2 = insert((x,s2),gamma) in
			       let tcc = subtypeRec(pairs,tcc,gamma1,
						    mkVar(x,s1),s1,s2) in
			       let tcc = subtypeRec(pairs,tcc,gamma2,
						    mkVar(x,s2),s2,s1) in
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

 op  equivalenceConjectures: MS.Term * Spec -> List TypeCheckCondition
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
    (mkQualifiedId(qual, name^"_transitive"),tyVars,
     mkBind(Forall,[x,y,z],mkImplies(MS.mkAnd(mkAppl(r,[mkVar x,mkVar y]),mkAppl(r,[mkVar y,mkVar z])),
				     mkAppl(r,[mkVar x,mkVar z])))),
    %% fa(x,y) r(x,y) => r(y,x)
    (mkQualifiedId(qual, name^"_symmetric"),tyVars,
     mkBind(Forall,[x,y],mkImplies(mkAppl(r,[mkVar x,mkVar y]),mkAppl(r,[mkVar y,mkVar x])))),
    %% fa(x) r(x,x)
    (mkQualifiedId(qual, name^"_reflexive"),tyVars,
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

 def checkSpec spc = 
   let localOps = spc.importInfo.localOps in
   let names = foldl (fn (Qualified (q, id), m) ->
		      if q = UnQualified then 
			m
		      else 
			StringMap.insert (m, id, 0))
                     empty 
		     localOps
   in
   let gamma0 = fn tvs -> fn tau -> fn qid -> fn nm -> ([], tvs, spc, qid, nm, tau, Ref names) in
   let tcc = ([],empty) in
   %% Definitions of ops
   let tcc = 
       foldriAQualifierMap
         (fn (q, id, info, tcc) ->

	  if member (Qualified (q, id), localOps) then
	    foldl (fn (dfn, tcc) ->
		   let (tvs, tau, term) = unpackTerm dfn in
		   let usedNames = addLocalVars (term, StringSet.empty) in
		   let term = etaExpand (spc, usedNames, tau, term) in
		   let term = renameTerm (emptyContext ()) term in 
		   let taus = case tau of
		                | And (srts, _) -> srts
				| _ -> [tau]
		   in
		   foldl (fn (tau, tcc) ->
			  (tcc, 
			   gamma0 
			   tvs 
			   (Some (unfoldStripSort (spc, tau, false)))
			   (Some (Qualified (q, id), (curriedParams term).1))
			   (Qualified (q, id ^ "_Obligation")))
			   |- 
			  term ?? tau)
		         tcc
		         taus)
	          tcc 
		  (opInfoDefs info)
	  else 
	    tcc)
	 tcc 
	 spc.ops
   in
   %% Properties (Axioms etc.)
   let tcc = foldl (fn (pr as (_,pname as Qualified (q, id),tvs,fm),tcc) ->
		    let fm = renameTerm (emptyContext()) fm in
		    (tcc, gamma0 tvs None None (mkQualifiedId (q, (id^"_Obligation"))))
		     |- fm ?? boolSort)
                   tcc 
		   (localProperties spc)
   in
   %% Quotient relations are equivalence relations
   let quotientRelations: Ref(List MS.Term) = Ref [] in
   let _ = appSpec (fn _ -> (), 
		    fn s -> case s of
			      | Quotient(_,r,_) ->
		                if List.exists (fn rx -> equalTerm?(r,rx)) (!quotientRelations) then
				  ()
				else 
				  let _ = (quotientRelations := Cons(r,!quotientRelations)) in 
				  ()
			      | _ -> (),
		    fn _ -> ())
                   spc
     in
     let tcc = foldl (fn (r,(tccs,names)) -> ((equivalenceConjectures(r,spc)) ++ tccs,names))
                     tcc 
		     (!quotientRelations)
     in			       
       tcc

 op  wfoSpecTerm: SpecCalc.Term Position
 def wfoSpecTerm = (UnitId (SpecPath_Relative {path       = ["Library","Base","WFO"], 
					       hashSuffix = None}),
		    noPos)

 def makeTypeCheckObligationSpec (spc,specCalcTerm) =
   %let spc = lambdaLift(instantiateHOFns(spc)) in
   case getOptSpec (Some "/Library/Base/WFO") of
     | None -> fail "Error in processing /Library/Base/WFO"
     | Some wfoSpec ->
   %% if you only do an addImport to the emptyspec you miss all the substance of the
   %% original spec, thus we do an setImports to spc.
   let tcSpec = spc << {importInfo = {imports         = [(specCalcTerm,spc),(wfoSpecTerm,wfoSpec)],
				      % importedSpec  = Some (addDisjointImport(spc,wfoSpec)),
				      localOps        = emptyOpNames,
				      localSorts      = emptySortNames,
				      localProperties = emptyPropertyNames}}
   in
   let tcSpec = addDisjointImport (tcSpec, wfoSpec) in
   addConjectures (rev (checkSpec spc).1, tcSpec)

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
