TypeObligations qualifying
spec 
  import /Languages/MetaSlang/Specs/Utilities
  import /Languages/MetaSlang/Specs/Environment
  import /Languages/MetaSlang/Transformations/Match

 op makeTypeCheckObligationSpec: Spec * SpecRef -> Spec
 op checkSpec : Spec -> TypeCheckConditions

% Auxiliary variable environment.
% Gamma maps local variables to their sorts, 
% and also accumulates local context assertions.

 sort Decl  = 
   | Var Var 
   | Cond Term 
   | LetRec List (Var * Term) 
   | Let List (Pattern * Term)

 sort Gamma = List Decl * TyVars * Spec * String * StringSet.Set

 op  insert       : Var * Gamma -> Gamma
 op  assertCond   : Term * Gamma -> Gamma
 op  insertLet    : List (Pattern * Term) * Gamma -> Gamma
 op  insertLetRec : List (Var * Term) * Gamma -> Gamma
 op  boundVars    : Gamma -> List Var
 op  boundTypeVars : Gamma -> TyVars
 op  patternVars  : Pattern -> List Var

 def assertSubtypeCond(term,srt:Sort,gamma) = 
     case srt
       of Subsort(srt,pred,_) ->
          let (ds,tvs,spc,name,names) = gamma in
          assertSubtypeCond(term,srt,(cons(Cond(mkLetOrApply(pred,term)):Decl,ds),
				      tvs,spc,name,names))
        | _ -> gamma

 def mkLetOrApply(fntm,arg) =
   case fntm of
     | Lambda ([(VarPat(v,_),Fun(Bool true, _,_),bod)],_) ->
       % StandardSpec.mkLet([(VarPat(v,a),arg)],bod)
       mapTerm (fn (tm) -> case tm of
	                    | Var(v1,_) -> if v1 = v then arg else tm
			    | _ -> tm,
	        id, id)
         bod
     | _ -> Apply(fntm,arg,noPos)

 def assertCond(cond,(ds,tvs,spc,name,names)) = 
     (cons(Cond cond:Decl,ds),tvs,spc,name,names)
 def insert((x,srt),(ds,tvs,spc,name,names))  = 
     let ds = cons(Var(x,srt):Decl,ds) in
     let gamma = (ds,tvs,spc,name,names) in
     let gamma = assertSubtypeCond(Var((x,srt),noPos),srt,gamma) in
     gamma
% Subsort conditions:
 def insertLet(decls,(ds,tvs,spc,name,names)) = 
     (cons(Let decls:Decl,ds),tvs,spc,name,names) %% Add let-bound names here. FIXME!
 def insertLetRec(decls,(ds,tvs,spc,name,names)) = 
     (cons(LetRec decls:Decl,ds),tvs,spc,name,
	StringSet.addList(names,List.map (fn((x,_),_)-> x) decls))


 def patternVars(p) = 
     let
	def loopP(p:Pattern,vs) = 
	    case p
	      of VarPat(v,_) -> cons(v,vs)
	       | RecordPat(fields,_) -> 
		 List.foldr (fn ((_,p),vs) -> loopP(p,vs)) vs fields
	       | EmbedPat(_,None,_,_) -> vs
	       | EmbedPat(_,Some p,_,_) -> loopP(p,vs)
	       | QuotientPat(p,_,_) -> loopP(p,vs)
	       | RelaxPat(p,_,_) -> loopP(p,vs)
	       | _ -> vs
     in
     loopP(p,[])

 def boundTypeVars(_,tyVars,_,_,_) = tyVars

 def boundVars(decls: List Decl,_,_,_,_) = 
     let
	def loopP(p,vs) = patternVars(p) @ vs
	def loop(decls : List Decl,vars) = 
	    case decls
	      of [] -> vars
	       | (Var v)::decls -> loop(decls,cons(v,vars))
	       | (Cond _)::decls -> loop(decls,vars)
	       | (LetRec(ds))::decls -> loop(decls,(List.map (fn (v,_)-> v) ds) @ vars)
	       | (Let(ds))::decls ->
		 loop(decls,List.foldr (fn ((p,_),vs) -> loopP(p,vs)) vars ds)
     in
	loop(decls,[])


 def printDecl(d:Decl) = 
     case d
       of Var (x,srt) -> x^":"^printSort srt
	| Cond term -> "assert "^printTerm term
	| LetRec (decls) -> printTerm (LetRec(decls,Record([],noPos),noPos))
	| Let decls -> printTerm (Let(decls,Record([],noPos),noPos))

 op printGamma: Gamma -> ()
 def printGamma(decls,_,_,_,_) = 
     let _ = app (fn decl -> 
		(String.toScreen (printDecl decl);
 		 String.toScreen "; "))
		(rev decls)
     in
     let _ = String.writeLine "" in
     ()
 

 sort TypeCheckCondition  = String * TyVars * Term 
 sort TypeCheckConditions = List TypeCheckCondition

 op addCondition : TypeCheckConditions * Gamma * Term -> 
		   TypeCheckConditions
 op addFailure :   TypeCheckConditions * Gamma * String -> 
		   TypeCheckConditions

 op freshName : Gamma * String -> String

 op  ?? infixl 9 : fa(a,b) a * b -> a * b
 def ??(x) = x


 op |- infixl 7 :    
      (TypeCheckConditions * Gamma) * 
       (Term * Sort) -> TypeCheckConditions

 op <= : TypeCheckConditions * Gamma * Term * Sort * Sort -> 
	 TypeCheckConditions

 op getSpec        : Gamma -> Spec
% op inferType  : Spec * Term -> Sort
% op domain     : Spec * Sort -> Sort
% op range      : Spec * Sort -> Sort
 op unfoldBase : Gamma * Sort -> Sort

 def getSpec (_,_,e,_,_) = e

 def unfoldBase((_,_,spc,_,_),tau) = 
     SpecEnvironment.unfoldBase(spc,tau)

% def arrow = SpecEnvironment.arrow
% def domain = SpecEnvironment.domain
% def range = SpecEnvironment.range
% def inferType = SpecEnvironment.inferType


 def addFailure(tcc,(_,_,_,name,_),description) = 
     cons((name^" :"^description,[],mkFalse()),tcc)

 def makeVerificationCondition((decls,tvs,spc,name,_),term) = 
     let
	def insert(decl:Decl,formula) = 
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
     (name,tvs,term)

 def addCondition(tcc,gamma,term) = 
     cons(makeVerificationCondition(gamma,term),tcc)

% Generate a fresh name with respect to all the
% names previously used in spec (as ops) and
% for the bound variables.
%
 def freshName((decls,_,_,opName,names),name) = 
     let name = StringUtilities.freshName(name,names) in
     name

% check type well formedness as well...

 def |-((tcc,gamma),(M,tau)) = 
     case M
       of Apply(N1,N2,_) -> 
	  let spc = getSpec gamma in
          let sigma1 = inferType(spc,N1) 		       in
	  let tcc  = (tcc,gamma) |- N1 ?? sigma1 	       in
	  let tcc  = (tcc,gamma) |- N2 ?? domain(spc,sigma1)   in
	  let tau2 = range(spc,sigma1) 		    	       in
	  let tcc  = <= (tcc,gamma,M,tau2,tau) 		       in
	  tcc
        | Record(fields,_) -> 
%% Not part of build 6-25-00.
	  let spc = getSpec gamma in
 	  let types = product(spc,tau) in
          let
 	      def checkField((id,term),(id2,tau),tcc) = 
 		  (tcc,gamma) |- term ?? tau
 	  in
 	  % Check recursively that every element is well typed 
          let tcc = ListPair.foldr checkField tcc (fields,types) in
 	  % Check possible subsort constraints in tau 
          let tcc = <= (tcc,gamma,M,Product(types,noPos),tau) in
          tcc

        | Bind(binder,vars,body,_) -> 
	  let gamma = foldr insert gamma vars      in
          let tcc = (tcc,gamma) |- body ?? boolSort     in
          let tcc = <= (tcc,gamma,M,boolSort,tau)        in
	  tcc
        | Let(decls,body,_)    -> tcc 	%%%%%%%%% FIXME
        | LetRec(decls,body,_) -> tcc 	%%%%%%%%% FIXME
        | Var((id,srt),_) -> 
          let tcc = <= (tcc,gamma,M,srt,tau)             in
          tcc
        | Fun(f,s,_) -> 
	  let tcc = <= (tcc,gamma,M,s,tau)	        in
%
% List subcases explicitly to leave place for 
% special treatment.
%
	  (case f
	     of Equals     -> tcc 
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
          let dom = domain(getSpec gamma,tau) 			in
          let rng = range(getSpec gamma,tau)  			in
	  let tcc = 
              foldr (checkRule(gamma,dom,rng)) tcc rules   in
          let rules = 
	      (List.map (fn(p,c,b) -> ([p],c,mkTrue())) rules)	in
          let x  = freshName(gamma,"x")				in
          let vs = [Var((x,dom),noPos):Term]	        	in
	  let (_,_,spc,name,_) = gamma				in
	  let context = {counter = Ref 0,
		         spc = spc,
	                 funName = name,
			 term = None}				in
          let trm = match(context,vs,rules,mkFalse(),mkFalse()) in
	  (case simplifyMatch(trm)
	     of Fun(Bool true,_,_) -> tcc
	      | trm -> addCondition(tcc,gamma,mkBind(Forall,[(x,dom)],trm)))
	
        | IfThenElse(t1,t2,t3,_) -> 
	  let tcc1   = (tcc,gamma)   |- t1 ?? boolSort 		in
	  let gamma1 = assertCond(t1,gamma) 			in
          let tcc2   = (tcc1,gamma1) |- t2 ?? tau 		in
	  let gamma2 = assertCond(mkNot t1,gamma) 		in
          let tcc3   = (tcc2,gamma2) |- t3 ?? tau 		in
	  tcc3
        | Seq([],_)    -> tcc
	| Seq([M],_)   -> (tcc,gamma) |- (M,tau)	
	| Seq(M::Ms,_) -> 
	  let sigma = inferType(getSpec gamma,M) 		in
	  let tcc   = (tcc,gamma) |- M ?? sigma			in
	  let tcc   = (tcc,gamma) |- Seq(Ms,noPos) ?? tau	in
	  tcc

% 
% This should also capture that the previous patterns failed.
%
 def checkRule(gamma,dom,rng) ((pat,cond,body),tcc) = 
     let (gamma1,_) = bindPattern(gamma,pat,dom) 		in
     let tcc = (tcc,gamma1) |- cond ?? boolSort 		in
     let gamma2 = assertCond(cond,gamma1)			in
     let tcc = (tcc,gamma2) |- body ?? rng 			in
     tcc



 op bindPattern : Gamma * Pattern * Sort  -> Gamma * Term

 def returnPatternRec(pairs,gamma,M,tau,sigma) =
     if tau = sigma or 
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
	  let gamma = assertCond(mkLetOrApply(pred,M),gamma) in
          returnPatternRec(pairs,gamma,M,tau2,sigma1)
	| _ -> 
     case sigma1 
       of Subsort(sigma2,pred,_) -> 
	  let gamma = assertCond(mkLetOrApply(pred,M),gamma) in
	  returnPatternRec(pairs,gamma,M,tau1,sigma2)
	| _ -> (gamma,M)
 
 def returnPattern(gamma,t,tau1,tau2) = 
     returnPatternRec([],gamma,t,tau1,tau2)

     
 def bindPattern(gamma:Gamma,pat:Pattern,tau) = 
         case pat
           of AliasPat(p1,p2,_) -> 
	      let (gamma,t1) = bindPattern(gamma,p1,tau) 	  in
	      let (gamma,t2) = bindPattern(gamma,p2,tau) 	  in
	      let gamma = assertCond(mkEquality(tau,t1,t2),gamma) in
	      (gamma,t1)
            | VarPat(v as (_,srt),_) -> 
	      let gamma1 = insert(v,gamma) 		        in
	      returnPattern(gamma1,Var(v,noPos),srt,tau)
            | EmbedPat(constr,Some p,tau_,_) -> 
	      let tau1 = patternSort p 			        in
	      let (gamma1,t1) = bindPattern(gamma,p,tau1)       in
	      let t2:Term     = Apply(Fun(Embed(constr,true),
					  Arrow(tau1,tau_,noPos),noPos),t1,noPos) in
	      returnPattern(gamma1,t2,tau_,tau)
	    | EmbedPat(constr,None,tau_,_) -> 
	      returnPattern(gamma,Fun(Embed(constr,false),tau_,noPos),tau_,tau)
	    | RecordPat(fields,_) -> 
	      let fs     = product(getSpec gamma,tau) in
	      let fields = ListPair.zip(fs,fields) 		 in
	      let (gamma,terms) = 
		  List.foldr 
	      	  (fn (((_,tau),(id,p)),(g,terms))-> 
		   let (gamma,trm) = bindPattern(g,p,tau) in 
		   (gamma,cons((id,trm),terms)))
			(gamma,[]) fields
              in
	      let trm: Term = Record(terms,noPos) 		 in
	      returnPattern(gamma, trm, patternSort pat,tau)
	    | WildPat(sigma,_)	-> 
	      let v = freshName(gamma,"v")		 in
              let v = (v,sigma)			 	 in
	      let gamma1 = insert(v,gamma) 		 in
	      (gamma1,Var(v,noPos))
	   | StringPat(s,_) 	->      
	     returnPattern(gamma,Fun(String s,stringSort,noPos),stringSort,tau)
           | BoolPat(b,_) 		->      
	     returnPattern(gamma,Fun(Bool b,boolSort,noPos),boolSort,tau)
           | CharPat(ch,_) 	->      
	     returnPattern(gamma,Fun(Char ch,charSort,noPos),charSort,tau)
           | NatPat(i,_) 		->      
	     returnPattern(gamma,Fun(Nat i,natSort,noPos),natSort,tau)
           | RelaxPat(p,pred,_) 	-> 
	     let tau1:Sort = Subsort(tau,pred,noPos) in
             let (gamma,trm) = bindPattern(gamma,p,tau1)  in
	     (gamma,Apply(Fun(Relax,Arrow(tau1,tau,noPos),noPos),trm,noPos):Term)
           | QuotientPat(p,pred,_) 	-> 
	     let Quotient(tau1,_,_):Sort = tau in
	     let (gamma,trm) = bindPattern(gamma,p,tau1)
	     in
	     (gamma,Apply(Fun(Quotient,Arrow(tau1,tau,noPos),noPos),trm,noPos):Term)



 def mkIfThenElse(t1,t2:Term,t3:Term):Term =
   case t2 of
     | Fun(Bool true,_,_)  -> mkOr(t1,t3)
     | Fun(Bool false,_,_) -> mkAnd(mkNot t1,t3)
     | _ ->
   case t2 of
     | Fun(Bool true,_,_)  -> mkOr(mkNot t1,t2)
     | Fun(Bool false,_,_) -> mkAnd(t1,t2)
     | _ ->
   IfThenElse(t1,t2,t3,noPos)

 def mkOr(t1,t2) = 
     case (t1:Term,t2:Term)
       of (Fun(Bool true,_,_),_) -> t1
	| (Fun(Bool false,_,_),_) -> t2
	| (_,Fun(Bool true,_,_)) -> t2
	| (_,Fun(Bool false,_,_)) -> t1
	| _ -> StandardSpec.mkOr(t1,t2)

 def mkAnd(t1,t2) = 
     case (t1:Term,t2:Term)
       of (Fun(Bool true,_,_),_) -> t2
	| (Fun(Bool false,_,_),_) -> t1
	| (_,Fun(Bool true,_,_)) -> t1
	| (_,Fun(Bool false,_,_)) -> t2
	| _ -> StandardSpec.mkAnd(t1,t2)

%
% Simplify term obtained from pattern matching compilation
% by replacing TranslationBuiltIn.failWith by "or"
%

 op simplifyMatch: Term -> Term
 def simplifyMatch(trm:Term) = 
     case trm
       of IfThenElse(t1,t2,t3,_) -> 
	  let t2 = simplifyMatch(t2) in
	  let t3 = simplifyMatch(t3) in
	  mkIfThenElse(t1,t2,t3)
	| Apply(Fun(Op(Qualified("TranslationBuiltIn","failWith"),_),_,_),
		Record([(_,t1),(_,t2)],_),_) -> 
	  let t1 = simplifyMatch(t1) in
	  let t2 = simplifyMatch(t2) in
	  mkOr(t1,t2)
	| Let(decls,body,_) -> 
	  let trm = simplifyMatch(body) in
	  (case trm
	     of Fun(Bool _,_,_) -> trm
	      | _ -> Let(decls,trm,noPos))
	| _ -> trm

 def <= (tcc,gamma,M,tau,sigma) = 
     (%String.writeLine
      %	   (printTerm M^ " : "^
      %         printSort tau^" <= "^
      %	        printSort sigma); 
     subtypeRec([],tcc,gamma,M,tau,sigma))

 def subtypeRec(pairs,tcc,gamma,M,tau,sigma) =
     if tau = sigma or 
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
	  let gamma = assertCond(mkLetOrApply(pred,M),gamma) in
          subtypeRec(pairs,tcc,gamma,M,tau2,sigma)
	| _ -> 
     case sigma1 
       of Subsort(sigma2,pred,_) -> 
%	  let _ = String.writeLine("Verifying "^printTerm pred) in
	  let tcc = subtypeRec(pairs,tcc,gamma,M,tau,sigma2) in
	  let tcc = addCondition(tcc,gamma,mkLetOrApply(pred,M)) in
	  tcc
	| _ ->
     case (tau1,sigma1)
       of (Arrow(tau1,tau2,_),Arrow(sigma1,sigma2,_)) -> 
	  let x = freshName(gamma,"x") 				in
          let xVar   = Var((x,sigma1),noPos):Term			in
          let gamma1 = insert((x,sigma1),gamma) 		in
          let tcc    = subtypeRec(pairs,tcc,gamma1,xVar,sigma1,tau1) in
          let tcc    = subtypeRec(pairs,tcc,gamma1,
				  mkLetOrApply(M,xVar),tau2,sigma2)   in
	  tcc
        | (Product(fields1,_),Product(fields2,_)) -> 
	  let tcc = ListPair.foldr 
		(fn((_,t1),(id,t2),tcc) -> 
		     subtypeRec(pairs,tcc,gamma,
				Apply(Fun(Project id,Arrow(sigma1,t1,noPos),noPos),
				      M,noPos),t1,t2))
		 tcc (fields1,fields2)
          in
          tcc
        | (CoProduct(fields1,_),CoProduct(fields2,_)) ->
	  let tcc = ListPair.foldr 
		(fn((_,t1),(id,t2),tcc) -> 
		   (case (t1,t2)
	              of (Some t1,Some t2) -> 
			 let gamma = assertCond(Apply(Fun(Embedded id,
							  Arrow(sigma,boolSort,noPos),
							  noPos),
						      M,noPos),
						gamma) in
		         subtypeRec(pairs,tcc,gamma,
				    Apply(Fun(Select id,
					      Arrow(sigma,t1,noPos),noPos),
					  M,noPos),
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
	      let tcc = ListPair.foldr
			   (fn (s1,s2,tcc) -> 
			       let x = freshName(gamma,"x") in
			       let gamma1 = insert((x,s1),gamma) in
			       let gamma2 = insert((x,s2),gamma) in
			       let tcc = subtypeRec(pairs,tcc,gamma1,
						    Var((x,s1),noPos),s1,s2) in
			       let tcc = subtypeRec(pairs,tcc,gamma2,
						    Var((x,s2),noPos),s2,s1) in
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


 def checkSpec(spc:Spec) = 
     let localOps = spc.importInfo.localOps in
     let names = StringSet.fromList (map (fn Qualified(q,id) -> id) localOps) in
     let gamma0 = fn tvs -> fn nm -> ([], tvs, spc, nm, names) in
     let tcc = [] in
     let tcc = 
	 StringMap.foldriDouble
	   (fn (qname, name, (names, fixity, (tvs,tau), defs), tcc) ->
	     if member(Qualified(qname, name),localOps) then
		 foldl (fn ((type_vars, term), tcc) ->
			(tcc,gamma0 tvs name) |- term ?? tau)
		       tcc
		       defs
	       else 
		 tcc)
	   tcc spc.ops
     in
     tcc

 def makeTypeCheckObligationSpec (spc,spcRef) =
   let tcSpec = addImport((spcRef,spc),emptySpec) in
   addConjectures(checkSpec(spc),tcSpec)

end