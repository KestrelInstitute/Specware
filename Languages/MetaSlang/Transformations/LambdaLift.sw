%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

(**
 Lambda lifting.
 ------------------------------------------------------------------------

 Perform lambda lifting in order to generation function definitions that
 work where only non-nested definitions are allowed.

 The lambda lifter is essentially a Johnson style lifter.
 See: Peyton Jones and Lester: Implementing functional languages, a tutorial.
 
 Assumption here is that all variables have unique names.
 **)

LambdaLift qualifying spec
 import ArityNormalize
 import Map qualifying /Library/Structures/Data/Maps/Simple

 sort Term = MS.Term

 op lambdaLift : Spec -> Spec

 sort LiftInfo = 
	{
	  ident    : String,    % Name of original identifier for lambda lifted term.
	  name     : String,    % Name of lambda-lifted function.
	  freeVars : FreeVars,  % Free variables in body (excluding those in pattern).
	  closure  : Term,      % Expression corresponding to name(freeVars)
	  pattern  : Pattern,   % Pattern.
	  body     : Term	% Body of lambda lifted expression.
	}
 %
 % The purpose of LiftInfo is to capture the situation where:
 % 
 % In the context where freeVars are declared we have:
 %
 %      ident = pattern -> body
 %
 % This is replaced by the context where no free variables are declared, and     
 %
 %    name = freeVars -> patterm -> body
 % 
 % and ident is replaced by name(freeVars) throughout the use of ident.
 % 
 % To target code where currying is not admitted, instead of the above we write: 
 %
 % name = (v,pattern) -> let freeVars = project(v) in body
 % 
 % and replace ident by 
 %
 %    closure: TranslationBuiltIn.makeClosure(name,freeVars)
 % 		   

 op  simulateClosures?: Boolean		% If false just use lambdas with free vars
 def simulateClosures? = false

 sort Ops      = Map.Map(String,LiftInfo)
 sort LLEnv      = 
      {
	spc 	    : Spec,
	opers       : Ops,
	opName      : String,
	qName       : String,
	counter	    : Ref Nat
      }
 sort FreeVars = List Var 



(* 
 * Term decorated with free variables in each sub-expression.
 *)

 sort VarTerm = VarTerm_ * FreeVars
 sort  VarTerm_ = 
  | Apply        VarTerm * VarTerm
  | Record       List(Id * VarTerm)
  | Bind         Binder * List(Var) * VarTerm
  | Let	         List(Pattern * VarTerm) * VarTerm
  | LetRec       List(Var * VarTerm) * VarTerm
  | Var          Var
  | Fun          Fun * Sort
  | Lambda       VarMatch
  | IfThenElse   VarTerm * VarTerm * VarTerm
  | Seq          List(VarTerm)
 sort VarMatch = List(Pattern * Term * VarTerm)
 op makeVarTerm: Term -> VarTerm
 op lambdaLiftTerm : LLEnv * VarTerm -> List(LiftInfo) * Term


(**
 op applyClosure : (A,B) Closure(A,B) * A -> B
 
 **)
(*
 * Free variables relative to environment supplying additional free variables associated
 * with variables that are to be bound to other terms with free variables.

 * Assumptions: 
	- All variables occur uniquely bound (fresh names have been generated).
	- Pattern matching compilation has been performed.
 *)

 def patternVars(pat:Pattern) = 
     case pat
       of VarPat(v,_) -> [v]
	| RecordPat(fields,_) -> foldr (fn((_,p),vs)-> patternVars p ++ vs) [] fields
	| WildPat _ -> []
        | EmbedPat(_,Some(pat),_,_) -> patternVars(pat)
        | EmbedPat(_,None,_,_) -> []
	| AliasPat(pat1,pat2,_) -> concat(patternVars pat1,patternVars pat2)
	| RelaxPat(pat,_,_) -> patternVars(pat)
	| QuotientPat(pat,_,_) -> patternVars(pat)
	| SortedPat(pat,_,_) -> patternVars(pat)
	| StringPat _ -> []
	| BoolPat _ -> []
	| CharPat _ -> []
	| NatPat _ -> []
	| _ -> System.fail("Unexpected pattern in match normalized expression: "^printPattern(pat))

 def makeVarTerm(term:Term) = 
   %let _ = String.writeLine("{") in
   %let _ = String.writeLine("makeVarTerm("^MetaSlangPrint.printTerm(term)^")...") in
   %let res =
     case term
       of Let(decls,body,a) -> 
	  let decls = List.map (fn(pat,term) -> (pat,makeVarTerm(term))) decls in
	  let vars  = flatten(List.map(fn(_,(_,vars))-> vars) decls) in
	  let letVars = flatten(List.map (fn(pat,_) -> patternVars pat) decls) in
	  let body as (_,bodyVars) = makeVarTerm(body) in
	  let vars = removeDuplicates(vars ++ diff(bodyVars,letVars)) in
	  (Let(decls,body),vars) 
	| LetRec(decls,body,a) -> 
	  let decls = List.map (fn(v,term) -> (v,makeVarTerm(term))) decls in
	  let vars  = flatten(List.map(fn(_,(_,vars))-> vars) decls) in
	  let letVars = List.map (fn(v,_)-> v) decls in
	  let body as (_,bodyVars) = makeVarTerm(body) in
	  let diffVars = diff(bodyVars,letVars) in
	  %let _ = String.writeLine("  bodyVars: "^varsToString(bodyVars)) in
	  %let _ = String.writeLine("  -letVars: "^varsToString(letVars)) in
	  %let _ = String.writeLine("  --------------------------------------") in
	  %let _ = String.writeLine("            "^varsToString(diffVars)) in
	  let vars = removeDuplicates(vars ++ diffVars) in
	  (LetRec(decls,body),vars)
	| Lambda(match,a) -> 
	  let (pat,_,_)::_ = match in
	  %let _ = String.writeLine("  lambda-term, pattern: "^MetaSlangPrint.printPattern(pat)) in
	  let match = map (fn(pat,cond,term)-> (pat,cond,makeVarTerm term)) match in
	  let vars  = flatten(map(fn(_,_,(_,vars))-> vars) match) in
	  let boundVars = flatten(map (fn(pat,_,_)-> patternVars(pat)) match) in
	  let vars = diff(vars,boundVars) in
	  (Lambda(match),vars)
	  
	| Var(v,a) -> (Var(v),[v])
	| Fun(f,s,a) -> (Fun(f,s),[])
	| IfThenElse(t1,t2,t3,a) -> 
	  let t1 as (_,vs1) = makeVarTerm(t1) in
	  let t2 as (_,vs2) = makeVarTerm(t2) in
	  let t3 as (_,vs3) = makeVarTerm(t3) in
	  (IfThenElse(t1,t2,t3),removeDuplicates(vs1 ++ vs2 ++ vs3))

	| Seq(terms,a) -> 
	  let terms = List.map makeVarTerm terms in
	  let vars  = flatten(List.map(fn(_,vs)-> vs) terms) in
	  let vars  = removeDuplicates(vars) in
	  (Seq(terms),vars)
	| Apply(t1,t2,a) -> 
	  let t1 as (_,vs1) = makeVarTerm(t1) in
	  let t2 as (_,vs2) = makeVarTerm(t2) in
	  (Apply(t1,t2),removeDuplicates(vs1 ++ vs2))
	| Record(fields,a) -> 
	  let fields = List.map (fn(id,t)-> (id,makeVarTerm(t))) fields in
	  let vars = flatten(List.map(fn(_,(_,vs))-> vs) fields) in
	  let vars = removeDuplicates(vars) in
	  (Record(fields),vars)
	| Bind(binder,bound,body,a) -> 
	  let body as (_,vs) = makeVarTerm(body) in
	  let vars = diff(vs,bound) in
	  (Bind(binder,bound,body),vars)
	| _ -> System.fail "makeVarTerm"
    %in
	  %let (_,vars) = res in
	  %let _ = String.writeLine("vars: "^varsToString(vars)) in
	  %let _ = String.writeLine("}") in
	  %res

 % Build:
 %
 %    closure: TranslationBuiltIn.makeClosure(name,freeVars)
 % 		   

 def makeClosureOp() = 
     let alpha = mkTyVar "alpha" in
     let beta  = mkTyVar "beta" in
     let gamma = mkTyVar "gamma" in
     let srt1  = mkArrow(mkProduct [alpha,beta],gamma) in
     let srt2  = mkArrow(mkProduct [srt1,alpha],mkArrow(beta,gamma)) in
     
%
% Later change this to:
% mkArrow(mkProduct [srt1,alpha],
%         (Base(Qualified("TranslationBuiltIn","Closure"),[beta,gamma]))) 
%
%
     mkOp(Qualified("TranslationBuiltIn","makeClosure"),srt2)


 def makeUnitClosureOp():Term = 
     let alpha = mkTyVar "alpha" in
     let beta  = mkTyVar "beta"  in
     mkOp(Qualified("TranslationBuiltIn","makeUnitClosure"),
	  mkArrow(mkArrow(alpha,beta),
	          (Base(Qualified("TranslationBuiltIn","Closure"),
			[alpha,beta],noPos))))
			       
%
% (dom sort should be a list of dom sorts corresponding to record/tuple patterns in functions)
%
 def makeClosureApplication(env,name,freeVars,dom,rng) = 
   let qualname = Qualified(env.qName,name) in
   case freeVars
     of [] -> mkOp(qualname,mkArrow(dom,rng))
(**
	 mkApply(makeClosureOp(),
		 mkTuple 
		 [
		   mkArityTuple(mkRecord [])
		 ])
**)
      | [(id,varSrt)] ->
         if ~simulateClosures?
	   then mkOp(qualname, mkArrow(mkProduct [varSrt,dom],rng))	     
	   else mkApply(makeClosureOp(),
			mkTuple [mkOp(Qualified(env.qName,name),
				      mkArrow(mkProduct [varSrt,dom],rng)),
				 mkVar (id,varSrt)])
      | _ ->
       if ~simulateClosures?
	 then
	   mkOp(qualname,
		mkArrow(mkProduct(productSorts(getSpecEnv env,dom)
				  ++ map (fn (_,varSrt) -> varSrt) freeVars),
			rng))
       else      
       let prod = mkTuple(List.map mkVar freeVars) in
       let srt1 = termSortEnv(getSpecEnv(env),prod) in
       let oper = mkOp(qualname, mkArrow(mkProduct [srt1,dom],rng))
       in
       mkApply(makeClosureOp(),
	       mkTuple[oper, ArityNormalize.mkArityTuple(env.spc,prod)])	

 def makeLiftInfo(env,id,name,pat,body,vars) = 
     {ident = id,
      name = name,
      freeVars = vars,
      closure = makeClosureApplication(env,name,vars,patternSort pat,
				       termSortEnv(getSpecEnv(env),body)),
      pattern = pat,
      body = body}

 def insertOper(liftInfo:LiftInfo,{qName,opName,opers,counter,spc}:LLEnv) =
     { 
	opName  = opName,
	qName   = qName,
       	opers   = Map.update(opers,liftInfo.ident,liftInfo),
       	counter = counter,
	spc     = spc
     }

 def actualFreeVars({qName,opName,opers,counter,spc}:LLEnv,vars) =
   %let _ = String.writeLine("actualFreeVars: vars="^varsToString(vars)) in
     let
	def lookup(v as (id,_)) = 
	    case Map.apply (opers, id)
	      of None -> [v]
	       | Some (info) -> info.freeVars
     in 
       let res = removeDuplicates(flatten(List.map lookup vars)) in
       %let _ = String.writeLine("freeVars: "^varsToString(res)) in
       res
  


 def removeBound(variableList,boundVars) = 
     case boundVars 
       of [] -> variableList 
	| (id,_)::bvs -> 
	  let
	     def removeOne(vars) = 
		 case vars
		   of [] -> []
		    | (v as (id2,_))::vs -> 
		      if id2 = id then removeOne(vs) else 
		      Cons(v,removeOne(vs))
	  in
	     removeBound(removeOne(variableList),bvs)

% ensure that the term is a closure
 def ensureClosure(term:Term):Term =
   if ~ simulateClosures? then term
   else
   let closureOp = makeClosureOp() in
   let unitClosureOp = makeUnitClosureOp() in
   case term
     of Apply(t1,t2,_) ->
       if (t1 = closureOp) or (t1 = unitClosureOp) then term
       else mkApply(makeUnitClosureOp(),term)
     |  _            -> mkApply(makeUnitClosureOp(),term)



(*

  Lambda lifting inserts ops with the following sorts:

   op clos : ('a * 'b -> 'c) * 'a -> ('b -> 'c)

 *)


 def lambdaLiftTerm(env,term as (trm,vars)) = 
     case trm of
       | Apply((Lambda(match as _::_),vars1),t) ->
         let (infos1,match) = foldl 
	        (fn((p,t1,trm2 as (t2,vars)),(infos,match)) -> 
		 %let (infos1,t1) = lambdaLiftTerm(env,(t1,[])) in
		 let (infos2,t2) = lambdaLiftTerm(env,trm2) in
		 let match = concat(match,[(p,t1,t2)]) in
		 let infos = infos++infos2 in
		 (infos,match)) ([],[]) match
	 in
	 let (infos2,t2) = lambdaLiftTerm(env,t) in
	 (infos1++infos2,Apply(Lambda(match,noPos),t2,noPos))
	 
(*
Let:

Given Let definition:

let a = body_1(x,y)  and b = body_2(y,z) in body(a,b)

Since names are unique after the renaming 
one can treat the let-declaration sequentially.

After pattern matching we can assume that the patterns 
a and b are always of the form (VarPat(v)).

Given let definition:
     let a = fn pat -> body_a(x,y) in body
 1. Get free variables from body_a to get the form

     let a = (fn (x,y) -> fn pat -> body_a(x,y)) (x,y) in body

 2. Lambda lift body_a

     let a = (fn (x,y) -> fn pat -> body_a_lifted(x,y)) (x,y) in body

 3. Insert association:
     [ a |-> (a_op,(x,y),fn pat -> body_a_lifted(x,y),sortOf_a) ]
    in env.

 4. Recursively lambda lift body(a)

 5. Return with other ops, also (a_op,(x,y),fn pat -> body_a_lifted(x,y),sortOf_a).

Given let definition:
     let a = body_a(x,y) in body
  1. Lambda lift body_a
  2. Recursively lambda lift body
  3. Return let a = body_a_lifted(x,y) in body_lifted

*)
    | Let(decls,body) -> 
      let opName = env.opName in
      let
	 def liftDecl((pat,term as (trm,vars)),(opers,env,decls)) =
	     case (pat,trm)
		of (VarPat((id,srt),_),Lambda([(pat2,cond,body)])) -> 
		   let (opers2,body) = lambdaLiftTerm(env,body) in
		   let name = opName ^ "_" ^ id in
		   let vars = actualFreeVars(env,vars) in
		   let oper = makeLiftInfo(env,id,name,pat2,body,vars) in
		   let env  = insertOper(oper,env) in
		   (cons(oper,opers ++ opers2),env,decls)
		 | _ ->
		   let (opers2,term) = lambdaLiftTerm(env,term) in
		   (opers ++ opers2,env,cons((pat,term),decls))
      in
      let (opers1,env,decls) = List.foldr liftDecl ([],env,[]) decls in
      let (opers2,body) = lambdaLiftTerm(env,body) in
      (opers1 ++ opers2,
       case decls
	 of [] -> body
	  | _  -> Let(decls,body,noPos)) 

(*
Let-rec:

Given Let-rec definition:

let
     def f = fn pat_1 -> body_1(f,g,x,y)
     def g = fn pat_2 -> body_2(f,g,y,z)
in
     body(f,g)

1. Get free variables from body_1 and body_2 to get the form:

  let
     def f = fn (x,y,z) -> fn pat_1 -> body_1(f,g,x,y)
     def g = fn (x,y,z) -> fn pat_2 -> body_2(f,g,y,z)
  in
     body(f,g)

2. Generate associations:

     opers:
     [
      f |-> (f_op,(x,y,z),pat_1,body_1(f,g,x,y)),
      g |-> (g_op,(x,y,z),pat_2,body_2(f,g,y,z))
     ]

   update the environment with these associations    

3. Lambda lift body_1 and body_2.

  let
     def f = fn (x,y,z) -> fn pat_1 -> body_1_lifted(f_op(x,y,z),g_op(x,y,z),x,y)
     def g = fn (x,y,z) -> fn pat_2 -> body_2_lifted(f_op(x,y,z),g_op(x,y,z),y,z)
  in
     body(f,g)

4. Recursively lambda lift body(f,g)

5. Return updated assocations:

     opers:
     [
      f |-> (f_op,(x,y,z),fn pat_1 -> body_1_lifted(f_op(x,y,z),g_op(x,y,z),x,y),sortOf_f_op),
      g |-> (g_op,(x,y,z),fn pat_2 -> body_2_lifted(f_op(x,y,z),g_op(x,y,z),y,z),sortOf_g_op)
     ]

   update the environment with these associations.    

*)
     | LetRec(decls,body) ->
       let opName = env.opName in
%
% Step 1.
% 
       let (free,bound) = 
	   List.foldr (fn((v,(_,vars)),(free,bound))->
		      (vars ++ bound,cons(v,bound))) ([],[]) decls in
       let vars = removeBound(free,bound) in
       let _(* free *) = removeDuplicates free in % unused. side-effect?
       let vars = actualFreeVars(env,vars) in

       % let opers  = env.opers in % unused
%
% Step 2.
% 
       let tmpOpers =
           map (fn(v as (id,srt),(Lambda([(pat,_,body)]),_)) ->
		  let name = opName ^ "_" ^ id in
		  (body,makeLiftInfo(env,id,name,pat,mkTrue()(* Dummy body *),
				     vars))
	         | _ -> System.fail "liftDecl Non-lambda abstracted term") decls
       in
       let env1 = foldr (fn((_,oper),env)-> insertOper(oper,env)) env tmpOpers in
%
% Step 3.
%
       let
	   def liftDecl((realBody,{ident,name,pattern,closure,body,freeVars}),
			opers) = 
	       let (opers2,body) = lambdaLiftTerm(env1,realBody) in
	       let oper = makeLiftInfo(env,ident,name,pattern,body,freeVars) in
%-		  (String.writeLine ("Lift recursive "^MetaSlangPrint.printTerm body);
	       cons(oper,opers ++ opers2)
       in
       let opers1 = List.foldr liftDecl [] tmpOpers in
%
% Step 4.
%
       let (opers2,body) = lambdaLiftTerm(env1,body) in
       (opers1 ++ opers2,body) 

     | Var(id,srt) ->
       (case Map.apply (env.opers, id)
	  of Some (liftInfo) -> 
	    let liftInfoClosure = ensureClosure(liftInfo.closure) in
	    ([],liftInfoClosure)
	  %of Some (liftInfo:LiftInfo) -> ([],mkApply(makeUnitClosureOp(),liftInfo.closure))
	   | None -> ([],(Var((id,srt),noPos)))
       )
%
% If returning a function not taking arguments, then 
% return a closure version of it.
%

     | Fun(f,srt) -> 
       let term = mkFun(f,srt) in
       ([],
	if ~simulateClosures? then term
	else
	let srt = unfoldToArrow(getSpecEnv(env),srt) in
	case srt
	  of (Arrow _) -> mkApply(makeUnitClosureOp(),term)
	   | (TyVar _) -> mkApply(makeUnitClosureOp(),term)
	   | _ -> term
	    )
     | Lambda [(pat,cond,body)] -> 
		%let _ = String.writeLine("lambdaLiftTerm: pattern: " ^ MetaSlangPrint.printPattern(pat)^", vars: "^varsToString(vars)) in
       let (opers,body) = lambdaLiftTerm(env,body) in
       let num = State.!(env.counter) in
       let _ = env.counter State.:= num + 1 in
       let name = env.opName ^ "_internal_" ^ (Nat.toString num) in

       %let _ = String.writeLine("  new oper: "^name) in

       let ident = name ^ "_closure" in
       let vars = actualFreeVars(env,vars) in

       let liftInfo = makeLiftInfo(env,ident,name,pat,body,vars) in

% [MA
% make sure that liftInfo.closure is really a closure
       let liftInfoClosure = ensureClosure(liftInfo.closure) in

       (cons(liftInfo,opers),liftInfoClosure)
       %(cons(liftInfo,opers),mkApply(makeUnitClosureOp(),liftInfo.closure))

     | Lambda match -> System.fail "Irregular lambda abstraction"

     | IfThenElse(t1,t2,t3) -> 
       let (opers1,t1) = lambdaLiftTerm(env,t1) in
       let (opers2,t2) = lambdaLiftTerm(env,t2) in
       let (opers3,t3) = lambdaLiftTerm(env,t3) in
       (opers1 ++ opers2 ++ opers3,(IfThenElse(t1,t2,t3,noPos)))
     | Seq(terms) -> 
       let
	  def liftRec(t,(opers,terms)) = 
	      let (opers2,t) = lambdaLiftTerm(env,t) in
	      (opers ++ opers2,cons(t,terms))
       in
       let (opers,terms) = List.foldr liftRec ([],[]) terms in
       (opers,Seq(terms,noPos))

     | Apply((Lambda [(pat,Fun(Bool true,_,_),body)],vars1),term) -> 
       lambdaLiftTerm(env,
	    (Let([(pat,term)],body),vars ++ vars1))


% Distinguish between pure function application and
% application of closure.
%


     | Apply(t1,t2) -> 
       let (opers2,nt2) = lambdaLiftTerm(env,t2) in
       let (opers1,nt1) = 
	   case t1
	     of (Fun(f,s),_) -> ([],Fun(f,s,noPos))
	      | _ -> lambdaLiftTerm(env,t1)
       in
       let opers = opers1 ++ opers2 in
       (case nt1
	  of (Fun f) ->
	     if ~simulateClosures?
	       then
	       (case t1 of
		  | (Var(id,srt),_) ->
		    (case Map.apply (env.opers, id)
		       of Some {ident,name,freeVars,closure,pattern,body} ->
			  let oldArgs = termToList nt2 in
			  let newArgs = map mkVar freeVars in
			  (opers,mkApply(nt1,mkTuple(oldArgs ++ newArgs)))
			| _ -> (opers,mkApply(nt1,nt2)))
		  | _ -> (opers,mkApply(nt1,nt2)))
	     else (opers,mkApply(nt1,nt2))	     
	   | _ ->
	     if ~simulateClosures?
	       then (opers,mkApply(nt1,nt2))
	     else 
	     let argument = mkTuple [nt1,toAny(nt2)] in
	     let alpha    = mkTyVar "alpha" in
	     let beta     = mkTyVar "beta" in
	     let fnSrt    = mkArrow(alpha,beta) in
	     let srt      = mkArrow(mkProduct [fnSrt,alpha],beta) in
	     let fnOp     = mkOp(Qualified("TranslationBuiltIn","applyClosure"),
				 srt) in
	     (opers,mkApply(fnOp,argument))
       )
     | Record fields -> 
       let
	  def liftRec((id,t),(opers,fields)) = 
	      let (opers2,t) = lambdaLiftTerm(env,t) in
	      (opers ++ opers2,cons((id,t),fields))
       in
       let (opers,fields) = List.foldr liftRec ([],[]) fields in
       (opers,(Record(fields,noPos)))
     | Bind(binder,bound,body) -> 
       System.fail "Unexpected binder"
     | _ -> System.fail "Unexpected term"

(*
 spec TranslationBuiltIn = 

   sort Any[T] = T

 end-spec
*)

(***
To take care of castings we introduce:

sort Any[T] = | Any  T
op fromAny : [T] Any[T] -> T
op toAny   : [T] T -> Any[T]

% How it would look like with quoting:

def mkAny srt = Sort `Any[^(srt)]`
def fromAny   = Term `TranslationBasic.fromAny`
def toAny     = Term `TranslationBasic.toAny` 


**)

% How it looks like without quoting:


 def mkAny srt = if simulateClosures?
                  then mkBase(Qualified("TranslationBuiltIn","Any"),[srt])
		  else srt
 def fromAny() = 
     let alpha = mkTyVar "alpha" in
     let any   = mkAny alpha in
     let srt   = mkArrow(any,alpha) in
     mkOp(Qualified("TranslationBuiltIn","fromAny"),srt)
 def toAny(t) =
   if ~simulateClosures? then t
     else
     let alpha = mkTyVar "alpha" in 
     let any   = mkAny alpha in
     let srt   = mkArrow(alpha,any) in
     mkApply(mkOp(Qualified("TranslationBuiltIn","toAny"),srt),t)

 op abstractName: LLEnv * String * FreeVars * Pattern * Term -> OpInfo
 def abstractName(env,_(* name *),freeVars,pattern,body) =
   if ~simulateClosures?
     then
       let oldPatLst = patternToList pattern in
       let newPattern = mkTuplePat(oldPatLst ++ map mkVarPat freeVars) in 
       ([], % TODO: Real names
	 Nonfix,
	 ([],mkArrow(patternSort newPattern,
		     termSortEnv(getSpecEnv(env),body))),
	 [([],mkLambda(newPattern,body))]
	)
     else
     let varSort = mkProduct (List.map (fn(_,srt)-> srt) freeVars) in
     let closureVar = ("closure-var",mkAny varSort) in
     let closureArg = mkApply(fromAny(),mkVar closureVar) in
     let closureVarPat = mkVarPat(closureVar) in
     let newPattern =
	 if null freeVars
	    then pattern
	 else 
 	 case pattern
	   of (VarPat _) -> (RecordPat([("1",pattern),("2",closureVarPat)],noPos))
	    | (RecordPat (fields,_)) -> 
	      (RecordPat (fields ++ 
			  [(Nat.toString(1+(length fields)),closureVarPat)],noPos))
     in	
     let 
	 def mkProject((id,srt),n) = 
	     (mkVarPat((id,srt)),
	      mkApply((Fun(Project(Nat.toString n),mkArrow(varSort,srt),noPos)),
		       closureArg))
     in
     let newBody = 
 	 case freeVars
	   of [] -> body
	    | [v] -> mkLet([(mkVarPat v,closureArg)],body)
	    | _ -> 
	      let (decls,n) = 
		  List.foldl 
		    (fn(v,(decls,n))->
			(cons(mkProject(v,n),decls),n + 1)) ([],1) freeVars
	      in
	      mkLet(decls,body)
     in	
	([], % TODO: Real names
	 Nonfix,
	 ([],mkArrow(patternSort newPattern,
		     termSortEnv(getSpecEnv(env),body))),
	 [([],mkLambda(newPattern,newBody))]
	)

op getSpecEnv: LLEnv -> Spec
def getSpecEnv(env) =
  env.spc			% Better be defined

(*
 def abstractVars(ident:String,freeVars,closure):Option OpInfo = 
     case freeVars 
       of [] -> None
	| [v as (_,dom)] ->
	  Some(Nonfix,([],mkArrow(dom,termSort(closure))),
		      Some(Lambda [(mkVarPat(v),mkTrue(),closure)]))
	| _ -> 
	  let pat = mkTuplePat(List.map mkVarPat freeVars) in
	  Some(Nonfix,([],mkArrow(patternSort pat,termSort(closure))),
		      Some(Lambda [(pat,mkTrue(),closure)]))

*)

 op  varsToString: List Var -> String
 def varsToString(vars) = (List.foldl (fn(v as (id,srt),s) ->
				       s ^ (if s = "[" then ""
					     else " ")
				         ^ id ^ ":" ^ printSort(srt))
			   "[" vars)^"]"

 def lambdaLift(spc) = 
     let counter = Ref 1 : Ref Nat in
     let def mkEnv(qname,name) =
           {opName = name,
	    qName  = qname,
	    spc = spc,
	    counter = counter,
	    opers = Map.emptyMap} in
     let
       def insertOpers(opers,qname,spc) = 
	 case opers
	   of [] -> spc
	    | {name,ident,pattern,freeVars,body,closure}::opers -> 
%%		  let spc = abstractVars(ident,freeVars,closure) in
	      let (nms, f,s,t)
	         = abstractName(mkEnv(qname,name), name, freeVars, pattern, body) in
	      %let (_,srt) = s in
	      %let _ = String.writeLine("addop "^name^":"^printSort(srt)) in
	      % TODO: Real names
	      let spc = addNewOp(Qualified(qname,name), f, s, t, spc) in
	      insertOpers(opers,qname,spc)
   in
     let 
       def doOp(qname,name,(names, fixity, (tvs,srt), defs),spc) = 
	 %let _ = String.writeLine("lambdaLift \""^name^"\"...") in
	 case defs
	   of [] ->
	     addNewOp (Qualified(qname,name), fixity, (tvs, srt), [], spc)
	    | [(def_tvs,Lambda([(pat,cond,term)],a))] -> 
	     let env = mkEnv(qname,name) in
	     let term = makeVarTerm(term) in
	     let (opers,term) = lambdaLiftTerm(env,term) in
	     let term = Lambda([(pat,cond,term)],a) in
	     %-let _ = String.writeLine("addop "^name^":"^printSort(srt)) in
	     let spc = addNewOp(Qualified(qname,name),fixity,(tvs,srt),[([],term)],
				spc)
	     in
	     insertOpers(opers,qname,spc)
	    | [(def_tvs,term)] -> 
	     let env = mkEnv(qname,name) in
	     let term = makeVarTerm(term) in
	     let (opers,term) = lambdaLiftTerm(env,term) in
	     %-let _ = String.writeLine("addop "^name^":"^printSort(srt)) in
	     let spc = addNewOp(Qualified(qname,name),fixity,(tvs,srt),[([],term)],
				spc)
	     in
	     insertOpers(opers,qname,spc)
   in
     let ops = spc.ops in
     let spc = 
	 { importInfo = spc.importInfo,
	   sorts = spc.sorts,
	   ops = emptyAQualifierMap,
	   properties = spc.properties
	 }
     in
     foldriAQualifierMap doOp spc ops

 op addNewOp :
    fa (a) QualifiedId * Fixity * ASortScheme a * List (ATermScheme a) * ASpec a
        -> ASpec a

 def addNewOp (new_op_name as Qualified(qualifier,id),
	       new_fixity,new_sort_scheme,new_defs,old_spec) =
   let newOps = insertAQualifierMap(old_spec.ops,qualifier,id,
				    ([new_op_name],
				     new_fixity,new_sort_scheme,new_defs))
   in
   let spc = setOps (old_spec, newOps) in
   addLocalOpName(spc, new_op_name)

endspec

