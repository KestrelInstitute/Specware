
\section{Rewrite rule control}

\begin{spec}
spec MetaSlangRewriter
 import /Library/Legacy/DataStructures/LazyList
 import DeModRewriteRules
 
 sort Context = HigherOrderMatching.Context

 op traceRewriting : Nat 
 def traceRewriting = 2

 def mkVar = HigherOrderMatching.mkVar     

%%
%% Application of set of rewrite rules
%%

\end{spec}
\begin{itemize}
\item 
	applyRewrites: 
	Application of rewrites to subterm.
%\item
%	matchEquality: 
%	Directly try to match left and right hand side of
%	an equality using the matcher.
\end{itemize}

\begin{spec}
 op applyRewrites : 
    Context * List RewriteRule * Subst 
       -> List Var * MS.Term 
	   -> LazyList (MS.Term * (Subst * RewriteRule * List RewriteRule))


 op applyRewrite  : Context * RewriteRule * Subst * MS.Term -> List Subst 

 def applyRewrite(context,rule,subst,term) = 
     let lhs = rule.lhs in
     filter 
	(fn subst -> completeMatch(lhs,subst))
	   (matchPairs(context,subst,stackFromList [(lhs,term)]))
     
 def applyRewrites(context,rules,subst) (boundVars,term) = 
     let context = setBound(context,boundVars) in
     mapEach 
     (fn (first,rule,rest) -> 
	 let substs = applyRewrite(context,rule,subst,term) in
	 if null substs
	    then emptyList
	 else
	 let rule1 = freshRule (context,rule) in
	 let rules = rest ++ first ++ [rule1] in
         fromList
	    (List.map (fn s -> (dereferenceAll s rule.rhs,(s,rule,rules))) substs)) 
     rules


 def applyDemodRewrites(context,subst) (boundVars,term,demod) = 
     let context = setBound(context,boundVars)  in
     let rules = Demod.getRules(demod,term)     in
     (mapFlat 
        (fn rule -> 
	    let substs = applyRewrite(context,rule,subst,term) in
	    fromList
	      (List.map (fn s -> (rule.rhs,(s,rule,demod))) substs)) 
        rules)
     @@ (fn () -> standardSimplify(term,subst,demod))


 def evalRule : RewriteRule = 
     { 
	name     = "Eval",
	freeVars = [],
	tyVars = [],
	condition = None,
	lhs   = mkVar(1,TyVar("''a",noPos)),
	rhs   = mkVar(2,TyVar("''a",noPos))
     } 

 def standardSimplify(term,subst,demod) =
   case tryEvalOne term of
     | Some eTerm -> unit (eTerm, (subst,evalRule,demod))
     | None -> Nil

 op assertRules: Context * MS.Term * String -> List RewriteRule
 def assertRules (context,term,desc) =
   let (freeVars,n,S,formula) =
     bound(Forall:Binder,0,term,[],[]) in
   let (condition,fml) = 
	case formula of
	  | Apply(Fun(Implies, _,_), Record([(_,M),(_,N)], _),_) -> 
	     (Some (substitute(M,S)),N)
	  | _ -> (None,formula)
   in
   case fml of
     | Apply(Fun(Not, _,_), p,_) ->
        let rhs = mkFalse() in
	if p = rhs then []
	else
        [freshRule(context,
		   {name      = desc,   condition = condition,
		    lhs       = p,      rhs       = mkFalse(),
		    tyVars    = [],     freeVars  = freeVars})]
      | _ ->
	let rhs = mkTrue() in
	if fml = rhs then []
	else
        [freshRule(context,
		   {name      = desc,   condition = condition,
		    lhs       = fml,    rhs       = mkTrue(),
		    tyVars    = [],     freeVars  = freeVars})]
   

 def negate term =
   case term of
     | Apply (Not, p,                        _) -> p
     | Apply (Or,  Record([(_,M),(_,N)], _), _) -> Utilities.mkAnd(negate M,negate N)
     | _ -> mkNot term

 (* Unnecessary as equality can be done as a built-in rule
     See spec builtInRewrites
 op matchEquality : 
    fa(rules) Context * rules * Subst 
       -> List Var * Term * Term -> LazyList (Subst * RewriteRule * rules)

 def equalityRule : RewriteRule = 
     { 
	name     = "=",
	freeVars = [(1,TyVar "''a")],
	tyVars = ["''a"],
	condition = None,
	lhs   = mkVar(1,TyVar "''a":Sort),
	rhs   = mkVar(2,TyVar "''a":Sort)
     } 


% Disambiguate between HigerOrderMatchingMetaSlang and MetaSlang
 def mkVar = HigherOrderMatchingMetaSlang.mkVar     

 def matchEquality (context,rules,subst) (boundVars,M,N) = 
     let context = setBound(context,boundVars) in
     let substs = matchPairs(context,subst, stackFromList [(M,N)]) in
     fromList (List.map (fn s -> (s,equalityRule,rules)) substs)
 *)
\end{spec}

%%
%% We will have to rename variables in used rewrite rules in order to 
%% use the triangular substitution to dereference terms (and not just apply
%% the obtained substitution directly)
%%  

\subsection{An inner-most rewriting strategy}

 Rewrite subterm using rewrite rules represented abstractly as a function
 returning a lazy list of terms and arbitrary other information.
 In its usage this information would consist of a substitution and  
 rewrite rule (with name and optional condition).
 
 Assumption: The rewriter does not attempt matching 
 directly upon meta variables. Directly true, 
 when term is always rigid.

\begin{spec}

 sort Rewriter a = List Var * MS.Term * Demod RewriteRule -> LazyList (MS.Term * a) 
 %sort Matcher  a = List Var * Term * Term -> LazyList a
 sort Strategy   = | Innermost | Outermost

 op rewriteTerm    : fa(a) {strategy:Strategy,rewriter:Rewriter a,context:Context}
                           * List Var * MS.Term * Demod RewriteRule
                           -> LazyList (MS.Term * a)
 op rewriteSubTerm : fa(a) {strategy:Strategy,rewriter:Rewriter a,context:Context}
                           * List Var * MS.Term * Demod RewriteRule
                           -> LazyList (MS.Term * a)

 def rewriteTerm (solvers as {strategy,rewriter,context},boundVars,term,rules) = 
     case strategy
       of Innermost -> 
          rewriteSubTerm(solvers,boundVars,term,rules) 
          @@
	  (fn () -> rewriter (boundVars,term,rules))
        | Outermost -> 
	  rewriter (boundVars,term,rules) 
	  @@
	  (fn () -> rewriteSubTerm(solvers,boundVars,term,rules))

 def rewriteSubTerm (solvers as {strategy,rewriter,context},boundVars,term,rules) = 
     (case term of
        | Apply(Fun(Not,s,_),arg,b) ->  
	   LazyList.map 
		(fn (arg,a) -> (Apply(Fun(Not,s,b), arg, b),a)) 
		(rewriteTerm(solvers,boundVars,arg,rules))
        | Apply(Fun(And,s,_),Record([(l1,M),(l2,N)], _),b) -> 
	   LazyList.map 
		(fn (N,a) -> (Apply(Fun(And,s,b),
				    Record([(l1,M),(l2,N)],b),b),a)) 
		(rewriteTerm(solvers,boundVars,N,rules)) @@
	   (fn () -> 
	   LazyList.map 
		(fn (M,a) -> (Apply(Fun(And,s,b),Record([(l1,M),(l2,N)],b),b),a)) 
		(rewriteTerm(solvers,boundVars,M,rules))) 
        | Apply(Fun(Or,s,_),Record([(l1,M),(l2,N)], _),b) -> 
	   LazyList.map 
		(fn (N,a) -> (Apply(Fun(Or,s,b),
				    Record([(l1,M),(l2,N)],b),b),a)) 
		(rewriteTerm(solvers,boundVars,N,rules)) @@
	   (fn () -> 
	   LazyList.map 
		(fn (M,a) -> (Apply(Fun(Or,s,b),Record([(l1,M),(l2,N)],b),b),a)) 
		(rewriteTerm(solvers,boundVars,M,rules))) 
        | Apply(Fun(Implies,s,_),Record([(l1,M),(l2,N)], _),b) -> 
	   LazyList.map 
		(fn (N,a) -> (Apply(Fun(Implies,s,b),
				    Record([(l1,M),(l2,N)],b),b),a)) 
		(rewriteTerm(solvers,boundVars,N,rules)) @@
	   (fn () -> 
	   LazyList.map 
		(fn (M,a) -> (Apply(Fun(Implies,s,b),Record([(l1,M),(l2,N)],b),b),a)) 
		(rewriteTerm(solvers,boundVars,M,rules))) 
        | Apply(Fun(Iff,s,_),Record([(l1,M),(l2,N)], _),b) -> 
	   LazyList.map 
		(fn (N,a) -> (Apply(Fun(Iff,s,b),
				    Record([(l1,M),(l2,N)],b),b),a)) 
		(rewriteTerm(solvers,boundVars,N,rules)) @@
	   (fn () -> 
	   LazyList.map 
		(fn (M,a) -> (Apply(Fun(Iff,s,b),Record([(l1,M),(l2,N)],b),b),a)) 
		(rewriteTerm(solvers,boundVars,M,rules))) 
        | Apply(Fun(Equals,s,_),Record([(l1,M),(l2,N)], _),b) -> 
	   LazyList.map 
		(fn (N,a) -> (Apply(Fun(Equals,s,b),
				    Record([(l1,M),(l2,N)],b),b),a)) 
		(rewriteTerm(solvers,boundVars,N,rules)) @@
	   (fn () -> 
	   LazyList.map 
		(fn (M,a) -> (Apply(Fun(Equals,s,b),Record([(l1,M),(l2,N)],b),b),a)) 
		(rewriteTerm(solvers,boundVars,M,rules))) 
        | Apply(Fun(NotEquals,s,_),Record([(l1,M),(l2,N)], _),b) -> 
	   LazyList.map 
		(fn (N,a) -> (Apply(Fun(NotEquals,s,b),
				    Record([(l1,M),(l2,N)],b),b),a)) 
		(rewriteTerm(solvers,boundVars,N,rules)) @@
	   (fn () -> 
	   LazyList.map 
		(fn (M,a) -> (Apply(Fun(NotEquals,s,b),Record([(l1,M),(l2,N)],b),b),a)) 
		(rewriteTerm(solvers,boundVars,M,rules))) 
	 | Apply(M,N,b) -> 
	   LazyList.map 
		(fn (N,a) -> (Apply(M,N,b),a)) 
		(rewriteTerm(solvers,boundVars,N,rules)) @@
	   (fn () -> 
	   LazyList.map 
		(fn (M,a) -> (Apply(M,N,b),a)) 
		(rewriteTerm(solvers,boundVars,M,rules)))
	 | Record(fields,b) -> 
	   mapEach 
  	    (fn (first,(label,M),rest) -> 
		rewriteTerm(solvers,boundVars,M,rules) >>= 
		(fn (M,a) -> unit(Record(first ++ [(label,M)] ++ rest,b),a)))
	   fields
         | Lambda(lrules,b) -> 
	   mapEach 
	     (fn (first,(pat,cond,M),rest) -> 
		rewriteTerm(solvers,(boundVars ++ patternVars pat),M,rules) >>=
		(fn (M,a) -> unit(Lambda (first ++ [(pat,cond,M)] ++ rest,b),a)))
	   lrules
         | Bind(qf,vars,M,b) -> 
	   LazyList.map (fn (M,a) -> (Bind(qf,vars,M,b),a))
		(rewriteTerm(solvers,boundVars ++ vars,M,rules))
	 | IfThenElse(M,N,P,b) -> 
   	   LazyList.map 
		(fn (M,a) -> (IfThenElse(M,N,P,b),a)) 
		(rewriteTerm(solvers,boundVars,M,rules)) @@
	   (fn () -> 
	   LazyList.map 
		(fn (N,a) -> (IfThenElse(M,N,P,b),a)) 
		(rewriteTerm(solvers,boundVars,N,
			     addDemodRules(assertRules(context,M,"if then"),rules)))) @@
	   (fn () -> 
	   LazyList.map 
		(fn (P,a) -> (IfThenElse(M,N,P,b),a)) 
		(rewriteTerm(solvers,boundVars,P,
			     addDemodRules(assertRules(context,negate M,"if else"),rules))))
	 | _ -> Nil)

\end{spec}


\subsection{Trace utilities}

\begin{spec}

 op printTerm: Nat * MS.Term -> String
 def printTerm (indent,term) = 
     let indent   = PrettyPrint.blanks indent 					 in
     let context  = initialize(asciiPrinter,false) in 
     let argument = ([],Top:ParentTerm) 				 in
     let termPP   = ppTerm context argument term 		 in
     let termPP   = PrettyPrint.prettysNone [PrettyPrint.string indent,termPP]   in
     PrettyPrint.toString(PrettyPrint.format(60,termPP))

 op traceTerm : Context * MS.Term * Subst -> ()
 def traceTerm(context:Context,term,(* subst *)_) = 
     if traceRewriting > 1 then 
     % if context.trace then 
	 (String.writeLine(printTerm(3 + ! context.traceIndent,term));
	  ()
	  ) 
     else ()

 def traceRule(context:Context,rule:RewriteRule) = 
     % if context.trace then
     if traceRewriting > 0 then 
	let depth = Nat.toString(! context.traceDepth) in
	(String.toScreen (PrettyPrint.blanks (! context.traceIndent));
	 String.writeLine("=  { "^depth^": "^ rule.name^" }"))
     else ()

\end{spec}

 Check condition of conditional rewrite rule

\begin{spec}

%%
%% Check that all variables in a term are bound by the substitution.
%%

 def completeMatch(term,subst:Subst) =
     let S = subst.2 in
     let 
	 def loop(term:MS.Term):Boolean = 
	     case term
	       of Fun(top,srt,_) -> true
	        | Var((id,srt), _)  -> true
	        | Let(decls,bdy,_) -> 
	          all (fn (_,M) -> loop M) decls & loop bdy
	        | LetRec(decls,bdy,_) -> 
	          all (fn (_,M) -> loop M) decls & loop bdy
	        | Record(row, _) -> 
	          all (fn (_,M) -> loop M) row
	        | IfThenElse(t1,t2,t3,_) -> loop t1 & loop t2 & loop t3
	        | Lambda(match,_) -> 
	          all  (fn (_,_,M) -> loop M) match
                | Bind(bnd,vars,trm,_) -> loop trm
	        | Apply(t1,t2,_) -> 
	          (case isFlexVar?(term) 
		     of Some n -> NatMap.inDomain(S,n) 
		      | None -> loop t1 & loop t2)
	        | Seq(terms,_) -> all loop terms
     in
     loop term

 sort History = List (RewriteRule * MS.Term * Subst)

 op historyRepetition: History -> Boolean
 def historyRepetition = 
     fn (_,term1,_)::(_,term2,_)::_ -> term1 = term2
      | _ -> false

 op rewriteRecursive : 
    Context * List Var * RewriteRules * MS.Term -> LazyList (History)

 op rewriteRecursivePre : 
    Context * List Var * DemodRewriteRules * MS.Term -> LazyList (History)


%%
%% Apply unconditional rewrite rules using inner-most strategy.
%% Apply conditional rewrite rules using outer-most strategy.
%%

 def rewriteRecursive(context,boundVars,rules,term) = 
     let rules = {unconditional = addDemodRules(rules.unconditional,Demod.empty),
		  conditional   = addDemodRules(rules.conditional,Demod.empty)}
     in rewriteRecursivePre(context,boundVars,rules,term)

 def rewriteRecursivePre(context,boundVars,rules,term) = 
   let	
      def rewritesToTrue(rules,term,subst,history): Option Subst = 
	  case rewriteRec(rules,subst,term,history,false) : LazyList History
	    of Nil -> if term = mkTrue() then Some subst else None
	     | Cons((_,t,subst)::history,b) -> 
	       if t = mkTrue() then Some subst else None
	     | Cons([],_) -> None

      def solveCondition(rules,rule,subst,history,solveCond) : Option Subst = 
	case rule.condition of
	   | None -> 
	     (traceRule(context,rule);
	      Some subst)
	   | Some cond ->
	if solveCond & completeMatch(rule.lhs,subst) then 
	    let traceIndent = ! context.traceIndent in
	    let res = if traceRewriting > 0 then
	      (context.traceIndent := traceIndent + 3;
	      String.toScreen ("=  "^PrettyPrint.blanks traceIndent^"{ "); 
	      String.writeLine (Nat.toString(! context.traceDepth)^" : "^rule.name);
%%              printSubst subst;
	      context.traceDepth := 0;
	      rewritesToTrue(rules,cond,subst,history))
	    else 
	      rewritesToTrue(rules,cond,subst,history) in
	    if traceRewriting > 0 then
	      (context.traceIndent := traceIndent;
	       String.writeLine ("   "^PrettyPrint.blanks traceIndent ^"}");
	       res)
	    else
	       res
	else None

      def rewriteRec({unconditional,conditional},subst,term,history,solveCond) =
	let _ = traceTerm(context,term,subst)     in
	let traceDepth = ! context.traceDepth + 1 in
	let 
	    def rewrite(strategy,rules) =
		rewriteTerm 
		  ({strategy = strategy,
		    rewriter = applyDemodRewrites(context,subst),
		    context = context},
		   boundVars,term,rules)     
	in
	if historyRepetition(history)
	    then unit (tl history)
	else
	% let rews = (rewrite(Innermost:Strategy,unconditional) >>= 
	let rews = (rewrite(Outermost:Strategy,unconditional) >>= 
		    (fn (term,(subst,rule,rules)) ->  
			unit (term,(subst,rule,
				    {unconditional = unconditional,
				     conditional = conditional}))) 
		    @@
		    (fn () -> 
		     rewrite(Outermost:Strategy,conditional) >>= 
		     (fn (term,(subst,rule,rules)) ->  
			unit (term,(subst,rule,
				    {conditional = conditional,
				     unconditional = unconditional})))))
	in
	case rews
	  of Nil -> unit history
	   | _ -> 
	rews >>=
	(fn (term,(subst,rule,rules)) -> 
	    (context.traceDepth := traceDepth;
	     case solveCondition(rules,rule,subst,history,solveCond)
	       of Some subst -> 
		 (context.traceDepth := traceDepth;
		  let term = dereferenceAll subst term in
		  let term = renameBound term in
		  (rewriteRec(rules,emptySubstitution,term,
			      cons((rule,term,subst),history),
			      solveCond)))
	       | None -> unit history))
   in
      let term = dereferenceAll emptySubstitution term in
      rewriteRec(rules,emptySubstitution,term,[],true)

 op rewriteOnce : 
    Context * List Var * RewriteRules * MS.Term -> List MS.Term

%%
%% Apply unconditional rewrite rules using outer-most strategy
%%
 def rewriteOnce(context,boundVars,rules,term) = 
     let unconditional = Demod.addRules(List.map (fn rl -> (rl.lhs,rl)) 
						rules.unconditional,Demod.empty) in
     (* unused...
     let conditional   = Demod.addRules(List.map (fn rl -> (rl.lhs,rl)) 
						rules.conditional,Demod.empty)  in
     *)

%    let {unconditional,conditional} = rules in
     let subst = emptySubstitution in
     let term = dereferenceAll emptySubstitution term in
     let rews = rewriteTerm
		 ({strategy = Innermost: Strategy,
		   rewriter = applyDemodRewrites(context,emptySubstitution),
		   context = context},
		  boundVars,term,unconditional)
     in
     let rews = LazyList.toList rews in
     List.map (fn (newTerm,(subst,rule,rules)) -> 
		  dereferenceAll subst newTerm) rews

	  
end-spec
\end{spec}

\subsection{Discussion}

\begin{itemize}
\item This allows to use rewriting as abstract execution. 
      What about compiled forms? A la type based partial evaluation forms, or
      unboxing analysis?

      Code generation should generate code of the form
      \begin{verbatim}
      (defun f (x) 
        (let ((x-unboxed (unbox x)))
             (if (boxed? x)
                 (box (cons :|Apply| AST-for-symbol-f x-unboxed))
	      (unboxed (standard-code-for-f x-unboxed)))))
      \end{verbatim}
\item Implement the boxification as a Spec to Spec transformation that allows
      to reuse one code generator.
      \begin{verbatim}
        sort Box a = | Boxed Term | UnBoxed a
        op  boxifySpec : Spec -> Spec
        op  boxifyTerm : Term -> Term
        op  boxifySort : Sort -> Sort
            
        boxifyDef(def f = fn x -> body) = 
            def f = fn Boxed x -> Boxed('Apply(f,x)) | UnBoxed x -> boxifyTerm body

        boxifyTerm(Apply(f,g)) = 
            case f
              of Boxed f -> Boxed('Apply(f,'g))
               | Unboxed f -> 
            case g
              of Unboxed g -> Apply(f,g)
               | Boxed g -> Boxed('Apply(f,g))

      \end{verbatim}
      
\item Extend partial evaluation/boxing format with calls to rewrite engine, or
      interleave these steps.

\end{itemize}
