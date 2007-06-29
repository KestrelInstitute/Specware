
(* Rewrite rule control *)

MetaSlangRewriter qualifying spec 
 import /Library/Legacy/DataStructures/LazyList
 import DeModRewriteRules
 
 type Context = HigherOrderMatching.Context

 type TermPredicate = MS.Term * MS.Term -> Boolean

 op traceRewriting : Nat 
 def traceRewriting = 0

 def mkVar = HigherOrderMatching.mkVar     

%%
%% Application of set of rewrite rules
%%

(*
	applyRewrites: 
	Application of rewrites to subterm.
%	matchEquality: 
%	Directly try to match left and right hand side of
%	an equality using the matcher.
*)

 op applyRewrites : 
    Context * List RewriteRule * Subst 
       -> List Var * MS.Term 
	   -> LazyList (MS.Term * (Subst * RewriteRule * List RewriteRule))

 op applyRewrite(context: Context, rule: RewriteRule, subst: Subst, term: MS.Term): List Subst = 
   let lhs = rule.lhs in
   filter (fn subst -> completeMatch(lhs,subst))
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
	      (map (fn s -> (dereferenceAll s (renameBoundVars(rule.rhs,boundVars)),
                             (s,rule,rules)))
                 substs)) 
       rules


 op applyDemodRewrites(context: Context, subst: Subst)
                      (boundVars: List Var, term: MS.Term, demod: Demod RewriteRule)
                      : LazyList(MS.Term * (Subst * RewriteRule * Demod RewriteRule))  = 
   let context = setBound(context,boundVars)  in
   let spc     = context.spc                  in
   let rules = Demod.getRules(demod,term)     in
   (mapFlat 
      (fn rule -> 
          let substs = applyRewrite(context,rule,subst,term) in
          fromList
            (map (fn s -> (renameBoundVars(rule.rhs,boundVars),(s,rule,demod))) substs)) 
      rules)
   @@ (fn () -> standardSimplify spc (term,subst,demod))


 def evalRule : RewriteRule = 
     { 
	name     = "Eval",
	freeVars = [],
	tyVars = [],
	condition = None,
	lhs   = mkVar(1,TyVar("''a",noPos)),
	rhs   = mkVar(2,TyVar("''a",noPos))
     } 

 def standardSimplify spc (term,subst,demod) =
   case tryEvalOne spc term of
     | Some eTerm ->
       % let _ = writeLine("EvalOne:\n"^printTerm term^"\nTo:\n"^printTerm eTerm) in
       unit (eTerm, (subst,evalRule,demod))
     | None -> Nil

 op assertRules: Context * MS.Term * String -> List RewriteRule
 def assertRules (context,term,desc) =
   let (freeVars,n,S,formula) = bound(Forall,0,term,[],[]) in
   let (condition,fml) = 
	case formula of
	  | Apply(Fun(Implies, _,_), Record([(_,M),(_,N)], _),_) -> 
	     (Some (substitute(M,S)),N)
	  | _ -> (None,formula)
   in
   case fml of
     | Apply(Fun(Not, _,_), p,_) ->
       if falseTerm? p then []
	else
        [freshRule(context,
		   {name      = desc,   condition = condition,
		    lhs       = p,      rhs       = falseTerm,
		    tyVars    = [],     freeVars  = freeVars})]
      | Apply(Fun(Equals,_,_),Record([(_,e1),(_,e2)], _),_) | evalConstant? e2 \_rightarrow
        [freshRule(context,
		   {name      = desc,   condition = condition,
		    lhs       = e1,     rhs       = e2,
		    tyVars    = [],     freeVars  = freeVars})]
      | Apply(Fun(Equals,_,_),Record([(_,e1 as Var _),(_,e2)], _),_) \_rightarrow
        [freshRule(context,
		   {name      = desc,   condition = condition,
		    lhs       = e2,     rhs       = e1,
		    tyVars    = [],     freeVars  = freeVars})]
      | _ ->
	if trueTerm? fml then []
	else
        [freshRule(context,
		   {name      = desc,   condition = condition,
		    lhs       = fml,    rhs       = trueTerm,
		    tyVars    = [],     freeVars  = freeVars})]
   

 op addPatternRestriction(context: Context, pat: Pattern, rules: Demod RewriteRule): Demod RewriteRule =
   case pat of
     | RestrictedPat(_,condn,_) ->
       addDemodRules(assertRules(context,condn,"Restriction"),rules)
     | _ -> rules

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
	lhs   = mkVar(1,TyVar "''a"),
	rhs   = mkVar(2,TyVar "''a")
     } 


% Disambiguate between HigerOrderMatchingMetaSlang and MetaSlang
 def mkVar = HigherOrderMatchingMetaSlang.mkVar     

 def matchEquality (context,rules,subst) (boundVars,M,N) = 
     let context = setBound(context,boundVars) in
     let substs = matchPairs(context,subst, stackFromList [(M,N)]) in
     fromList (List.map (fn s -> (s,equalityRule,rules)) substs)
 *)

%%
%% We will have to rename variables in used rewrite rules in order to 
%% use the triangular substitution to dereference terms (and not just apply
%% the obtained substitution directly)
%%  


(* An inner-most rewriting strategy

 Rewrite subterm using rewrite rules represented abstractly as a function
 returning a lazy list of terms and arbitrary other information.
 In its usage this information would consist of a substitution and  
 rewrite rule (with name and optional condition).
 
 Assumption: The rewriter does not attempt matching 
 directly upon meta variables. Directly true, 
 when term is always rigid.

*)

 type Rewriter a = List Var * MS.Term * Demod RewriteRule -> LazyList (MS.Term * a) 
 %type Matcher  a = List Var * Term * Term -> LazyList a
 type Strategy   = | Innermost | Outermost

 op rewriteTerm    : [a] {strategy:Strategy,rewriter:Rewriter a,context:Context}
                           * List Var * MS.Term * Demod RewriteRule
                           -> LazyList (MS.Term * a)
 op rewriteSubTerm : [a] {strategy:Strategy,rewriter:Rewriter a,context:Context}
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
	   LazyList.map (fn (N,a) -> (Apply(M,N,b),a)) 
             (rewriteTerm(solvers,boundVars,N,rules))
           @@ (fn () -> 
                 LazyList.map (fn (M,a) -> (Apply(M,N,b),a)) 
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
		rewriteTerm(solvers,(boundVars ++ patternVars pat),M,
                            addPatternRestriction(context,pat,rules))
                >>=
		(fn (M,a) -> unit(Lambda (first ++ [(pat,cond,M)] ++ rest,b),a)))
	     lrules
         | Let(binds,M,b) ->
           mapEach (fn (first,(pat,N),rest) ->
                      rewriteTerm(solvers,boundVars,N,rules) >>=
                      (fn (N,a) -> unit(Let(first ++ [(pat,N)] ++ rest,M,b),a)))
             binds
           @@ (fn () ->
                 let let_vars = flatten (map (fn (pat, _) -> patternVars pat) binds) in
                 LazyList.map (fn (M,a) -> (Let(binds,M,b),a)) 
                   (rewriteTerm(solvers,boundVars ++ let_vars,M,rules)))
         | LetRec(binds,M,b) ->
           let letrec_vars = map(fn (v, _) -> v) binds in
           let boundVars = boundVars ++ letrec_vars in
           mapEach (fn (first,(v,N),rest) ->
                      rewriteTerm(solvers,boundVars,N,rules) >>=
                      (fn (N,a) -> unit(LetRec(first ++ [(v,N)] ++ rest,M,b),a)))
             binds
           @@ (fn () ->
                 LazyList.map (fn (M,a) -> (LetRec(binds,M,b),a)) 
                   (rewriteTerm(solvers,boundVars,M,rules)))

%           let let_vars = map(fn (v, _) -> v) bind in
%           LazyList.map (fn (M,a) -> (Bind(qf,vars,M,b),a))
%		(rewriteTerm(solvers,boundVars ++ let_vars,M,rules))
         | Bind(qf,vars,M,b) -> 
	   LazyList.map (fn (M,a) -> (Bind(qf,vars,M,b),a))
		(rewriteTerm(solvers,boundVars ++ vars,M,rules))
         | The (var,M,b) -> 
	   LazyList.map (fn (M,a) -> (The(var,M,b),a))
		(rewriteTerm(solvers,boundVars ++ [var],M,rules))
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
         | SortedTerm(M,s,b) ->
           LazyList.map (fn (M,a) -> (SortedTerm(M,s,b),a))
		(rewriteTerm(solvers,boundVars,M,rules))
          | Pi(tvs,M,b) ->
           LazyList.map (fn (M,a) -> (Pi(tvs,M,b),a))
		(rewriteTerm(solvers,boundVars,M,rules))
       %  | And(tms,b) ->
           
	 | _ -> Nil)


(* Trace utilities *)

 op printTerm: Nat * MS.Term -> String
 def printTerm (indent,term) = 
     let indent   = PrettyPrint.blanks indent in
     let context  = initialize(asciiPrinter,false) in 
     let argument = ([],Top) in
     let termPP   = ppTerm context argument term in
     let termPP   = PrettyPrint.prettysNone [PrettyPrint.string indent,termPP] in
     PrettyPrint.toString(PrettyPrint.format(60,termPP))

 op traceTerm : Context * MS.Term * Subst -> ()
 def traceTerm(context,term,(* subst *)_) = 
     if traceRewriting > 1 then 
     % if context.trace then 
	 (writeLine(printTerm(3 + ! context.traceIndent,term));
	  ()
	  ) 
     else ()

 op traceRule(context:Context,rule:RewriteRule): () = 
     % if context.trace then
     if traceRewriting > 0 then 
	let depth = toString(! context.traceDepth) in
	(toScreen (PrettyPrint.blanks (! context.traceIndent));
	 writeLine("=  { "^depth^": "^ rule.name^" }"))
     else ()

(* Check condition of conditional rewrite rule *)

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
                | The(var,trm,_) -> loop trm
                | Bind(bnd,vars,trm,_) -> loop trm
	        | Apply(t1,t2,_) -> 
	          (case isFlexVar?(term) 
		     of Some n -> NatMap.inDomain(S,n) 
		      | None -> loop t1 & loop t2)
	        | Seq(terms,_) -> all loop terms
     in
     loop term

 type History = List (RewriteRule * MS.Term * Subst)

 op historyRepetition: History -> Boolean
 def historyRepetition = 
     fn (_,term1,_)::(_,term2,_)::_ -> equalTerm?(term1,term2)
      | _ -> false

 op rewriteRecursive : 
    Context * List Var * RewriteRules * MS.Term * Nat -> LazyList (History)

 op rewriteRecursivePre : 
    Context * List Var * DemodRewriteRules * MS.Term * Nat -> LazyList (History)


%%
%% Apply unconditional rewrite rules using inner-most strategy.
%% Apply conditional rewrite rules using outer-most strategy.
%%

 def rewriteRecursive(context,boundVars,rules,term, maxDepth) = 
     let rules = {unconditional = addDemodRules(rules.unconditional,Demod.empty),
		  conditional   = addDemodRules(rules.conditional,Demod.empty)}
     in rewriteRecursivePre(context,boundVars,rules,term,maxDepth)

 def rewriteRecursivePre(context,boundVars,rules,term,maxDepth) = 
   let	
      def rewritesToTrue(rules,term,subst,history): Option Subst = 
	  case rewriteRec(rules,subst,term,history,false)
	    of Nil -> if trueTerm? term then Some subst else None
	     | Cons((_,t,subst)::history,b) -> 
	       if trueTerm? t then Some subst else None
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
                         toScreen ("=  "^PrettyPrint.blanks traceIndent^"{ "); 
                         writeLine (toString(! context.traceDepth)^" : "^rule.name);
                         %%              printSubst subst;
                         context.traceDepth := 0;
                         rewritesToTrue(rules,cond,subst,history))
                      else 
                        rewritesToTrue(rules,cond,subst,history)
            in
	    if traceRewriting > 0 then
	      (context.traceIndent := traceIndent;
	       writeLine ("   "^PrettyPrint.blanks traceIndent ^"}");
	       res)
	    else
	       res
	else None

      def rewriteRec({unconditional,conditional},subst,term,history,solveCond) =
	let _ = traceTerm(context,term,subst)     in
	let traceDepth = ! context.traceDepth + 1 in
        if traceDepth > maxDepth then unit history
        else
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
	% let rews = (rewrite(Innermost,unconditional) >>= 
	let rews = (rewrite(Outermost,unconditional) >>= 
		    (fn (term,(subst,rule,rules)) ->  
			unit (term,(subst,rule,
				    {unconditional = unconditional,
				     conditional = conditional}))) 
		    @@
		    (fn () -> 
		     rewrite(Outermost,conditional) >>= 
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
		 ({strategy = Innermost,
		   rewriter = applyDemodRewrites(context,emptySubstitution),
		   context = context},
		  boundVars,term,unconditional)
     in
     let rews = LazyList.toList rews in
     List.map (fn (newTerm,(subst,rule,rules)) -> 
		  dereferenceAll subst newTerm) rews

	  
end-spec

(*
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
*)