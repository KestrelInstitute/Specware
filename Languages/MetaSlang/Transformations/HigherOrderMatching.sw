\section{Higher-Order matching for MetaSlang}

\subsection{API}

\begin{description}
\item[match(lhs,rhs,flexTerms,context)] \ \ 
\begin{itemize}
 \item[lhs, rhs] 	are the two terms to be matched
 \item[flexTerms] 	are terms denoting flexible variables.
 \item[context]	contains rewrite laws, theorems, and tracing information.
\end{itemize}
\item[matchPairs]
 The main recursive matching loop.
\end{description}
\begin{spec}
HigherOrderMatching qualifying
spec
 import ../Specs/Environment
 import ../Specs/Utilities

 op match : Context -> MS.Term * MS.Term -> List Subst

 op matchPairs : Context * Subst * Stack -> List Subst

\end{spec}

\subsection{Sort declarations}

\begin{spec} 
 sort Term = MS.Term
 sort Context = 
      { 
        spc         : Spec,
        trace 	    : Boolean,
        traceDepth  : Ref Nat,
	traceIndent : Ref Nat,
	boundVars   : List Var,
        counter     : Ref Nat
      }

  op withSpec infixl 17 : Context * Spec -> Context
  def withSpec (ctxt,spc) = { 
        spc = spc,
        trace = ctxt.trace,
        traceDepth = ctxt.traceDepth,
        traceIndent = ctxt.traceIndent,
        boundVars = ctxt.boundVars,
        counter = ctxt.counter
      }

%% . spc        : Spec
%% . trace      : print trace?
%% . traceDepth : Counter keeping track of how deeply 
%%                the rewrites have been applied
%% . traceIndent: Counter keeping track of trace indentation.
%% . boundVars  : List of bound variables in scope of term
%% . counter    : Counter to generate fresh variables

% A substitution maps type variables to sorts and 
% flexible variables to terms.

 sort Subst    = StringMap Sort * NatMap.Map MS.Term
 sort OptTerm  = Option MS.Term

 sort Stack = {new : List (MS.Term * MS.Term), flex:  List (MS.Term * MS.Term)}

\end{spec}

\subsection{Stack operations}

The agenda is placed on a stack with {\em new}, unexamined entries,
and {\em flex}, entries whose heads are flexible and in general lead to
non-unitary matching.
The stack is accessed and modified using the operations
{\em next} and {\em insert}.

\begin{description}
\item[emptyStack] The empty stack
\item[next]  Get next element in the stack to match
\item[insert]  Insert a new pair in the agenda
\end{description}

\begin{spec}

 op emptyStack : Stack
 op next : Stack -> Option (Stack * MS.Term * MS.Term)
 op insert : MS.Term * MS.Term * Stack -> Stack

 def emptyStack = {new = [],flex = []}

 def next({new,flex}) = 
     case new
       of (M,N)::new ->
	  (case isFlexVar?(M)
	     of Some _ -> Some({new = new,flex = flex},M,N)
	      | None -> 
	   case hasFlexHead?(M)
	     of Some _ -> next {new = new,flex = cons((M,N),flex)} 
	      | None -> Some({new = new,flex = flex},M,N))
	| [] -> 
     case flex
       of (M,N)::flex -> Some({new = new,flex = flex},M,N)
	| [] -> None

 def insert(M,N,{new,flex}) = {new = cons((M,N),new),flex = flex}
 op stackFromList: List(MS.Term * MS.Term) -> Stack
 def stackFromList pairs = 
     foldr (fn ((M,N),stack) -> insert(M,N,stack)) emptyStack pairs

\end{spec}

\subsection{Utilities for fresh and bound variables}

\begin{spec}

 op freshVar : Context * Sort -> MS.Term

% Meta variables (flexible variables) are represented in the form
% Apply(Fun(Op "%Flex",Arrow(Nat,s)),Fun(Int n,Nat))

 op mkVar: Nat * Sort -> MS.Term
 def mkVar(num,srt) = 
     Apply(Fun(Op (mkUnQualifiedId "%Flex",Nonfix),Arrow(natSort,srt,noPos),noPos),
	   Fun(Nat num,natSort,noPos),noPos)

 def freshVar (context,srt) = 
     let num = ! context.counter in
     (context.counter := num + 1;
      mkVar(num,srt)
     )

 def freshBoundVar (context:Context,srt) = 
     let num = ! context.counter in
     (context.counter := num + 1;
      ("x%"^Nat.toString num,srt))

 op isFlexVar? : MS.Term -> Option Nat
 def isFlexVar?(term) = 
     case term
       of Apply (Fun(Op(Qualified (UnQualified,"%Flex"),_),_,_),Fun(Nat n,_,_),_) -> 
	  Some n
	| _ -> None
 op  hasFlexHead? : MS.Term -> Option Nat
 def hasFlexHead?(term) = isFlexVar?(hd(headForm term))

\end{spec}

\subsection{Term normalization}
A main utility in normalizing terms and applying the current 
substitution is the {\tt dereference} utility, which
uses the current substitution and $\beta$-reduction to 
normalize a term with respect to the current substitution.

This computes weak head normal form with respect
to current substitution. This entails unraveling all
applications and applying the head beta redexes 
that appear.

The weak head normal form of a term is of the form
\[
      (c\; M_2\;\ldots\; M_k)
\]
where standardly $c$ is a constant, a bound variable.
In our case we allow $c$ to be anything but an abstraction of
irrefutable patterns, where it is obvious how to perform 
$\beta$ contraction.

\begin{spec}
 op dereferenceR : Subst -> MS.Term -> MS.Term
 op dereference : Subst -> MS.Term -> MS.Term

 def dereferenceR (S as (sortSubst,termSubst)) term = 
     (case term
       of Apply (Fun(Op(Qualified (UnQualified,"%Flex"),_),_,_),Fun(Nat n,_,_),_) -> 
	  (case NatMap.find(termSubst,n)
	     of Some term -> dereferenceR S term
	      | None -> term)
	| Apply(M,N,a) -> 
	  (case dereferenceR S M
	     of Lambda(rules, _) -> 
		let N = dereferenceR S N in 
		(case patternMatchRules(rules,N)
		   of None -> Apply(M,N,a)
		    | Some (sub,M) -> dereferenceR S (substitute(M,sub)))
	      | M as Fun(Project l,_,_) -> 
	        (case dereferenceR S N
		   of Record(fields, _) -> 
		      (case find (fn (l2,_) -> l = l2) fields
		         of Some(_,trm) -> trm
			  | None -> System.fail ("Label "^l^" not found"))
		    | N -> Apply(M,N,a))
	      | M -> Apply(M,N,a))
	| _ -> term)


 def dereference S term = 
     let term1 = dereferenceR S term in
     (%writeLine (MetaSlangPrint.printTerm term ^" |-> "^
      %			MetaSlangPrint.printTerm term1);
      term1)

 op  patternMatchRules : Match * MS.Term -> Option (List (Var * MS.Term) * MS.Term)
 def patternMatchRules(rules,N) = 
     case rules 
       of [] -> None
        | (pat,Fun(Bool true,_,_),body)::rules -> 
	  (case patternMatch(pat,N,[])
	     of Match S -> Some(S,body)
	      | NoMatch -> patternMatchRules(rules,N)
	      | DontKnow -> None)
	| _ :: rules -> None

 sort MatchResult = | Match (List (Var * MS.Term)) | NoMatch | DontKnow

 op  patternMatch : Pattern * MS.Term * List (Var * MS.Term) -> MatchResult 

 def patternMatch(pat:Pattern,N,S) = 
     case pat
       of VarPat(x, _) -> Match(cons((x,N),S))
	| WildPat _ -> Match S
	| RecordPat(fields, _) -> 
	  let fields2 = map (fn (l,p) -> (l,patternSort p,p)) fields in
	  let srt:Sort = Product(map (fn (l,s,_) -> (l,s)) fields2,noPos) in
	  let 
	      def loop(fields,S) : MatchResult = 
	          case fields
		    of (l,s,p)::fields ->
			let N =
			    (case N
			       of Record(NFields,_) -> findField(l,NFields)
		                | _ -> Apply(Fun(Project l,Arrow(srt,s,noPos),noPos),N,noPos)) in
		        (case patternMatch(p,N,S)
			   of Match S -> loop(fields,S)
			    | r -> r)
		     | [] -> Match S
	  in
	  loop(fields2,S)
	| EmbedPat(lbl,None,srt,_) -> 
	  (case N
	     of Fun(Embed(lbl2,_),_,_) -> if lbl = lbl2 then Match S else NoMatch
	      | Apply(Fun(Embed(_,true),_,_),_,_) -> NoMatch
	      | _ -> DontKnow)
	| EmbedPat(lbl,Some p,srt,_) -> 
	  (case N
	     of Fun(Embed(lbl2,_),_,_) -> NoMatch
	      | Apply(Fun(Embed(lbl2,true),_,_),N2,_) -> 
		if lbl = lbl2 
		   then patternMatch(p,N2,S)
		else NoMatch
	      | _ -> DontKnow)
	| StringPat(n,_) ->
	  (case N
	    of Fun(String m,_,_) -> (if n = m then Match S else NoMatch)
	     | _ -> DontKnow)
	| BoolPat(n,_) ->
	  (case N
	    of Fun(Bool m,_,_) -> (if n = m then Match S else NoMatch)
	     | _ -> DontKnow)
	| CharPat(n,_) ->
	  (case N
	    of Fun(Char m,_,_) -> (if n = m then Match S else NoMatch)
	     | _ -> DontKnow)
	| NatPat(n,_) ->
	  (case N
	    of Fun(Nat m,_,_) -> (if n = m then Match S else NoMatch)
	     | _ -> DontKnow)
	| _ -> DontKnow

%%
%% Wasteful, but simple beta-normalizer.
%%

 def dereferenceAll subst term = 
     let (sortSubst,termSubst) = subst in
     let
	def deref (term) = 
	    case isFlexVar?(term)
	      of Some n -> 
		 (case NatMap.find(termSubst,n)
		    of Some term -> 
		       derefAll term %Memoization by using refs?
		     | None -> term)
	       | None -> 
	  (case term
	     of Apply (M as Lambda(rules,_),N,_) -> 
		(case patternMatchRules(rules,N)
		   of None -> Apply(M,N,noPos)
		    | Some (sub,M) -> derefAll (substitute(M,sub)))
	      | Apply(M as Fun(Project l,_,_),Record(fields, _),_) -> 
	        (case find (fn (l2,_) -> l = l2) fields
		   of Some(_,trm) -> trm
		    | None -> System.fail ("Label "^l^" not found"))
	      | _ -> term)
	def derefAll term = dereferenceAll subst term
		
    in
    mapTerm(deref,fn s -> dereferenceSort(subst,s),fn p -> p) term
		 		  


 def bindPattern (pat,trm):MS.Term = Lambda([(pat,mkTrue(),trm)],noPos)

% Get list of applications, assumes that the term is already dereferenced.
 op  headForm : MS.Term -> List MS.Term
 def headForm (term) = 
     case isFlexVar? term
       of Some n -> [term]
        | None -> 
     case term
       of Apply(M,N,_) -> headForm M ++ [N]
        | _ -> [term]
     
 def insertFields = 
     ListPair.foldr 
	(fn((_,x),(_,y),stack) -> insert(x,y,stack))	

\end{spec}

\subsection{The matcher}

\newcommand{\inferenceRule}[2]{
\begin{array}{c}
#1 
\\
\hline
#2
\end{array}
}

The main matching steps consist in decomposing pairs to be matched according
to the following rules:
\[
\begin{array}{|ll|}
\hline
& \\[2em]
\Pi-\Pi & 
\inferenceRule{
 \pi_i\theta = \pi'_i\theta, M_i\theta = N_i\theta}
{
\lambda\ \pi_i\rightarrow M_i = \lambda\ \pi'_i \rightarrow N_i } 
\\[2em]

\Sigma-\Sigma & 
\inferenceRule{M_1 = N_1,\ldots,M_n = N_n}
{
\langle M_1,\ldots,M_n\rangle = \langle N_1,\ldots,N_n\rangle
} 
\\[2em]

{\bf Flex}-{\bf App} & 
\inferenceRule{
X \mapsto \lambda x_1\ldots x_n \  . \ f (X_1\; M_1\ldots M_n)\ldots (X_k\; M_1\ldots M_n)\ \ 
X_1\; M_1\ldots M_n = N_1,\ldots
}
{X\; M_1\; \ldots M_n = f\;N_1\;\ldots\; N_k} 
\\[2em]

{\bf Flex}-\Sigma & 
\inferenceRule{X \mapsto \lambda x_1\ldots x_n \  . \ \langle (X_1\; M_1\ldots M_n),\ldots, (X_k\; M_1\ldots M_n)\rangle}
{
 X\; M_1\; \ldots M_n = \langle N_1\;\ldots\; N_k\rangle 
}
\\[2em]

{\bf Var} & 
\inferenceRule{X \mapsto N}
{X = N} \ \ \ \mbox{$N$ is closed} \\[2em]

{\bf Imitate} & 
\inferenceRule{X \mapsto \lambda x_1 \ . \ldots .\lambda x_k \ . \ N}
{
 (X\;M_1\;\ldots\; M_k) = N
}  \\[2em]

{\bf Project} & 
\inferenceRule{X \mapsto \lambda x_1 \ldots x_{j} \ . \ {\tt project}(i),\ M_i  = N}
{
  (X\;M'_1\ldots M'_j\; \langle M_1,\ldots,M_k\rangle\ldots) = N 
}
\\[2em]

{\bf Project} & 
\inferenceRule{X \mapsto \lambda x_1\ldots,x_k \ . \ x_i,\ \ M_i = N}
{(X\;M_1\ldots M_i\;\ldots\;M_k) = N}  \\[2em]
\hline
\end{array}
\]
where all applicable rules are taken, and may contribute with
a list of substitutions (matches).

The conditions for the imitation steps are not complete. They should
apply to any head normal form, and also allow to match against a non-application
right-hand side.
The conditions for projection should also be completed.

Note: projections should in general be represented as 
$\lambda (x_1,\ldots,x_i,\ldots,x_n) \ . \ x_i$ with a suitable match on a 
record type.

Handle also $\eta$ rules for $\Pi$, $\Sigma$, and the other sort constructors.

\begin{spec}

 def emptySubstitution = (StringMap.empty,NatMap.empty)

 def match context (M,N) = 
     matchPairs(context,emptySubstitution,insert(M,N,emptyStack))

 def matchPairs (context,subst,stack) = 
   case next stack
     of None -> [subst]
      | Some(stack,M,N) -> 
%     let _ = writeLine 
%	(MetaSlangPrint.printTerm (dereference subst M) ^ " = = "^
%	 MetaSlangPrint.printTerm N) 
%     in
%     let _ = printSubst subst in
   case (dereference subst M,N)
     of 
%%
%% Pi-Pi
%%

	(Lambda(rules1, _),Lambda(rules2, _)) -> 
	if length rules1 = length rules2
	   then matchRules(context,subst,stack,rules1,rules2)
	else []
%%
%% Var 
%% Check that N does not contain bound variables.
%% sjw: 2/15/01 Moved before Eta
      | (Apply (Fun(Op(Qualified (UnQualified,"%Flex"),_),Arrow(_,s,_),_),
		Fun(Nat n,_,_),_),
	 N) ->
	if closedTermV(N,context.boundVars) & ~(occursProper n N)
	   then 
	   let srt2 = inferType(context.spc,subst,N) in
	   (case unifySorts(context,subst,s,srt2)
	      of Some subst -> 
		 matchPairs(context,updateSubst(subst,n,N),stack)
	       | None -> []) 
	else []
%%
%% Eta rules
%%
      | (M as Lambda([(VarPat((_,srt), _),Fun(Bool true,_,_),_)], _),N) -> 
	(case unifySorts(context,subst,
			 inferType(context.spc,subst,M),
			 inferType(context.spc,subst,N))
	   of None -> []
	    | Some subst -> 
	let x = freshBoundVar(context,srt) in
	matchPairs (context,subst,
		      insert(Apply(M,Var(x,noPos),noPos),Apply(N,Var(x,noPos),noPos),stack)))
      | (M,Lambda([(VarPat((_,srt), _),Fun(Bool true,_,_),_)], _)) -> 
	(case unifySorts(context,subst,
			 inferType(context.spc,subst,M),
			 inferType(context.spc,subst,N))
	   of None -> []
	    | Some subst -> 
	let x = freshBoundVar(context,srt) in
	matchPairs(context,subst,
		      insert(bindPattern(VarPat(x,noPos),Apply(M,Var(x,noPos),noPos)),
			     N,stack)))
%%
%% Sigma-Sigma
%%
      | (Record(fields1, _),Record(fields2, _)) -> 
	matchPairs (context,subst,insertFields stack (fields1,fields2))
%%
%% Constants
%%
      | (Fun(f1,srt1,_),Fun(f2,srt2,_)) ->  
	matchBase(context,f1,srt1,f2,srt2,stack,subst)
      | (Var((n1,srt1), _),Var((n2,srt2), _)) ->  
	matchBase(context,n1,srt1,n2,srt2,stack,subst)
      | (Bind(qf1,vars1,M,_),Bind(qf2,vars2,N,_)) -> 
	if ~(qf1 = qf2) or ~(length vars1 = length vars2)
	   then []
	else
	let (S1,S2,subst,flag) = 
	    ListPair.foldr
	      (fn ((v1,s1),(v2,s2),(S1,S2,subst,flag)) -> 
	      if ~ flag
		 then (S1,S2,subst,flag)
	      else
	      case unifySorts(context,subst,s1,s2)
		of Some subst -> 
		   let x = freshBoundVar(context,s1) in
		   let S1 = cons(((v1,s1),Var(x,noPos)),S1) in
		   let S2 = cons(((v2,s2),Var(x,noPos)),S2) in
		   (S1,S2,subst,true)
		 | None -> (S1,S2,subst,false)) 
	      ([],[],subst,true) (vars1,vars2)
	in
	if ~flag
	   then []
	else
	let M = substitute(M,S1) in
	let N = substitute(N,S2) in
	matchPairs (context,subst,insert(M,N,stack))
      | (IfThenElse(M1,M2,M3,_),IfThenElse(N1,N2,N3,_)) -> 
	matchPairs(context,subst,insert(M1,N1,insert(M2,N2,insert(M3,N3,stack))))
      | (M,_) -> 
%	  let _ = writeLine "matchPair" in
%	  let _ = writeLine(MetaSlangPrint.printTerm M) in
%	  let _ = writeLine(MetaSlangPrint.printTerm N) in
%	  let _ = printSubst subst in
	let srt1 = inferType(context.spc,subst,M) in
	let srt2 = inferType(context.spc,subst,N) in
	case unifySorts(context,subst,srt1,srt2)
	  of None -> []
	   | Some subst -> 
	case headForm(M)
	  of [M] -> []
%
% Flexible head
%
	   | Ms as 
	     ((Apply (Fun(Op(Qualified (UnQualified,"%Flex"),_), Arrow(_,s,_),_),
		      Fun(Nat n,_,_),_))::terms) -> 
	     if occursProper n N 
		 then [] 
	     else
	     let Ns = headForm N in
	     let substs = if length Ns = length Ms
			   then
			    let stack1 = foldr
					   (fn ((M,N),stack) -> insert(M,N,stack))
					   stack (ListPair.zip(Ms, Ns)) in
			    matchPairs(context,subst,stack1)
			   else []
	     in
	     if ~(substs = []) then substs
	     else
	     let termTypes = map (fn M -> inferType(context.spc,subst,M)) terms in
	     let vars  = map (fn srt -> freshBoundVar(context,srt)) termTypes in

% 1. Recursive matching

% This was incomplete as formulated in the LaTeX documentation.
% It is being replaced by code that maps
%  n to fn x1 -> ... fn xn -> N1 (X1 x1 ... xn) ... (Xk x1 .. xn)
% where n is |terms| and k+1 = |Ns|.

	     let pats = map (fn v -> VarPat(v,noPos):Pattern) vars in
	     let varTerms = map (fn v -> Var(v,noPos)) vars in	
	     let (sound,N1,pairs) = 
		 case Ns
%
% When matching against a record X M1 ... Mn = (N1,...,Nk)
% create the instantiation X |-> fn x1 .. xn -> (X1 x1..xn,...,Xk x1..xn) 
% and also the matching pairs X1 M1 ... Mn = N1 ...  Xk M1 ... Mn = Nk
%
		   of [Record(fields, _)] -> 
		      let ls = 
			  map 
			      (fn (l,trm) -> 
			      let srt = inferType(context.spc,subst,trm) in
			      let srt = foldr mkArrow srt termTypes in
			      let v = freshVar(context,srt) in
			      ((l,
			       foldl (fn (t1,t2)-> Apply(t2,t1,noPos)) v varTerms),
			       (foldl(fn (t1,t2)-> Apply(t2,t1,noPos)) v terms,
			       trm))
			   ) fields
		      in
		      let (fields,pairs) = ListPair.unzip ls in
		      (true,Record(fields,noPos),pairs)
%
% When matching against an application X M1 .. Mn = N1 ... Nk
% create the instantiation  X |-> fn x1 .. xn -> N1 (X2 x1..xn) ... (Xk x1..xn) 
% and also the matching pairs X2 M1 ... Mn = N2 ...  Xk M1 ... Mn = Nk
%
%
% N should be a closed term for this step to be legal/sound.
%
		    | N::Ns ->
		      if closedTermV(N,context.boundVars)
		      then 
		      let ls = 
			  map 
			      (fn trm -> 
			       let srt = inferType(context.spc,subst,trm) in
			       let srt = foldr mkArrow srt termTypes in
			       let v = freshVar(context,srt) in
			      (foldl (fn (t1,t2)-> Apply(t2,t1,noPos)) v varTerms,
			       (foldl (fn (t1,t2)-> Apply(t2,t1,noPos)) v terms,
			       trm))
			   ) Ns
		      in
		      let (Ns,pairs) = ListPair.unzip ls in
		      (true,foldl (fn (t1,t2) -> Apply(t2,t1,noPos)) N Ns,pairs)
		      else
		      (false,N,[])
	    in
	    (if sound 
		then
		let N2     = foldr bindPattern N1 pats 			in
		let stack1 = foldr (fn ((M,N),stack) -> insert(M,N,stack)) stack pairs in
		matchPairs(context,updateSubst(subst,n,N2),stack1)
	     else [])
	    ++
% 2. Projection.
	   (let projs  = projections (context,subst,terms,vars,srt2) 		in
	   ((flatten
	      (map 
		 (fn (subst,proj) -> 
		      let subst = updateSubst(subst,n,proj) in
		      %% Repeat with the updated substitution, gets rid
		      %% of the flexible head.
		      matchPairs(context,subst,insert(M,N,stack)))
		 projs)) 
	    ++ 
% 3. Imitation.
	    (if closedTermV(N,context.boundVars)
		then 
		let pats   = map (fn srt -> WildPat(srt,noPos):Pattern) termTypes in 
		let trm    = foldr bindPattern N pats 			  in
		let subst  = updateSubst(subst,n,trm) in
		matchPairs(context,subst,stack) 
	    else [])))
	   | Ms -> 
%%
%% Rigid head
%%
	case insertPairs(Ms,headForm N,stack)
	  of Some stack -> matchPairs(context,subst,stack)
	   | None -> []

  op  insertPairs : List MS.Term * List MS.Term * Stack -> Option Stack

  def insertPairs(Ms,Ns,stack): Option Stack = 
      case (Ms,Ns)
	of (M::Ms,N::Ns) -> insertPairs(Ms,Ns,insert(M,N,stack))
	 | ([],[]) -> Some stack
	 | _ -> None


  def updateSubst((sortSubst,termSubst),n,M) = 
      case isFlexVar?(M)
	of Some m -> 
	   if n = m then (sortSubst,termSubst) else
		(sortSubst,NatMap.insert(termSubst,n,M))
	 | None -> (sortSubst,NatMap.insert(termSubst,n,M))

%%
%% Infer type with sort dereferencing
%%
 op inferType: Spec * Subst * MS.Term -> Sort
 def inferType(spc,subst,N) = 
     case N
       of Apply(t1,t2,_) -> 
	  let srt = dereferenceSort(subst,inferType(spc,subst,t1)) in
	  (case SpecEnvironment.rangeOpt(spc,srt)
	     of Some rng -> rng
	      | None -> 
		(% System.print N; printSpecWithSortsToTerminal spc;
         System.fail 
		("Could not extract type for "^
		 printTermWithSorts N)))
        | Bind _ -> boolSort
        | Record(fields,a) -> 
	  Product(map (fn (id,t)-> (id,inferType(spc,subst,t))) fields,a)
        | Let(_,term,_) -> inferType(spc,subst,term)
        | LetRec(_,term,_) -> inferType(spc,subst,term)
        | Var((_,srt), _) -> srt
        | Fun(_,srt, _) -> srt
        | Lambda((Cons((pat,_,body),_)), _) -> 
	  mkArrow(patternSort pat,inferType(spc,subst,body))
        | Lambda([], _) -> System.fail "Ill formed lambda abstraction"
        | IfThenElse(_,t2,t3,_) -> inferType(spc,subst,t2)
        | Seq([],a) -> Product([],a)
        | Seq([M],_) -> inferType(spc,subst,M)
        | Seq(M::Ms,a) -> inferType(spc,subst,Seq(Ms,a))
        | _ -> System.fail "Non-exhaustive match"


\end{spec}
{\tt matchPairs} should also handle "IfThenElse", "Let", "LetRec", "Seq", 
possibly by using pre-cooking.

\subsection{Projections}

Projections are correctly computed based on the sort structure of the flexible variable.
Thus, if 
\[
   X : \sigma_1 \rightarrow \sigma_2 \rightarrow \cdots \rightarrow \sigma_k \rightarrow \tau
\]
and we process the equality
\[
   (X\; M_1\; \ldots\; M_k) \ = \ N,
\]
then we generate the terms
\[
   \lambda x_1 \ . \ \lambda x_2 \ . \ \ldots \ \lambda x_k \ . \ \pi(x_i)
\]
where $\pi(x_i)$ is a projection on $x_i$ and has type $\tau$.
The projection is computed using the following recursive unification procedure:
\[
\begin{array}{llll}
N : \sigma  \simeq  \tau &  \{ N \} & \mbox{if $\sigma\sqcap\tau \neq \bot$} \\
N : \sigma_1 \times \sigma_2  \simeq  \tau & N.1: \sigma_1 \simeq \tau \ \ \cup \ \ 
					     N.2: \sigma_2 \simeq \tau \\
N : \sigma_1 \rightarrow \sigma_2 \simeq  \tau 
			& (N\;(F\; x_1\;\ldots\; x_n)):\sigma_2 \simeq \tau 
\end{array}
\]

\begin{spec}

  op projections : Context * Subst * List MS.Term * List Var * Sort 
				-> List (Subst * MS.Term)

  def projectTerm (fields,label,srt,N):MS.Term = 
      Apply(Fun(Project label,Arrow(Product(fields,noPos),srt,noPos),noPos),N,noPos)

  def projections (context,subst,(* terms *)_,vars,srt) =
      let
	  def projectSort(srt1,N) = 
	      (case unifySorts(context,subst,srt1,srt)
		 of None -> []
		  | Some subst -> [(subst,N)])
	      ++
	      (case dereferenceSort(subst,srt1)
		 of Product(fields, _) -> 
		    flatten 
			(map (fn (l,s) -> 
			      projectSort(s,projectTerm(fields,l,s,N))) fields)
		  | Arrow(srt1,srt2,_) -> 
		    let srt1 = foldr mkArrow srt1 (map (fn (_,s) -> s) vars) in
		    let X = freshVar(context,srt1) in
		    let trm = foldl (fn (v,t2) -> Apply(t2,Var(v,noPos),noPos)) X vars in
		    projectSort(srt2,Apply(N,trm,noPos)) 
		  | _ -> [])
      in
      let terms = map (fn (x,s) -> projectSort(s,Var((x,s),noPos))) vars in
      let terms = flatten terms in
      let terms = map (fn (subst,M) -> 
		(subst,foldr (fn(v,M) -> bindPattern(VarPat(v,noPos),M)) M vars)) terms 
      in
      terms

\end{spec}
 \subsection{Recursive matching utilities}

  Constants and bound variables are matched using {\tt matchBase}.
\begin{spec}

  op matchBase : fa(a) Context * a * Sort * a * Sort * Stack * Subst -> List Subst
  def matchBase (context,x,srt1,y,srt2,stack,subst) = 
      if x = y
	 then 
	    (case unifySorts(context,subst,srt1,srt2)
	       of Some subst -> matchPairs(context, subst,stack)
	        | None -> [])
      else []

\end{spec}
  $\lambda$-binders are matched by matching every pair of pattern against eachother.
  The pair of patterns that are compared must match precisely the same instances, thus,
  for example embed patterns must be equal.
  The variables that are bound by the patterns are substituted into the conditions and
  respective bodies such that variables bound at the same positions are equal.
\begin{spec}

  def matchRules(context,subst,stack,rules1,rules2) = 
      case (rules1,rules2)
        of ((pat1,cond1,body1)::rules1,(pat2,cond2,body2)::rules2) -> 
	   (case matchPattern(context,pat1,pat2,[],[],[])
	      of Some (S1,S2) -> 
		 let stack = insert(substitute(body1,S1),substitute(body2,S2),stack) in
		 let stack = insert(substitute(cond1,S1),substitute(cond2,S2),stack) in
		 matchRules(context,subst,stack,rules1,rules2)
	       | None -> [])
	 | ([],[]) -> matchPairs(context,subst,stack)
	 | _ -> []

\end{spec}
  {\tt matchPattern}, {\tt matchPatterns}, and {\tt matchIrefutablePattern} recurse on
  aligning the same pattern matches.
\begin{spec}

   def matchPattern(context,pat1:Pattern,pat2:Pattern,pairs,S1,S2):
       Option (List (Var * MS.Term) * List (Var * MS.Term)) = 
       case (pat1,pat2)
         of (VarPat((x,srt1), _),VarPat((y,srt2), _)) ->
	    let z  = freshBoundVar(context,srt1) in
	    let S1 = cons(((x,srt1),Var(z,noPos)),S1) in
	    let S2 = cons(((y,srt2),Var(z,noPos)),S2) in
	    matchPatterns(context,pairs,S1,S2)
	  | (EmbedPat(c1,None,srt1,_),EmbedPat(c2,None,srt2,_)) -> 
            if c1 = c2
		then matchPatterns(context,pairs,S1,S2)
	    else None
	  | (EmbedPat(c1,Some pat1,srt1,_),EmbedPat(c2,Some pat2,srt2,_)) -> 
	    if c1 = c2
		then matchPattern(context,pat1,pat2,pairs,S1,S2)
	    else None
	  | (RecordPat(fields1, _),RecordPat(fields2, _)) -> 
	    let pairs1 = ListPair.map (fn ((_,p1),(_,p2))-> (p1,p2)) (fields1,fields2) in
	    matchPatterns(context,pairs1 ++ pairs,S1,S2)
	  | (WildPat(srt1, _),WildPat(srt2, _)) -> Some(S1,S2)
	  | (StringPat(s1, _),StringPat(s2, _)) -> 
	    if s1 = s2 then matchPatterns(context,pairs,S1,S2) else None
	  | (BoolPat(b1, _),BoolPat(b2, _)) -> 
	    if b1 = b2 then matchPatterns(context,pairs,S1,S2) else None
	  | (CharPat(c1, _),CharPat(c2, _)) -> 
	    if c1 = c2 then matchPatterns(context,pairs,S1,S2) else None
	  | (NatPat(i1, _),NatPat(i2, _)) -> 
	    if i1 = i2 then matchPatterns(context,pairs,S1,S2) else None
%
% Possibly generalize the matching to include matching on (t1,t2), assuming t1 can
% contain meta variables.
% 
	  | (RelaxPat(p1,t1,_),RelaxPat(p2,t2,_)) -> 
	    if t1 = t2 then matchPatterns(context,pairs,S1,S2) else None
	  | (QuotientPat(p1,t1,_),QuotientPat(p2,t2,_)) -> 
	    if t1 = t2 then matchPatterns(context,pairs,S1,S2) else None
	  | _ -> 
	     case matchIrefutablePattern(context,pat1,S1)
	       of None -> None
		| Some S1 -> 
	     case matchIrefutablePattern(context,pat2,S2)
	       of Some S2 -> matchPatterns(context,pairs,S1,S2)
		| None -> None

  def matchPatterns(context,pairs,S1,S2) = 
      case pairs
        of (p1,p2)::pairs -> matchPattern(context,p1,p2,pairs,S1,S2)
	 | [] -> Some (S1,S2)	   
  def matchIrefutablePattern(context,pat:Pattern,S): Option (List (Var * MS.Term)) = 
      case pat
        of WildPat _ -> Some S
	 | VarPat((x,s),a) -> 
	   let z = freshBoundVar(context,s) in 
	   Some(cons(((x,s),Var(z,a)),S))
	 | RecordPat(fields, _) -> 
	   let
	       def loop(fields,S): Option (List (Var * MS.Term)) = 
		   case fields
		     of (l,p)::fields -> 
			(case matchIrefutablePattern(context,p,S)
			   of Some S -> loop(fields,S)
			    | None -> None)
		      | [] -> Some S
	   in
		loop(fields,S)
	 | _ -> None


\end{spec}

\subsection{Occurs check}
Our matching algorithm includes the occurs check, as there we do not require the 
input to be a matching problem. In fact, in the glue code generation, proper 
skolemization transforms a proper matching problem into an inproper one.

\begin{spec}
  op occursProper : Nat -> MS.Term -> Boolean
  def occursProper n M = 
      case isFlexVar?(M)
	of Some _ -> false
	 | None -> occurs n M

  op occurs : Nat -> MS.Term -> Boolean
  op occursP : fa(a) Nat -> a * MS.Term -> Boolean
  def occursP n (_,M) = occurs n M
  def occurs n term = 
      case term
        of Var _ -> false
	 | Fun _ -> false
	 | Apply(M,N,_) -> 
	   (case isFlexVar?(term)
	      of Some m -> n = m
	       | None -> occurs n M or occurs n N)
	 | Record(fields, _) -> 
	   exists (occursP n) fields
	 | Lambda(rules, _) -> 
	   exists (fn (_,cond,body) -> 
			occurs n cond or occurs n body) rules
	 | Seq(Ms, _) -> exists (occurs n) Ms
	 | IfThenElse(M1,M2,M3,_) -> 
	   occurs n M1 or occurs n M2 or occurs n M3
	 | Bind(_,vars,M,_) -> occurs n M
	 | Let(decls,M,_) -> 
	   occurs n M or exists (occursP n) decls
	 | LetRec(decls,M,_) ->
	   occurs n M or exists (occursP n) decls
\end{spec}

\subsection{Closed terms}

\begin{description}
\item[{\tt closedTerm}]
 determines whether a term contains any 
        free variables or not.
\item[{\tt closedTermV}] detects existence of 
       free variables not included in the
        argument 
\end{description}

\begin{spec}

  op closedTerm : MS.Term -> Boolean
  op closedTermV : MS.Term * List Var -> Boolean

  def closedTerm(term) = closedTermV(term,[])

%  def patternVars(pat:Pattern) = 
%      case pat
%        of VarPat(v, _) -> [v]
%	 | WildPat _ -> []
%	 | RecordPat(fields, _) -> 
%	   flatten (map (fn (_,p) -> patternVars p) fields)
%	 | EmbedPat(_,None,_,_) -> []
%	 | EmbedPat(_,Some p,_,_) -> patternVars p
%	 | RelaxPat(p,t,_) -> patternVars p
%	 | QuotientPat(p,t,_) -> patternVars p
%	 | AliasPat(p1,p2,_) -> patternVars p1 ++ patternVars p2 
%	 | _ -> []

  def closedTermV(term,bound) = 
      case term
        of Var(v, _) -> exists (fn w -> v = w) bound	        
	 | Fun _ -> true
	 | Apply(M,N,_) -> closedTermV(M,bound) & closedTermV(N,bound)
	 | Record(fields, _) -> 
	   all (fn (_,M) -> closedTermV(M,bound)) fields
	 | Lambda(rules, _) -> 
	   all (fn (pat,cond,body) -> 
			let bound = patternVars(pat) ++ bound in
			(closedTermV(cond,bound) & 
			 closedTermV(body,bound))) rules
	 | Seq(Ms, _) -> all (fn M -> closedTermV(M,bound)) Ms
	 | IfThenElse(M1,M2,M3,_) -> 
	   closedTermV(M1,bound) & 
	   closedTermV(M2,bound) & 
	   closedTermV(M3,bound)
	 | Bind(_,vars,M,_) -> closedTermV(M,vars ++ bound)
	 | Let(decls,M,_) -> 
	   all (fn (_,M) -> closedTermV(M,bound)) decls 
	   & 
	   (let bound = foldr 
		(fn ((pat,_),bound) -> patternVars pat ++ bound) 
		bound decls 
	   in
	   closedTermV(M,bound) )
	 | LetRec(decls,M,_) ->
	   let bound = (map (fn (v,_) -> v) decls) ++ bound in
	   closedTermV(M,bound) & 
	   (all (fn (_,M) -> closedTermV(M,bound)) decls) 
\end{spec}	 

\subsection{Sort unification} 
 Unification of sorts is similar to the one in AstTypes.
 It uses a list of already processed sort pairs to avoid cycling through
 recursive definitions.

\begin{spec}

  op unifySorts : Context * Subst * Sort * Sort -> Option Subst

  sort Unification = 
    | NotUnify  Sort * Sort 
    | Unify     Subst 

  op  unifyL : fa(a) Subst * Sort * Sort * List(a) * List(a) * List (Sort * Sort) * 
                  (Subst * a * a  * List(Sort * Sort) -> Unification) ->  Unification
  def unifyL(subst,srt1,srt2,l1,l2,equals,unify):Unification = 
      case (l1,l2)
        of ([],[]) -> Unify subst
         | (e1::l1,e2::l2) -> 
	   (case unify(subst,e1,e2,equals):Unification
	      of Unify subst -> unifyL(subst,srt1,srt2,l1,l2,equals,unify)
	       | notUnify -> notUnify)
         | _ -> NotUnify(srt1,srt2)

  op  occursRec : Subst * String * Sort -> Boolean
  def occursRec (subst,v,srt) = 
      case srt 
        of Base(_,srts,_) -> exists (fn s -> occursRec(subst,v,s)) srts
 	 | Arrow(s1,s2,_) -> occursRec(subst,v,s1) or occursRec(subst,v,s2)
	 | Product(fields, _) -> exists (fn (_,s) -> occursRec(subst,v,s)) fields
	 | CoProduct(fields, _) -> 
	   exists (fn(_,None)-> false | (_,Some s)-> occursRec(subst,v,s)) fields
	 | TyVar(w, _) -> 
	   (case StringMap.find(subst.1,w)
	      of Some s -> occursRec (subst,v,s)
	       | None -> v = w) 
	 | Subsort(s,_,_) -> occursRec(subst,v,s)
	 | Quotient(s,_,_) -> occursRec(subst,v,s)

  def dereferenceSort(subst:Subst,srt) = 
      case srt:Sort
        of TyVar(v, _) -> 
	   (case StringMap.find(subst.1,v)
              of Some srt -> dereferenceSort(subst,srt)	
	       | None -> srt)
	 | _ -> srt

  def unifySorts(context,subst,srt1,srt2) = 
      let spc = context.spc in
      let
	def insert(v,srt,(sortSubst,termSubst)) = 
	    (StringMap.insert(sortSubst,v,srt),termSubst)
	def unifyCP(subst,srt1,srt2,r1,r2,equals):Unification = 
	    unifyL(subst,srt1,srt2,r1,r2,equals,
		   fn(subst,(id1,s1),(id2,s2),equals) -> 
		      if id1 = id2 
			then 
			(case (s1,s2)
			   of (None,None) -> Unify subst 
			    | (Some s1,Some s2) -> unify(subst,s1,s2,equals)
			    | _ -> NotUnify(srt1,srt2))
		      else NotUnify(srt1,srt2))
	def unifyP(subst,srt1,srt2,r1,r2,equals):Unification = 
	    unifyL(subst,srt1,srt2,r1,r2,equals,
		   fn(subst,(id1,s1),(id2,s2),equals) -> 
		      if id1 = id2 
			then unify(subst,s1,s2,equals)
		      else NotUnify(srt1,srt2))
	def unify(subst,srt1:Sort,srt2:Sort,equals) : Unification = 
	    case (dereferenceSort(subst,srt1):Sort,dereferenceSort(subst,srt2):Sort)
	      of (CoProduct(r1,_),CoProduct(r2,_)) -> 
		 unifyCP(subst,srt1,srt2,r1,r2,equals)
	       | (Product(r1,_),Product(r2,_)) -> 
		 unifyP(subst,srt1,srt2,r1,r2,equals)
	       | (Arrow(t1,t2,_),Arrow(s1,s2,_)) -> 
		 (case unify(subst,t1,s1,equals)
		    of Unify (subst) -> unify(subst,t2,s2,equals)
		     | notUnify -> notUnify)
	       | (Quotient(ty,trm1,_),Quotient(ty_,trm2,_)) -> 
		 if trm1 = trm2
		    then unify(subst,ty,ty_,equals)
		 else NotUnify (srt1,srt2)
	       | (Subsort(ty,_,_),ty2) -> unify(subst,ty,ty2,equals)
	       | (ty,Subsort(ty2,_,_)) -> unify(subst,ty,ty2,equals)
	       | (srt1 as Base(id,ts,_),srt2 as Base(id_,ts_,_)) -> 
		 if exists (fn p -> p = (srt1,srt2)) equals
		    then Unify (subst)
		 else 
		 if id = id_ 
		    then unifyL(subst,srt1,srt2,ts,ts_,equals,unify)
	         else 
		 let s1_ = SpecEnvironment.unfoldBase(spc,srt1) in
		 let s2_ = SpecEnvironment.unfoldBase(spc,srt2) in
		 if srt1 = s1_ & s2_ = srt2
		    then  NotUnify (srt1,srt2)
		 else unify(subst,s1_,s2_,cons((srt1,srt2),equals))
	       | (TyVar(v, _),TyVar(w, _)) -> 
		 if v = w then Unify subst else Unify (insert(v,srt2,subst))
	       | (TyVar(v, _),_) -> 
		     if occursRec(subst,v,srt2) 
			 then NotUnify (srt1,srt2)
		     else Unify(insert(v,srt2,subst))
	       | (_,TyVar(v, _)) -> 
		     if occursRec(subst,v,srt1) 
			 then NotUnify (srt1,srt2)
		     else Unify(insert(v,srt1,subst))
	       | (srt1 as Base _,srt2) -> 
 		  let  s1_ = SpecEnvironment.unfoldBase(spc,srt1) in
		  if srt1 = s1_
		     then NotUnify (srt1,srt2)
	 	  else unify(subst,s1_,srt2,cons((srt1,srt2),equals))
	       | (srt1,srt2 as Base _) ->
		 let s2_ = SpecEnvironment.unfoldBase(spc,srt2)  in
		 if srt2 = s2_
		     then NotUnify (srt1,srt2)
		 else unify(subst,srt1,s2_,cons((srt1,srt2),equals))
	       | _ -> NotUnify(srt1,srt2)
      in
      case unifyL(subst,srt1,srt2,[srt1],[srt2],[],unify)
	of NotUnify (s1,s2) -> 
	   (%% writeLine (MetaSlangPrint.printSort s1^" ! = "^
	    %%      MetaSlangPrint.printSort s2);
	    %% printSubst subst; 
	     None)
	 | Unify subst -> Some subst

\end{spec}

\subsection{Normalization}
To make the matching steps easier we normalize specifications
before matching by deleting {\tt IfThenElse}, {\tt Let}, and 
{\tt LetRec}, replacing these by function symbols and applications.

\begin{spec}

  op doNormalizeTerm : Spec -> MS.Term -> MS.Term
  def doNormalizeTerm spc term = 
    case term of
      | Let ([(pat,N)],M,a) -> Apply (Lambda([(pat,mkTrue(),M)],a),N,a)
      | Let (decls,M,a) -> 
         let (pats,Ns) = ListPair.unzip decls in
          Apply (Lambda([(mkTuplePat pats,mkTrue(),M)], a),mkTuple Ns,a)
%       | IfThenElse (M,N,P) -> 
%          let srt = SpecEnvironment.inferType(spc,N) in
%          Apply(Fun(Op(Qualified("TranslationBuiltIn","IfThenElse"),Nonfix),
%                Arrow(mkProduct [boolSort,srt,srt],srt)),
%                mkTuple [M,N,P])
%       | LetRec(decls,M,_) -> 
%          System.fail "Replacement of LetRec by fix has not been implemented"
      | Seq (Ms,a) -> 
         let
            def loop Ms = 
              case Ms of
                | [] -> mkTuple []
                | [M] -> M
                |  M::Ms -> 
                    let srt = SpecEnvironment.inferType(spc,M) in
                      Apply(bindPattern(WildPat(srt,a),loop Ms),M,a)
          in
            loop Ms
       | term -> term

  def normalizeTerm (spc:Spec) = 
      let doTerm = doNormalizeTerm spc in
      mapTerm(doTerm,fn s -> s,fn p -> p)

  def normalizeSpec (spc:Spec) =
      let doTerm = doNormalizeTerm spc in
      mapSpec(doTerm,fn s -> s,fn p -> p) spc

  def doDeNormalizeTerm(term:MS.Term):MS.Term = 
      case term
	of Apply(Lambda([(WildPat _,Fun(Bool true,_,_),M)], _),N,a) -> 
	   Seq([N,M],a)
	 | Apply(Lambda([(pat,Fun(Bool true,_,_),M)], _),N,a) -> 
	   Let([(pat,N)],M,a)
%	 | Apply(Fun(Op(Qualified("TranslationBuiltIn","IfThenElse"),
%		     Nonfix),_),Record [(_,M),(_,N),(_,P)]) -> 
%	   IfThenElse(M,N,P)
	 | term -> term 

  def deNormalizeSpec = 
      mapSpec(doDeNormalizeTerm,fn s -> s,fn p -> p) 

  def deNormalizeTerm  = 
      mapTerm(doDeNormalizeTerm,fn s -> s,fn p -> p)


\end{spec}

\subsection{Create a fresh context}

\begin{spec}

 op makeContext : Spec -> Context

 def makeContext spc = 
     {
	spc        = spc,
	trace      = true,
	traceDepth = Ref 0,
	traceIndent = Ref 0,
        boundVars  = [],
	counter    = Ref 0
     }
 
 op setBound : Context * List Var -> Context
 def setBound({spc,trace,traceDepth,traceIndent,boundVars,counter},bv) = 
     {spc = spc,trace = trace,
      traceDepth = traceDepth,
      traceIndent = traceIndent,
      boundVars = bv,counter = counter}

\end{spec}



\begin{spec}

  op printSubst: fa(a) StringMap(ASort a) * NatMap.Map(ATerm a) -> ()
  def printSubst(sortSubst,termSubst) = 
      (writeLine "---------- substitution ---------";
	StringMap.appi 
	(fn (s,srt) -> 
	     writeLine(s^" |-> "^printSort srt^" "))
	sortSubst;
       writeLine "";
       NatMap.appi
	(fn (i,trm) -> 
	     writeLine(Nat.toString i^" |-> "^ printTerm trm^" "))
	termSubst;
	writeLine "")
\end{spec}
\subsection{Freeze and thaw type variables in term}
In order to ensure that type variables in a term to be rewritten are not
participating in unification we introduce freeze and thaw operations.

\begin{spec} 

 def freezeTerm(spc,term:MS.Term) = 
     let term = normalizeTerm spc term in
     let
	doFreeze = fn (s as TyVar _:Sort) -> Base(mkUnQualifiedId("TypeVar!"),[s],noPos):Sort
		  | s -> s
     in
     mapTerm(fn tm -> tm,doFreeze,fn p -> p) term

 def thawTerm(term:MS.Term) =
     let term = deNormalizeTerm term in
     let
	doThaw = fn(Base(Qualified (UnQualified,"TypeVar!"),[s],_):Sort) -> s
		  | s -> s
     in
     mapTerm(fn tm -> tm,doThaw,fn p -> p) term

endspec

\end{spec}
