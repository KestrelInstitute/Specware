(* Higher-Order matching for MetaSlang

API

match(lhs,rhs,flexTerms,context)
 [lhs, rhs] 	are the two terms to be matched
 [flexTerms] 	are terms denoting flexible variables.
 [context]	contains rewrite laws, theorems, and tracing information.
 [matchPairs]   The main recursive matching loop.
*)

HigherOrderMatching qualifying spec
 import /Languages/MetaSlang/Specs/Environment
 import /Languages/MetaSlang/Specs/Utilities
 import Simplify
 import Interpreter

 type SubstC    = StringMap MSType * NatMap.Map MSTerm * MSTerms

 op match : Context -> MSTerm * MSTerm -> List SubstC

 op matchPairs : Context * SubstC * Stack -> List SubstC

 type Context = 
      { 
        spc         : Spec,
        trace 	    : Bool,
        traceDepth  : Ref Nat,
	traceIndent : Ref Nat,
	boundVars   : MSVars,
        counter     : Ref Nat,
        %% Data to control Rewriter
        traceRewriting          : Nat,
        traceShowsLocalChanges? : Bool,
        useStandardSimplify?    : Bool,
        debugApplyRewrites?     : Bool,
        maxDepth                : Nat,
        backwardChainMaxDepth   : Nat,
        conditionResultLimit    : Nat,
        termSizeLimit           : Nat
      }

  op withSpec infixl 17 : Context * Spec -> Context
  def withSpec (ctxt,spc) = ctxt << {spc = spc}

%% . spc        : Spec
%% . trace      : print trace?
%% . traceDepth : Counter keeping track of how deeply 
%%                the rewrites have been applied
%% . traceIndent: Counter keeping track of trace indentation.
%% . boundVars  : List of bound variables in scope of term
%% . counter    : Counter to generate fresh variables

% A substitution maps type variables to types and 
% flexible variables to terms.

 type Stack = {new : List (MSTerm * MSTerm * Option MSType), flex: List (MSTerm * MSTerm * Option MSType)}

(*  Stack operations

The agenda is placed on a stack with {\em new}, unexamined entries,
and {\em flex}, entries whose heads are flexible and in general lead to
non-unitary matching.
The stack is accessed and modified using the operations
{\em next} and {\em insert}.

\item[emptyStack] The empty stack
\item[next]  Get next element in the stack to match
\item[insert]  Insert a new pair in the agenda
*)

 op emptyStack : Stack
 op next : Stack -> Option (Stack * MSTerm * MSTerm * Option MSType)
 op insert : MSTerm * MSTerm * Option MSType * Stack -> Stack

 def emptyStack = {new = [],flex = []}

 def next({new,flex}) = 
     case new
       of (M,N,OT)::new ->
	  (case isFlexVar?(M)
	     of Some _ -> Some({new = new,flex = flex},M,N,OT)
	      | None -> 
	   case hasFlexHead?(M)
	     of Some _ -> next {new = new,flex = Cons((M,N,OT),flex)} 
	      | None -> Some({new = new,flex = flex},M,N,OT))
	| [] -> 
     case flex
       of (M,N,OT)::flex -> Some({new = new,flex = flex},M,N,OT)
	| [] -> None

 def insert(M,N,OT,{new,flex}) = {new = (M,N,OT) ::new, flex = flex}
 op stackFromList: List(MSTerm * MSTerm * Option MSType) -> Stack
 def stackFromList pairs = 
     foldr (fn ((M,N,OT),stack) -> insert(M,N,OT,stack)) emptyStack pairs


(* Utilities for fresh and bound variables *)

 op freshVar : Context * MSType -> MSTerm

% Meta variables (flexible variables) are represented in the form
% Apply(Fun(Op "%Flex",Arrow(Nat,s)),Fun(Int n,Nat))
 op flexQId: QualifiedId = mkUnQualifiedId "%Flex"

 op mkVar: Nat * MSType -> MSTerm
 def mkVar(num,ty) = 
     Apply(Fun(Op (flexQId,Nonfix),Arrow(natType,ty,noPos),noPos),
	   Fun(Nat num,natType,noPos),noPos)

 def freshVar (context,ty) = 
     let num = ! context.counter in
     (context.counter := num + 1;
      mkVar(num,ty)
     )

 def freshBoundVar (context:Context,ty) = 
     let num = ! context.counter in
     (context.counter := num + 1;
      ("x%"^show num,ty))

 op flexRef?(t: MSTerm): Bool =
   case t of
     | Fun(Op(Qualified (UnQualified,"%Flex"),_),_,_) -> true
     | _ -> false

 op hasFlexRef?(t: MSTerm): Bool =
   existsSubTerm flexRef? t

 op isFlexVar? : MSTerm -> Option Nat
 def isFlexVar?(term) = 
     case term
       of Apply (Fun(Op(Qualified (UnQualified,"%Flex"),_),_,_),Fun(Nat n,_,_),_) -> 
	  Some n
	| _ -> None
 op  hasFlexHead? : MSTerm -> Option Nat
 def hasFlexHead?(term) = isFlexVar?(head(headForm term))

(*
\subsection{Term normalization}
A main utility in normalizing terms and applying the current 
substitution is the {\tt dereference} utility, which
uses the current substitution and beta-reduction to 
normalize a term with respect to the current substitution.

This computes weak head normal form with respect
to current substitution. This entails unraveling all
applications and applying the head beta redexes 
that appear.

The weak head normal form of a term is of the form
      (c M_2 \_dots M_k)
where standardly c is a constant, a bound variable.
In our case we allow c to be anything but an abstraction of
irrefutable patterns, where it is obvious how to perform 
beta contraction.
*)

 op dereferenceR : SubstC -> MSTerm -> MSTerm
 op dereference : SubstC -> MSTerm -> MSTerm

 def dereferenceR (S as (typeSubst,termSubst,_)) term = 
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
		      (case findLeftmost (fn (l2,_) -> l = l2) fields
		         of Some(_,trm) -> trm
			  | None -> System.fail ("Label "^l^" not found"))
		    | N -> Apply(M,N,a))
	      | M -> Apply(M,N,a))
	| _ -> term)


 def dereference S term = 
     let term1 = dereferenceR S term in
     (%writeLine (printTerm term ^" |-> \n"^ printTerm term1);
      term1)

%%
%% Wasteful, but simple beta-normalizer.
%%

 op dereferenceAll (subst: SubstC) (term: MSTerm): MSTerm =
%   let freeNames = NatMap.foldri (fn (_,trm,vs) ->
%                                    StringSet.union (StringSet.fromList
%                                                       (map (fn (n,_) -> n) (freeVars trm)),
%                                                     vs))
%                     StringSet.empty subst.2
%   in
%   let term = substitute2(term,[],freeNames) in % Purely for renaming to avoid name clashes
   let (typeSubst,termSubst,_) = subst in
   let def deref (term) = 
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
                   (case findLeftmost (fn (l2,_) -> l = l2) fields
                      of Some(_,trm) -> trm
                       | None -> System.fail ("Label "^l^" not found"))
                 | _ -> term)
       def derefAll term = dereferenceAll subst term
   in
   mapTerm(deref,fn s -> dereferenceType(subst,s),fn p -> p) term
		 		  


 def bindPattern (pat,trm):MSTerm = Lambda([(pat,trueTerm,trm)],noPos)

% Get list of applications, assumes that the term is already dereferenced.
 op headForm (term: MSTerm): MSTerms = 
     case isFlexVar? term
       of Some n -> [term]
        | None -> 
     case term
       of Apply(M,N,_) -> headForm M ++ [N]
        | _ -> [term]

 op headFormOTypes (term: MSTerm, ot: Option MSType): List (Option MSType) =
   case isFlexVar? term
       of Some n -> [None]
        | None -> 
     case term
       of Apply(M,N,_) ->
          (let (o_dom, o_ran) =
               case maybeTermType M of
                 | Some(Arrow(dom, ran, _)) -> (Some dom, Some ran)
                 | _ -> (None, None)
           in
           headFormOTypes(M, None) ++ [o_dom])
        | _ -> [ot]


 op getFieldType(ot: Option MSType, id: Id): Option MSType =
   case ot of
     | Some(Product(flds, _)) ->
       (case findLeftmost (fn (idi, _) -> idi = id) flds of
        | Some(_, fld_ty) -> Some fld_ty
        | None -> None)
     | _ -> None

 op insertFields (stack: Stack) (fields1: List(Id * MSTerm), fields2: List(Id * MSTerm)) (OT: Option MSType): Stack = 
   %% Try to put the easy cases that don't generate multiple possibilities first
   let (pairs, hard_pairs) =
     ListPair.foldr
	(fn((_,x),(id,y), (pairs, hard_pairs)) ->
           if some?(hasFlexHead? x)
             then (pairs, (x, y, getFieldType(OT, id)) :: hard_pairs)
             else ((x, y, getFieldType(OT, id)) ::  pairs, hard_pairs))
        ([],[]) (fields1, fields2)
   in
     foldl (fn (stack,(x,y,ot)) -> insert(x,y,ot,stack))	
        stack (pairs ++ hard_pairs)

(*
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
{X = N} \ \ \ \mbox{N is closed} \\[2em]

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
\lambda (x_1,\ldots,x_i,\ldots,x_n) \ . \ x_i with a suitable match on a 
record type.

Handle also \eta rules for \Pi, \Sigma, and the other type constructors.
*)

 op emptySubstitution: SubstC = (StringMap.empty,NatMap.empty,[])
 op debugHOM: Ref Nat = Ref 0
 op evaluateConstantTerms?: Bool = false     % For now until utility is proven
 op allowTrivialMatches?: Bool = false       % Allow matches that don't use match terms
 op resultLimitHOM: Nat = 8

 def match context (M,N) = 
     matchPairs(context,emptySubstitution,insert(M,N,None,emptyStack))

 op onlyTrivialMatchesPossible?(topStack:  Option (Stack * MSTerm * MSTerm * Option MSType)): Bool =
   case topStack of
     | None -> false
     | Some(_,M,N,_) ->
       (existsSubTerm
           (fn mi ->
              case mi of
                | Fun(Op(qid_m,_),_,_) | qid_m ~= flexQId ->
                  ~(existsSubTerm (fn ni ->
                                     case ni of
                                       | Fun(Op(qid_n,_),_,_) ->
                                         qid_m = qid_n
                                       | _ -> false)
                      N)
                %% Could also look for if-then-else, let or other Funs
                | _ -> false)
           M)

 op matchPairsTop (context: Context, subst: SubstC, stack0: Stack): List SubstC =
   if allowTrivialMatches? || ~(onlyTrivialMatchesPossible?(next stack0))
     then matchPairs(context, subst, stack0)
     else []

 def matchPairs (context,subst,stack0) = 
  %let _ = writeLine("Stack:\n"^ anyToString stack0) in
  let result =
   case next stack0
     of None -> [subst]
      | Some(stack,M,N,OT) -> 
   let _ = (if !debugHOM > 0 then
              (debugHOM := !debugHOM - 1;
               writeLine (printTerm (dereference subst M) ^ " =?= "
                           ^ printTerm N);
               (case OT of None -> () | Some ty -> writeLine ("ctxt_ty: "^printType ty));
               printSubst subst)
            else ())
   in
   case (dereference subst M,N)
     of 
%%
%% Pi-Pi
%%

	(Lambda(rules1, _),Lambda(rules2, _)) -> 
	if length rules1 = length rules2
	   then matchRules(context,subst,stack,rules1,rules2,[])
	else []
%%
%% Var 
%% Check that N does not contain bound variables.
%% sjw: 2/15/01 Moved before Eta
      | (Apply (Fun(Op(Qualified (UnQualified,"%Flex"),_),Arrow(_,s : MSType,_),_),
		Fun(Nat n,_,_),_),
	 N) ->
	if closedTermV(N,context.boundVars) && ~(occursProper n N)
	   then 
	   let ty2 = inferType(context.spc,subst,N) in
	   foldr (fn (subst,r) ->
                    matchPairs(context,updateSubst(subst,n,N),stack) ++ r)
             [] (unifyTypes2(context,subst,s,ty2,OT,Some N))
	else []
      | (M, N as Apply (Fun(Op(Qualified (UnQualified,"%Flex"),_),_,_), _,_)) | ~(hasFlexRef? M) ->
        matchPairs(context,subst,insert(N,M,None,insert(N,M,None,stack)))
%%
%% Eta rules
%%
      | (M as Lambda([(VarPat((_,ty), _),Fun(Bool true,_,_),_)], _),N) -> 
	foldr (fn (subst,r) -> 
               let x = freshBoundVar(context,ty) in
               matchPairs (context,subst,
                           insert(mkApply(M,mkVar x), mkApply(N,mkVar x), None, stack))   % !! Fix None
                 ++ r)
          [] (unifyTypes(context,subst,
			 inferType(context.spc,subst,M),
			 inferType(context.spc,subst,N),
                         Some N))
      | (M,Lambda([(VarPat((_,ty), _),Fun(Bool true,_,_),_)], _)) -> 
	foldr (fn (subst,r) ->
                 let x = freshBoundVar(context,ty) in
                 matchPairs(context,subst,
                            insert(bindPattern(mkVarPat x,Apply(M,mkVar x,noPos)),
                                   N,OT,stack))
                   ++ r)
          [] (unifyTypes(context,subst,
			 inferType(context.spc,subst,M),
			 inferType(context.spc,subst,N),
                         Some N))
%%
%% Sigma-Sigma
%%
      | (Record(fields1, _),Record(fields2, _)) -> 
	matchPairs (context,subst,insertFields stack (fields1,fields2) OT)
%%
%% Constants
%%
      | (Fun(f1,ty1,_),Fun(f2,ty2,_)) ->
        if f1 = Equals && f2 = Equals || f1 = NotEquals && f2 = NotEquals
          then matchPairs(context, subst, stack)
        else matchFuns(context,f1,ty1,f2,ty2,stack,subst,N)
      | (M, N as Fun(f2,ty2,_)) | evaluateConstantTerms?
                                && ~(hasFlexRef? M)
                                && ~(constantTerm? M)
                                && freeVarsRec M = [] ->
        let v = eval(M,context.spc) in
        if fullyReduced? v
          then
            let new_M = valueToTerm v in
            if equalTerm?(new_M, M)
              then []
            else if equalTerm?(new_M, N)
              then matchPairs(context,subst,stack)
            else []
        else []
      | (Var((n1,ty1), _),Var((n2,ty2), _)) ->  
	matchBase(context,n1,ty1,n2,ty2,stack,subst,N)
      %% Special case of Let for now
      | (Let([(VarPat((v1,ty1), _), e1)], b1, _), Let([(VarPat((v2,ty2), _), e2)], b2, _)) ->
        foldr (fn (subst, r) ->
                 let x = freshBoundVar(context,ty1) in
                 let S1 = [((v1,ty1), mkVar x)] in
                 let S2 = [((v2,ty2), mkVar x)] in
                 let b1 = substitute(b1,S1) in
                 let b2 = substitute(b2,S2) in
                 matchPairs (context,subst,insert(b1,b2,OT,insert(e1,e2,Some ty2,stack)))
                   ++ r)
          [] (unifyTypes(context,subst,ty1,ty2,None))
      | (Bind(qf1,vars1,M,_),Bind(qf2,vars2,N,_)) -> 
	if ~(qf1 = qf2) || ~(length vars1 = length vars2)
	   then []
	else
	let (S1,S2,subst,flag) = 
	    ListPair.foldr
	      (fn ((v1,s1),(v2,s2),(S1,S2,subst,flag)) -> 
	      if ~ flag
		 then (S1,S2,subst,flag)
	      else
	      case unifyTypes(context,subst,s1,s2,None)   % None ??
		of subst :: _ ->                          % Need to generalize!!
		   let x = freshBoundVar(context,s1) in
		   let S1 = Cons(((v1,s1),mkVar(x)),S1) in
		   let S2 = Cons(((v2,s2),mkVar(x)),S2) in
		   (S1,S2,subst,true)
		 | [] -> (S1,S2,subst,false)) 
	      ([],[],subst,true) (vars1,vars2)
	in
	if ~flag
	   then []
	else
	let M = substitute(M,S1) in
	let N = substitute(N,S2) in
	matchPairs (context,subst,insert(M,N,None,stack))
      | (IfThenElse(M1,M2,M3,_),IfThenElse(N1,N2,N3,_)) -> 
	matchPairs(context,subst,insert(M1,N1,None,insert(M2,N2,OT,insert(M3,N3,OT,stack))))
      | (Seq(tms1, _), Seq(tms2, _)) | length tms1 = length tms2 ->
        matchPairs(context,subst, foldl (fn (stack, (M,N)) -> insert(M,N,None,stack)) stack (zip(tms1, tms2)))
      | (The ((id1,ty1),M,_),The ((id2,ty2),N,_)) -> 
        foldr (fn (subst,r) ->
                 let x = freshBoundVar(context,ty1) in
                 let S1 = [((id1,ty1),mkVar x)] in
                 let S2 = [((id2,ty2),mkVar x)] in
                 let M = substitute(M,S1) in
                 let N = substitute(N,S2) in
                 matchPairs (context,subst,insert(M,N,None,stack))
                  ++ r)
          [] (unifyTypes(context,subst,ty1,ty2,Some(mkVar(id2,ty2))))
      | (LetRec(dfns1, bod1, _), LetRec(dfns2, bod2, _)) ->
        if length dfns1 = length dfns2
             && forall? (fn (((id1, ty1), _), ((id2, ty2), _)) -> id1 = id2 && unifyTypes(context,subst,ty1,ty2,None) ~= [])
                  (zip(dfns1, dfns2))
          then matchPairs(context, subst,
                          foldl (fn (stack, ((_,M),(_,N))) -> insert(M,N,None,stack))
                            (insert(bod1,bod2,None,stack))
                            (zip(dfns1, dfns2)))
          else []
                           
      | (M,_) -> 
 	%   let _ = writeLine "matchPair" in
 	%   let _ = writeLine(printTerm M) in
 	%   let _ = writeLine(printTerm N) in
 	%   let _ = printSubst subst in
	% let ty1 = inferType(context.spc,subst,M) in
	let ty2 = inferType(context.spc,subst,N) in
	% let substs = unifyTypes(context,subst,ty1,ty2,Some N) in
        let substs = [subst] in
        foldr (fn (subst, r) ->
               (case headForm(M) of
                 | [M] -> []
%
% Flexible head
%
                 | Ms as 
                   ((Apply (Fun(Op(Qualified (UnQualified,"%Flex"),_), Arrow(_,s,_),_),
                              Fun(Nat n,_,_),_))::terms) ->
                   if occursProper n N || (exists? (fn v -> ~(inVars?(v,context.boundVars))
                                                     && ~(exists? (fn t -> inVars?(v,freeVars t)) Ms))
                                             (freeVars N))
                     then [] 
                   else
                   let Ns = headForm N in
                   let OTs = headFormOTypes(N, OT) in
                   let _ = if length Ns = length OTs then () else (writeLine("Length mismatch:\n"^printTerm N);
                                                                   app (fn ot -> writeLine(case ot of None -> "None"
                                                                                             | Some ty -> "Some "^printType ty)) OTs) in
                   let substs = if length Ns = length Ms
                                  then
                                    let stack1 = foldr
                                                   (fn ((M,N,OT),stack) -> insert(M,N,OT,stack))
                                                   stack (zip3(Ms, Ns, OTs)) in
                                    matchPairs(context,subst,stack1)
                                else []
                   in
                   if ~(substs = []) then substs
                   else
                   let termTypes = map (fn M -> inferType(context.spc,subst,M)) terms in
                   
                   %% Special case of imitation where other cases are equivalent
                   if closedTermV(N,context.boundVars)
                     && ~(exists? (existsSubTerm (fn t -> some?(isFlexVar? t))) terms)
                     && noReferencesTo?(N,terms)
                    then 
                     let pats   = map (fn ty -> WildPat(ty,noPos)) termTypes in 
                     let trm    = foldr bindPattern N pats 			  in
                     let subst  = updateSubst(subst,n,trm) in
                     matchPairs(context,subst,stack) 
                   else 
                   let vars  = map (fn ty -> freshBoundVar(context,ty)) termTypes in

% 1. Recursive matching

% This was incomplete as formulated in the LaTeX documentation.
% It is being replaced by code that maps
%  n to fn x1 -> ... fn xn -> N1 (X1 x1 ... xn) ... (Xk x1 .. xn)
% where n is |terms| and k+1 = |Ns|.

                   let pats = map (fn v -> VarPat(v,noPos)) vars in
                   let varTerms = map (fn v -> Var(v,noPos)) vars in	
                   let def makeMatchForSubTerm (trm: MSTerm, bound_vs: MSVars, o_ctxt_ty: Option MSType) =
                         let ty = inferType(context.spc,subst,trm) in
                         let ty = foldr mkArrow ty (termTypes ++ List.map(fn(_,ty) -> ty) bound_vs) in
                         let v = freshVar(context,ty) in
                         (foldl (fn (t1,t2)-> Apply(t1,t2,noPos)) v (varTerms ++ map mkVar bound_vs),
                          (foldl (fn (t1,t2)-> Apply(t1,t2,noPos)) v (terms ++ map mkVar bound_vs), trm, o_ctxt_ty))

                   in
                   let (sound,N1,pairs) = 
                       case Ns
%
% When matching against a record X M1 ... Mn = (N1,...,Nk)
% create the instantiation X |-> fn x1 .. xn -> (X1 x1..xn,...,Xk x1..xn) 
% and also the matching pairs X1 M1 ... Mn = N1 ...  Xk M1 ... Mn = Nk
%
                         of [Record(fields, _)] -> 
                           let ls = map (fn (l,trm) -> 
                                           let (s_tm,pr) = makeMatchForSubTerm (trm,[],getFieldType(OT,l)) in
                                           ((l, s_tm), pr))
                                      fields
                           in
                           let (fields,pairs) = unzip ls in
                           (true, Record(fields,noPos), pairs)

                         | [IfThenElse(p,q,r,a)] ->
                           let (p1,p_pr) = makeMatchForSubTerm (p,[],None) in
                           let (q1,q_pr) = makeMatchForSubTerm (q,[],OT) in
                           let (r1,r_pr) = makeMatchForSubTerm (r,[],OT) in
                           (true, IfThenElse(p1,q1,r1,a), [p_pr,q_pr,r_pr])
                         | [Bind(qf,vs,bod,a)] ->
                           let (bod1,bod_pr) = makeMatchForSubTerm(bod,vs,None) in
                           (true, Bind(qf,vs,bod1,a), [bod_pr])
                         | [Let([(pat,bt)],bod,a)] ->
                           let pvs = patternVars pat in
                           let (bod1, bod_pr) = makeMatchForSubTerm (bod, pvs, OT) in
                           let (bt1, bt_pr) = makeMatchForSubTerm(bt, [], Some(patternType pat)) in
                           (true, Let([(pat,bt1)],bod1,a), [bt_pr, bod_pr])                           
 %                   %% case expression
                         | [Lambda(matches,a), case_arg] ->
                           let (matches1, pairs) =
                               foldr (fn ((p,c,t), (matches1, pairs)) ->
                                        let pvs = patternVars p in
                                        let (c1,c_pr) = makeMatchForSubTerm (c,pvs,None) in
                                        let (t1,t_pr) = makeMatchForSubTerm (t,pvs,OT) in
                                        (Cons((p,c1,t1), matches1),
                                         [c_pr,t_pr] ++ pairs))
                                 ([],[]) matches
                           in
                           let (case_arg1,case_arg_pr) = makeMatchForSubTerm (case_arg,[],None) in
                           (true, mkApply(Lambda(matches1,a),case_arg1), Cons(case_arg_pr, pairs))

% When matching against an application X M1 .. Mn = N1 ... Nk
% create the instantiation  X |-> fn x1 .. xn -> N1 (X2 x1..xn) ... (Xk x1..xn) 
% and also the matching pairs X2 M1 ... Mn = N2 ...  Xk M1 ... Mn = Nk
%
%
% N should be a closed term for this step to be legal/sound.
%
                           | N::Ns ->
                             %% Added Ns ~= [] because otherwise redundant with Imitation
                             if Ns ~= [] && closedTermV(N,context.boundVars)
                               then 
                                 let ls = map (fn (n,ot) -> makeMatchForSubTerm(n,[],ot)) (zip(Ns,tail OTs)) in
                                 let (Ns,pairs) = unzip ls in
                                 (true,foldl (fn (t1,t2) -> Apply(t1,t2,noPos)) N Ns,pairs)
                             else
                               (false,N,[])
                   in
                   let rec_results =
                       (if sound 
                          then
                            let N2     = foldr bindPattern N1 pats in
                            let stack1 = foldr (fn ((M,N,OT),stack) -> insert(M,N,OT,stack)) stack pairs in % Fix None
                            matchPairs(context,updateSubst(subst,n,N2),stack1)
                        else [])
                   in
                   if length rec_results  > resultLimitHOM
                     then
                       (writeLine("Result limit exceeded... "^show(length rec_results)^"\n");
                        % app printSubst rec_results;                       
                        rec_results)
                   else
                   let proj_results =
                       rec_results
                      ++
% 2. Projection.
                       (let projs  = projections (context,subst,terms,vars,ty2) in
                          (flatten
                             (map 
                                (fn (subst,proj) -> 
                                   let subst = updateSubst(subst,n,proj) in
                                   %% Repeat with the updated substitution, gets rid
                                   %% of the flexible head.
                                   let result = matchPairs(context,subst,insert(M,N,OT,stack)) in
                                   result)
                                projs)))
                    in
                    if length proj_results > resultLimitHOM
                      then proj_results
                    else
                      proj_results
                        ++ 
                        % 3. Imitation.
                        (if simpleTerm N && closedTermV(N,context.boundVars)
                           then 
                             let pats   = map (fn ty -> WildPat(ty,noPos)) termTypes in 
                             let trm    = foldr bindPattern N pats in
                             let subst  = updateSubst(subst,n,trm) in
                             matchPairs(context,subst,stack) 
                         else [])
                        
              | Ms -> 
%%
%% Rigid head
%%
	        case insertPairs(Ms, headForm N, headFormOTypes(N, OT), stack)
                  of Some stack -> matchPairs(context,subst,stack)
                   | None -> []) ++ r)
          [] substs
     in
     let _ = if !debugHOM > 0
               then if result = []
                  then (writeLine("MatchPairs failed!");
                         case next stack0
                           of None -> ()
                            | Some(_,M,N,_) ->
                              writeLine (printTerm (dereference subst M) ^ " =~= "^ printTerm N)
                             )
                  else (writeLine("MatchPairs: "^show(length result)^" results.");
                        if length result > 0 then
                          ((case next stack0 of
                              | Some(_,M,N,_) -> 
                                writeLine (printTerm (dereference subst M) ^ " = = "^ printTerm N)
                              | None -> ()) ;
                           app printSubst result)
                        else ())
              else ()
     in
     result

  op insertPairs(Ms: MSTerms, Ns: MSTerms, OTs: List(Option MSType), stack: Stack): Option Stack = 
      case (Ms,Ns,OTs)
	of (M::Ms,N::Ns,OT::OTs) -> insertPairs(Ms,Ns,OTs,insert(M,N,OT,stack))
	 | ([],[],[]) -> Some stack
	 | _ -> None


  def updateSubst((typeSubst,termSubst,condns),n,M) = 
      case isFlexVar?(M)
	of Some m | n = m -> (typeSubst,termSubst,condns)
	 | _ -> (typeSubst,NatMap.insert(termSubst,n,M),condns)

%%
%% Infer type with type dereferencing
%%
 %% Why is there a second version of this here?
 op inferType: Spec * SubstC * MSTerm -> MSType
 def inferType(spc,subst,N) = 
     case N
       of Apply(t1,t2,_) -> 
	  let ty = dereferenceType(subst,inferType(spc,subst,t1)) in
	  (case Utilities.rangeOpt(spc,ty)
	     of Some rng -> rng
	      | None -> 
		(% System.print N; printSpecWithTypesToTerminal spc;
                 System.fail 
                   ("Could not extract type for "^
                      printTermWithTypes N)))
        | Bind _ -> boolType
        | Record(fields,a) -> 
	  Product(map (fn (id,t)-> (id,inferType(spc,subst,t))) fields,a)
        | Let(_,term,_) -> inferType(spc,subst,term)
        | LetRec(_,term,_) -> inferType(spc,subst,term)
        | Var((_,ty), _) -> ty
        | Fun(_,ty, _) -> ty
        | Lambda((Cons((pat,_,body),_)), _) -> 
	  mkArrow(patternType pat,inferType(spc,subst,body))
        | Lambda([], _) -> System.fail "Ill formed lambda abstraction"
        | The ((_,ty),_,_) -> ty
        | IfThenElse(_,t2,t3,_) -> inferType(spc,subst,t2)
        | Seq([],a) -> Product([],a)
        | Seq([M],_) -> inferType(spc,subst,M)
        | Seq(M::Ms,a) -> inferType(spc,subst,Seq(Ms,a))
        | And     (t1::_,                _) -> inferType (spc, t1)
	| Any a -> Any a
        | TypedTerm  (_, ty, _) -> ty
        | mystery -> System.fail ("HO inferType: Non-exhaustive match for " ^ anyToString mystery)


(* {\tt matchPairs} should also handle "IfThenElse", "Let", "LetRec", "Seq", 
possibly by using pre-cooking.

\subsection{Projections}

Projections are correctly computed based on the type structure of the flexible variable.
Thus, if 

   X : \sigma_1 --> \sigma_2 --> \cdots --> \sigma_k --> \tau

and we process the equality

   (X M_1 ... M_k)  =  N,

then we generate the terms

   \lambda x_1  .  \lambda x_2  .  ...  \lambda x_k  .  \pi(x_i)

where \pi(x_i) is a projection on x_i and has type \tau.
The projection is computed using the following recursive unification procedure:

\begin{array}{llll}
N : \sigma  \simeq  \tau &  \{ N \} & \mbox{if \sigma\sqcap\tau \neq \bot} \\
N : \sigma_1 \times \sigma_2  \simeq  \tau & N.1: \sigma_1 \simeq \tau   \cup   
					     N.2: \sigma_2 \simeq \tau \\
N : \sigma_1 --> \sigma_2 \simeq  \tau 
			& (N\;(F\; x_1\;...\; x_n)):\sigma_2 \simeq \tau 
\end{array}
\]
*)

  op projections : Context * SubstC * MSTerms * MSVars * MSType -> List (SubstC * MSTerm)

  def projectTerm (fields,label,ty,N):MSTerm = 
      mkApply(mkFun(Project label,mkArrow(Product(fields,noPos),ty)),N)

  def projections (context,subst,(* terms *)_,vars,ty) =
      let
	  def projectType(ty1,N) = 
	      (case unifyTypes(context,subst,ty1,ty,None)  % None ??
		 of [] -> []
		  | subst :: _ -> [(subst,N)])    % Need to generalize!
	      ++
	      (case dereferenceType(subst,ty1)
		 of Product(fields, _) -> 
		    flatten 
			(map (fn (l,s) -> 
			      projectType(s,projectTerm(fields,l,s,N))) fields)
		  | Arrow(ty1,ty2,_) -> 
		    let ty1 = foldr mkArrow ty1 (map (fn (_,s) -> s) vars) in
		    let X = freshVar(context,ty1) in
		    let trm = foldl (fn (t1,v) -> mkApply(t1,mkVar(v))) X vars in
		    projectType(ty2,mkApply(N,trm)) 
		  | _ -> [])
      in
      let terms = map (fn (x,s) -> projectType(s,mkVar(x,s))) vars in
      let terms = flatten terms in
      let terms = map (fn (subst,M) -> 
                         (subst,foldr (fn(v,M) -> bindPattern(mkVarPat(v),M)) M vars))
                    terms 
      in
        let _ = if !debugHOM > 0 then
           (writeLine("Projections");
              app (fn (_,tm)  -> writeLine(printTerm tm)) terms)
              else () in

      terms

(* Recursive matching utilities

  Constants and bound variables are matched using {\tt matchBase}.
*)
  op matchBase : [a] Context * a * MSType * a * MSType * Stack * SubstC * MSTerm-> List SubstC
  def matchBase (context,x,ty1,y,ty2,stack,subst,N) =
    % let _ = writeLine("matchBase: "^anyToString x^" =?= "^ anyToString y^"\n"^printType ty1^"\n"^printType ty2) in
      if x = y
	 then 
	    foldr (fn (subst,r) -> matchPairs(context, subst,stack) ++ r)
              [] (unifyTypes(context,subst,ty1,ty2,Some N))
      else []

  op matchFuns : Context * MSFun * MSType * MSFun * MSType * Stack * SubstC * MSTerm -> List SubstC
  def matchFuns (context,x,ty1,y,ty2,stack,subst,N) =
      % let _ = writeLine("matchBase: "^anyToString x^" =?= "^ anyToString y^"\n"^printType ty1^"\n"^printType ty2) in
      if equalFun?(x, y)
	 then
            if similarType? context.spc (ty1,ty2)
               then matchPairs(context, subst, stack)
            else
            % let _ = writeLine("matchFuns: "^anyToString x^"\n"^printType ty1^"\n ~= \n"^printType ty2) in
	    foldr (fn (subst,r) -> matchPairs(context, subst, stack) ++ r)
              [] (unifyTypes(context,subst,ty1,ty2,Some N))
      else []


(* lambda-binders are matched by matching every pair of pattern against eachother.
  The pair of patterns that are compared must match precisely the same instances, thus,
  for example embed patterns must be equal.
  The variables that are bound by the patterns are substituted into the conditions and
  respective bodies such that variables bound at the same positions are equal.
*)

  def matchRules(context,subst,stack,rules1,rules2,v_subst) = 
      case (rules1,rules2)
        of ((pat1,cond1,body1)::rules1,(pat2,cond2,body2)::rules2) -> 
	   (case matchPattern(context,pat1,pat2,[],[],[])
	      of Some (S1,S2) -> 
		 let stack = insert(substitute(body1,S1),substitute(body2,S2),None,stack) in  % !! Fix None
		 let stack = insert(substitute(cond1,S1),substitute(cond2,S2),None,stack) in  % !! Fix None
		 matchRules(context,subst,stack,rules1,rules2,S2++v_subst)
	       | None -> [])
	 | ([],[]) ->
           let results = matchPairs(context,subst,stack) in
           map (fn (m1,m2,condns) ->
                  (m1,m2,map (fn t -> invertSubst(t,v_subst)) condns))
             results
	 | _ -> []

(* matchPattern, matchPatterns, and matchIrefutablePattern recurse on
  aligning the same pattern matches. *)

  op matchPattern(context: Context, pat1: MSPattern, pat2: MSPattern, pairs: List(MSPattern * MSPattern),
                  S1: MSVarSubst, S2: MSVarSubst)
      : Option (MSVarSubst * MSVarSubst) = 
      case (pat1,pat2)
        of (VarPat((x,ty1), _),VarPat((y,ty2), _)) ->
           let z  = freshBoundVar(context,ty1) in
           let S1 = Cons(((x,ty1),mkVar(z)),S1) in
           let S2 = Cons(((y,ty2),mkVar(z)),S2) in
           matchPatterns(context,pairs,S1,S2)
         | (EmbedPat(c1,None,ty1,_),EmbedPat(c2,None,ty2,_)) -> 
           if c1 = c2
               then matchPatterns(context,pairs,S1,S2)
           else None
         | (EmbedPat(c1,Some pat1,ty1,_),EmbedPat(c2,Some pat2,ty2,_)) -> 
           if c1 = c2
               then matchPattern(context,pat1,pat2,pairs,S1,S2)
           else None
         | (RecordPat(fields1, _),RecordPat(fields2, _)) -> 
           let pairs1 = ListPair.map (fn ((_,p1),(_,p2))-> (p1,p2)) (fields1,fields2) in
           matchPatterns(context,pairs1 ++ pairs,S1,S2)
         | (WildPat(ty1, _),WildPat(ty2, _)) -> Some(S1,S2)
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
         | (QuotientPat(p1,t1,_,_),QuotientPat(p2,t2,_,_)) -> 
           if t1 = t2 then matchPatterns(context,pairs,S1,S2) else None
         | (RestrictedPat(p1,t1,_),RestrictedPat(p2,t2,_)) -> 
           if equalTerm?(t1,t2) then matchPatterns(context,pairs,S1,S2) else None
         | _ -> 
            case matchIrefutablePattern(context,pat1,S1)
              of None -> None
               | Some S1 -> 
            case matchIrefutablePattern(context,pat2,S2)
              of Some S2 -> matchPatterns(context,pairs,S1,S2)
               | None -> None

  op matchPatterns(context: Context, pairs: List(MSPattern * MSPattern), S1: MSVarSubst, S2: MSVarSubst)
     : Option (MSVarSubst * MSVarSubst) = 
     case pairs
       of (p1,p2)::pairs -> matchPattern(context,p1,p2,pairs,S1,S2)
        | [] -> Some (S1,S2)	   
  op matchIrefutablePattern(context: Context, pat: MSPattern, S: MSVarSubst)
     : Option MSVarSubst = 
     case pat
       of WildPat _ -> Some S
        | VarPat((x,s),a) -> 
          let z = freshBoundVar(context,s) in 
          Some(Cons(((x,s),Var(z,a)),S))
        | RecordPat(fields, _) -> 
          let
              def loop(fields,S): Option MSVarSubst = 
                  case fields
                    of (l,p)::fields -> 
                       (case matchIrefutablePattern(context,p,S)
                          of Some S -> loop(fields,S)
                           | None -> None)
                     | [] -> Some S
          in
               loop(fields,S)
        | _ -> None


(*
Occurs check.
Our matching algorithm includes the occurs check, as there we do not require the 
input to be a matching problem. In fact, in the glue code generation, proper 
skolemization transforms a proper matching problem into an inproper one.
*)

  op occursProper : Nat -> MSTerm -> Bool
  def occursProper n M = 
      case isFlexVar?(M)
	of Some _ -> false
	 | None -> occurs n M

  op occurs : Nat -> MSTerm -> Bool
  op occursP : [a] Nat -> a * MSTerm -> Bool
  def occursP n (_,M) = occurs n M
  def occurs n term = 
      case term
        of Var _ -> false
	 | Fun _ -> false
	 | Apply(M,N,_) -> 
	   (case isFlexVar?(term)
	      of Some m -> n = m
	       | None -> occurs n M || occurs n N)
	 | Record(fields, _) -> 
	   exists? (occursP n) fields
	 | Lambda(rules, _) -> 
	   exists? (fn (_,cond,body) -> 
			occurs n cond || occurs n body) rules
	 | Seq(Ms, _) -> exists? (occurs n) Ms
	 | IfThenElse(M1,M2,M3,_) -> 
	   occurs n M1 || occurs n M2 || occurs n M3
	 | The (var,M,_) -> occurs n M
	 | Bind(_,vars,M,_) -> occurs n M
	 | Let(decls,M,_) -> 
	   occurs n M || exists? (occursP n) decls
	 | LetRec(decls,M,_) ->
	   occurs n M || exists? (occursP n) decls

(*
Closed terms
closedTerm  determines whether a term contains any free variables or not.
closedTermV detects existence of free variables not included in the argument 
*)
  op closedTerm : MSTerm -> Bool
  op closedTermV : MSTerm * MSVars -> Bool

  def closedTerm(term) = closedTermV(term,[])

%  def patternVars(pat:Pattern) = 
%      case pat
%        of VarPat(v, _) -> [v]
%	 | WildPat _ -> []
%	 | RecordPat(fields, _) -> 
%	   flatten (map (fn (_,p) -> patternVars p) fields)
%	 | EmbedPat(_,None,_,_) -> []
%	 | EmbedPat(_,Some p,_,_) -> patternVars p
%	 | QuotientPat(p,t,_) -> patternVars p
%	 | AliasPat(p1,p2,_) -> patternVars p1 ++ patternVars p2 
%	 | _ -> []

  def closedTermV(term,bound) = 
      case term
        of Var((v,_), _) -> exists? (fn (w,_) -> v = w) bound	        
	 | Fun _ -> true
	 | Apply(M,N,_) -> closedTermV(M,bound) && closedTermV(N,bound)
	 | Record(fields, _) -> 
	   forall? (fn (_,M) -> closedTermV(M,bound)) fields
	 | Lambda(rules, _) -> 
	   forall? (fn (pat,cond,body) -> 
			let bound = patternVars(pat) ++ bound in
			(closedTermV(cond,bound) && 
			 closedTermV(body,bound))) rules
	 | Seq(Ms, _) -> forall? (fn M -> closedTermV(M,bound)) Ms
	 | IfThenElse(M1,M2,M3,_) -> 
	   closedTermV(M1,bound) && 
	   closedTermV(M2,bound) && 
	   closedTermV(M3,bound)
	 | Bind(_,vars,M,_) -> closedTermV(M,vars ++ bound)
	 | The (var,M,_) -> closedTermV (M,Cons(var, bound))
	 | Let(decls,M,_) -> 
	   forall? (fn (_,M) -> closedTermV(M,bound)) decls 
	   && 
	   (let bound = foldr 
		(fn ((pat,_),bound) -> patternVars pat ++ bound) 
		bound decls 
	   in
	   closedTermV(M,bound) )
	 | LetRec(decls,M,_) ->
	   let bound = (map (fn (v,_) -> v) decls) ++ bound in
	   closedTermV(M,bound) && 
	   (forall? (fn (_,M) -> closedTermV(M,bound)) decls) 

 op noReferencesTo?(tm: MSTerm, tms: MSTerms): Bool =
   ~(existsSubTerm (fn t -> termIn?(t,tms)) tm)

(* Type unification}
 Unification of types is similar to the one in AstTypes.
 It uses a list of already processed type pairs to avoid cycling through
 recursive definitions.
*)

  type Unification = 
    | NotUnify  MSType * MSType 
    | Unify     SubstC 

  op  unifyL : [a] SubstC * MSType * MSType * List(a) * List(a) * List (MSType * MSType) * Option MSTerm *
                  (SubstC * a * a * a * List(MSType * MSType) * Option MSTerm -> List Unification)
                  ->  List Unification
  def unifyL(subst,ty1,ty2,l1,l2,equals,optTerm,unify): List Unification = 
      case (l1,l2)
        of ([],[]) -> [Unify subst]
         | (e1::l1,e2::l2) -> 
	   (foldr (fn (r1,r) ->
                     case r1 of
                       | Unify subst -> unifyL(subst,ty1,ty2,l1,l2,equals,None,unify) ++ r
                       | notUnify -> Cons(notUnify, r) )
              []  (unify(subst,e1,e2,e1,equals,optTerm)))
         | _ -> [NotUnify(ty1,ty2)]

  op  occursRec : SubstC * String * MSType -> Bool
  def occursRec (subst,v,ty) = 
      case ty 
        of Base(_,tys,_) -> exists? (fn s -> occursRec(subst,v,s)) tys
 	 | Arrow(s1,s2,_) -> occursRec(subst,v,s1) || occursRec(subst,v,s2)
	 | Product(fields, _) -> exists? (fn (_,s) -> occursRec(subst,v,s)) fields
	 | CoProduct(fields, _) -> 
	   exists? (fn(_,None)-> false | (_,Some s)-> occursRec(subst,v,s)) fields
	 | TyVar(w, _) -> 
	   (case StringMap.find(subst.1,w)
	      of Some s -> occursRec (subst,v,s)
	       | None -> v = w) 
	 | Subtype(s,_,_) -> occursRec(subst,v,s)
	 | Quotient(s,_,_) -> occursRec(subst,v,s)
         | Boolean _ -> false
%         | _ -> let _ = writeLine("occursRec missing case: "^printMSType ty) in
%                false

  def dereferenceType(subst:SubstC,ty) = 
      case ty
        of TyVar(v, _) -> 
	   (case StringMap.find(subst.1,v)
              of Some ty -> dereferenceType(subst,ty)	
	       | None -> ty)
	 | _ -> ty

  op conditionalMatch?(unifiers: List SubstC): Bool =
    case unifiers of
      | [(_, _, conds)] -> conds ~= []
      | _ -> false

  op unifyTypes2(context: Context, subst: SubstC, ty1: MSType, ty2: MSType, OT: Option MSType, optTerm: Option MSTerm): List SubstC = 
    let main_unifiers = unifyTypes(context, subst, ty1, ty2, optTerm) in
    case OT of
      | Some ctxt_ty2 | conditionalMatch? main_unifiers && ~(equalType?(ty2, ctxt_ty2)) ->
        % let _ = writeLine("Trying to match "^printType ctxt_ty2^" instead of "^printType ty2) in
        unifyTypes(context, subst, ty1, ctxt_ty2, optTerm) ++ main_unifiers
      | _ -> main_unifiers


  %% Not symmetric wrt subtypes
  op unifyTypes(context: Context, subst: SubstC, ty1: MSType, ty2: MSType, optTerm: Option MSTerm): List SubstC = 
      % let _ = case optTerm of None -> () | Some t -> writeLine("Term: "^printTerm t) in
      let spc = context.spc in
      let
	def insert(v,ty,(typeSubst,termSubst,condns)): SubstC = 
	    (StringMap.insert(typeSubst,v,ty),termSubst,condns)
        def addCondition(condn: MSTerm, subst as (typeSubst,termSubst,condns): SubstC): SubstC =
          if trueTerm? condn || termIn?(condn,condns) then subst
            else (typeSubst,termSubst,Cons(condn,condns))
	def unifyCP(subst,ty1,ty2,r1,r2,equals):List Unification = 
	    unifyL(subst,ty1,ty2,r1,r2,equals,None,
		   fn(subst,(id1,s1),(id2,s2),_,equals,_) -> 
		      if id1 = id2 
			then 
			(case (s1,s2)
			   of (None,None) -> [Unify subst] 
			    | (Some s1,Some s2) -> unify(subst,s1,s2,s1,equals,None)
			    | _ -> [NotUnify(ty1,ty2)])
		      else [NotUnify(ty1,ty2)])
	def unifyP(subst,ty1,ty2,r1,r2,equals): List Unification = 
	    unifyL(subst,ty1,ty2,r1,r2,equals,None,
		   fn(subst,(id1,s1),(id2,s2),_,equals,_) -> 
		      if id1 = id2 
			then unify(subst,s1,s2,s1,equals,None)
		      else [NotUnify(ty1,ty2)])
	def unify(subst,ty1:MSType,ty2:MSType,ty1_orig:MSType,equals,optTerm: Option MSTerm): List Unification =
              % let _ = writeLine("Matching "^printType ty1^" --> "^printType(dereferenceType(subst,ty1))^" with \n"
              %                 ^printType ty2^" --> "^printType(dereferenceType(subst,ty2))) in
              % let _ = writeLine(case optTerm of None -> "No term" | Some t -> "Term: "^printTerm t) in
	    case (dereferenceType(subst,ty1), dereferenceType(subst,ty2))
	      of (Boolean _, Boolean_) -> [Unify subst]
               | (CoProduct(r1,_),CoProduct(r2,_)) -> 
		 unifyCP(subst,ty1,ty2,r1,r2,equals)
	       | (Product(r1,_),Product(r2,_)) -> 
		 unifyP(subst,ty1,ty2,r1,r2,equals)
	       | (Arrow(t1,t2,_),Arrow(s1,s2,_)) -> 
		 foldr (fn (r1,r) ->
                          case r1 of
                            | Unify (subst) -> unify(subst,t2,s2,t2,equals,None) ++ r
                            | notUnify -> Cons(notUnify, r))
                   [] (unify(subst,t1,s1,t1,equals,None))
	       | (Quotient(ty1,trm1,_),Quotient(ty2,trm2,_)) -> % Shouldn't happen anymore
		 if equalTerm?(trm1, trm2)
		    then unify(subst,ty1,ty2,ty1,equals,None)
		 else [NotUnify (ty1,ty2)]
	       | (Subtype(ty1,p1,_),Subtype(ty2,p2,_))
                   | equalTermStruct?(p1,p2) || equalTermStruct?(dereferenceAll subst p1, dereferenceAll subst p2) ->
                 unify(subst,ty1,ty2,ty1_orig,equals,optTerm)
	       | (bty1 as Base(id1,ts1,_), bty2 as Base(id2,ts2,_)) -> 
		 if exists? (fn p -> p = (bty1,bty2)) equals
		    then [Unify subst]
		 else 
		 if id1 = id2 
		    then
                      % let (n_ty1, n_ty2) = raiseSubtypes(bty1, bty2, spc) in
                      % let _ = writeLine("Lifted types:\n"^printType(n_ty1)^"\n"^printType n_ty2) in
                      unifyL(subst,bty1,bty2,ts1,ts2,equals,None,unify)
	         else
                 (case (tryUnfoldBase spc bty1, tryUnfoldBase spc bty2) of
                    | (None, None) -> [NotUnify (bty1,bty2)]
                    | (Some s1, Some s2) ->
                      if possiblySubtypeOf?(bty1, bty2, spc)
                        then unify(subst,s1,bty2,ty1_orig,
                                   Cons((bty1,bty2),equals),optTerm)
                        else if possiblySubtypeOf?(bty2, bty1, spc)
                        then unify(subst,bty1,s2,ty1_orig,
                                   Cons((bty1,bty2),equals),optTerm)
                        else unify(subst,s1,s2,ty1_orig,
                                   Cons((bty1,bty2),equals),optTerm)
                    | (Some s1, None)    -> unify(subst,s1,bty2,ty1_orig,
                                                  Cons((bty1,bty2),equals),optTerm)
                    | (None, Some s2)    -> unify(subst,bty1,s2,ty1_orig,
                                                  Cons((bty1,bty2),equals),optTerm))
	       | (TyVar(v, _),TyVar(w, _)) -> 
		 if v = w then [Unify subst] else [Unify (insert(v,ty2,subst))]
	       | (TyVar(v, _),_) -> 
		     if occursRec(subst,v,ty2) 
			 then [NotUnify (ty1,ty2)]
		     else [Unify(insert(v,ty2,subst))]
	       | (_,TyVar(v, _)) -> 
		     if occursRec(subst,v,ty1) 
			 then [NotUnify (ty1,ty2)]
		     else [Unify(insert(v,ty1,subst))]
	       | (bty1 as Base _, bty2)
                   | some?(tryUnfoldBase spc bty1) && ~(possiblySubtypeOf?(bty2, bty1, spc))-> 
                 let Some s1 = tryUnfoldBase spc bty1 in
                 unify(subst,s1,bty2,ty1_orig,Cons((bty1,bty2),equals),optTerm)
	       | (bty1, bty2 as Base _)
                   | some?(tryUnfoldBase spc bty2) && ~(possiblySubtypeOf?(bty1, bty2, spc))->
		 let Some s2 = tryUnfoldBase spc bty2 in
		 unify(subst,bty1,s2,ty1_orig,Cons((bty1,bty2),equals),optTerm)
               %% Analysis could be smarter here so that order of subtypes is not so important
               | (bty1 as Subtype(ty1 ,p1, _), ty2) | ~(possiblySubtypeOf?(ty2, bty1, spc)) ->
                 % let _ = writeLine(case optTerm of None -> "No term" | Some t -> "Term: "^printTerm t) in
                 (case optTerm of
                       | None -> [NotUnify(bty1,ty2)]
                       | Some tm ->
                         case unify(subst,ty1,ty2,ty1_orig,equals,optTerm) of
                           | (Unify subst) :: _ ->    % Should generalize
                             let p1 = dereferenceAll subst p1 in
                             % let _ = writeLine("Pred: "^printTermWithTypes p1) in
                             % let _ = printSubst subst in
                             let condn = simplifiedApply(p1,tm,context.spc) in
                             % let _ = writeLine("Condn: "^printTermWithTypes condn) in
                             if falseTerm? condn then [NotUnify(ty1,ty2)]
                             else [Unify(addCondition(condn, subst))]
                           | result -> result)
                 ++ (case ty1_orig of
                    | TyVar(v,_) | equalType?(stripSubtypes(spc,ty1), stripSubtypes(spc,ty2)) ->
                      %% If we are matching a type variable then loosen match of variable
                      %% Could using ty2 cause overshoot?
                      [Unify(insert(v,ty2,subst))]
                    | _ -> [])
	       | (ty,Subtype(ty2,_,_)) -> unify(subst,ty,ty2,ty1_orig,equals,optTerm)
	       | _ -> [NotUnify(ty1,ty2)]
      in
      let results = unifyL(subst,ty1,ty2,[ty1],[ty2],[],optTerm,unify) in
      let good_results = removeDuplicates(filter (embed? Unify) results) in
      let _ = if length good_results > 1 then writeLine("unifyTypes: "^show (length good_results)^" results!\n"
                                                          ^anyToPrettyString(map (fn Unify x -> x) good_results)) else () in
      let results = if good_results = [] then results else good_results in
      foldr (fn (r1,r) ->
             case r1 of
               | NotUnify (s1,s2) -> 
                 (if !debugHOM > 0 then (writeLine (printType s1^" ~= "^printType s2);
                                         printSubst subst)
                  else ();
                  r)
               | Unify subst ->
                 (if !debugHOM > 0 then (writeLine (printType ty1^" =t= "^printType ty2);
                                         printSubst subst)
                    else (); 
                  Cons(subst,r)))
        [] results

(* Normalization
To make the matching steps easier we normalize specifications
before matching by deleting {\tt IfThenElse}, {\tt Let}, and 
{\tt LetRec}, replacing these by function symbols and applications.
*)

  op doNormalizeTerm : Spec -> MSTerm -> MSTerm
  def doNormalizeTerm spc term = 
    case term of
      | Let ([(pat,N)],M,a) -> Apply (Lambda([(pat,trueTerm,M)],a),N,a)
      | Let (decls,M,a) -> 
         let (pats,Ns) = unzip decls in
          Apply (Lambda([(mkTuplePat pats,trueTerm,M)], a),mkTuple Ns,a)
       % | IfThenElse (M,N,P,a) -> 
       %    let ty = inferType(spc,N) in
       %    Apply(Fun(Op(Qualified("TranslationBuiltIn","IfThenElse"),Nonfix),
       %              mkArrow(mkProduct [boolType,ty,ty],ty), a),
       %          mkTuple [M,N,P], a)
%       | LetRec(decls,M,_) -> 
%          System.fail "Replacement of LetRec by fix has not been implemented"
      | Seq (Ms,a) -> 
         let
            def loop Ms = 
              case Ms of
                | [] -> mkTuple []
                | [M] -> M
                |  M::Ms -> 
                    let ty = Utilities.inferType(spc,M) in
                      Apply(bindPattern(WildPat(ty,a),loop Ms),M,a)
          in
            loop Ms
       | term -> term

  def normalizeTerm (spc:Spec) = 
      let doTerm = doNormalizeTerm spc in
      mapTerm(doTerm,fn s -> s,fn p -> p)

  def normalizeSpec (spc:Spec) =
      let doTerm = doNormalizeTerm spc in
      mapSpec(doTerm,fn s -> s,fn p -> p) spc

  def doDeNormalizeTerm(term:MSTerm):MSTerm = 
      case term
	of Apply(Lambda([(WildPat _,Fun(Bool true,_,_),M)], _),N,a) -> 
	   Seq([N,M],a)
	 | Apply(Lambda([(pat,Fun(Bool true,_,_),M)], _),N,a) -> 
	   Let([(pat,N)],M,a)
	 % | Apply(Fun(Op(Qualified("TranslationBuiltIn","IfThenElse"),
	 %             Nonfix),_,_),
         %         Record([(_,M),(_,N),(_,P)], _), a) -> 
	 %   IfThenElse(M,N,P, a)
	 | term -> term 

  def deNormalizeSpec = 
      mapSpec(doDeNormalizeTerm,fn s -> s,fn p -> p) 

  def deNormalizeTerm  = 
      mapTerm(doDeNormalizeTerm,fn s -> s,fn p -> p)

%% Rewriter ccontrol defaults
 op MetaSlangRewriter.traceRewriting : Nat = 0
 op MetaSlangRewriter.traceShowsLocalChanges?: Bool = true
 op MetaSlangRewriter.useStandardSimplify?: Bool = true
 op MetaSlangRewriter.debugApplyRewrites?:  Bool = false
 op MetaSlangRewriter.maxDepth: Nat = 100
 op MetaSlangRewriter.backwardChainMaxDepth: Nat = 10
 op MetaSlangRewriter.conditionResultLimit: Nat = 4
 op MetaSlangRewriter.termSizeLimit: Nat = 1000

 op makeContext (spc: Spec): Context = 
     {  spc        = spc,
	trace      = true,
	traceDepth = Ref 0,
	traceIndent = Ref 0,
        boundVars  = [],
	counter    = Ref 1,
        traceRewriting          = traceRewriting,
        traceShowsLocalChanges? = traceShowsLocalChanges?,
        useStandardSimplify?    = useStandardSimplify?,
        debugApplyRewrites?     = debugApplyRewrites?,
        maxDepth                = maxDepth,
        backwardChainMaxDepth   = backwardChainMaxDepth,
        conditionResultLimit    = conditionResultLimit,
        termSizeLimit           = termSizeLimit     % Should be computed
      }
 
 op printContextOptions(context: Context): () =
   (writeLine("\nContext:");
    writeLine("traceRewriting: "^show context.traceRewriting);
    writeLine("traceShowsLocalChanges?: "^show context.traceShowsLocalChanges?);
    writeLine("useStandardSimplify?: "^show context.useStandardSimplify?);
    writeLine("debugApplyRewrites?: "^show context.debugApplyRewrites?);
    writeLine("maxDepth: "^show context.maxDepth);
    writeLine("backwardChainMaxDepth: "^show context.backwardChainMaxDepth);
    writeLine("conditionResultLimit: "^show context.conditionResultLimit);
    writeLine("termSizeLimit: "^show context.termSizeLimit))

 op setBound : Context * MSVars -> Context
 def setBound(ctxt,bv) = ctxt << {boundVars = bv}


  op [a] printSubst: StringMap(AType a) * NatMap.Map(ATerm a) * List (ATerm a) -> ()
  def printSubst(typeSubst,termSubst,condns) = 
      (writeLine "---------- substitution ---------";
	StringMap.appi 
	(fn (s,ty) -> 
	     writeLine(s^" |-> "^printType ty^" "))
	typeSubst;
       writeLine "";
       NatMap.appi
	(fn (i,trm) -> 
	     writeLine(Nat.show i^" |-> "^ printTerm trm^" "))
	termSubst;
       writeLine "";
       if condns = [] then ()
         else (writeLine "Conditions:";
               List.app (fn t -> writeLine(printTerm t)) condns);
               writeLine "")

(* Freeze and thaw type variables in term
In order to ensure that type variables in a term to be rewritten are not
participating in unification we introduce freeze and thaw operations.
*)

 def freezeTerm(spc,term:MSTerm) = 
     let term = normalizeTerm spc term in
     let
	doFreeze = fn (s as TyVar _) -> Base(mkUnQualifiedId("TypeVar!"),[s],noPos)
		  | s -> s
     in
     mapTerm(fn tm -> tm,doFreeze,fn p -> p) term

 def thawTerm(term:MSTerm) =
     let term = deNormalizeTerm term in
     let
	doThaw = fn(Base(Qualified (UnQualified,"TypeVar!"),[s],_)) -> s
		  | s -> s
     in
     mapTerm(fn tm -> tm,doThaw,fn p -> p) term

endspec

