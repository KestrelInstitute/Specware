% derived from SW4/Languages/MetaSlang/ADT/Specs/SpecUtilities.sl, v1.3

spec { 
 import StandardSpec    % defines sorts Spec, Term, etc.
 import ../Legacy/DataStructures/IntegerSet
 import ../Legacy/DataStructures/ListPair 
 import ../Legact/DataStructures/ListUtilities
 import ../Legacy/DataStructures/StringUtilities 
 import TypeCheckUtilities

 sort Vars = List Var

 op specEqual? : Spec * Spec -> Boolean
 op subspec?   : Spec * Spec -> Boolean

 op substitute    : Term * List (Var * Term) -> Term
%op freeVars      : fa(a) ATerm a -> Vars
 op freeVars      : Term -> Vars

 %% Translate a term encoding an assignment to a list of pairs.
 %% Redundant assignments of a variable to itself are eliminated.

 op extractAssignment : Term * Term -> List (Pattern * Term)

 %% Unfold the imports by expanding the argument
 %% list of specs.

 op unfoldImports  : List(Spec) * Spec -> Spec 

 %% merge in imports without renaming sorts and ops.
 %% mergeImports is used when ops or sorts are not redefined
 %% in the spec, and the other specs do not import things themselves (besides
 %% Nat, String, List, Integer, Boolean, Char).

 op mergeImports : List(Spec) * Spec -> Spec

 op removeDefinitions : Spec -> Spec

 op disableProperties : IntegerSet.Set * Spec -> Spec

 %% Were in ../transformations/meta-slang-match.sl
 op isFree        : Var * Term -> Boolean
 op replace       : Term * List (Term * Term) -> Term
 op patternToTerm : Pattern -> Option Term

% --------------------------------------------------------------------------
 def isFree(v,term:Term) = 
   case term
     of Var(w,_)               -> v = w
      | Apply(M1,M2,_)         -> isFree(v,M1) or isFree(v,M2)
      | Record(fields,_)       -> exists (fn (_,M) -> isFree(v,M)) fields
      | Fun _                  -> false
      | Lambda(rules,_)        -> exists (fn (pat,cond,body) -> 
					  ~(isPatBound(v,pat)) 
					  & 
					  (isFree(v,cond) or isFree(v,body)))
                                         rules
      | Let(decls,M,_)         -> exists (fn (_,M) -> isFree(v,M)) decls
			  	  or
				  (all (fn (p,_) -> ~(isPatBound(v,p))) decls
				   &
				   isFree(v,M))
      | LetRec(decls,M,_)      -> all (fn (w,_) -> ~(v = w)) decls 
				  & 
				  (exists (fn (_,M) -> isFree(v,M)) decls
				   or 
				   isFree(v,M)) 
      | Bind(b,vars,M,_)       -> all (fn w -> ~(v = w)) vars 
			          & 
			          isFree(v,M)
      | IfThenElse(t1,t2,t3,_) -> isFree(v,t1) or 
			          isFree(v,t2) or 
				  isFree(v,t3)

 def isPatBound(v,pat:Pattern) = 
   case pat
     of AliasPat(p1,p2,_)      -> isPatBound(v,p1) or isPatBound(v,p2)
      | EmbedPat(_,Some p,_,_) -> isPatBound(v,p)
      | VarPat(w,_)            -> v = w
      | RecordPat(fields,_)    -> exists (fn (_,p) -> isPatBound(v,p)) fields
      | RelaxPat(p,_,_)        -> isPatBound(v,p)
      | QuotientPat(p,_,_)     -> isPatBound(v,p)
      | _ -> false

 def replace(M,sub) = 
   if null sub then 
     M 
   else 
     let freeNames = 
         foldr 
	   (fn ((_,trm),vs) -> 
	    StringSet.union (StringSet.fromList (map (fn (n,_)-> n) (freeVars trm)),
			     vs))
	   StringSet.empty sub
     in 
     replace2(M,sub,freeNames)
 
 def replace2(M,sub,freeNames) = 
   let
       def rep(M:Term):Term = 
         case lookup(fn N -> N = M,sub)
	   of Some N -> N
	    | None -> 
	 case M
	   of Apply(M1,N1,a)  -> 
	      Apply(rep M1,
		    rep N1,
		    a)
	    | Record(fields,a) -> 
	      Record (map (fn (l,M)-> (l,rep M)) fields,
		      a)
	    | Let(decls,M,a) -> 
	      let decls = map (fn(p,M)-> (p,rep M)) decls in
	      let (decls,freeNames,sub) = foldr repLet ([],freeNames,sub) decls
	      in
	      Let(decls,
		  replace2(M,sub,freeNames),
		  a)
	    | LetRec(decls,M,a) -> 
	      let (vars,sub,freeNames) = repBoundVars(map (fn(v,_) -> v) decls,sub,freeNames) 
	      in
	      let terms = List.map (fn (_,trm) -> replace2(trm,sub,freeNames)) decls in
	      let decls = ListPair.zip (vars,terms) in
	      LetRec(decls,
		     replace2(M,sub,freeNames),
		     a)
	    | Lambda(rules,a) -> 
	      Lambda(List.map repRule rules,
		     a)
	    | Bind(b,vars,M,a) -> 
	      let (vars,sub,freeNames) = repBoundVars(vars,sub,freeNames) in
	      Bind(b,
		   vars,
		   replace2(M,sub,freeNames),
		   a)
	    | Seq(Ms,a) ->
	      Seq (List.map rep Ms,
		   a)
	    | IfThenElse(M1,M2,M3,a) -> 
	      IfThenElse(rep M1,
			 rep M2,
			 rep M3,
			 a)
	    | M -> M

	def repRule (pat,cond,term) = 
	  let (pat,sub,freeNames) = repPattern(pat,sub,freeNames) in
	  if null sub then
	    (pat, cond, term) 
	  else
	    (pat, replace2(cond,sub,freeNames), replace2(term,sub,freeNames)) 

	def repLet ((pat,trm),(decls,freeNames,sub)) = 
	  let (pat,sub,freeNames) = repPattern(pat,sub,freeNames) in
	  (cons((pat,trm),decls),freeNames,sub)
   in
     rep(M)

 op repPattern : Pattern * List (Term * Term) * StringSet.Set -> Pattern * List (Term * Term) * StringSet.Set
 op repBoundVars: Vars *  List (Term * Term) * StringSet.Set -> Vars *  List (Term * Term) * StringSet.Set


 def repBoundVars(vars,sub,freeNames) = 
   foldr (fn(v,(vars,sub,freeNames)) -> 
	  let (v,sub,freeNames) = repBoundVar(v,sub,freeNames) in
	  (cons(v,vars),sub,freeNames))
         ([],sub,freeNames) vars
	
 def repBoundVar((id,s),sub,freeNames) = 
   if StringSet.member(freeNames,id) then
     let id2 = StringUtilities.freshName(id,freeNames) in
     let sub2 = cons((mkVar(id,s),mkVar(id2,s)),sub) in
     ((id2,s),sub2,freeNames)
   else
     ((id,s),sub,freeNames)

 def repPattern(pat,sub,freeNames) = 
   case pat:Pattern
     of VarPat(v,a) ->
        let (v,sub,freeNames) = repBoundVar(v,sub,freeNames) in
	(VarPat(v,a),sub,freeNames) 
      | RecordPat(fields,a) -> 
	let (fields,sub,freeNames) = 
	    foldr (fn ((id,p),(fields,sub,freeNames)) -> 
		   let (p,sub,freeNames) = repPattern(p,sub,freeNames) in
		   (cons((id,p),fields),sub,freeNames))
	          ([],sub,freeNames) fields
	in
	  (RecordPat(fields,a),sub,freeNames)
      | EmbedPat(oper,Some pat,srt,a) -> 
	let (pat,sub,freeNames) = repPattern(pat,sub,freeNames) in
	(EmbedPat(oper,Some pat,srt,a),sub,freeNames)
      | EmbedPat(oper,None,srt,_) -> 
	(pat,sub,freeNames)
      | AliasPat(p1,p2,a) ->
	let (p1,sub,freeNames) = repPattern(p1,sub,freeNames) in
	let (p2,sub,freeNames) = repPattern(p2,sub,freeNames) in
	(AliasPat(p1,p2,a),sub,freeNames)
      | QuotientPat(pat,trm,a) -> 
	let (pat,sub,freeNames) = repPattern(pat,sub,freeNames) in
	(QuotientPat(pat,trm,a),sub,freeNames)
      | RelaxPat(pat,trm,a) -> 	
	let (pat,sub,freeNames) = repPattern(pat,sub,freeNames) in
	(RelaxPat(pat,trm,a),sub,freeNames)
      | _ -> (pat,sub,freeNames)


 %----------------------
 def freeVars(M) = 
   let vars = freeVarsRec(M) in
   ListUtilities.removeDuplicates vars

 def freeVarsRec(M:Term) =   
   case M
     of Var(v,_) -> [v]
      | Apply(M1,M2,_)   -> freeVarsRec(M1) ++ freeVarsRec(M2)
      | Record(fields,_) -> freeVarsList fields
      | Fun _            -> []
      | Lambda(rules,_)  -> List.foldr (fn (rl,vs) -> vs ++ freeVarsMatch rl) [] rules
      | Let(decls,M,_)   -> 
        let (patVars,trmVars) = List.foldr (fn((p,trm),(vs1,vs2)) -> 
					    (patVars  p ++ vs1,
					     freeVarsRec trm ++ vs2))
                                           ([],[]) decls
	in
        let mVars = freeVarsRec(M) in
	trmVars ++ (deleteVars(mVars,patVars)) 
      | LetRec(decls,M,_) -> 
	let vars1 = freeVarsRec M in
	let vars2 = freeVarsList(decls) in
	deleteVars(List.map (fn(v,_) -> v) decls,vars1 ++ vars2)
      | Bind(b,vars,M,_)  -> 
	deleteVars(freeVarsRec(M),vars)
      | IfThenElse(t1,t2,t3,_) -> 
	freeVarsRec(t1) ++ freeVarsRec(t2) ++ freeVarsRec(t3)

 op  freeVarsList : fa(a) List(a * Term) -> Vars
 def freeVarsList list = 
   List.foldr (fn ((_,trm),vs) -> vs ++ freeVarsRec trm) [] list

 def deleteVars(vars1,vars2) = 
   List.foldr ListUtilities.delete vars1 vars2

 def freeVarsMatch (pat,cond,body) = 
   let vars  = patVars pat in
   let vars1 = freeVarsRec cond in
   let vars2 = freeVarsRec body in
   deleteVars(vars1 ++ vars2,vars)

 def patVars(pat:Pattern) = 
   case pat
     of AliasPat(p1,p2,_)      -> patVars(p1) ++ patVars(p2)
      | VarPat(v,_)            -> [v]
      | EmbedPat(_,Some p,_,_) -> patVars p
      | EmbedPat _             -> []
      | RecordPat(fields,_)    -> List.foldr (fn ((_,p),vars) -> patVars p ++ vars) 
                                             [] fields
      | WildPat _              -> []
      | StringPat _            -> []
      | BoolPat _              -> []
      | CharPat _              -> []
      | NatPat  _              -> []
      | RelaxPat(p,_,_)        -> patVars p
      | QuotientPat(p,_,_)     -> patVars p


 op  lookup : fa(a,b) (a  -> Boolean) * List(a * b) -> Option b 
 def lookup (desired_key?, association_list) = 
   case association_list of
    | [] -> None
    | (key,value) :: alist_tail -> 
      if desired_key?(key) then Some value else lookup(desired_key?, alist_tail)

 % This implementation of substitution 
 % completely ignores free variables in sorts.
 %
 % This is legal if indeed sorts do not have free variables,
 % which is a reasonable assumption given how Specware sorts
 % are handled.

 def substituteType(srt,S) = 
   let freeNames = List.foldr (fn ((v,trm),vs) -> 
			       StringSet.union (StringSet.fromList
						(List.map (fn (n,_) -> n)
						          (freeVars trm)),
						vs))
                              StringSet.empty S
   in 
   substituteType2(srt,S,freeNames) 

 def substituteType2(srt,S,freeNames) = 
   let def subst(s:Sort):Sort = 
	   case s
	     of Base(id,srts,a) -> 
	        Base(id,
		     List.map subst srts,
		     a)
	      | Arrow(d,r,a) -> 
		Arrow(subst d,
		      subst r,
		      a)
	      | Product(fields,a) -> 
		Product(List.map (fn (l,s) -> (l,subst s)) fields,
			a)
	      | CoProduct(fields,a) -> 
		CoProduct(List.map (fn (l,s) -> (l,mapOption subst s)) fields,
			  a)
	      | Subsort(s,p,a) -> 
		Subsort(subst s,
			substitute2(p,S,freeNames),
			a)
	      | Quotient(s,p,a) -> 
		Quotient(subst s,
			 substitute2(p,S,freeNames),
			 a)
	      | TyVar(v,a) -> 
		TyVar(v,a)
   in
   subst(srt) 

 def substitute(M,sub) = 
   if null sub then M else 
   let freeNames = List.foldr (fn ((v,trm),vs) -> 
			       StringSet.union (StringSet.fromList
						(List.map (fn (n,_) -> n)
						          (freeVars trm)),
					       vs)) 
                              StringSet.empty sub
   in 
   substitute2(M,sub,freeNames)
 
 def substitute2(M,sub,freeNames) = 
   % let _ = String.writeLine "Map is " in
   % let _ = List.app (fn ((v,_),tm) -> 
   %		       String.writeLine (v^" |-> "^MetaSlangPrint.printTerm tm)) sub in	
   let
       def subst(M:Term):Term = 
         case M
	   of Var ((s,_),_) -> 
	      (%String.writeLine ("Looking up "^s);
	       case lookup(fn (s2,_) -> s = s2,sub) 
		 of None   -> (%String.writeLine "not found"; 
			       M) 
		  | Some N -> (%String.writeLine "found "; 
			       N))
	    | Apply(M1,M2,a)  -> 
	      Apply(subst M1,subst M2,
		    a) 
	    | Record(fields,a) -> 
	      Record(List.map (fn(f,M)-> (f,subst M)) fields,
		     a)
	    | Fun _         -> M 
	    | Lambda(rules,a)  -> 
	      Lambda(List.map substRule rules,
		     a)
	    | Let(decls,M,a)  -> 
	      let decls = List.map (fn(p,M)-> (p,subst M)) decls in
	      let (decls,freeNames,sub) = List.foldr substLet ([],freeNames,sub) decls
	      in
	      Let(decls,
		  substitute2(M,sub,freeNames),
		  a)
	    | LetRec(decls,M,a) -> 
	      let (vars,sub,freeNames) = substBoundVars(List.map (fn(v,_) -> v) decls,sub,freeNames) 
	      in
	      let terms = List.map (fn (_,trm) -> substitute2(trm,sub,freeNames)) decls in
	      let decls = ListPair.zip (vars,terms) in
	      LetRec(decls,
		     substitute2(M,sub,freeNames),
		     a)
	    | Bind(b,vars,M,a)  -> 
	      let (vars,sub,freeNames) = substBoundVars(vars,sub,freeNames) in
	      Bind(b,
		   vars,
		   substitute2(M,sub,freeNames),
		   a)
	    | IfThenElse(t1,t2,t3,a) -> 
	      IfThenElse(subst(t1),
			 subst(t2),
			 subst(t3),
			 a)
	    | Seq(terms,a) -> 
	      Seq(List.map subst terms,
		  a)

	def substRule (pat,cond,term) = 
	  let (pat,sub,freeNames) = substPattern(pat,sub,freeNames) in
	  if null sub then
	    (pat, cond, term) 
	  else
	    (pat,
	     substitute2(cond,sub,freeNames),
	     substitute2(term,sub,freeNames)) 

	def substLet ((pat,trm),(decls,freeNames,sub)) = 
	  let (pat,sub,freeNames) = substPattern(pat,sub,freeNames) in
	  (cons((pat,trm),decls),
	   freeNames,
	   sub)
   in
   let M1 = subst(M) in
   (%String.writeLine ("Returning "^MetaSlangPrint.printTerm M1);
    M1)

 def substBoundVars(vars,sub,freeNames) = 
   List.foldr (fn(v,(vars,sub,freeNames)) -> 
	       let (v,sub,freeNames) = substBoundVar(v,sub,freeNames) in
	       (cons(v,vars),sub,freeNames))
              ([],sub,freeNames) vars
	
 def substBoundVar((id,s),sub,freeNames) = 
   if StringSet.member(freeNames,id) then
     let id2 = StringUtilities.freshName(id,freeNames) in
     let sub2 = cons(((id,s),mkVar(id2,s)),sub) in
     ((id2,s),sub2,freeNames)
   else
     ((id,s),deleteVar((id,s),sub,[]),freeNames)

 def deleteVar(v,sub,sub2) = 
   case sub
     of []         -> sub2
      | (w,M)::sub -> if v = w 
		      then sub ++ sub2
		      else deleteVar(v,sub,cons((w,M),sub2))

 def substPattern(pat,sub,freeNames) = 
   case pat:Pattern
     of VarPat(v,a) ->
        let (v,sub,freeNames) = substBoundVar(v,sub,freeNames) in
	(VarPat(v,a),sub,freeNames) 
      | RecordPat(fields,a) -> 
	let (fields,sub,freeNames) = 
	    List.foldr 
              (fn ((id,p),(fields,sub,freeNames)) -> 
	       let (p,sub,freeNames) = substPattern(p,sub,freeNames) in
	       (cons((id,p),fields),sub,freeNames))
	      ([],sub,freeNames) fields
	in
	(RecordPat(fields,a),sub,freeNames)
      | EmbedPat(oper,Some pat,srt,a) -> 
	let (pat,sub,freeNames) = substPattern(pat,sub,freeNames) in
	(EmbedPat(oper,Some pat,srt,a),sub,freeNames)
      | EmbedPat(oper,None,srt,_) -> 
	(pat,sub,freeNames)
      | AliasPat(p1,p2,a) ->
	let (p1,sub,freeNames) = substPattern(p1,sub,freeNames) in
	let (p2,sub,freeNames) = substPattern(p2,sub,freeNames) in
	(AliasPat(p1,p2,a),sub,freeNames)
      | QuotientPat(pat,trm,a) -> 
	let (pat,sub,freeNames) = substPattern(pat,sub,freeNames) in
	(QuotientPat(pat,trm,a),sub,freeNames)
      | RelaxPat(pat,trm,a) -> 	
	let (pat,sub,freeNames) = substPattern(pat,sub,freeNames) in
	(RelaxPat(pat,trm,a),sub,freeNames)
      | _ -> 
	(pat,sub,freeNames)

 def extractAssignment (variables, arguments) = 
   case (variables,arguments) 
     of ((Var(v,a)),(Var(w,_))) -> 
	if v = w then
	  []
	else 
	  [(VarPat(v,a),arguments)]
      | (Var v,_) -> 
  	  [(VarPat v,arguments)]
      | (Record(fields,_),Record(fields2,_)) -> 
	  ListPair.foldr 
	    (fn((_,(Var(v,_)):Term),(_,arg:Term),assignments)->
	     (case arg
		of (Var(w,_)) -> if v = w 
                                 then assignments else
                		 cons((mkVarPat v,arg),assignments)
		 | _ -> cons((mkVarPat v,arg),assignments)))
	    [] (fields,fields2) 

 %- --------------------------------------------------------------------------

 def report_unimplemented_for_cgen = false
 def externalopshfile(specname:String) = specname^"_extops.h"
 def cgeninfohead = ";;;CGEN-INFO "

 % ----------------------------------------------------------------------


  %% Spec equality

 def specEqual? (s1, s2) =
   (s1.imports                = s2.imports)                &
   % (s1.importedSpec           = s2.importedSpec)           & % ??
   (s1.properties             = s2.properties)             &
   (StringMap.toList s1.sorts = StringMap.toList s2.sorts) &
   (StringMap.toList s1.ops   = StringMap.toList s2.ops)

 def subspec? (s1, s2) =
   ListUtilities.subset? (s1.imports,    s2.imports)    &
   ListUtilities.subset? (s1.properties, s2.properties) &
   StringMap.subset?     (s1.sorts,      s2.sorts)      &
   StringMap.subset?     (s1.ops,        s2.ops)


 %% Remove op definitions, axioms, and theorems from a spec.

 def removeDefinitions spc =
   {imports          = spc.imports,
    importedSpec     = spc.importedSpec,
    ops              = StringMap.map (fn m -> StringMap.map (fn (op_names, fixity, srt, optTerm) -> 
							        (op_names, fixity, srt, None : Option Term))
				                            m)
                                     spc.ops,
    sorts            = spc.sorts,
    properties       = emptyProperties}



 op disableProperties: IntegerSet.Set * Spec -> Spec
 def disableProperties(indices,spc:Spec) = 
   if IntegerSet.isEmpty indices then
     spc
   else
     let idx = Ref 0 in
     let revised_ops =
         StringMap.map
	   (fn m -> StringMap.map
	              (fn(op_names,fixity,srt,defn) ->
		       (idx := !idx - 1;
		        if IntegerSet.member(indices,!idx)
			 then (op_names,fixity,srt,None)
			 else (op_names,fixity,srt,defn)))
		      m)
	   spc.ops
     % let (_,ops) =
     %     (fn (m,StringMap.foldri 
     %             (fn (nm,(fxty,srt,defn),(idx,ops)) -> 
     %		    if IntegerSet.member(indices,idx)
     %			  then (idx - 1,StringMap.insert(ops,nm,(fxty,srt,None):OpInfo))
     %		    else (idx - 1,StringMap.insert(ops,nm,(fxty,srt,defn)))) 
     %	           (Integer.~ 1,StringMap.empty) spc.ops)) 
     in
     {imports          = spc.imports,
      importedSpec     = spc.importedSpec,
      sorts            = spc.sorts,
      ops              = revised_ops,
      properties       = filterWithIndex (fn (i,n) -> ~(IntegerSet.member(indices,i))) 
                                         spc.properties
     } 

 op filterWithIndex : (Integer * Property -> Boolean) -> Properties -> Properties
 def filterWithIndex p l = 
   let def fRec(n,l) = 
         case l 
	   of []    -> [] 
            | x::xs -> if p(n,x) 
	               then cons(x,fRec(n + 1,xs))
		       else fRec(n + 1,xs)
   in
     fRec(0,l)

 op convertConjecturesToAxioms : Spec -> Spec
 def convertConjecturesToAxioms (spc : Spec) =
   setProperties (spc, 
		  List.map (fn (ty,n,t,f) ->
				 (case ty of
				   | Conjecture:PropertyType -> Axiom:PropertyType
				   | _ -> ty,
				 n,t,f))
                                spc.properties)


 %- --------------------------------------------------------------------------------
 %- modify op and sort names in a spec, term, sort, etc.
 %- - mSrt is a function for modifying sort QualifiedId's
 %- - mOp is a function for modifying op QualifiedId's
 %- --------------------------------------------------------------------------------
 
 op modifyNamesSort: (QualifiedId -> QualifiedId) * (QualifiedId -> QualifiedId) * Sort -> Sort
 def modifyNamesSort(mSrt,mOp,srt) =
  case srt of
   | Arrow(s1,s2,a) ->
     Arrow(modifyNamesSort(mSrt,mOp,s1),
	   modifyNamesSort(mSrt,mOp,s2),
	   a)
   | Product(fields,a) ->
     Product(List.map (fn(id,s) -> (id,modifyNamesSort(mSrt,mOp,s))) fields,
	     a)
   | CoProduct(fields,a) ->
     CoProduct(List.map (fn(id,optsrt) ->
			 (id, case optsrt of
			       | Some s -> Some(modifyNamesSort(mSrt,mOp,s))
			       | None  -> None)) 
	                fields,
			a)
   | Quotient(srt,term,a) ->
     Quotient(modifyNamesSort(mSrt,mOp,srt),
	      modifyNamesTerm(mSrt,mOp,term),
	      a)
   | Subsort(srt,term,a) ->
     Subsort(modifyNamesSort(mSrt,mOp,srt),
	     modifyNamesTerm(mSrt,mOp,term),
	     a)
   | Base(qid,srts,a) ->
     Base(mSrt qid,
	  List.map (fn(s) -> modifyNamesSort(mSrt,mOp,s)) srts,
	  a)
   | _ -> srt

 op modifyNamesTerm: (QualifiedId -> QualifiedId) * (QualifiedId -> QualifiedId) * Term -> Term
 def modifyNamesTerm(mSrt,mOp,term) =
   case term
     of Apply(t1,t2,a) ->
        Apply(modifyNamesTerm(mSrt,mOp,t1),
	      modifyNamesTerm(mSrt,mOp,t2),
	      a)
      | Record(fields,a) ->
	Record(List.map (fn(id,t) -> (id,modifyNamesTerm(mSrt,mOp,t))) fields,
	       a)
      | Bind(bnd,vars,t,a) -> 
	Bind(bnd,
	     List.map(fn(v) -> modifyNamesVar(mSrt,mOp,v)) vars,
	     modifyNamesTerm(mSrt,mOp,t),
	     a)
      | Let(pts,t,a) -> 
	Let(List.map (fn(pat,t) -> (modifyNamesPattern(mSrt,mOp,pat),modifyNamesTerm(mSrt,mOp,t))) pts,
	    modifyNamesTerm(mSrt,mOp,t),
	    a)
      | LetRec(vts,t,a) -> 
	LetRec(List.map (fn(v,t) -> (modifyNamesVar (mSrt,mOp,v),
				     modifyNamesTerm(mSrt,mOp,t))) 
	                vts,
	       modifyNamesTerm(mSrt,mOp,t),
	       a)
      | Var(v,a) -> 
	Var(modifyNamesVar(mSrt,mOp,v),
	    a)
      | Fun(f,s,a) -> 
	Fun(modifyNamesFun(mSrt,mOp,f),
	    modifyNamesSort(mSrt,mOp,s),
	    a)
      | Lambda(match,a)        -> 
	Lambda(List.map (fn(pat,t1,t2) -> (modifyNamesPattern(mSrt,mOp,pat),
					   modifyNamesTerm(mSrt,mOp,t1),
					   modifyNamesTerm(mSrt,mOp,t2))) 
                        match,
               a)
      | IfThenElse(t1,t2,t3,a) -> 
	IfThenElse(modifyNamesTerm(mSrt,mOp,t1),
		   modifyNamesTerm(mSrt,mOp,t2),
		   modifyNamesTerm(mSrt,mOp,t3),
		   a)
      | Seq(tl,a) -> 
	Seq(List.map (fn(t) -> modifyNamesTerm(mSrt,mOp,t)) tl,
	    a)
      | _ -> term

 op modifyNamesVar: (QualifiedId -> QualifiedId) * (QualifiedId -> QualifiedId) * Var -> Var
 def modifyNamesVar(mSrt,mOp,(id,srt)) = (id,modifyNamesSort(mSrt,mOp,srt))

 op modifyNamesPattern: (QualifiedId -> QualifiedId) * (QualifiedId -> QualifiedId) * Pattern -> Pattern
 def modifyNamesPattern(mSrt,mOp,pat) = 
   case pat
     of AliasPat(p1,p2,a) -> 
        AliasPat(modifyNamesPattern(mSrt,mOp,p1),
		 modifyNamesPattern(mSrt,mOp,p2),
		 a)
      | VarPat(v,a) -> 
	VarPat(modifyNamesVar(mSrt,mOp,v),
	       a)
      | EmbedPat(id,optpat,srt,a) -> 
	EmbedPat(id,
		 case optpat
		   of None   -> None
		    | Some p -> Some(modifyNamesPattern(mSrt,mOp,p)),
		 modifyNamesSort(mSrt,mOp,srt),
		 a)
      | RecordPat(fields,a) ->
	RecordPat(List.map (fn(id,p) -> (id,modifyNamesPattern(mSrt,mOp,p))) fields,
		  a)
      | WildPat(srt,a) -> 
	WildPat(modifyNamesSort(mSrt,mOp,srt),
		a)
      | RelaxPat(p,t,a) -> 
	RelaxPat(modifyNamesPattern(mSrt,mOp,p),
		 modifyNamesTerm(mSrt,mOp,t),
		 a)
      | QuotientPat(p,t,a) -> 
	QuotientPat(modifyNamesPattern(mSrt,mOp,p),
		    modifyNamesTerm(mSrt,mOp,t),
		    a)
      | _ -> pat

 op modifyNamesFun: (QualifiedId -> QualifiedId) * (QualifiedId -> QualifiedId) * Fun -> Fun
 def modifyNamesFun(_(* mSrt *),mOp,fun) =
   case fun
     of Op(qid,fxty) -> Op(mOp qid,fxty)
      | _            -> fun

 op modifyNamesSortInfo: (QualifiedId -> QualifiedId) * (QualifiedId -> QualifiedId) * SortInfo -> SortInfo
 def modifyNamesSortInfo(mSrt,mOp,(sort_names, tyvars, opt_def)) =
   (rev (foldl (fn (sort_name, new_names) -> cons(mSrt sort_name, new_names)) nil sort_names),
    tyvars,
    case opt_def
      of Some(s) -> Some(modifyNamesSort(mSrt, mOp, s))
       | None    -> None
  )

 op modifyNamesOpInfo: (QualifiedId -> QualifiedId) * (QualifiedId -> QualifiedId) * OpInfo -> OpInfo
 def modifyNamesOpInfo(mSrt, mOp, (op_names, fixity, (tyvars, srt), opt_def)) =
   (rev (foldl (fn (op_name, new_names) -> cons(mOp op_name, new_names)) nil op_names),
    fixity,
    (tyvars, modifyNamesSort(mSrt,mOp,srt)),
    case opt_def
      of Some term -> Some(modifyNamesTerm(mSrt,mOp,term))
       | None      -> None)

(*
 %% TODO: ??? FIX THIS
 op modifyNamesSpec: (QualifiedId -> QualifiedId) * (QualifiedId -> QualifiedId) * Spec -> Spec
 def modifyNamesSpec (mSrt, mOp, spc) =
   {imports      = spc.imports,
    importedSpec = spc.ImportedSpec,
    sorts        = StringMap.map (fn qmap -> StringMap.foldri (fn (id, si, res) -> 
								   let UnQualified newsrt = mSrt(UnQualified id) in
								   StringMap.insert (res,
										     newsrt,
										     modifyNamesSortInfo(mSrt,mOp,si)))
				                                  StringMap.empty 
								  qmap)
                                     spc.sorts,
    ops          = StringMap.map (fn qmap -> StringMap.foldri (fn (id, oi, res) -> 
								   let UnQualified newop = mOp(UnQualified id) in
								   StringMap.insert (res,
										     newop,
										     modifyNamesOpInfo (mSrt, mOp, oi)))
				                                  StringMap.empty
								  qmap)
                                     spc.ops,
    properties   = spc.properties
   }
*)

 %- ----------------------------------------------------------------

 op letRecToLetTermSort: Sort -> Sort
 def letRecToLetTermSort srt =
   case srt
     of Arrow(s1,s2,a)  -> 
        Arrow(letRecToLetTermSort(s1),
	      letRecToLetTermSort(s2),
	      a)
      | Product(fields,a) -> 
	Product(List.map (fn(id,s) -> (id, letRecToLetTermSort(s))) fields,
		a)
      | CoProduct(fields,a) -> 
	CoProduct(List.map (fn (id,optsrt) ->
			    (id, case optsrt
				   of Some s -> Some(letRecToLetTermSort(s))
				    | None  -> None)) 
		           fields,
		  a)
      | Quotient(srt,term,a) ->
	Quotient(letRecToLetTermSort(srt),
		 letRecToLetTermTerm(term),
		 a)
      | Subsort(srt,term,a) ->
	Subsort(letRecToLetTermSort(srt),
		letRecToLetTermTerm(term),
		a)
      | Base(qid,srts,a) -> 
	Base(qid,
	     List.map (fn(s) -> letRecToLetTermSort(s)) srts,
	     a)
      | _ -> srt

 op letRecToLetTermTerm: Term -> Term
 def letRecToLetTermTerm term =
   case term
     of Apply(t1,t2,a) -> 
       Apply(letRecToLetTermTerm(t1),
	     letRecToLetTermTerm(t2),
	     a)
      | Record(fields,a) -> 
        Record(List.map (fn(id,t) -> (id,letRecToLetTermTerm(t))) fields,
	       a)
      | Bind(bnd,vars,trm,a) -> 
	Bind(bnd,
	     List.map(fn(v) -> letRecToLetTermVar(v)) vars,
	     letRecToLetTermTerm trm,
	     a)
      | Let(pts,trm,a) -> 
	Let(List.map (fn(pat,t) -> (letRecToLetTermPattern(pat),letRecToLetTermTerm(t))) pts,
	    letRecToLetTermTerm trm,
	    a)
      | LetRec(vts,t,a) -> 
	let vts = List.map (fn(v,t) -> (letRecToLetTermVar(v),letRecToLetTermTerm(t))) vts in
	let t = letRecToLetTermTerm(t) in
	let pts = List.map (fn(v,t) -> (VarPat(v,()),t)) vts in
	let dummyterm = mkTrue() in
	let dummypts = List.map (fn(pat,t) -> 
				 case t
				   of Lambda(match,a) ->
				      let newmatch = List.map (fn (pat,term,_) -> 
							       %-let dummyterm = 
							       %-     getdummytermwithunboundvars(pat,term) in
							       (pat,term,dummyterm))
				                              match
	                              in
					(pat,Lambda(newmatch,a))
				    | _ ->
					(pat,dummyterm))
	                        pts 
        in
	%Let(dummypts,Let(pts,t))
        Let(dummypts,
	    Let(pts, 
		Let(pts,t,a),
		a),
	    a)
      | Var(v,a) -> 
	Var(letRecToLetTermVar(v),
	    a)
      | Fun(f,s,a) -> 
	Fun(letRecToLetTermFun(f),
	    letRecToLetTermSort(s),
	    a)
      | Lambda(match,a) -> 
	Lambda(List.map (fn(pat,t1,t2) -> 
			 (letRecToLetTermPattern(pat),
			  letRecToLetTermTerm(t1),
			  letRecToLetTermTerm(t2))) 
	                match,
	       a)
      | IfThenElse(t1,t2,t3,a) -> 
	IfThenElse(letRecToLetTermTerm(t1),
		   letRecToLetTermTerm(t2),
		   letRecToLetTermTerm(t3),
		   a)
      | Seq(tl,a) -> 
	Seq(List.map (fn(t) -> letRecToLetTermTerm(t)) tl,
	    a)
      | _  -> term

 op letRecToLetTermVar: Var -> Var
 def letRecToLetTermVar ((id, srt)) = (id, letRecToLetTermSort srt)

 op letRecToLetTermPattern: Pattern -> Pattern
 def letRecToLetTermPattern pat = 
   case pat
     of AliasPat(p1,p2,a) -> 
        AliasPat(letRecToLetTermPattern(p1),
		 letRecToLetTermPattern(p2),
		 a)
      | VarPat(v,a) -> 
	VarPat(letRecToLetTermVar(v),
	       a)
      | EmbedPat(id,optpat,srt,a) -> 
	EmbedPat(id,
		 case optpat
		   of  None   -> None
		    | Some p -> Some(letRecToLetTermPattern(p)),
		 letRecToLetTermSort(srt),
		 a)
      | RecordPat(fields,a) -> 
	RecordPat(List.map (fn(id,p) -> (id,letRecToLetTermPattern(p))) fields,
		  a)
      | WildPat(srt,a) -> 
	WildPat(letRecToLetTermSort(srt),
		a)
      | RelaxPat(p,t,a) -> 
	RelaxPat(letRecToLetTermPattern(p),
		 letRecToLetTermTerm(t),
		 a)
      | QuotientPat(p,t,a) -> 
	QuotientPat(letRecToLetTermPattern(p),
		    letRecToLetTermTerm(t),
		    a)
      | _ -> pat

 op letRecToLetTermFun: Fun -> Fun
 def letRecToLetTermFun fun = fun

 op letRecToLetTermSortInfo: SortInfo -> SortInfo
 def letRecToLetTermSortInfo ((sort_names, tyvars, opt_def)) =
   (sort_names,
    tyvars,
    case opt_def
      of Some srt -> Some(letRecToLetTermSort srt)
       | None     -> None)

 op letRecToLetTermOpInfo: OpInfo -> OpInfo
 def letRecToLetTermOpInfo((op_names, fixity, (tyvars, srt), opt_def)) =
   (op_names, 
    fixity, 
    (tyvars, letRecToLetTermSort srt),
    case opt_def
      of Some term -> Some(letRecToLetTermTerm term)
       | None      -> None)

 op letRecToLetTermSpec: Spec -> Spec
 def letRecToLetTermSpec(spc) =
   {imports          = spc.imports,
    importedSpec     = spc.importedSpec,
    sorts            = StringMap.mapDouble letRecToLetTermSortInfo spc.sorts,
    ops              = StringMap.mapDouble letRecToLetTermOpInfo   spc.ops,
    properties       = spc.properties}

 %- --------------------------------------------------------------------------------

 def cString (id : String) : String = 
   let id = String.map cChar id in
   if isCKeyword id then
     cString("slang_" ^ id)
   else 
     substGlyphInIdent(id)

 %-% TODO: transform glyph identifier, e.g. "+++", "%^&*" to C idents

 %[MA
 def substGlyphInIdent(id:String) : String =
   let def substGlyphChar(c:Char) : List Char =
        let ord = Char.ord(c) in
	if ord < 32 
	  then [#_]
	else if ord > 126 
	  then [#_]
        else if ((ord >= 48) & (ord <=  57)) 
	     or ((ord >= 65) & (ord <=  90))
	     or ((ord >= 97) & (ord <= 122))
	     or (ord = 95) 
	 then [c]
        else
	 case ord
	   of  32 -> String.explode("Space")
	    |  33 -> String.explode("Exclam")
	    |  34 -> String.explode("Quotedbl")
	    |  35 -> String.explode("Numbersign")
	    |  36 -> String.explode("Dollar")
	    |  37 -> String.explode("Percent")
	    |  38 -> String.explode("Ampersand")
	    |  39 -> String.explode("Quotesingle")
	    |  40 -> String.explode("Parenleft")
	    |  41 -> String.explode("Parenright")
	    |  42 -> String.explode("Asterisk")
	    |  43 -> String.explode("Plus")
	    |  44 -> String.explode("Comma")
	    |  45 -> String.explode("Hyphen")
	    |  46 -> String.explode("Period")
	    |  47 -> String.explode("Slash")
	    |  58 -> String.explode("Colon")
	    |  59 -> String.explode("Semicolon")
	    |  60 -> String.explode("Less")
	    |  61 -> String.explode("Equal")
	    |  62 -> String.explode("Greater")
	    |  63 -> String.explode("Q")
	    |  64 -> String.explode("At")
	    |  91 -> String.explode("Bracketleft")
	    |  92 -> String.explode("Backslash")
	    |  93 -> String.explode("Bracketright")
	    |  94 -> String.explode("Caret")
	    |  96 -> String.explode("Grave")
	    | 123 -> String.explode("Braceleft")
	    | 124 -> String.explode("Bar")
	    | 125 -> String.explode("Braceright")
	    | 126 -> String.explode("Tilde")
	    | _ -> [#_]
    in
    let def substGlyph(carray) =
       case carray
	 of c::carray0  -> concat(substGlyphChar(c),substGlyph(carray0))
	  | []         -> []
    in
      String.implode(substGlyph(String.explode(id)))
 % MA]

 def cChar (c : Char) : Char =
   case c
     %-      of #- -> #_
     of #? -> #Q
      | _  -> c

 def isCKeyword s =
   member (s, cKeywords)

 def cKeywords =
   ["auto",     "break",  "case",     "char",    "const",    "continue",
    "default",  "do",     "double",   "else",    "enum",     "extern",
    "float",    "for",    "goto",     "if",      "int",      "long",
    "register", "return", "short",    "signed",  "sizeof",   "static",
    "struct",   "switch", "typedef",  "union",   "unsigned", "void",
    "volatile", "while"]
}
