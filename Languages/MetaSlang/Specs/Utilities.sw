Utilities qualifying spec  
 import StandardSpec    % defines sorts Spec, Term, etc.
 import /Library/Legacy/DataStructures/IntSetSplay
 import /Library/Legacy/DataStructures/ListPair 
 import /Library/Legacy/DataStructures/ListUtilities
 import /Library/Legacy/DataStructures/StringUtilities 
 import Elaborate/Utilities

 sort Vars = List Var

(* ### unused ?
 op specEqual? : Spec * Spec -> Boolean
 op subspec?   : Spec * Spec -> Boolean
*)

 op substitute    : MS.Term * List (Var * MS.Term) -> MS.Term
 op freeVars      : MS.Term -> Vars

 %% Translate a term encoding an assignment to a list of pairs.
 %% Redundant assignments of a variable to itself are eliminated.

 op extractAssignment : MS.Term * MS.Term -> List (Pattern * MS.Term)

 op removeDefinitions  : fa(a) ASpec a -> ASpec a
 op removeUndefinedOps : fa(a) ASpec a -> ASpec a

 op patternToTerm : Pattern -> Option MS.Term

 op isFree : Var * MS.Term -> Boolean
 def isFree (v,term) = 
   case term of
     | Var(w,_)               -> v = w
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

 op isPatBound : Var * Pattern -> Boolean
 def isPatBound (v,pat) = 
   case pat of
     | AliasPat(p1,p2,_)      -> isPatBound(v,p1) or isPatBound(v,p2)
     | EmbedPat(_,Some p,_,_) -> isPatBound(v,p)
     | VarPat(w,_)            -> v = w
     | RecordPat(fields,_)    -> exists (fn (_,p) -> isPatBound(v,p)) fields
     | RelaxPat(p,_,_)        -> isPatBound(v,p)
     | QuotientPat(p,_,_)     -> isPatBound(v,p)
     | _ -> false

 op replace : MS.Term * List (MS.Term * MS.Term) -> MS.Term
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
       def rep(M:MS.Term):MS.Term = 
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

 op repPattern : Pattern * List (MS.Term * MS.Term) * StringSet.Set -> Pattern * List (MS.Term * MS.Term) * StringSet.Set
 op repBoundVars: Vars *  List (MS.Term * MS.Term) * StringSet.Set -> Vars *  List (MS.Term * MS.Term) * StringSet.Set


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
 def freeVars (M) = 
   let vars = freeVarsRec(M) in
   ListUtilities.removeDuplicates vars

 def freeVarsRec(M:MS.Term) =   
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
	deleteVars(vars1 ++ vars2,List.map (fn(v,_) -> v) decls)
      | Bind(b,vars,M,_)  -> 
	deleteVars(freeVarsRec(M),vars)
      | IfThenElse(t1,t2,t3,_) -> 
	freeVarsRec(t1) ++ freeVarsRec(t2) ++ freeVarsRec(t3)
      | Seq(tms,_) -> foldr (fn (trm,vs) -> vs ++ freeVarsRec trm) [] tms

 op  freeVarsList : fa(a) List(a * MS.Term) -> Vars
 def freeVarsList list = 
   List.foldr (fn ((_,trm),vs) -> vs ++ freeVarsRec trm) [] list

 def deleteVars(vars1,vars2) = 
   List.foldr ListUtilities.delete vars1 vars2

 def freeVarsMatch (pat,cond,body) = 
   let vars  = patVars pat in
   let vars1 = freeVarsRec cond in
   let vars2 = freeVarsRec body in
   deleteVars(vars1 ++ vars2,vars)

 op  patVars: Pattern -> List Var
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

 op  getParams: Pattern -> List Pattern
 def getParams(pat:Pattern) = 
   case pat
     of VarPat(v,_)-> [pat]
      | RecordPat(fields,_) ->
	if all (fn (_,VarPat _) -> true | (_,RecordPat _) -> true | _ -> false) fields
	  then map (fn (_,vpat) -> vpat) fields
	  else []
      | _ -> []

 op  lookup : fa(a,b) (a  -> Boolean) * List(a * b) -> Option b 
 def lookup (desired_key?, association_list) = 
   case association_list of
    | [] -> None
    | (key,value) :: alist_tail -> 
      if desired_key?(key) then Some value else lookup(desired_key?, alist_tail)



 op  freeTyVars: Sort -> TyVars
 def freeTyVars(srt) = 
   let vars = Ref [] in
   let def vr(srt) = 
         case srt of
	   | TyVar(tv,_) -> (vars := Cons (tv,! vars); ())
	   | MetaTyVar(tv,pos) -> 
	     (case unlinkSort srt of
	       | TyVar(tv,_) -> (vars := Cons (tv,! vars); ())
	       | _ -> ())
	   | _ -> ()
   in
   let _ = appSort(fn _ -> (),vr,fn _ -> ()) srt in
   ! vars

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
       def subst(M:MS.Term):MS.Term = 
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
   let sub = deleteVar((id,s),sub,[]) in
   if StringSet.member(freeNames,id) then
     let id2 = StringUtilities.freshName(id,freeNames) in
     let sub2 = cons(((id,s),mkVar(id2,s)),sub) in
     ((id2,s),sub2,freeNames)
   else
     ((id,s),sub,freeNames)

 def deleteVar(v,sub,sub2) = 
   case sub
     of []         -> sub2
      | (w,M)::sub -> if v.1 = w.1
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
	    (fn((_,(Var(v,_)):MS.Term),(_,arg:MS.Term),assignments)->
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
(* ### unused?
 def specEqual? (s1, s2) =
   %% don't test importInfo as it just gives info about how the spec was constructed
   %(s1.imports                = s2.imports)                &
   % (s1.importedSpec           = s2.importedSpec)           & % ??
   (s1.properties             = s2.properties)             &
   equalAQualifierMap?(s1.sorts, s2.sorts) &
   equalAQualifierMap?(s1.ops, s2.ops)

 def subspec? (s1, s2) =
   %ListUtilities.subset? (s1.imports,    s2.imports)    &
   ListUtilities.subset? (s1.properties, s2.properties) &
   subsetAQualifierMap?  (s1.sorts,      s2.sorts)      &
   subsetAQualifierMap?  (s1.ops,        s2.ops)
*)


 %% Remove op definitions, axioms, and theorems from a spec.

 def removeDefinitions spc =
   {importInfo       = spc.importInfo,
    ops              = mapAQualifierMap (fn (op_names, fixity, srt, _) -> 
					 (op_names, fixity, srt, []))
                         spc.ops,
    sorts            = spc.sorts,
    properties       = emptyAProperties}

 def removeUndefinedOps spc =
   {importInfo       = spc.importInfo,
    ops              = mapiPartialAQualifierMap (fn (_,_,opinfo as (op_names, fixity, srt, defs)) -> 
					         if defs = [] then None else Some opinfo)
                         spc.ops,
    sorts            = spc.sorts,
    properties       = emptyAProperties}

 op disableProperties : IntegerSet.Set * Spec -> Spec
 def disableProperties (indices,spc) = 
   if IntegerSet.isEmpty indices then
     spc
   else
     let idx = Ref 0 in
     let revised_ops =
         mapAQualifierMap
	   (fn(op_names,fixity,srt,defs) ->
		       (idx := !idx - 1;
		        if IntegerSet.member(indices,!idx)
			 then (op_names,fixity,srt,[])
			 else (op_names,fixity,srt,defs)))
	   spc.ops
     % let (_,ops) =
     %     (fn (m,StringMap.foldri 
     %             (fn (nm,(fxty,srt,defn),(idx,ops)) -> 
     %		    if IntegerSet.member(indices,idx)
     %			  then (idx - 1,StringMap.insert(ops,nm,(fxty,srt,None):OpInfo))
     %		    else (idx - 1,StringMap.insert(ops,nm,(fxty,srt,defn)))) 
     %	           (Integer.~ 1,StringMap.empty) spc.ops)) 
     in
     {importInfo       = spc.importInfo,
      sorts            = spc.sorts,
      ops              = revised_ops,
      properties       = filterWithIndex (fn (i,n) -> ~(IntegerSet.member(indices,i))) 
                                         spc.properties
     } 

 op filterWithIndex : (Integer * Property -> Boolean) -> Properties -> Properties
 def filterWithIndex p l = 
   let def fRec(n,l) = 
     case l of
       | []    -> [] 
       | x::xs ->
           if p(n,x) then
             cons(x,fRec(n + 1,xs))
		   else
             fRec(n + 1,xs)
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


(*
 * ### As far as I can tell, the modifyNames family of functions are not used
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

 op modifyNamesTerm: (QualifiedId -> QualifiedId) * (QualifiedId -> QualifiedId) * MS.Term -> MS.Term
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
 def modifyNamesSortInfo(mSrt,mOp,(sort_names, tyvars, defs)) =
   (rev (foldl (fn (sort_name, new_names) -> cons(mSrt sort_name, new_names)) nil sort_names),
    tyvars,
    map (fn (type_vars, srt) -> 
	 (type_vars, modifyNamesSort(mSrt, mOp, srt))) 
        defs)


 op modifyNamesOpInfo: (QualifiedId -> QualifiedId) * (QualifiedId -> QualifiedId) * OpInfo -> OpInfo
 def modifyNamesOpInfo(mSrt, mOp, (op_names, fixity, (tyvars, srt), defs)) =
   (rev (foldl (fn (op_name, new_names) -> cons(mOp op_name, new_names)) nil op_names),
    fixity,
    (tyvars, modifyNamesSort(mSrt,mOp,srt)),
    map (fn (type_vars, term) ->
	 (type_vars, modifyNamesTerm(mSrt,mOp,term)))
        defs)
*)

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

 op letRecToLetTermTerm: MS.Term -> MS.Term
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
	let pts = List.map (fn(v,t) -> (VarPat(v,noPos),t)) vts in
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
 def letRecToLetTermSortInfo ((sort_names, tyvars, defs)) =
   (sort_names,
    tyvars,
    map (fn (type_vars, srt) ->
	 (type_vars, letRecToLetTermSort srt))
        defs)

 op letRecToLetTermOpInfo: OpInfo -> OpInfo
 def letRecToLetTermOpInfo((op_names, fixity, (tyvars, srt), defs)) =
   (op_names, 
    fixity, 
    (tyvars, letRecToLetTermSort srt),
    map (fn (type_vars, term) ->
	 (type_vars, letRecToLetTermTerm term))
        defs)

 op letRecToLetTermSpec: Spec -> Spec
 def letRecToLetTermSpec(spc) =
   {importInfo       = spc.importInfo,
    sorts            = mapAQualifierMap letRecToLetTermSortInfo spc.sorts,
    ops              = mapAQualifierMap letRecToLetTermOpInfo   spc.ops,
    properties       = spc.properties}

 op  patternVars  : Pattern -> List Var
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
	       | AliasPat(p1,p2,_) -> loopP(p1,loopP(p2,vs))
	       | _ -> vs
     in
     loopP(p,[])

 op  mkLetWithSubst: MS.Term * List (Var * MS.Term) -> MS.Term
 def mkLetWithSubst(tm,sb) =
   if sb = [] then tm
     else mkLet(map (fn (v,val) -> (mkVarPat v,val)) sb, tm)

 def mkIfThenElse(t1,t2:MS.Term,t3:MS.Term):MS.Term =
   case t2 of
     | Fun(Bool true,_,_)  -> mkOr(t1,t3)
     | Fun(Bool false,_,_) -> mkAnd(mkNot t1,t3)
     | _ ->
   case t3 of
     | Fun(Bool true,_,_)  -> mkOr(mkNot t1,t2)
     | Fun(Bool false,_,_) -> mkAnd(t1,t2)
     | _ ->
   IfThenElse(t1,t2,t3,noPos)

 %% Utilities.mkOr, etc:

 op  mkOr: MS.Term * MS.Term -> MS.Term 
 def mkOr(t1,t2) = 
     case (t1,t2)
       of (Fun(Bool true,_,_),_) -> t1
	| (Fun(Bool false,_,_),_) -> t2
	| (_,Fun(Bool true,_,_)) -> t2
	| (_,Fun(Bool false,_,_)) -> t1
	| _ -> MS.mkOr(t1,t2)

 op  mkAnd: MS.Term * MS.Term -> MS.Term 
 def mkAnd(t1,t2) = 
     case (t1,t2)
       of (Fun(Bool true,_,_),_) -> t2
	| (Fun(Bool false,_,_),_) -> t1
	| (_,Fun(Bool true,_,_)) -> t1
	| (_,Fun(Bool false,_,_)) -> t2
	| _ -> MS.mkAnd(t1,t2)

 op  mkSimpConj: List MS.Term -> MS.Term
 def mkSimpConj(cjs) =
  case cjs
    of []     -> mkTrue()
     | [x]    -> x
     | x::rcs -> mkAnd (x, mkConj rcs)

 op  mkSimpOrs: List MS.Term -> MS.Term
 def mkSimpOrs(cjs) =
  case cjs
    of []     -> mkTrue()
     | [x]    -> x
     | x::rcs -> mkOr (x, mkOrs rcs)

 op mkSimpBind: Binder * List Var * MS.Term -> MS.Term
 def mkSimpBind(b, vars, term) =
   if vars = [] then term
     else Bind(b,vars,term,noPos)

 op  mkSimpImplies: MS.Term * MS.Term -> MS.Term
 def mkSimpImplies (t1, t2) =
   case t1 of
     | Fun(Bool true,_,_)  -> t2
     | Fun(Bool false,_,_) -> mkFalse()
     | _ -> mkApply (impliesOp, mkTuple [t1,t2])


 op  identityFn?: fa(a) ATerm a -> Boolean
 def identityFn? f =
   case f of
     | Lambda([(VarPat(x,_),_,Var(y,_))],_) -> x = y
     | _ -> false

 
 op  getConjuncts: fa(a) ATerm a -> List (ATerm a)
 def getConjuncts t =
   case t of
     | Apply(Fun(Op(Qualified("Boolean","&"),_),_,_),
	     Record([("1",p),("2",q)],_),_)
       -> getConjuncts p ++ getConjuncts q
     | Apply(Fun(And,_,_), Record([("1",p),("2",q)],_),_)
       -> getConjuncts p ++ getConjuncts q
     | _ -> [t]

  %% Given a universal quantification return list of quantified variables, conditions and rhs
  op  forallComponents: fa(a) ATerm a -> List (AVar a) * List (ATerm a) * ATerm a
  def forallComponents t =
    case t of
      | Bind(Forall,vs,bod,_) ->
	let (rVs,rLhsCjs,rRhs) = forallComponents bod in
	(vs ++ rVs,rLhsCjs,rRhs)
      | Apply(Fun(Op(Qualified("Boolean","=>"),_),_,_),
	     Record([("1",lhs),("2",rhs)],_),_) ->
        let (rVs,rLhsCjs,rRhs) = forallComponents rhs in
	(rVs,getConjuncts lhs ++ rLhsCjs,rRhs)
      | Apply(Fun(Implies, _,_),
	     Record([("1",lhs),("2",rhs)],_),_) ->
        let (rVs,rLhsCjs,rRhs) = forallComponents rhs in
	(rVs,getConjuncts lhs ++ rLhsCjs,rRhs)
      | _ -> ([],[],t)

  %% Given an existential quantification return list of quantified variables and conjuncts
  op  existsComponents: fa(a) ATerm a -> List (AVar a) * List (ATerm a)
  def existsComponents t =
    case t of
      | Bind(Exists,vs,bod,_) ->
	let (rVs,rLhsCjs) = existsComponents bod in
	(vs ++ rVs,rLhsCjs)
      | Apply(Fun(Op(Qualified("Boolean","&"),_),_,_),
	      Record([("1",lhs),("2",rhs)],_),_) ->
        let (lVs,lLhsCjs) = existsComponents lhs in
        let (rVs,rLhsCjs) = existsComponents rhs in
	(lVs ++ rVs,lLhsCjs ++ rLhsCjs)
      | Apply(Fun(And,_,_), Record([("1",lhs),("2",rhs)],_),_) ->
        let (lVs,lLhsCjs) = existsComponents lhs in
        let (rVs,rLhsCjs) = existsComponents rhs in
	(lVs ++ rVs,lLhsCjs ++ rLhsCjs)
      | _ -> ([],[t])

  op  constantTerm?: fa(a) ATerm a -> Boolean
  def constantTerm? t =
    case t of
      | Lambda _ -> true
      | Fun _    -> true
      | Record(fields,_) -> exists (fn (_,stm) -> constantTerm? stm) fields
      | _        -> false

  op  lambda?: fa(a) ATerm a -> Boolean
  def lambda? t =
    case t of
      | Lambda _ -> true
      | _ -> false

 %% Evaluation of constant terms
 def evalSpecNames = ["Nat","Integer","String","Boolean"]
 def evalConstant?(term) =
   case term
     of Fun(f,_,_) ->
        (case f
	   of Nat _ -> true
	    | Char _ -> true
	    | String _ -> true
	    | Bool _ -> true
	    | _ -> false)
      | _ -> false

 op  natVal: MS.Term -> Nat
 def natVal = fn (Fun(Nat i,_,_)) -> i
 op  natVals: List(Id * MS.Term) -> List Nat
 def natVals = map (fn (_,t) -> natVal t)

 op  charVal: MS.Term -> Char
 def charVal = fn (Fun(Char c,_,_)) -> c
 op  charVals: List(Id * MS.Term) -> List Char
 def charVals = map (fn (_,t) -> charVal t)

 op  stringVal: MS.Term -> String
 def stringVal = fn (Fun(String s,_,_)) -> s
 op  stringVals: List(Id * MS.Term) -> List String
 def stringVals = map (fn (_,t) -> stringVal t)

 op  booleanVal: MS.Term -> Boolean
 def booleanVal = fn (Fun(Bool s,_,_)) -> s
 op  booleanVals: List(Id * MS.Term) -> List Boolean
 def booleanVals = map (fn (_,t) -> booleanVal t)


 op  sortFromField: List(Id * MS.Term) * Sort -> Sort
 def sortFromField(fields,defaultS) =
   case fields
     of (_,Fun(_,s,_))::_-> s
      | _ -> defaultS

 def sortFromArg(arg: MS.Term,defaultS:Sort): Sort =
   case arg
     of Fun(_,s,_) -> s
      | _ -> defaultS

 op  evalBinary: fa(a) (a * a -> Fun) * (List(Id * MS.Term) -> List a)
                      * List(Id * MS.Term) * Sort
                     -> Option MS.Term
 def evalBinary(f, fVals, fields, srt) =
   case fVals fields
     of [i,j] -> Some(Fun(f(i,j),srt,noPos))
      | _ -> None

 op nat: fa(a) (a -> Nat) -> a -> Fun
 op char: fa(a) (a -> Char) -> a -> Fun
 op str: fa(a) (a -> String) -> a -> Fun
 op bool: fa(a) (a -> Boolean) -> a -> Fun
 def nat f x  = Nat(f x)
 def char f x = Char(f x)
 def str f x = String(f x)
 def bool f x = Bool(f x)

 op  attemptEval1: String * MS.Term -> Option MS.Term
 def attemptEval1(opName,arg) =
   case (opName,arg) of
      | ("~", Fun (Nat i,_,aa)) -> Some(Fun (Nat (~i), natSort,aa))
      | ("~", Fun (Bool b,_,aa)) -> Some(Fun (Bool (~b), boolSort,aa))
      | ("pred", Fun (Nat i,_,aa)) -> Some(Fun (Nat (pred i), natSort,aa))
      | ("toString", Fun (Nat i,_,aa)) -> Some (Fun (String (toString i), stringSort,aa))
      | ("succ",Fun (Nat i,_,aa)) -> Some(Fun (Nat (succ i), natSort,aa))

      | ("length",Fun (String s,_,aa)) -> Some(Fun (Nat(length s),natSort,aa))
      | ("stringToInt",Fun (String s,_,aa)) -> Some(Fun (Nat (stringToInt s),natSort,aa))

      | ("isUpperCase",Fun (Char c,_,aa)) ->
          Some(Fun (Bool(isUpperCase c),boolSort,aa))
      | ("isLowerCase",Fun (Char c,_,aa)) ->
          Some(Fun (Bool(isLowerCase c),boolSort,aa))
      | ("isAlphaNum",Fun (Char c,_,aa)) ->
          Some(Fun(Bool(isAlphaNum c),boolSort,aa))
      | ("isAlpha",Fun (Char c,_,aa)) -> Some(Fun (Bool(isAlpha c),boolSort,aa))
      | ("isNum",Fun (Char c,_,aa)) -> Some(Fun (Bool(isNum c),boolSort,aa))
      | ("isAscii",Fun (Char c,_,aa)) -> Some(Fun (Bool(isAscii c),boolSort,aa))
      | ("toUpperCase",Fun (Char c,_,aa)) ->
          Some(Fun (Char(toUpperCase c),charSort,aa))
      | ("toLowerCase",Fun (Char c,_,aa)) ->
          Some(Fun (Char(toLowerCase c),charSort,aa))
      | ("ord",Fun (Char c,_,aa)) -> Some(Fun (Nat(ord c),natSort,aa))
      | ("chr",Fun (Nat i,_,aa)) -> Some(Fun (Char(chr i),charSort,aa))
      | _ -> None

 op  attemptEvaln: String * List(Id * MS.Term) ->  Option MS.Term
 def attemptEvaln(opName,fields) =
   case opName of
      %% Nat operations
      | "+" ->
        Some(Fun(Nat((foldl +) 0 (natVals fields)),
		 sortFromField(fields,natSort),noPos))
      | "*" ->
        Some(Fun(Nat((foldl *) 1 (natVals fields)),
		 sortFromField(fields,natSort),noPos))
      | "-"   -> evalBinary(nat -,natVals,fields,
			  sortFromField(fields,natSort))
      | "<"   -> evalBinary(bool <,natVals,fields,boolSort)
      | "<="  -> evalBinary(bool <=,natVals,fields,boolSort)
      | ">"   -> evalBinary(bool >,natVals,fields,boolSort)
      | ">="  -> evalBinary(bool >=,natVals,fields,boolSort)
      | "min" -> evalBinary(nat min,natVals,fields,
			    sortFromField(fields,natSort))
      | "max" -> evalBinary(nat max,natVals,fields,
			    sortFromField(fields,natSort))
      | "rem" -> evalBinary(nat rem,natVals,fields,natSort)
      | "div" -> evalBinary(nat div,natVals,fields,natSort)

      %% string operations
      | "concat" -> evalBinary(str concat,stringVals,fields,stringSort)
      | "++"  -> evalBinary(str ++,stringVals,fields,stringSort)
      | "^"   -> evalBinary(str ^,stringVals,fields,stringSort)
      | "substring" ->
	(case fields
	   of [(_,s),(_,i),(_,j)] ->
	      Some(Fun(String(substring(stringVal s,natVal i,natVal j)),
		       stringSort,noPos))
	    | _ -> None)
      | "leq" -> evalBinary(bool leq,stringVals,fields,boolSort)
      | "lt"  -> evalBinary(bool lt,stringVals,fields,boolSort)

      %% Boolean operations
      | "&"   -> evalBinary(bool  &,booleanVals,fields,boolSort)
      | "or"  -> evalBinary(bool or,booleanVals,fields,boolSort)
      | "=>"  -> evalBinary(bool =>,booleanVals,fields,boolSort)

      | _ -> None

 op  attemptEval: MS.Term -> MS.Term
 def attemptEval t = mapSubTerms attemptEvalOne t

 op  attemptEvalOne: MS.Term -> MS.Term
 def attemptEvalOne t =
   case tryEvalOne t of
     | Some t1 -> t1
     | None    -> t

 op  tryEvalOne: MS.Term -> Option MS.Term
 def tryEvalOne term =
   case term
     of Apply(Fun(Op(Qualified(spName,opName),_),s,_),arg,_) ->
        (if member(spName,evalSpecNames)
	 then (case arg
		 of Record(fields, _) ->
		    (if all (fn (_,tm) -> evalConstant?(tm)) fields
		      then attemptEvaln(opName,fields)
		      else None)
		   | _ -> (if evalConstant?(arg)
			    then attemptEval1(opName,arg)
			    else None))
	  else None)
      | Apply(Fun(Equals,_,_),Record([(_,N1),(_,N2)], _),_) ->
	if evalConstant?(N1) & evalConstant?(N2)
	  then Some(mkBool(equalTerm?(N1,N2)))
	  else None
      | Apply(Fun(NotEquals,_,_),Record([(_,N1),(_,N2)], _),_) ->
	if evalConstant?(N1) & evalConstant?(N2)
	  then Some(mkBool(~ (equalTerm?(N1,N2))))
	  else None
      | Apply(Fun(Not,  _,_),arg,                       _) -> 
	  (case arg of
	     | Fun (Bool b,_,aa) -> Some(Fun (Bool (~ b), boolSort,noPos))
	     | _ -> None)
      | Apply(Fun(And,  _,_),Record(fields as [(_,N1),(_,N2)], _),_) -> 
	  (case (N1, N2) of
	     | (Fun(Bool b1,_,_), Fun(Bool b2,_,_)) -> Some (Fun (Bool (b1 & b2), boolSort, noPos))
	     | _ -> None)
      | Apply(Fun(Or,   _,_),Record(fields as [(_,N1),(_,N2)], _),_) -> 
	  (case (N1, N2) of
	     | (Fun(Bool b1,_,_), Fun(Bool b2,_,_)) -> Some (Fun (Bool (b1 or b2), boolSort, noPos))
	     | _ -> None)
      | Apply(Fun(Implies, _,_),Record(fields as [(_,N1),(_,N2)], _),_) -> 
	  (case (N1, N2) of
	     | (Fun(Bool b1,_,_), Fun(Bool b2,_,_)) -> Some (Fun (Bool (b1 => b2), boolSort, noPos))
	     | _ -> None)
      | Apply(Fun(Iff, _,_),Record(fields as [(_,N1),(_,N2)], _),_) -> 
	  (case (N1, N2) of
	     | (Fun(Bool b1,_,_), Fun(Bool b2,_,_)) -> Some (Fun (Bool (b1 <=> b2), boolSort, noPos))
	     | _ -> None)
      | _ -> None

  op  printDefinedOps: fa(a) ASpec a -> String
  def printDefinedOps spc =
      let spc = removeUndefinedOps spc       in
      let spc = setSorts(spc,emptyASortMap)  in
      let spc = setImports(spc,emptyImports) in
      printSpec spc

endspec
