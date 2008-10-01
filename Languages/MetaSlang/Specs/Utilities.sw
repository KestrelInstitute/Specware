Utilities qualifying spec  
 import MSTerm    % defines sorts Spec, Term, etc.
 import /Library/Legacy/DataStructures/IntSetSplay
 import /Library/Legacy/DataStructures/ListPair 
 import /Library/Legacy/DataStructures/ListUtilities
 import /Library/Legacy/DataStructures/StringUtilities 
 import Elaborate/Utilities
 import Equivalences
 import ../AbstractSyntax/Fold

 type Vars = List Var
 type VarSubst = List (Var * MS.Term)

 op substitute    : MS.Term * VarSubst -> MS.Term
 op freeVars      : MS.Term -> Vars

 %% Translate a term encoding an assignment to a list of pairs.
 %% Redundant assignments of a variable to itself are eliminated.

 op extractAssignment : MS.Term * MS.Term -> List (Pattern * MS.Term)

 op patternToTerm : Pattern -> Option MS.Term

 def patternToTerm(pat) = 
     case pat
       of EmbedPat(con,None,srt,a) -> 
          Some(Fun(Embed(con,false),srt,a))
        | EmbedPat(con,Some p,srt,a) -> 
          (case patternToTerm(p)
             of None -> None
	      | Some (trm) -> 
		let srt1 = patternSort p in
		Some (Apply(Fun(Embed(con,true),Arrow(srt1,srt,a),a),trm,a)))
        | RecordPat(fields,a) -> 
	  let
	     def loop(new,old) = 
	         case new
                   of [] -> Some(Record(rev old,a))
	            | (l,p)::new -> 
	         case patternToTerm(p)
	           of None -> None
	            | Some(trm) -> 
	              loop(new,List.cons((l,trm),old))
          in
          loop(fields,[])
        | NatPat(i, _) -> Some(mkNat i)
        | BoolPat(b, _) -> Some(mkBool b)
        | StringPat(s, _) -> Some(mkString s)
        | CharPat(c, _) -> Some(mkChar c)
        | VarPat((v,srt), a) -> Some(Var((v,srt), a))
        | WildPat(srt,_) -> None
        | QuotientPat(pat,cond,_)  -> None %% Not implemented
        | RestrictedPat(pat,cond,_)  ->
	  patternToTerm pat		% cond ??
%	| AliasPat(VarPat(v, _),p,_) -> 
%	  (case patternToTerm(p) 
%             of None -> None
%	      | Some(trm) -> 
%	        Some(trm,vars,cons((v,trm),S)))
	| AliasPat _ -> None %% Not supported
	 
 op  patternToTermPlusConds : Pattern -> (Option MS.Term * List MS.Term)
 def patternToTermPlusConds(pat) = 
     case pat
       of EmbedPat(con,None,srt,a) -> 
          (Some(Fun(Embed(con,false),srt,a)),[])
        | EmbedPat(con,Some p,srt,a) -> 
          (case patternToTermPlusConds p
             of (None,conds) -> (None,conds)
	      | (Some trm,conds) -> 
		let srt1 = patternSort p in
		(Some (Apply(Fun(Embed(con,true),Arrow(srt1,srt,a),a),trm,a)),conds))
        | RecordPat(fields,a) -> 
	  let
	     def loop(new,old,old_conds) = 
	         case new
                   of [] -> (Some(Record(rev old,a)),old_conds)
	            | (l,p)::new -> 
	         case patternToTermPlusConds(p)
	           of (None,conds) -> (None,old_conds++conds)
	            | (Some trm,conds) -> 
	              loop(new,Cons((l,trm),old),old_conds++conds)
          in
          loop(fields,[],[])
        | NatPat(i, _) -> (Some(mkNat i),[])
        | BoolPat(b, _) -> (Some(mkBool b),[])
        | StringPat(s, _) -> (Some(mkString s),[])
        | CharPat(c, _) -> (Some(mkChar c),[])
        | VarPat((v,srt), a) -> (Some(Var((v,srt), a)),[])
        | WildPat(srt,_) -> (None,[])
        | QuotientPat(pat,qid,_)  -> 
	  (case patternToTermPlusConds pat of
             | (None,   conds) -> (None,conds)
             | (Some t, conds) -> (Some(mkQuotient(t,qid,termSort t)), conds))
        | RestrictedPat(pat,cond,_)  ->
	  let (p,conds) = patternToTermPlusConds pat in (p,Cons(cond,conds))
	| AliasPat(p1,p2,_) -> 
	  (case patternToTermPlusConds(p2) 
             of (None,conds2) ->
	        let (ot1,conds1) = patternToTermPlusConds p1 in
		(ot1,conds1++conds2)
	      | (Some t2,conds2) -> 
		(case patternToTermPlusConds p1 of
		   | (None,conds1) ->
		     (Some t2,conds1++conds2)
		   | (Some t1,conds1) ->
		     (Some t2,[mkEquality(termSort t1,t1,t2)]++conds1++conds2)))


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
			          && isFree(v,M)
     | The(w,M,_)             -> ~(v = w) && isFree(v,M)
     | IfThenElse(t1,t2,t3,_) -> isFree(v,t1) or 
			          isFree(v,t2) or 
				  isFree(v,t3)
     | SortedTerm(t,_,_)      -> isFree(v,t)
     | Seq(tms,_)             -> exists (fn t -> isFree(v,t)) tms

 op isPatBound : Var * Pattern -> Boolean
 def isPatBound (v,pat) = 
   case pat of
     | AliasPat(p1,p2,_)      -> isPatBound(v,p1) or isPatBound(v,p2)
     | EmbedPat(_,Some p,_,_) -> isPatBound(v,p)
     | VarPat(w,_)            -> v = w
     | RecordPat(fields,_)    -> exists (fn (_,p) -> isPatBound(v,p)) fields
     | QuotientPat(p,_,_)     -> isPatBound(v,p)
     | RestrictedPat(p,_,_)   -> isPatBound(v,p)
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
	      let decls = zip (vars,terms) in
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
   case pat
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
      | RestrictedPat(pat,trm,a) -> 
	let (pat,sub,freeNames) = repPattern(pat,sub,freeNames) in
	(RestrictedPat(pat,trm,a),sub,freeNames)
      | _ -> (pat,sub,freeNames)

 %----------------------
 def freeVars (M) = 
   let vars = freeVarsRec(M) in
   removeDuplicateVars vars

  op inVars?(v: Var, vs: List Var): Boolean =
    exists (fn v1 -> equalVar?(v,v1)) vs

  op hasRefTo?(t: MS.Term, vs: List Var): Boolean =
    exists (fn v -> inVars?(v, vs)) (freeVars t)

 op removeDuplicateVars: List Var -> List Var
 def removeDuplicateVars vars = 
   case vars of
     | [] -> []
     | var :: vars -> insertVar (var, removeDuplicateVars vars)

 def insertVar (new_var, vars) = 
   if (exists (fn v -> v.1 = new_var.1) vars) then
     vars
   else
     Cons (new_var, vars)

 def deleteVar (var_to_remove, vars) = 
   List.filter (fn v -> v.1 ~= var_to_remove.1) vars

 def insertVars (vars_to_add,    original_vars) = foldl (fn (vars, new_var)       -> insertVar(new_var,       vars)) original_vars vars_to_add
 def deleteVars (vars_to_remove, original_vars) = foldl (fn (vars, var_to_remove) -> deleteVar(var_to_remove, vars)) original_vars vars_to_remove

 def freeVarsRec (M : MS.Term) =   
   case M of
     | Var    (v,      _) -> [v]

     | Apply  (M1, M2, _) -> insertVars (freeVarsRec M1, freeVarsRec M2)

     | Record (fields, _) -> freeVarsList fields

     | Fun    _           -> []

     | Lambda (rules,  _) -> foldl (fn (vars, rl) -> insertVars (freeVarsMatch rl, vars)) [] rules

     | Let (decls, M,  _) -> 
       let (pVars, tVars) =
           foldl (fn ((pVars, tVars), (pat, trm)) -> 
		  (insertVars (patVars     pat, pVars),
		   insertVars (freeVarsRec trm, tVars)))
	         ([], []) 
		 decls
       in
       let mVars = freeVarsRec M in
       insertVars (tVars, deleteVars (pVars, mVars))

     | LetRec (decls, M, _) -> 
       let pVars = List.map (fn (v, _) -> v) decls in
       let tVars = freeVarsList decls in
       let mVars = freeVarsRec  M in
       deleteVars (pVars, insertVars (tVars, mVars))

     | Bind (_, vars, M, _) -> deleteVars (vars, freeVarsRec M)
     | The  (var,     M, _) -> deleteVar  (var,  freeVarsRec M)

     | IfThenElse (t1, t2, t3, _) -> 
       insertVars (freeVarsRec t1, insertVars (freeVarsRec t2, freeVarsRec t3))

     | Seq (tms, _) -> foldl (fn (vars,tm) -> insertVars (freeVarsRec tm, vars)) [] tms

     | SortedTerm (tm, _, _) -> freeVarsRec tm

     | Pi (_, tm, _) -> freeVarsRec tm
     
     | And(tms, _) -> foldl (fn (vars,tm) -> insertVars (freeVarsRec tm, vars)) [] tms
     | Any _ -> []

 op  freeVarsList : [a] List(a * MS.Term) -> Vars
 def freeVarsList tms = 
   foldl (fn (vars,(_,tm)) -> insertVars (freeVarsRec tm, vars)) [] tms

 def freeVarsMatch (pat, cond, body) = 
   let pvars = patVars     pat  in
   let cvars = freeVarsRec cond in
   let bvars = freeVarsRec body in
   deleteVars (pvars, insertVars (cvars, bvars))

 op  patVars: Pattern -> List Var
 def patVars(pat:Pattern) = 
   case pat
     of AliasPat(p1,p2,_)      -> insertVars (patVars p1, patVars p2)
      | VarPat(v,_)            -> [v]
      | EmbedPat(_,Some p,_,_) -> patVars p
      | EmbedPat _             -> []
      | RecordPat(fields,_)    -> foldl (fn (vars,(_,p)) -> insertVars (patVars p, vars)) [] fields
      | WildPat _              -> []
      | StringPat _            -> []
      | BoolPat _              -> []
      | CharPat _              -> []
      | NatPat  _              -> []
      | QuotientPat(p,_,_)     -> patVars p
      | RestrictedPat(p,_,_)   -> patVars p
      | SortedPat(p,_,_)       -> patVars p

 op  getParams: Pattern -> List Pattern
 def getParams(pat:Pattern) = 
   case pat
     of VarPat(v,_)-> [pat]
      | RecordPat(fields,_) ->
	if all (fn (_,VarPat _) -> true | (_,RecordPat _) -> true | _ -> false) fields
	  then map (fn (_,vpat) -> vpat) fields
	  else []
      | _ -> []

 op  lookup : [a,b] (a  -> Boolean) * List(a * b) -> Option b 
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

 op boundVars(t: MS.Term): List Var =
   case t of
     | Let(decls, _, _) -> flatten (map (fn (pat, _) -> patternVars pat) decls)
     | LetRec (decls, _, _) ->  map (fn (v, _) -> v) decls
     | Lambda (match, _) -> flatten (map (fn (pat,_,_) -> patternVars pat) match)
     | Bind (_, bound, _, _) -> bound
     | _ -> []

 op boundVarsIn(t: MS.Term): List Var =
   removeDuplicateVars(foldSubTerms (fn (t,r) -> boundVars t ++ r) [] t)

 op boundVarNamesIn(t: MS.Term): List Id =
   map (fn (vn,_) -> vn) (boundVarsIn t)

 % This implementation of substitution 
 % completely ignores free variables in sorts.
 %
 % This is legal if indeed sorts do not have free variables,
 % which is a reasonable assumption given how Specware sorts
 % are handled.

 def substituteType(srt,S) = 
   let freeNames = foldr (fn ((v,trm),vs) -> 
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
   let freeNames = foldr (fn ((v,trm),vs) -> 
                            StringSet.union (StringSet.fromList
                                               (List.map (fn (n,_) -> n)
                                                  (freeVars trm)),
                                             vs)) 
                     StringSet.empty sub
   in 
   substitute2(M,sub,freeNames)
 
 op substitute2(M: MS.Term, sub: VarSubst, freeNames: StringSet.Set): MS.Term = 
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
	      let decls = zip (vars,terms) in
	      LetRec(decls,
		     substitute2(M,sub,freeNames),
		     a)
	    | Bind(b,vars,M,a)  -> 
	      let (vars,sub,freeNames) = substBoundVars(vars,sub,freeNames) in
	      Bind(b,
		   vars,
		   substitute2(M,sub,freeNames),
		   a)
	    | The(var,M,a)  -> 
	      let ([var],sub,freeNames) = substBoundVars([var],sub,freeNames) in
	      The (var, 
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
	    | SortedTerm(term, srt, a) ->
	      SortedTerm(subst(term), srt, a)

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
   let sub = deleteVarFromSub((id,s),sub,[]) in
   if StringSet.member(freeNames,id) then
     let id2 = StringUtilities.freshName(id,freeNames) in
     let sub2 = cons(((id,s),mkVar(id2,s)),sub) in
     ((id2,s),sub2,StringSet.add(freeNames,id2))
   else
     ((id,s),sub,freeNames)

 def deleteVarFromSub(v,sub,sub2) = 
   case sub
     of []         -> sub2
      | (w,M)::sub -> if v.1 = w.1
		      then sub ++ sub2
		      else deleteVarFromSub (v, sub, cons((w,M),sub2))

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
      | RestrictedPat(pat,trm,a) -> 
	let (pat,sub,freeNames) = substPattern(pat,sub,freeNames) in 
	(RestrictedPat(pat,substitute2(trm,sub,freeNames),a),sub,freeNames)
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


 op renameBoundVars(term: MS.Term, vs: List Var): MS.Term =
   let freeNames = StringSet.fromList(map(fn (n,_) -> n) vs) in
   substitute2(term,[],freeNames)

 %- --------------------------------------------------------------------------

 def report_unimplemented_for_cgen = false
 def externalopshfile(specname:String) = specname^"_extops.h"
 def cgeninfohead = ";;;CGEN-INFO "

 % ----------------------------------------------------------------------

 op  mkConjecture: QualifiedId * TyVars * MS.Term -> SpecElement
 def mkConjecture(qid,tvs,fm) =
   Property(Conjecture,qid,tvs,fm,noPos)

 %% Remove op definitions, axioms, and theorems from a spec.

 op convertConjecturesToAxioms : Spec -> Spec
(* Not used ?
 def convertConjecturesToAxioms (spc : Spec) =
   setProperties (spc, 
		  List.map (fn (ty,n,t,f) ->
			    (case ty of
			       | Conjecture:PropertyType -> Axiom:PropertyType
			       | _ -> ty,
			     n,t,f))
                           spc.properties)
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
     %| Boolean is the same as default case
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
      | QuotientPat (p,                        qid, a) -> 
	QuotientPat (letRecToLetTermPattern p, qid, a)
      | RestrictedPat(p,t,a) -> 
	RestrictedPat(letRecToLetTermPattern(p),
		      letRecToLetTermTerm(t),
		      a)
      | _ -> pat

 op letRecToLetTermFun: Fun -> Fun
 def letRecToLetTermFun fun = fun

 op letRecToLetTermSpec: Spec -> Spec
 def letRecToLetTermSpec spc =
   let 
     def letRecToLetTermSortInfo info =
       let pos = sortAnn info.dfn in
       let (old_decls, old_defs) = sortInfoDeclsAndDefs info in
       let new_defs = 
           map (fn srt ->
		let pos = sortAnn srt in
		let (tvs, srt) = unpackSort srt in
		Pi (tvs, letRecToLetTermSort srt, pos))
	       old_defs
       in
	 info << {dfn = maybeAndSort (old_decls ++ new_defs, pos)}

     def letRecToLetTermOpInfo info = 
       let pos = termAnn info.dfn in
       let (old_decls, old_defs) = opInfoDeclsAndDefs info in
       let new_defs = 
           map (fn tm ->
		let pos = termAnn tm in
		let (tvs, srt, tm) = unpackTerm tm in
		Pi (tvs, SortedTerm (tm, letRecToLetTermSort srt, pos), pos))
	       old_defs
       in
	 info << {dfn = maybeAndTerm (old_decls ++ new_defs, pos)}

   in
   spc <<
   {sorts = mapSortInfos letRecToLetTermSortInfo spc.sorts,
    ops   = mapOpInfos   letRecToLetTermOpInfo   spc.ops}

 op  patternVars  : Pattern -> List Var
 def patternVars(p) = 
     let
	def loopP(p:Pattern,vs) = 
	    case p
	      of VarPat(v,_) -> cons(v,vs)
	       | RecordPat(fields,_) -> 
		 foldr (fn ((_,p),vs) -> loopP(p,vs)) vs fields
	       | EmbedPat(_,None,_,_) -> vs
	       | EmbedPat(_,Some p,_,_) -> loopP(p,vs)
	       | QuotientPat(p,_,_) -> loopP(p,vs)
	       | AliasPat(p1,p2,_) -> loopP(p1,loopP(p2,vs))
	       | RestrictedPat(p,_,_) -> loopP(p,vs)
               | SortedPat(p,_,_) -> loopP(p,vs)
	       | _ -> vs
     in
     loopP(p,[])

 op  mkLetWithSubst: MS.Term * VarSubst -> MS.Term
 def mkLetWithSubst(tm,sb) =
   if sb = [] then tm
     else mkLet(map (fn (v,val) -> (mkVarPat v,val)) sb, tm)

 def mkIfThenElse(t1,t2:MS.Term,t3:MS.Term):MS.Term =
   case t1 of
     | Fun(Bool true,_,_)  -> t2
     | Fun(Bool false,_,_) -> t3
     | _ ->
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
	| _ ->
          if termIn?(t1, getConjuncts t2)
            then t2
            else MS.mkAnd(t1,t2)

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
   if vars = []
     then term
     else Bind(b,vars,term,noPos)

 op  mkSimpImplies: MS.Term * MS.Term -> MS.Term
 def mkSimpImplies (t1, t2) =
   case t1 of
     | Fun(Bool true,_,_)  -> t2
     | Fun(Bool false,_,_) -> mkTrue() % was mkFalse() !!
     | _ -> 
       case t2 of
        % We can't optimize (x => true) to true, as one might expect from logic.
        % The semantics for => dictates that we need to eval t1 (e.g., for side-effects) before looking at t2.  
         | Fun(Bool true,_,_) | sideEffectFree t1 -> mkTrue() 
	 | Fun(Bool false,_,_) -> mkNot t1
	 | _ -> mkImplies (t1,t2)

 op  mkSimpIff: MS.Term * MS.Term -> MS.Term
 def mkSimpIff (t1, t2) =
   case t1 of
     | Fun(Bool true,_,_)  -> t2
     | Fun(Bool false,_,_) -> negateTerm(t2) %mkTrue() % was mkFalse() !!
     | _ -> 
       case t2 of
	 | Fun(Bool true,_,_)  -> t1
	 | Fun(Bool false,_,_) -> negateTerm(t1)
	 | _ -> mkIff (t1,t2)


  op mkOptLambda(pat: Pattern, tm: MS.Term): MS.Term =
    case tm of
      | Apply(f,arg,_) ->
        (case patternToTerm pat of
           | Some pat_tm | equalTerm?(pat_tm, arg) -> f
           | _ -> mkLambda(pat, tm))
      | _ -> mkLambda(pat, tm)

 op  identityFn?: [a] ATerm a -> Boolean
 def identityFn? f =
   case f of
     | Lambda([(VarPat(x,_),_,Var(y,_))],_) -> x = y
     | _ -> false

 op [a] caseExpr?(t: ATerm a): Boolean =
   case t of
     | Apply(Lambda _, _, _) -> true
     | _ -> false

 
 op  getConjuncts: [a] ATerm a -> List (ATerm a)
 def getConjuncts t =
   case t of
     | Apply(Fun(And,_,_), Record([("1",p),("2",q)],_),_)
       -> getConjuncts p ++ getConjuncts q
     | _ -> [t]

  %% Given a universal quantification return list of quantified variables, conditions and rhs
  op  forallComponents: [a] ATerm a -> List (AVar a) * List (ATerm a) * ATerm a
  def forallComponents t =
    case t of
      | Bind(Forall,vs,bod,_) ->
	let (rVs,rLhsCjs,rRhs) = forallComponents bod in
	(vs ++ rVs,rLhsCjs,rRhs)
      | Apply(Fun(Implies, _,_),
	     Record([("1",lhs),("2",rhs)],_),_) ->
        let (rVs,rLhsCjs,rRhs) = forallComponents rhs in
	(rVs,getConjuncts lhs ++ rLhsCjs,rRhs)
      | _ -> ([],[],t)

  %% Given an existential quantification return list of quantified variables and conjuncts
  op  existsComponents: [a] ATerm a -> List (AVar a) * List (ATerm a)
  def existsComponents t =
    case t of
      | Bind(Exists,vs,bod,_) ->
	let (rVs,rLhsCjs) = existsComponents bod in
	(vs ++ rVs,rLhsCjs)
      | Apply(Fun(And,_,_), Record([("1",lhs),("2",rhs)],_),_) ->
        let (lVs,lLhsCjs) = existsComponents lhs in
        let (rVs,rLhsCjs) = existsComponents rhs in
	(lVs ++ rVs,lLhsCjs ++ rLhsCjs)
      | _ -> ([],[t])

  %% Given an existential (one) quantification return list of quantified variables and conjuncts
  op  exists1Components: [a] ATerm a -> List (AVar a) * List (ATerm a)
  def exists1Components t =
    case t of
      | Bind(Exists1,vs,bod,_) ->
	let (rVs,rLhsCjs) = exists1Components bod in
	(vs ++ rVs,rLhsCjs)
      | Apply(Fun(And,_,_), Record([("1",lhs),("2",rhs)],_),_) ->
        let (lVs,lLhsCjs) = exists1Components lhs in
        let (rVs,rLhsCjs) = exists1Components rhs in
	(lVs ++ rVs,lLhsCjs ++ rLhsCjs)
      | _ -> ([],[t])

  op  varTerm?: [a] ATerm a -> Boolean
  def varTerm? t =
    case t of
      | Var _ -> true
      | _     -> false


  op  constantTerm?: [a] ATerm a -> Boolean
  def constantTerm? t =
    case t of
      | Lambda _ -> true
      | Fun _    -> true
      | Record(fields,_) -> exists (fn (_,stm) -> constantTerm? stm) fields
      | _        -> false

  op [a] containsOpRef?(term: ATerm a): Boolean =
    existsSubTerm (fn t -> case t of
                             | Fun(Op _,_,_) -> true
                             | _ -> false)
      term

  op [a] containsRefToOp?(term: ATerm a, qid: QualifiedId): Boolean =
    existsSubTerm (fn t -> case t of
                             | Fun(Op(qid1,_),_,_) -> qid = qid1
                             | _ -> false)
      term

  op opsInTerm(tm: MS.Term): List QualifiedId =
    foldSubTerms (fn (t,opids) ->
                    case t of
                      | Fun(Op(qid,_),_,_) | ~(member(qid,opids)) ->
                        Cons(qid, opids)
                      | _ -> opids)
      [] tm

  op opsInType(ty: Sort): List QualifiedId =
    foldSort (fn result -> fn t ->
                case t of
                  | Fun(Op(qid,_),_,_) | qid nin? result -> qid::result
                  | _ -> result,
              fn result -> fn _ -> result,
              fn result -> fn _ -> result)

      [] ty

  op typesInTerm(tm: MS.Term): List QualifiedId =
    foldTerm (fn result -> fn _ -> result,
              fn result -> fn t ->
                case t of
                  | Base(qid,_,_) | qid nin? result -> qid::result
                  | _ -> result,
              fn result -> fn _ -> result)

      [] tm

  op typesInType(ty: Sort): List QualifiedId =
    foldSort (fn result -> fn _ -> result,
              fn result -> fn t ->
                case t of
                  | Base(qid,_,_) | qid nin? result -> qid::result
                  | _ -> result,
              fn result -> fn _ -> result)

      [] ty



  op  lambda?: [a] ATerm a -> Boolean
  def lambda? t =
    case t of
      | Lambda _ -> true
      | _ -> false

  %% List Term set operations
  op [a] termIn?(t1: ATerm a, tms: List (ATerm a)): Boolean =
    exists (fn t2 -> equalTerm?(t1,t2)) tms

  op [a] termsDiff(tms1: List (ATerm a), tms2: List (ATerm a)): List (ATerm a) =
    filter(fn t1 -> ~(termIn?(t1, tms2))) tms1

  op [a] termsUnion(tms1: List (ATerm a), tms2: List (ATerm a)): List (ATerm a) =
    termsDiff(tms1,tms2) ++ tms2

  op [a] termsIntersect(tms1: List (ATerm a), tms2: List (ATerm a)): List (ATerm a) =
    filter(fn t1 -> termIn?(t1, tms2)) tms1

  op [a] typeIn?(t1: ASort a, tms: List (ASort a)): Boolean =
    exists (fn t2 -> equalType?(t1,t2)) tms

 %% Evaluation of constant terms
 def evalSpecNames = ["Nat","Integer","String"] 
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

 op  booleanVal?(t: MS.Term): Boolean =
   case t of
     | Fun(Bool _,_,_) -> true
     | _ -> false

 op  booleanVal: MS.Term -> Boolean
 def booleanVal = fn (Fun(Bool s,_,_)) -> s
 op  booleanVals: List(Id * MS.Term) -> List Boolean
 def booleanVals = map (fn (_,t) -> booleanVal t)


 op  sortFromField: List(Id * MS.Term) * Sort -> Sort
 def sortFromField(fields,defaultS) =
   case fields
     of (_,Fun(_,s,_)) :: _ -> s
      | _ -> defaultS

 def sortFromArg(arg: MS.Term,defaultS:Sort): Sort =
   case arg
     of Fun(_,s,_) -> s
      | _ -> defaultS

  op  knownSideEffectFreeQIds: List(Qualifier * Id)
  def knownSideEffectFreeQIds =
    [("Integer", "~"),  % TODO: deprecate
     ("IntegerAux","-"),
     ("Integer","+"),
     ("Integer","<"),
     ("Integer",">"),
     ("Integer","<="),
     ("Integer",">="),
     ("Integer","-"),
     ("Integer","div"),
     ("Integer","rem"),
     ("Integer","abs"),
     ("Integer","min"),
     ("Integer","max"),
     ("Integer","compare"),
     ("List","length")]

  op  knownSideEffectFreeFn?: Fun -> Boolean
  def knownSideEffectFreeFn? f =
    case f of
      | Op(Qualified(qid),_) ->
        member(qid,knownSideEffectFreeQIds)
      % Not, And, Or, Implies, Iff, Equals, NotEquals -> true
      | _ -> true
      
 op  sideEffectFree: MS.Term -> Boolean
 def sideEffectFree(term) = 
     case term
       of Var _ -> true
	| Record(fields,_) -> List.all (fn(_,t)-> sideEffectFree t) fields
	| Apply(Fun(f,_,_),t,_) -> knownSideEffectFreeFn? f & sideEffectFree t
	| Fun _ -> true
	| IfThenElse(t1,t2,t3,_) -> 
		(sideEffectFree t1) 
	      & (sideEffectFree t2) 
	      & (sideEffectFree t3)
	| _ -> false 

 op  evalBinary: [a] (a * a -> Fun) * (List(Id * MS.Term) -> List a)
                      * List(Id * MS.Term) * Sort
                     -> Option MS.Term
 def evalBinary(f, fVals, fields, srt) =
   case fVals fields
     of [i,j] -> Some(Fun(f(i,j),srt,noPos))
      | _ -> None

 op  evalBinaryNotZero: (Nat * Nat -> Fun) * (List(Id * MS.Term) -> List Nat)
                      * List(Id * MS.Term) * Sort
                     -> Option MS.Term
 def evalBinaryNotZero(f, fVals, fields, srt) =
   case fVals fields
     of [i,j] ->
        if j=0 then None
	  else Some(Fun(f(i,j),srt,noPos))
      | _ -> None

 op nat:  [a] (a -> Nat) -> a -> Fun
 op char: [a] (a -> Char) -> a -> Fun
 op str:  [a] (a -> String) -> a -> Fun
 op bool: [a] (a -> Boolean) -> a -> Fun
 def nat f x  = Nat(f x)
 def char f x = Char(f x)
 def str f x = String(f x)
 def bool f x = Bool(f x)

 op  attemptEval1: String * MS.Term -> Option MS.Term
 def attemptEval1(opName,arg) =
   case (opName,arg) of
      | ("~", Fun (Nat i,_,aa)) -> Some(Fun (Nat (- i), natSort,aa))
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

 op  attemptEvaln: String * String * List(Id * MS.Term) ->  Option MS.Term
 def attemptEvaln(spName,opName,fields) =
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
      | "<"   -> if spName = "String"
	          then evalBinary(bool <,stringVals,fields,boolSort)
		  else evalBinary(bool <,natVals,fields,boolSort)
      | "<="  -> if spName = "String"
	          then evalBinary(bool <=,stringVals,fields,boolSort)
		  else evalBinary(bool <=,natVals,fields,boolSort)
      | ">"   -> if spName = "String"
	          then evalBinary(bool >,stringVals,fields,boolSort)
		  else evalBinary(bool >,natVals,fields,boolSort)
      | ">="  -> if spName = "String"
	          then evalBinary(bool >=,stringVals,fields,boolSort)
		  else evalBinary(bool >=,natVals,fields,boolSort)
      | "min" -> evalBinary(nat min,natVals,fields,
			    sortFromField(fields,natSort))
      | "max" -> evalBinary(nat max,natVals,fields,
			    sortFromField(fields,natSort))
      | "rem" -> evalBinaryNotZero(nat rem,natVals,fields,natSort)
      | "div" -> evalBinaryNotZero(nat div,natVals,fields,natSort)

      %% string operations
      | "concat" -> evalBinary(str concat,stringVals,fields,stringSort)
      | "++"  -> evalBinary(str ++,stringVals,fields,stringSort)
      | "^"   -> evalBinary(str ^,stringVals,fields,stringSort)
      | "substring" ->
	(case fields
	   of [(_,s),(_,i),(_,j)] ->
	      let sv = stringVal s in
	      let iv = natVal i in
	      let jv = natVal j in
	      if iv <= jv && jv <= length sv
		then Some(Fun(String(substring(sv,iv,jv)),
			      stringSort,noPos))
		else None
	    | _ -> None)
      | "leq" -> evalBinary(bool leq,stringVals,fields,boolSort)
      | "lt"  -> evalBinary(bool lt,stringVals,fields,boolSort)

      | _ -> None

 op  attemptEval: Spec -> MS.Term -> MS.Term
 def attemptEval spc t = mapSubTerms (attemptEvalOne spc) t

 op  attemptEvalOne: Spec -> MS.Term -> MS.Term
 def attemptEvalOne spc t =
   case tryEvalOne spc t of
     | Some t1 -> t1
     | None    -> t

 op  tryEvalOne: Spec -> MS.Term -> Option MS.Term
 def tryEvalOne spc term =
   case term
     of Apply(Fun(Op(Qualified(spName,opName),_),s,_),arg,_) ->
        (if member(spName,evalSpecNames)
	 then (case arg
		 of Record(fields, _) ->
		    (if all (fn (_,tm) -> evalConstant?(tm)) fields
		      then attemptEvaln(spName,opName,fields)
		      else None)
		   | _ -> (if evalConstant?(arg)
			    then attemptEval1(opName,arg)
			    else None))
	  else None)
      | Apply(Fun(Equals,_,_),Record([(_,N1),(_,N2)], _),_) ->
          %% CAREFUL: if N1 and N2 are equivalent, we can simplify to true,
          %%          but otherwise we cannot act, since they might be ops later equated to each other
	if constantTerm?(N1) && constantTerm?(N2) then
          (let eq? = equivTerm? spc (N1,N2) in % equalTerm? would reject 0:Nat = 0:Integer
             if eq? || (~(containsOpRef? N1) && ~(containsOpRef? N2))
               then Some(mkBool eq?)
             else None)
        else None
      | Apply(Fun(NotEquals,_,_),Record([(_,N1),(_,N2)], _),_) ->
	if evalConstant?(N1) & evalConstant?(N2) then
          %% CAREFUL: if N1 and N2 are equivalent, we can simplify to false,
          %%          but otherwise we cannot act, since they might be ops later equated to each other
          (let eq? = equivTerm? spc (N1,N2) in  % equalTerm? would reject 0:Nat = 0:Integer
             if eq? || (~(containsOpRef? N1) && ~(containsOpRef? N2))
               then Some(mkBool(~eq?))
           else
             None)
        else None
      | Apply(Fun(Not,  _,_),arg,                       _) -> 
	(case arg of
           | Fun (Bool b,_,aa) -> Some(mkBool (~ b))
           | Apply(Fun(NotEquals,ty,a1),args,a2) ->
             Some(Apply(Fun(Equals,ty,a1),args,a2))
           | _ -> None)
      | Apply(Fun(And,  _,_),Record(fields as [(_,N1),(_,N2)], _),_) ->
        if booleanVal? N1 || booleanVal? N2 then Some (mkAnd(N1,N2)) else None
      | Apply(Fun(Or,   _,_),Record(fields as [(_,N1),(_,N2)], _),_) -> 
        if booleanVal? N1 || booleanVal? N2 then Some (mkOr(N1,N2)) else None
      | Apply(Fun(Implies, _,_),Record(fields as [(_,N1),(_,N2)], _),_) ->
        if booleanVal? N1 || (booleanVal? N2 && sideEffectFree N1) then Some (mkSimpImplies(N1,N2)) else None
      | Apply(Fun(Iff, _,_),Record(fields as [(_,N1),(_,N2)], _),_) -> 
	if booleanVal? N1 || booleanVal? N2 then Some (mkSimpIff(N1,N2)) else None
      | IfThenElse(p,q,r,_) ->
        if trueTerm? p then Some q
          else if falseTerm? p then Some r
          else if equivTerm? spc (q,r) & sideEffectFree p then Some q
          else if trueTerm? q && falseTerm? r then Some p
          else if falseTerm? q && trueTerm? r then Some (negateTerm p)
          else None
        %% {id1 = v1, ..., idn = vn}.idi = vi
      | Apply(Fun(Project i,_,_),Record(m,_),_) ->
        (case getField(m,i) of
           | Some fld -> Some fld
           | None -> None)
      | Fun(Op(Qualified ("Integer", "zero"),_),_,a) -> Some(mkFun(Nat 0, integerSort))
      | _ -> None

 op  disjointMatches: Match -> Boolean
 def disjointMatches = 
     fn [] -> true
      | (pat1,_,_)::matches -> 
         List.all 
           (fn(pat2,_,_) -> disjointPatterns(pat1,pat2)) 
             matches 
        & disjointMatches matches

 op  disjointPatterns: Pattern * Pattern -> Boolean
 def disjointPatterns = 
     (fn (EmbedPat(con1,Some p1,_,_):Pattern,
	  EmbedPat(con2,Some p2,_,_):Pattern) -> 
	 if con1 = con2
	    then disjointPatterns(p1,p2)
         else true
       | (EmbedPat(con1,None,_,_),EmbedPat(con2,None,_,_)) -> 
         ~(con1 = con2)
       | (EmbedPat _,EmbedPat _) -> true
       | (RecordPat(fields1, _),RecordPat(fields2, _)) -> 
	 ListPair.exists 
	   (fn ((_,p1),(_,p2)) -> disjointPatterns(p1,p2)) (fields1,fields2)
       | (AliasPat(p1,p2,_),p3) -> 
	 disjointPatterns(p1,p3) or disjointPatterns(p2,p3)
       | (p1,AliasPat(p2,p3,_)) -> 
	 disjointPatterns(p1,p2) or disjointPatterns(p1,p3)
       | (NatPat(i1, _),NatPat(i2, _)) -> ~(i1 = i2)
       | (BoolPat(b1, _),BoolPat(b2, _)) -> ~(b1 = b2)
       | (CharPat(c1, _),CharPat(c2, _)) -> ~(c1 = c2)
       | (StringPat(s1, _),StringPat(s2, _)) -> ~(s1 = s2)
       | _ -> false
      )

 op substSort : fa(a) List (Id * ASort a) * ASort a -> ASort a
 def substSort (S, srt) =
  let def find (name, S, a) =  
       case S 
         of []            -> TyVar(name,a)
          | (id, srt) ::S -> if name = id then srt else find (name, S, a) 
  in 
  let def subst1 srt =  
       case srt of
          | TyVar (name, a) -> find (name, S, a)
          | _ -> srt
  in 
  mapSort (id, subst1, id) srt
 
 op unfoldBase  : Spec * Sort -> Sort 
 def unfoldBase (sp, srt) =
   unfoldBaseV (sp, srt, true)

 op unfoldBaseV : Spec * Sort * Boolean -> Sort 
 def unfoldBaseV (sp, srt, verbose) = 
  case srt of
    | Base (qid, srts, a) ->
      (case findTheSort (sp, qid) of
	 | None -> srt
	 | Some info ->
	   if definedSortInfo? info then
	     let (tvs, srt_def) = unpackFirstSortDef info in
             if length tvs ~= length srts
               then (% writeLine("Type arg# mismatch: "^printSort srt);
                     %% This can arise because of inadequacy of patternSort on QuotientPat
                     srt_def)
             else
	     let ssrt = substSort (zip (tvs, srts), srt_def) in
	     unfoldBaseV (sp, ssrt, verbose)
	   else
	     srt)
    | _ -> srt

 op  unfoldBaseOne : Spec * Sort -> Sort 
 def unfoldBaseOne (sp, srt) = 
  case srt of
    | Base (qid, srts, a) ->
      (case findTheSort (sp, qid) of
	 | None -> srt
	 | Some info ->
	   if definedSortInfo? info then
	     let (tvs, srt) = unpackFirstSortDef info in
	     let ssrt = substSort (zip (tvs, srts), srt) in
	     ssrt
	   else
	     srt)
    | _ -> srt

  op tryUnfoldBase (spc: Spec) (ty: Sort): Option Sort =
    let exp_ty = unfoldBaseOne(spc, ty) in
    if embed? CoProduct exp_ty || embed? Quotient exp_ty || equalType?(exp_ty, ty)
      then None
      else Some exp_ty

 op existsInFullType? (spc: Spec) (pred?: Sort -> Boolean) (ty: Sort): Boolean =
   pred? ty ||
   (case ty of
      | Base _ ->
        (case tryUnfoldBase spc ty of
           | None -> false
           | Some uf_ty -> existsInFullType? spc pred? uf_ty)
      | Arrow(x,y,_) -> existsInFullType? spc pred? x || existsInFullType? spc pred? y
      | Product(prs,_) -> exists (fn (_,f_ty) -> existsInFullType? spc pred? f_ty) prs
      | CoProduct(prs,_)  -> exists (fn (_,o_f_ty) ->
                                       case o_f_ty of
                                         | Some f_ty -> existsInFullType? spc pred? f_ty
                                         | None -> false)
                               prs
      | Quotient(x,_,_) -> existsInFullType? spc pred? x
      | Subsort(x,_,_) -> existsInFullType? spc pred? x
      | And(tys,_) -> exists (existsInFullType? spc pred?) tys
      | _ -> false)

 op subtype?(sp: Spec, srt: Sort): Boolean =
   case srt of
     | Subsort _ -> true
     | _ ->
       let exp_srt =  unfoldBase (sp, srt) in
       if srt = exp_srt then false
         else subtype?(sp, exp_srt)

 op subtypeComps(sp: Spec, ty: Sort): Option(Sort * MS.Term) =
   case ty of
     | Subsort(sty,p,_) -> Some(sty,p)
     | _ ->
       let exp_ty =  unfoldBase (sp, ty) in
       if ty = exp_ty then None
         else subtypeComps(sp, exp_ty)

  op raiseSubtype(ty: Sort, spc: Spec): Sort =
  %% Bring subtypes to the top-level
    % let _ = writeLine("rt: "^printSort ty) in
    case ty of
      | Base(qid, args, a) ->
        let args = map (fn tyi -> raiseSubtype(tyi, spc)) args in
        if exists (fn tyi -> subtype?(spc, tyi)) args
          then
          let Qualified(q,id) = qid in
          let pred_name = id^"_P" in
          let pred_qid = Qualified(q, pred_name) in
          (case AnnSpec.findTheOp(spc, pred_qid) of
             | Some _ ->
               let arg_comps = map (fn tyi ->
                                    case subtypeComps(spc, tyi) of
                                      | Some pr -> pr
                                      | None -> (tyi, mkLambda(mkWildPat tyi, trueTerm)))
                                 args
               in
               let (bare_args, arg_preds) = unzip arg_comps in
               let bare_ty = Base(qid, bare_args, a) in
               Subsort(bare_ty,
                       mkAppl(mkOp(pred_qid, mkArrow(mkProduct(map (fn ty -> mkArrow(ty, boolSort)) bare_args),
                                                     mkArrow(bare_ty, boolSort))),
                              arg_preds),
                       a)
             | None ->
               (case tryUnfoldBase spc ty of
                  | None -> ty
                  | Some exp_ty -> raiseSubtype(exp_ty, spc)))
        else
          (case tryUnfoldBase spc ty of
             | None -> ty
             | Some exp_ty -> raiseSubtype(exp_ty, spc))
      | Subsort(s_ty, p, a) ->
        (case raiseSubtype(s_ty, spc) of
           | Subsort(sss_ty, pr, _) ->
             let v = ("x", sss_ty) in
             Subsort(sss_ty, mkLambda(mkVarPat v, mkAnd(mkApply(p, mkVar v), mkApply(pr, mkVar v))), a)
           | _ -> ty)
      | Product(flds, a) ->
        if exists (fn (_,tyi) -> subtype?(spc, tyi)) flds
          then let (bare_flds, arg_fld_vars, pred,_) =
                foldl (fn ((bare_flds, arg_fld_vars, pred, i),(id,tyi)) ->
                         case subtypeComps(spc, tyi) of
                           | Some(t,p) -> let v = ("x"^toString i, t)  in
                                          (bare_flds ++ [(id,t)],
                                           arg_fld_vars ++ [(id,mkVarPat v)],
                                           mkAnd(pred, mkApply(p, mkVar v)),
                                           i+1)
                           | None -> (bare_flds ++ [(id,tyi)],
                                      arg_fld_vars ++ [(id,mkWildPat tyi)],
                                      pred,
                                      i+1))
                  ([],[],trueTerm,0) flds
               in
               Subsort(Product(bare_flds,a), mkLambda(mkRecordPat arg_fld_vars, pred), a)
          else ty
 %     | Arrow(dom, rng ,a) ->
%        (case raiseSubtype(dom,spc) of
%           | Subsort(d,d_p,_) ->
%             %% Using d would be more natural, but then you have to change the type of all variable refs
%             %% to avoid unnecessary type annotation in Isabelle output (or else freeVars needs to be
%             %% fixed to ignore types
%             let f_ty = Arrow(dom,rng,a) in
%             Subsort(f_ty, mkSubtypeFnPredicate(d_p, f_ty, d, rng), a)
%           | _ -> ty)
      | _ -> ty


  type TyVarSubst = List(TyVar * Sort)
  op  instantiateTyVars: Sort * TyVarSubst -> Sort
  def instantiateTyVars(s,tyVarSubst) =
    case s of
      | TyVar (name, _) ->
	(case find (fn (nm,_) -> nm = name) tyVarSubst of
	   | Some(_,ss) -> ss
	   | _ -> s)
      | _ -> s

  op instantiateTyVarsInType(ty: Sort, subst: TyVarSubst): Sort =
    mapSort (id, fn ty -> instantiateTyVars(ty,subst), id) ty

  op instantiateTyVarsInTerm(tm: MS.Term, subst: TyVarSubst): MS.Term =
    mapTerm (id, fn ty -> instantiateTyVars(ty,subst), id) tm

  op instantiateTyVarsInPattern(pat: Pattern, subst: TyVarSubst): Pattern =
    mapPattern (id, fn ty -> instantiateTyVars(ty,subst), id) pat

  op  typeMatch: Sort * Sort * Spec * Boolean -> Option TyVarSubst
  def typeMatch(s1,s2,spc,ign_subtypes?) =
   let def match(srt1: Sort, srt2: Sort, pairs: TyVarSubst): Option TyVarSubst =
        % let _ = writeLine(printSort srt1^" =?= "^ printSort srt2) in
        let result =
            case (srt1,srt2) of
              | (TyVar(id1,_), srt2) -> 
                (case (find (fn (id,_) -> id = id1) pairs) of
                   | Some(_,msrt1) -> if equalType?(msrt1,srt2) then Some pairs else None  % TODO: should equalType? be equivType? ??
                   | None -> Some(Cons((id1,srt2),pairs)))
              | (Arrow(t1,t2,_),Arrow(s1,s2,_)) ->
                (case match(t1,s1,pairs) of
                   | Some pairs -> match(t2,s2,pairs)
                   | None -> None)
              | (Product(r1,_),Product(r2,_)) -> 
                typeMatchL(r1,r2,pairs,fn((_,s1),(_,s2),pairs) -> match(s1,s2,pairs)) 
              | (CoProduct(r1,_),CoProduct(r2,_)) -> 
                typeMatchL(r1,r2,pairs,
                           fn((id1,s1),(id2,s2),pairs) ->
                             if id1 = id2 then
                               (case (s1,s2) of
                                  | (None,None) -> Some pairs 
                                  | ((Some ss1),(Some ss2)) -> match(ss1,ss2,pairs)
                                  | _ -> None)
                             else None)
              | (Quotient(ty,t1,_),Quotient(ty2,t2,_)) -> 
                if equalTerm?(t1,t2) then % not equivTerm?
                  match(ty,ty2,pairs)
                else 
                  None
              | (Subsort(ty,t1,_),Subsort(ty2,t2,_)) | equalTerm?(t1,t2) ->  % not equivTerm?
                match(ty,ty2,pairs)
              | (Subsort(ty,_,_), ty2) | ign_subtypes? ->
                match(ty,ty2,pairs)
              | (ty1, Subsort(ty,_,_)) | ign_subtypes? ->
                match(ty1,ty,pairs)
              | (Base(id,ts,pos1),Base(id2,ts2,pos2)) ->
                if id = id2
                  then typeMatchL(ts,ts2,pairs,match)
                else
                  let s2x = unfoldBase(spc,srt2) in
                  if embed? CoProduct s2x || embed? Quotient s2x  % If names different then not equal
                    then None
                  else
                  if equalType? (srt2,s2x) %% equivType? spc (srt2,s2x)  would also be reasonable -- see NormalizeTypes.sw for usage
                    then Some pairs
                  else match(srt1,s2x,pairs)
              | (_,Base _) ->
                let s2x = unfoldBase(spc,srt2) in
                if equalType? (srt2,s2x)     %% equivType? spc (srt2,s2x)  would also be reasonable -- see NormalizeTypes.sw for usage
                  then None
                else match(srt1,s2x,pairs)
              | (Base _,_) ->
                let s1x = unfoldBase(spc,srt1) in
                if equalType? (srt1,s1x)     %% equivType? spc (srt1,s1x)  would also be reasonable -- see NormalizeTypes.sw for usage
                  then None
                else match(s1x,srt2,pairs)
              | (Boolean _, Boolean _) -> Some pairs
              | _ -> None
        in
        % let _ = writeLine("Result: "^anyToString result) in
        result
  in match(s1,s2,[])

  op typeMatchL: [a] List a * List a * TyVarSubst * (a * a * TyVarSubst -> Option TyVarSubst)
                 -> Option TyVarSubst
  def typeMatchL(l1,l2,pairs,matchElt) =
    case (l1,l2)
     of (e1::l1,e2::l2) ->
        (case matchElt(e1,e2,pairs) of
	   | Some pairs -> typeMatchL(l1,l2,pairs,matchElt)
	   | None -> None)
      | _ -> Some pairs

  op mkOpFromDef(qid: QualifiedId, ty: Sort, spc: Spec): MS.Term =
    case findTheOp(spc, qid) of
      | Some opinfo ->
        (let (tvs,ty1,_) = unpackFirstOpDef opinfo in
         case typeMatch(ty1,ty,spc,true) of
           | Some subst ->
             let inst_ty = instantiateTyVarsInType(ty1, subst) in
             mkInfixOp(qid, opinfo.fixity, inst_ty)
           | None ->  mkOp(qid, ty)) 
      | _ -> mkOp(qid, ty)

  op termSize (t: MS.Term): Nat =
    foldSubTerms (fn (_,i) -> i + 1) 0 t

  op [a] maximal (f: a -> Nat) (l: List a): Option a =
    let def loop (l,m,best) =
          case l of
            | [] -> Some best
            | x::r ->
              let new = f x in
              if new > m
                then loop(r,new,x)
                else loop(r,m,best)
    in
    case l of
      | [] -> None
      | x::r -> loop(r,f x,x)

  op newName (name: String, names: List String): String = 
    let
      def loop i =
        let n = name ^ (toString i) in
        if exists (fn m -> n = m) names then
          loop (i + 1)
        else 
          n
    in
      loop 1

  op knownNonEmptyBaseTypes: List QualifiedId =
    [Qualified("Integer", "Integer"), Qualified("Nat","Nat"), Qualified("Char","Char"),
     Qualified("String", "String"), Qualified("List","List"), Qualified("Option","Option")]

  op existsOpWithType?(ty: Sort, spc: Spec): Boolean =
    foldriAQualifierMap
      (fn (q, id, info, result) ->
         result
        || (equalType?(firstOpDefInnerSort info, ty) ))
      false spc.ops

  op existsTrueExistentialAxiomForType?(ty: Sort, spc: Spec): Boolean =
    foldlSpecElements (fn (result,el) ->
                         result || (case el of
                                      | Property(Axiom, _, _,
                                                 Bind(Exists, [(_,ex_ty)], Fun(Bool true,_,_), _),_) ->
                                        equalType?(ex_ty, ty)
                                      | _ -> false))
      false spc.elements

  op knownNonEmpty?(ty: Sort, spc: Spec): Boolean =
    case ty of
      | Base(qid,tvs,_) ->
        member(qid, knownNonEmptyBaseTypes)
          || tvs ~= []                  % Not completely safe
          || (let Some info = findTheSort(spc, qid) in
              knownNonEmpty?(info.dfn, spc))
          || existsOpWithType?(ty, spc)
         %% Leave out for now as it messes up emptyTypesToSubtypes
         %% || existsTrueExistentialAxiomForType?(ty, spc)
      | Quotient(sty,_,_) -> knownNonEmpty?(sty, spc)
      | Pi(_,sty,_) -> knownNonEmpty?(sty, spc)
      | And(sty::_,_) -> knownNonEmpty?(sty, spc)
      | Subsort _ -> false
      | TyVar _ -> false
      | Any _ -> false
      | _ -> true

endspec
