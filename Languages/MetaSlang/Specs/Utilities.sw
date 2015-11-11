Utilities qualifying spec  
 import MSTerm    % defines types Spec, Term, etc.
 import /Library/Legacy/DataStructures/IntSetSplay
 import /Library/Legacy/DataStructures/ListPair 
 import /Library/Legacy/DataStructures/ListUtilities
 import /Library/Legacy/DataStructures/StringUtilities 
 import Elaborate/Utilities
 import Equivalences
 import ../AbstractSyntax/Fold
 import /Languages/Lisp/Suppress

 op [a] varNames (vs: AVars a): List Id = map (fn (vn,_) -> vn) vs

 op substitute  : MSTerm * MSVarSubst -> MSTerm
 op freeVars    : [a] ATerm a -> AVars a

 %% Translate a term encoding an assignment to a list of pairs.
 %% Redundant assignments of a variable to itself are eliminated.

 op extractAssignment : MSTerm * MSTerm -> List (MSPattern * MSTerm)

 % Try to turn a pattern into the most general term it matches against
 op patternToTerm : MSPattern -> Option MSTerm

 def patternToTerm(pat) = 
     case pat
       of EmbedPat(con,None,ty,a) -> 
          Some(Fun(Op(con,Constructor0),ty,a))
        | EmbedPat(con,Some p,ty,a) -> 
          (case patternToTerm(p)
             of None -> None
	      | Some (trm) -> 
		let ty1 = patternType p in
		Some (Apply(Fun(Op(con, Constructor1),Arrow(ty1,ty,a),a),trm,a)))
        | RecordPat(fields,a) -> 
	  let
	     def loop(new,old) = 
	         case new
                   of [] -> Some(Record(reverse old,a))
	            | (l,p)::new -> 
	         case patternToTerm(p)
	           of None -> None
	            | Some(trm) -> 
	              loop(new,Cons((l,trm),old))
          in
          loop(fields,[])
        | NatPat(i, _) -> Some(mkNat i)
        | BoolPat(b, _) -> Some(mkBool b)
        | StringPat(s, _) -> Some(mkString s)
        | CharPat(c, _) -> Some(mkChar c)
        | VarPat((v,ty), a) -> Some(Var((v,ty), a))
        | WildPat(ty,_) -> None
        | QuotientPat(pat,cond,_,_)  -> None %% Not implemented
        | RestrictedPat(pat,cond,_)  ->
	  patternToTerm pat		% cond ??
%	| AliasPat(VarPat(v, _),p,_) -> 
%	  (case patternToTerm(p) 
%             of None -> None
%	      | Some(trm) -> 
%	        Some(trm,vars,cons((v,trm),S)))
	| AliasPat _ -> None %% Not supported

 op  patternToTermPlusExConds(pat: MSPattern): MSTerm * MSTerms * MSVars =
   let wild_num = mkRef 0 in
   let def patToTPV pat =
         case pat
           of EmbedPat(con, None, ty, a) -> 
              (Fun(Op(con, Constructor0), ty, a), [], [])
            | EmbedPat(con, Some p, ty, a) -> 
              let (trm, conds, vs) = patToTPV p in
              let ty1 = patternType p in
              (Apply(Fun(Op(con, Constructor1), Arrow(ty1, ty, a), a), trm, a), conds, vs)
            | RecordPat(fields, a) -> 
              let
                 def loop(new, old, old_conds, old_vs) = 
                     case new
                       of [] -> (Record(reverse old, a), old_conds, old_vs)
                        | (l, p)::new -> 
                     let (trm, conds, vs) = patToTPV p in
                     loop(new, (l, trm)::old, old_conds++conds, old_vs++vs)
              in
              loop(fields, [], [], [])
            | NatPat(i, _) -> (mkNat i, [], [])
            | BoolPat(b, _) -> (mkBool b, [], [])
            | StringPat(s, _) -> (mkString s, [], [])
            | CharPat(c, _) -> (mkChar c, [], [])
            | VarPat(v, a) -> (Var(v, a), [], [v])
            | WildPat(ty, _) ->
              let gen_var = ("zz__" ^ show(!wild_num), ty) in
              (wild_num := !wild_num + 1;
               (mkVar gen_var, [], [gen_var]))
            | QuotientPat(qpat, qid, _, _)  -> 
              let (t, conds, vs) = patToTPV qpat in
              % let _ = writeLine("pttpec: "^printPattern pat^": "^printType(patternType pat)^"\n"^printTermWithTypes t) in
              % let _ = writeLine(printType(termType(mkQuotient(t, qid, termType t)))) in
              (mkQuotient(t, qid, termType t), conds, vs)
            | RestrictedPat(pat, cond, _)  ->
              let (p, conds, vs) = patToTPV pat in (p, getConjuncts cond ++ conds, vs)
            | AliasPat(p1, p2, _) -> 
              let (t2, conds2, vs2) = patToTPV p2 in
              let (t1, conds1, vs1) = patToTPV p1 in
              (t2, [mkEquality(termType t1, t1, t2)]++conds1++conds2, vs1++vs2)
   in
   patToTPV pat

 op termToPattern(tm: MSTerm): Option MSPattern =
   case tm of
     | Var v -> Some(VarPat v)
     | Record(fields,a) ->
       (case foldr (fn ((id, tm), o_flds) ->
                     case o_flds of
                       | None -> None
                       | Some flds ->
                     case termToPattern tm of
                       | Some p -> Some((id, p) :: flds)
                       | None -> None)
             (Some []) fields
        of None -> None
         | Some p_fields -> Some(RecordPat(p_fields, a)))
     | Fun(Embed(con,false),ty,a) -> Some(EmbedPat(con,None,ty,a))
     | Fun(Op(con,Constructor0),ty,a) -> Some(EmbedPat(con,None,ty,a))
     | Apply(Fun(Embed(con,true), Arrow(_,ty,_),_),trm,a) ->
       (case termToPattern trm of
        | None -> None
        | Some p -> Some(EmbedPat(con,Some p,ty,a)))
     | Apply(Fun(Op(con,Constructor1), Arrow(_,ty,_),_),trm,a) ->
       (case termToPattern trm of
        | None -> None
        | Some p -> Some(EmbedPat(con,Some p,ty,a)))
     | Fun(Nat n, _, a) -> Some(NatPat(n, a))
     | Fun(Bool b, _, a) -> Some(BoolPat(b, a))
     | Fun(String s, _, a) -> Some(StringPat(s, a))
     | Fun(Char c, _, a) -> Some(CharPat(c, a))
     | _ -> None

 op isFree : MSVar * MSTerm -> Bool
 def isFree (v, term) = 
   case term of
     | Var(w,_)               -> v = w
     | Apply(M1,M2,_)         -> isFree(v,M1) || isFree(v,M2)
     | Record(fields,_)       -> exists? (fn (_,M) -> isFree(v,M)) fields
     | Fun _                  -> false
     | Lambda(rules,_)        -> exists? (fn (pat,cond,body) -> 
					  ~(isPatBound(v,pat)) 
					  && 
					  (isFree(v,cond) || isFree(v,body)))
                                         rules
     | Let(decls,M,_)         -> exists? (fn (_,M) -> isFree(v,M)) decls
			  	  ||
				  (forall? (fn (p,_) -> ~(isPatBound(v,p))) decls
				   &&
				   isFree(v,M))
     | LetRec(decls,M,_)      -> forall? (fn (w,_) -> ~(v = w)) decls 
				  && 
				  (exists? (fn (_,M) -> isFree(v,M)) decls
				   || 
				   isFree(v,M)) 
     | Bind(b,vars,M,_)       -> forall? (fn w -> ~(v = w)) vars 
			          && isFree(v,M)
     | The(w,M,_)             -> ~(v = w) && isFree(v,M)
     | IfThenElse(t1,t2,t3,_) -> isFree(v,t1) || 
			          isFree(v,t2) || 
				  isFree(v,t3)
     | TypedTerm(t,_,_)       -> isFree(v,t)
     | Seq(tms,_)             -> exists? (fn t -> isFree(v,t)) tms
     | mystery -> fail ("unrecognized argument to isFree : " ^ anyToString mystery)

 op isPatBound : MSVar * MSPattern -> Bool
 def isPatBound (v,pat) = 
   case pat of
     | AliasPat(p1,p2,_)      -> isPatBound(v,p1) || isPatBound(v,p2)
     | EmbedPat(_,Some p,_,_) -> isPatBound(v,p)
     | VarPat(w,_)            -> v = w
     | RecordPat(fields,_)    -> exists? (fn (_,p) -> isPatBound(v,p)) fields
     | QuotientPat(p,_,_,_)     -> isPatBound(v,p)
     | RestrictedPat(p,_,_)   -> isPatBound(v,p)
     | _ -> false

 op replace : MSTerm * List (MSTerm * MSTerm) -> MSTerm
 def replace(M,sub) = 
   if empty? sub then 
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
       def rep(M:MSTerm):MSTerm = 
         case lookup (fn N -> equalTerm? (N, M), sub)
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
	  if empty? sub then
	    (pat, cond, term) 
	  else
	    (pat, replace2(cond,sub,freeNames), replace2(term,sub,freeNames)) 

	def repLet ((pat,trm),(decls,freeNames,sub)) = 
	  let (pat,sub,freeNames) = repPattern(pat,sub,freeNames) in
	  (Cons((pat,trm),decls),freeNames,sub)
   in
     rep(M)

 op repPattern : MSPattern * List (MSTerm * MSTerm) * StringSet.Set -> MSPattern * List (MSTerm * MSTerm) * StringSet.Set
 op repBoundVars: MSVars *  List (MSTerm * MSTerm) * StringSet.Set -> MSVars *  List (MSTerm * MSTerm) * StringSet.Set


 def repBoundVars(vars,sub,freeNames) = 
   foldr (fn(v,(vars,sub,freeNames)) -> 
	  let (v,sub,freeNames) = repBoundVar(v,sub,freeNames) in
	  (Cons(v,vars),sub,freeNames))
         ([],sub,freeNames) vars
	
 def repBoundVar((id,s),sub,freeNames) = 
   if StringSet.member(freeNames,id) then
     let id2 = StringUtilities.freshName(id,freeNames) in
     let sub2 = Cons((mkVar(id,s),mkVar(id2,s)),sub) in
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
		   (Cons((id,p),fields),sub,freeNames))
	          ([],sub,freeNames) fields
	in
	  (RecordPat(fields,a),sub,freeNames)
      | EmbedPat(oper,Some pat,ty,a) -> 
	let (pat,sub,freeNames) = repPattern(pat,sub,freeNames) in
	(EmbedPat(oper,Some pat,ty,a),sub,freeNames)
      | EmbedPat(oper,None,ty,_) -> 
	(pat,sub,freeNames)
      | AliasPat(p1,p2,a) ->
	let (p1,sub,freeNames) = repPattern(p1,sub,freeNames) in
	let (p2,sub,freeNames) = repPattern(p2,sub,freeNames) in
	(AliasPat(p1,p2,a),sub,freeNames)
      | QuotientPat(pat,trm,tys,a) -> 
	let (pat,sub,freeNames) = repPattern(pat,sub,freeNames) in
	(QuotientPat(pat,trm,tys,a),sub,freeNames)
      | RestrictedPat(pat,trm,a) -> 
	let (pat,sub,freeNames) = repPattern(pat,sub,freeNames) in
        let new_trm = replace2(trm, sub, freeNames) in
	(RestrictedPat(pat,new_trm,a),sub,freeNames)
      | _ -> (pat,sub,freeNames)


 op printVar ((id, ty) : MSVar) : String =
   id ^ ": " ^ printType ty

 op printVars (vars : MSVars) : String =
  (foldl (fn (s, v) ->
            s ^ (if s = "[" then "" else " ")
              ^ printVar v)
         "[" 
         vars)
  ^ "]"


 %----------------------
 def freeVars (M) = 
   let vars = freeVarsRec M true in
   removeDuplicateVars vars

 op [a] freeVarsAll (M: ATerm a): AVars a =
  %% Include conditions of simple lambdas. E.g. fn (x | p x) -> ...
   let vars = freeVarsRec M false in
   removeDuplicateVars vars

  op [a] inVars?(v: AVar a, vs: AVars a): Bool =
    exists? (fn v1 -> equalVar?(v,v1)) vs

  op [a] disjointVars?(vs1: AVars a, vs2: AVars a): Bool =
     ~(exists? (fn v -> inVars?(v, vs1)) vs2)

  op [a] hasRefTo?(t: ATerm a, vs: AVars a): Bool =
    existsSubTerm (fn t -> case t of
                             | Var(v,_) -> inVars?(v, vs)
                             | _ -> false)
      t

 op [a] hasVarNameConflict?(tm: ATerm a, vs: AVars a): Bool =
   let names = map (project 1) vs in
   (existsSubTerm (fn t -> case t of
                            | Var((nm,_),_) -> nm in? names
                            | _ -> false)
     tm)
     && exists? (fn (nm, _) -> nm in? names) (freeVars tm)

 op [a] disjointVarNames?(vs1: AVars a, vs2: AVars a): Bool =
   forall? (fn (vn1, _) -> forall? (fn (vn2, _) -> vn1 ~= vn2) vs2) vs1

 op [a] removeDuplicateVars: AVars a -> AVars a
 def removeDuplicateVars vars = 
   case vars of
     | [] -> []
     | var :: vars -> insertVar (var, removeDuplicateVars vars)

 op [a] insertVar (new_var: AVar a, vars: AVars a): AVars a = 
   if (exists? (fn v -> v.1 = new_var.1) vars) then
     vars
   else
     Cons (new_var, vars)

 op [a] deleteVar (var_to_remove: AVar a, vars: AVars a): AVars a = 
   List.filter (fn v -> v.1 ~= var_to_remove.1) vars

 op [a] insertVars (vars_to_add: AVars a, original_vars: AVars a): AVars a =
   foldl (fn (vars, new_var)       -> insertVar(new_var,       vars)) original_vars vars_to_add
 op [a] deleteVars (vars_to_remove: AVars a, original_vars: AVars a): AVars a =
   foldl (fn (vars, var_to_remove) -> deleteVar(var_to_remove, vars)) original_vars vars_to_remove

 %% Call with islcs? is you want to ignore the conditions of simple lambdas. E.g. fn (x | p x) -> ...
 op [a] freeVarsRec (M : ATerm a) (islcs?: Bool): AVars a =   
   case M of
     | Var    (v,      _) -> [v]

     | Apply  (M1, M2, _) -> insertVars (freeVarsRec M1 islcs?, freeVarsRec M2 islcs?)

     | Record (fields, _) -> freeVarsList fields islcs?

     | Fun    _           -> []

     %% This treats a singleton lambda specially because a singleton case should not be conditional
     %% Maybe there should be a flag for this case
     | Lambda ([(pat, cond, body)],   _) | islcs? -> deleteVars(patVars pat, insertVars(freeVarsRec cond islcs?, freeVarsRec body islcs?))

     | Lambda (rules,  _) -> foldl (fn (vars, rl) -> insertVars (freeVarsMatch rl islcs?, vars)) [] rules

     | Let (decls, M,  _) -> 
       let (pVars, tVars) =
           foldl (fn ((pVars, tVars), (pat, trm)) ->
                  let pvs = patVars pat in
                  let pbvs = deleteVars(pvs, freeVarsPat pat islcs?) in
		  (insertVars (pvs, pVars),
		   insertVars(pbvs, insertVars (freeVarsRec trm islcs?, tVars))))
	         ([], []) 
		 decls
       in
       let mVars = freeVarsRec M islcs? in
       insertVars (tVars, deleteVars (pVars, mVars))

     | LetRec (decls, M, _) -> 
       let pVars = List.map (fn (v, _) -> v) decls in
       let tVars = freeVarsList decls islcs? in
       let mVars = freeVarsRec M islcs? in
       deleteVars (pVars, insertVars (tVars, mVars))

     | Bind (_, vars, M, _) -> deleteVars (vars, freeVarsRec M islcs?)
     | The  (var,     M, _) -> deleteVar  (var,  freeVarsRec M islcs?)

     | IfThenElse (t1, t2, t3, _) -> 
       insertVars (freeVarsRec t1 islcs?, insertVars (freeVarsRec t2 islcs?, freeVarsRec t3 islcs?))

     | ApplyN(tms, _) -> foldl (fn (vars,tm) -> insertVars (freeVarsRec tm islcs?, vars)) [] tms

     | Seq (tms, _) -> foldl (fn (vars,tm) -> insertVars (freeVarsRec tm islcs?, vars)) [] tms

     | TypedTerm (tm, _, _) -> freeVarsRec tm islcs?

     | Pi (_, tm, _) -> freeVarsRec tm islcs?
     
     | And(tms, _) -> foldl (fn (vars,tm) -> insertVars (freeVarsRec tm islcs?, vars)) [] tms
     | _ -> []

 op  freeVarsList : [a, b] List(a * ATerm b) -> Bool -> AVars b
 def freeVarsList tms islcs? = 
   foldl (fn (vars,(_,tm)) -> insertVars (freeVarsRec tm islcs?, vars)) [] tms

 def freeVarsMatch (pat, cond, body) islcs? = 
   let pvars  = patVars     pat  in
   let cvars  = freeVarsPat pat islcs?  in
   let cvars1 = freeVarsRec cond islcs? in
   let bvars  = freeVarsRec body islcs? in
   deleteVars (pvars, insertVars(cvars1, insertVars (cvars, bvars)))

 op [a] patVars(pat: APattern a): AVars a = 
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
      | QuotientPat(p,_,_,_)     -> patVars p
      | RestrictedPat(p,_,_)   -> patVars p
      | TypedPat(p,_,_)        -> patVars p

 op [a] freeVarsPat(pat:APattern a) (islcs?: Bool): AVars a = 
   case pat
     of AliasPat(p1,p2,_)      -> insertVars (freeVarsPat p1 islcs?, freeVarsPat p2 islcs?)
      | VarPat(v,_)            -> []
      | EmbedPat(_,Some p,_,_) -> freeVarsPat p islcs?
      | EmbedPat _             -> []
      | RecordPat(fields,_)    -> foldl (fn (vars,(_,p)) -> insertVars (freeVarsPat p islcs?, vars)) [] fields
      | WildPat _              -> []
      | StringPat _            -> []
      | BoolPat _              -> []
      | CharPat _              -> []
      | NatPat  _              -> []
      | QuotientPat(p,_,_,_)   -> freeVarsPat p islcs?
      | RestrictedPat(p,t,_)   -> insertVars(freeVarsRec t islcs?, freeVarsPat p islcs?)
      | TypedPat(p,_,_)        -> freeVarsPat p islcs?

 op  getParams: MSPattern -> MSPatterns
 def getParams(pat:MSPattern) = 
   case pat
     of VarPat(v,_)-> [pat]
      | RecordPat(fields,_) ->
	if forall? (fn (_,VarPat _) -> true | (_,RecordPat _) -> true | _ -> false) fields
	  then map (fn (_,vpat) -> vpat) fields
	  else []
      | _ -> []

 op  lookup : [a,b] (a  -> Bool) * List(a * b) -> Option b 
 def lookup (desired_key?, association_list) = 
   case association_list of
    | [] -> None
    | (key,value) :: alist_tail -> 
      if desired_key?(key) then Some value else lookup(desired_key?, alist_tail)

 op tyVarsInTerm(tm: MSTerm): TyVars =
   let vars = mkRef [] in
   let def vr(ty) = 
         case ty of
	   | TyVar(tv,_) -> (vars := insert (tv,! vars); ())
	   | MetaTyVar(tv,pos) -> 
	     (case unlinkType ty of
	       | TyVar(tv,_) -> (vars := insert (tv,! vars); ())
	       | _ -> ())
	   | _ -> ()
   in
   let _ = appTerm(fn _ -> (),vr,fn _ -> ()) tm in
   ! vars


 op freeTyVars(ty: MSType): TyVars = 
   let vars = mkRef [] in
   let def vr(ty) = 
         case ty of
	   | TyVar(tv,_) -> (vars := insert (tv,! vars); ())
	   | MetaTyVar(tv,pos) -> 
	     (case unlinkType ty of
	       | TyVar(tv,_) -> (vars := insert (tv,! vars); ())
	       | _ -> ())
	   | _ -> ()
   in
   let _ = appType(fn _ -> (),vr,fn _ -> ()) ty in
   ! vars

op freeTyVarsInTerm(tm: MSTerm): TyVars = 
   let vars = mkRef [] in
   let def vr(ty) = 
         case ty of
	   | TyVar(tv,_) -> (vars := insert (tv,! vars); ())
	   | MetaTyVar(tv,pos) -> 
	     (case unlinkType ty of
	       | TyVar(tv,_) -> (vars := insert (tv,! vars); ())
	       | _ -> ())
	   | _ -> ()
   in
   let _ = appTerm(fn _ -> (),vr,fn _ -> ()) tm in
   ! vars

 op [a] boundVars(t: ATerm a): AVars a =
   case t of
     | Let(decls, _, _) -> flatten (map (fn (pat, _) -> patternVars pat) decls)
     | LetRec (decls, _, _) ->  map (fn (v, _) -> v) decls
     | Lambda (match, _) -> flatten (map (fn (pat,_,_) -> patternVars pat) match)
     | Bind (_, bound, _, _) -> bound
     | _ -> []

 op [a] boundVarsIn(t: ATerm a): AVars a =
   removeDuplicateVars(foldSubTerms (fn (t,r) -> boundVars t ++ r) [] t)

 op [a] boundVarNamesIn(t: ATerm a): List Id =
   varNames(boundVarsIn t)

 % This implementation of substitution 
 % completely ignores free variables in types.
 %
 % This is legal if indeed types do not have free variables,
 % which is a reasonable assumption given how Specware types
 % are handled.

 % FIXME: this isn't used, and can be replaced by instantiateTyVars,
 % below, anyway
 def substituteType(ty,S) = 
   let freeNames = foldr (fn ((v,trm),vs) -> 
                            StringSet.union (StringSet.fromList
						(List.map (fn (n,_) -> n)
						          (freeVars trm)),
						vs))
                     StringSet.empty S
   in 
   substituteType2(ty,S,freeNames) 

 def substituteType2(ty,S,freeNames) = 
   let def subst(s:MSType):MSType = 
	   case s of
             | Base(id,tys,a) | tys ~= [] -> Base(id, map subst tys, a)
             | Arrow(d,r,a) -> Arrow(subst d, subst r, a)
             | Product(fields,a) -> Product(List.map (fn (l,s) -> (l,subst s)) fields, a)
             | CoProduct(fields,a) -> CoProduct(List.map (fn (l,s) -> (l,mapOption subst s)) fields, a)
             | Subtype(s,p,a) -> Subtype(subst s, substitute2(p,S,freeNames), a)
             | Quotient(s,p,a) -> Quotient(subst s, substitute2(p,S,freeNames), a)
             | _ -> s
   in
   subst(ty) 

 op printVarSubst(sb: MSVarSubst): () =
   app (fn ((v,_),tm) -> writeLine (v^" |-> "^printTerm tm)) sb

 def substitute(M,sub) = 
   if empty? sub then M else
   let M_names = StringSet.fromList(varNames(freeVars M)) in
   let freeNames = foldr (fn ((v,trm),vs) -> 
                            StringSet.union (StringSet.fromList(varNames(freeVars trm)),
                                             vs)) 
                     M_names sub
   in 
   substitute2(M,sub,freeNames)
 
 op substitute2(M: MSTerm, sub: MSVarSubst, freeNames: StringSet.Set): MSTerm = 
   % let _ = writeLine("subst: "^printTerm M) in
   % let _ = writeLine "Map is " in
   % let _ = List.app (fn ((v,_),tm) -> writeLine (v^" |-> "^printTerm tm)) sub in	
   let
       def subst(M:MSTerm):MSTerm = 
         case M
	   of Var ((s,ty),a) -> 
	      (% writeLine ("Looking up "^s);
	       case lookup(fn (s2,_) -> s = s2,sub) 
		 of None   -> (%String.writeLine "not found"; 
			       M) 
		  | Some N -> (%String.writeLine "found "; 
			       N))
	    | Apply(M1,M2,a)  -> Apply(subst M1,subst M2, a) 
	    | Record(fields,a) -> Record(List.map (fn(f,M)-> (f,subst M)) fields, a)
            | Fun(f as Op _, ty, a) -> Fun(f, substituteType2(ty, sub, freeNames), a)
	    | Fun _         -> M 
	    | Lambda(rules,a)  -> Lambda(List.map substRule rules, a)
	    | Let(decls,M,a)  -> 
	      let decls = List.map (fn(p,M)-> (p,subst M)) decls in
	      let (decls,freeNames,sub) = List.foldr substLet ([],freeNames,sub) decls
	      in
	      Let(decls, substitute2(M,sub,freeNames), a)
	    | LetRec(decls,M,a) -> 
	      let (vars,sub,freeNames) = substBoundVars(List.map (fn(v,_) -> v) decls,sub,freeNames) 
	      in
	      let terms = List.map (fn (_,trm) -> substitute2(trm,sub,freeNames)) decls in
	      let decls = zip (vars,terms) in
	      LetRec(decls, substitute2(M,sub,freeNames), a)
	    | Bind(b,vars,M,a)  -> 
	      let (vars,sub,freeNames) = substBoundVars(vars,sub,freeNames) in
	      Bind(b, vars, substitute2(M,sub,freeNames), a)
	    | The(var,M,a)  -> 
	      let ([var],sub,freeNames) = substBoundVars([var],sub,freeNames) in
	      The (var, substitute2(M,sub,freeNames), a)
	    | IfThenElse(t1,t2,t3,a) -> IfThenElse(subst(t1), subst(t2), subst(t3), a)
	    | Seq(terms,a) -> Seq(map subst terms, a)
	    | ApplyN(terms,a) -> ApplyN(map subst terms, a)
	    | TypedTerm(term, ty, a) -> TypedTerm(subst(term), ty, a)
            | _ -> M

	def substRule (pat,cond,term) = 
	  let (pat,sub,freeNames) = substPattern(pat,sub,freeNames) in
	  % if empty? sub && freeNames = empty then
	  %   (pat, cond, term) 
	  % else
	    (pat, substitute2(cond,sub,freeNames), substitute2(term,sub,freeNames)) 

	def substLet ((pat,trm),(decls,freeNames,sub)) = 
	  let (pat,sub,freeNames) = substPattern(pat,sub,freeNames) in
	  (Cons((pat,trm),decls),
	   freeNames,
	   sub)
   in
   let M1 = subst(M) in
   (%String.writeLine ("Returning "^MetaSlangPrint.printTerm M1);
    M1)

 op substType2(ty: MSType, sub: MSVarSubst, freeNames: StringSet.Set): MSType =
   mapType (id, fn tyi -> case tyi of
                            | Subtype(s_tyi, pred, a) ->
                              Subtype(s_tyi, substitute2(pred, sub, freeNames), a)
                            | _ -> tyi,
            id)
     ty   

 def substBoundVars(vars, sub, freeNames) = 
   foldr (fn(v, (vars, sub, freeNames)) -> 
            let (v, sub, freeNames) = substBoundVar(v, sub, freeNames) in
            (v::vars, sub, freeNames))
     ([], sub, freeNames) vars
	
 def substBoundVar((id, ty), sub, freeNames) =
   let new_ty = substType2(ty, sub, freeNames) in
   let sub = deleteVarFromSub((id, ty), sub, []) in
   if StringSet.member(freeNames, id) then
     let id2 = StringUtilities.freshName(id, freeNames) in
     let sub2 = ((id, ty), mkVar(id2, new_ty)) :: sub in
     ((id2, new_ty), sub2, StringSet.add(freeNames, id2))
   else
     let sub2 = if equalType?(ty, new_ty) then sub
                 else ((id, ty), mkVar(id, new_ty)) :: sub in
     ((id, new_ty), sub2, freeNames)

 def deleteVarFromSub(v, sub, sub2) = 
   case sub
     of []          -> sub2
      | (w, M)::sub -> if v.1 = w.1
		      then sub ++ sub2
		      else deleteVarFromSub (v, sub, (w,M)::sub2)

 def substPattern(pat,sub,freeNames) = 
   case pat
     of VarPat(v,a) ->
        let (v,sub,freeNames) = substBoundVar(v,sub,freeNames) in
	(VarPat(v,a),sub,freeNames) 
      | RecordPat(fields,a) -> 
	let (fields,sub,freeNames) = 
	    List.foldr 
              (fn ((id,p),(fields,sub,freeNames)) -> 
	       let (p,sub,freeNames) = substPattern(p,sub,freeNames) in
	       (Cons((id,p),fields),sub,freeNames))
	      ([],sub,freeNames) fields
	in
	(RecordPat(fields,a),sub,freeNames)
      | EmbedPat(oper,Some pat,ty,a) -> 
	let (pat,sub,freeNames) = substPattern(pat,sub,freeNames) in
	(EmbedPat(oper,Some pat,ty,a),sub,freeNames)
      | EmbedPat(oper,None,ty,_) -> 
	(pat,sub,freeNames)
      | AliasPat(p1,p2,a) ->
	let (p1,sub,freeNames) = substPattern(p1,sub,freeNames) in
	let (p2,sub,freeNames) = substPattern(p2,sub,freeNames) in
	(AliasPat(p1,p2,a),sub,freeNames)
      | QuotientPat(pat,trm,tys,a) -> 
	let (pat,sub,freeNames) = substPattern(pat,sub,freeNames) in
	(QuotientPat(pat,trm,tys,a),sub,freeNames)
      | RestrictedPat(pat,trm,a) -> 
	let (pat,sub,freeNames) = substPattern(pat,sub,freeNames) in 
	(RestrictedPat(pat,substitute2(trm,sub,freeNames),a),sub,freeNames)
      | _ -> 
	(pat,sub,freeNames)

type VarPatSubst = List (MSVar * MSPattern)

op substPat(pat: MSPattern, sub: VarPatSubst): MSPattern = 
   case pat
     of VarPat(v,a) ->
        (case lookup(fn sv -> sv = v, sub) 
           of None   -> (%writeLine "not found"; 
                           pat) 
            | Some N -> (%writeLine "found "; 
                           N))
      | RecordPat(fields,a) -> 
	RecordPat(map (fn (id, p) -> (id, substPat(p,sub))) fields, a)
      | EmbedPat(oper,Some pat,ty,a) -> 
	let pat = substPat(pat,sub) in
	EmbedPat(oper,Some pat,ty,a)
      | AliasPat(p1,p2,a) ->
	let p1 = substPat(p1,sub) in
	let p2 = substPat(p2,sub) in
	AliasPat(p1,p2,a)
      | QuotientPat(pat,trm,tys,a) -> 
	let pat = substPat(pat,sub) in
	QuotientPat(pat,trm,tys,a)
      | RestrictedPat(pat,trm,a) -> 
	let pat = substPat(pat,sub) in 
	RestrictedPat(pat,trm,a)        % trm ??
      | _ -> pat

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
	    (fn((_,(Var(v,_)):MSTerm),(_,arg:MSTerm),assignments)->
	     (case arg
		of (Var(w,_)) -> if v = w 
                                 then assignments else
                		 Cons((mkVarPat v,arg),assignments)
		 | _ -> Cons((mkVarPat v,arg),assignments)))
	    [] (fields,fields2) 


 % Ensure that none of vs are used as bound variables in term. Also
 % removes any variable shadowing as a side effect.
 op renameBoundVars(term: MSTerm, vs: MSVars): MSTerm =
   let freeNames = StringSet.fromList(varNames vs) in
   substitute2(term,[],freeNames)

 op renameShadowedVars(term: MSTerm): MSTerm =
   renameBoundVars(term, freeVars term)

 op reverseSubst (v_subst: MSVarSubst) (t: MSTerm): MSTerm =
   case v_subst of
     | [] -> t
     | (v,vt)::_ | equalTerm?(vt,t) && ~(embed? Fun vt) -> mkVar v
     | _ :: r -> reverseSubst r t

 op invertSubst (tm: MSTerm, sbst: MSVarSubst): MSTerm =
   if sbst = [] then tm
     else mapTerm (reverseSubst sbst, id, id) tm

 %- --------------------------------------------------------------------------

 def report_unimplemented_for_cgen = false
 def externalopshfile(specname:String) = specname^"_extops.h"
 def cgeninfohead = ";;;CGEN-INFO "

 % ----------------------------------------------------------------------

 op mkConjecture(qid: QualifiedId, tvs: TyVars, fm: MSTerm): SpecElement =
   Property(Conjecture,qid,tvs,fm,noPos)

 op mkTheorem(qid: QualifiedId, tvs: TyVars, fm: MSTerm): SpecElement =
   Property(Theorem,qid,tvs,fm,noPos)

 op mkAxiom(qid: QualifiedId, tvs: TyVars, fm: MSTerm): SpecElement =
   Property(Axiom,qid,tvs,fm,noPos)

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

 op letRecToLetTermType: MSType -> MSType
 def letRecToLetTermType ty =
   case ty
     of Arrow(s1,s2,a)  -> 
        Arrow(letRecToLetTermType(s1),
	      letRecToLetTermType(s2),
	      a)
      | Product(fields,a) -> 
	Product(List.map (fn(id,s) -> (id, letRecToLetTermType(s))) fields,
		a)
      | CoProduct(fields,a) -> 
	CoProduct(List.map (fn (id,optty) ->
			    (id, case optty
				   of Some s -> Some(letRecToLetTermType(s))
				    | None  -> None)) 
		           fields,
		  a)
      | Quotient(ty,term,a) ->
	Quotient(letRecToLetTermType(ty),
		 letRecToLetTermTerm(term),
		 a)
      | Subtype(ty,term,a) ->
	Subtype(letRecToLetTermType(ty),
		letRecToLetTermTerm(term),
		a)
      | Base(qid,tys,a) -> 
	Base(qid,
	     List.map (fn(s) -> letRecToLetTermType(s)) tys,
	     a)
     %| Boolean is the same as default case
      | _ -> ty

 op letRecToLetTermTerm: MSTerm -> MSTerm
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
	    letRecToLetTermType(s),
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

 op letRecToLetTermVar: MSVar -> MSVar
 def letRecToLetTermVar ((id, ty)) = (id, letRecToLetTermType ty)

 op letRecToLetTermPattern: MSPattern -> MSPattern
 def letRecToLetTermPattern pat = 
   case pat
     of AliasPat(p1,p2,a) -> 
        AliasPat(letRecToLetTermPattern(p1),
		 letRecToLetTermPattern(p2),
		 a)
      | VarPat(v,a) -> 
	VarPat(letRecToLetTermVar(v),
	       a)
      | EmbedPat(id,optpat,ty,a) -> 
	EmbedPat(id,
		 case optpat
		   of  None   -> None
		    | Some p -> Some(letRecToLetTermPattern(p)),
		 letRecToLetTermType(ty),
		 a)
      | RecordPat(fields,a) -> 
	RecordPat(List.map (fn(id,p) -> (id,letRecToLetTermPattern(p))) fields,
		  a)
      | WildPat(ty,a) -> 
	WildPat(letRecToLetTermType(ty),
		a)
      | QuotientPat (p,                        qid, tys, a) -> 
	QuotientPat (letRecToLetTermPattern p, qid, tys, a)
      | RestrictedPat(p,t,a) -> 
	RestrictedPat(letRecToLetTermPattern(p),
		      letRecToLetTermTerm(t),
		      a)
      | _ -> pat

 op letRecToLetTermFun: MSFun -> MSFun
 def letRecToLetTermFun fun = fun

 op letRecToLetTermSpec: Spec -> Spec
 def letRecToLetTermSpec spc =
   let 
     def letRecToLetTermTypeInfo info =
       let pos = typeAnn info.dfn in
       let (old_decls, old_defs) = typeInfoDeclsAndDefs info in
       let new_defs = 
           map (fn ty ->
		let pos = typeAnn ty in
		let (tvs, ty) = unpackType ty in
		Pi (tvs, letRecToLetTermType ty, pos))
	       old_defs
       in
	 info << {dfn = maybeAndType (old_decls ++ new_defs, pos)}

     def letRecToLetTermOpInfo info = 
       let pos = termAnn info.dfn in
       let (old_decls, old_defs) = opInfoDeclsAndDefs info in
       let new_defs = 
           map (fn tm ->
		let pos = termAnn tm in
		let (tvs, ty, tm) = unpackFirstTerm tm in
		Pi (tvs, TypedTerm (tm, letRecToLetTermType ty, pos), pos))
	       old_defs
       in
	 info << {dfn = maybeAndTerm (old_decls ++ new_defs, pos)}

   in
   spc <<
   {types = mapTypeInfos letRecToLetTermTypeInfo spc.types,
    ops   = mapOpInfos   letRecToLetTermOpInfo   spc.ops}

 op  [a] patternVars  : APattern a -> AVars a
 def [a] patternVars(p) = 
     let
	def loopP(p:APattern a,vs) = 
	    case p
	      of VarPat(v,_) -> v :: vs
	       | RecordPat(fields,_) -> 
		 foldr (fn ((_,p),vs) -> loopP(p,vs)) vs fields
	       | EmbedPat(_,None,_,_) -> vs
	       | EmbedPat(_,Some p,_,_) -> loopP(p,vs)
	       | QuotientPat(p,_,_,_) -> loopP(p,vs)
	       | AliasPat(p1,p2,_) -> loopP(p1,loopP(p2,vs))
	       | RestrictedPat(p,_,_) -> loopP(p,vs)
               | TypedPat(p,_,_) -> loopP(p,vs)
	       | _ -> vs
     in
     loopP(p,[])

 op [a] patternVarsL (pats: List (APattern a)): AVars a =
   List.foldl (fn (pvs, pat) ->
            List.foldl (fn (pvs, v) -> if inVars?(v, pvs) then pvs else v :: pvs) pvs (patternVars pat))
     [] pats

 op  mkLetWithSubst: MSTerm * MSVarSubst -> MSTerm
 def mkLetWithSubst(tm,sb) =
   if sb = [] then tm
     else mkLet(map (fn (v,val) -> (mkVarPat v,val)) sb, tm)

 % FIXME: duplicate of negateTerm in MSTerm
 op negate (term: MSTerm): MSTerm =
   case term of
     | Fun (Bool b,_,aa) -> mkBool (~ b)
     | Apply (Fun(Not,_,_), p,                        _) -> p
     | Apply (Fun(Or,_,_),  Record([(_,M),(_,N)], _), _) ->
       mkAnd(negate M,negate N)
     | Apply(Fun(NotEquals,ty,a1),args,a2) ->
       Apply(Fun(Equals,ty,a1),args,a2)
     | _ -> mkNot term

 op mkIfThenElse(t1,t2:MSTerm,t3:MSTerm):MSTerm =
   case t1 of
     | Fun(Bool true,_,_)  -> t2
     | Fun(Bool false,_,_) -> t3
     | _ ->
   case t2 of
     | Fun(Bool true,_,_)  -> mkOr(t1,t3)
     %| Fun(Bool false,_,_) -> mkAnd(negate t1,t3)
     | _ ->
   case t3 of
     %| Fun(Bool true,_,_)  -> mkOr(negate t1,t2)
     | Fun(Bool false,_,_) -> mkAnd(t1,t2)
     | _ ->
   if equalTermAlpha?(t2, t3) && sideEffectFree t1 then t2
     else IfThenElse(t1,t2,t3,noPos)

 %% Utilities.mkOr, etc:

 op  mkOr: MSTerm * MSTerm -> MSTerm 
 def mkOr(t1,t2) =
   if boolVal? t1
     then (if boolVal t1 then trueTerm else reduceTerm1 t2)
    else if boolVal? t2
      then (if boolVal t2 && sideEffectFree t1 then trueTerm else reduceTerm1 t1)
    else if equalTermAlpha?(t1, negateTerm t2) && sideEffectFree t1 && sideEffectFree t2 then trueTerm
    else if equalTermAlpha?(t1, t2) then t2
         else MS.mkOr(t1,t2)

 op  mkAnd: MSTerm * MSTerm -> MSTerm 
 def mkAnd(t1,t2) =
   let t1_cjs = getConjuncts t1 in
   let t2_cjs = getConjuncts t2 in
   let t1_cjs = filter (fn cj -> ~(trueValTerm? cj || termIn?(t1, t2_cjs))) t1_cjs in
   let t2_cjs = filter (fn cj -> ~(trueValTerm? cj)) t2_cjs in
   let new_cjs = t1_cjs ++ t2_cjs in
   if exists? falseValTerm? new_cjs
     then falseTerm
     else if new_cjs = [] then trueTerm
            else foldr MS.mkAnd (reduceTerm1 (last new_cjs)) (butLast new_cjs)
 
 op  mkSimpConj: MSTerms -> MSTerm
 def mkSimpConj(cjs) =
  let cjs = foldl (fn (cjs, cj) -> if termIn?(cj, cjs) then cjs else cj::cjs) [] cjs in
  case reverse cjs
    of []     -> mkTrue()
     | [x]    -> x
     | x::rcs -> mkAnd (x, mkConj rcs)

 op  mkSimpOrs: MSTerms -> MSTerm
 def mkSimpOrs(cjs) =
  case cjs
    of []     -> mkTrue()
     | [x]    -> x
     | x::rcs ->
       if exists? (fn ti -> equalTermAlpha?(x,ti)) rcs
         then mkOrs rcs
       else mkOr (x, mkOrs rcs)

 op mkSimpBind: Binder * MSVars * MSTerm -> MSTerm
 def mkSimpBind(b, vars, term) =
   if vars = []
     then term
     else Bind(b,vars,term,noPos)

 op  mkSimpImplies: MSTerm * MSTerm -> MSTerm
 def mkSimpImplies (t1, t2) =
   if boolVal? t1
     then (if boolVal t1 then reduceTerm1 t2 else trueTerm)
   else if boolVal? t2
     then (if boolVal t2
             then (if sideEffectFree t1 then trueTerm else mkSeq[t1, trueTerm])
             else negate t1)
   else case t2 of
          | Apply(Fun (Implies, _, _), Record([(_,p1), (_,q1)], _), _) ->
            mkSimpImplies(mkAnd(t1,p1), q1)
          | _ ->
            let lhs_cjs = getConjuncts t1 in
            let sb = map (fn cji -> case cji of
                                      | Apply(Fun(Not,_,_), neg_cji, _) -> (neg_cji, falseTerm)
                                      | _ -> (cji, trueTerm))
                       lhs_cjs
            in
            let new_t2 = termSubst(t2, sb) in
            let new_t2 = if equalTermAlpha?(t2, new_t2) then new_t2 else reduceTerm1 new_t2 in
            if equalTerm?(new_t2, t2)
              then mkImplies (t1, new_t2)
            else mkSimpImplies (t1, new_t2)

 op  mkSimpIff: MSTerm * MSTerm -> MSTerm
 def mkSimpIff (t1, t2) =
   case t1 of
     | Fun(Bool true,_,_)  -> t2
     | Fun(Bool false,_,_) -> negateTerm(t2) %mkTrue() % was mkFalse() !!
     | _ -> 
       case t2 of
	 | Fun(Bool true,_,_)  -> t1
	 | Fun(Bool false,_,_) -> negateTerm(t1)
	 | _ -> mkIff (t1,t2)


  op mkOptLambda(pat: MSPattern, tm: MSTerm): MSTerm =
    case tm of
      | Apply(f,arg,_) ->
        (case patternToTerm pat of
           | Some pat_tm | equalTermAlpha?(pat_tm, arg) -> f
           | _ -> mkLambda(pat, tm))
      | _ -> mkLambda(pat, tm)

 op  identityFn?: [a] ATerm a -> Bool
 def identityFn? f =
   case f of
     | Lambda([(VarPat(x,_),_,Var(y,_))],_) -> x = y
     | _ -> false

 op [a] caseExpr?(t: ATerm a): Bool =
   case t of
     | Apply(Lambda _, _, _) -> true
     | _ -> false

 
 op [a] getConjuncts(t: ATerm a): List (ATerm a) =
   case t of
     | Apply(Fun(And,_,_), Record([("1",p),("2",q)],_),_)
       -> getConjuncts p ++ getConjuncts q
     | _ -> [t]

 op [a] conjunction?(t: ATerm a): Bool =
   case t of
     | Apply(Fun(And,_,_), _,_) -> true
     | _ -> false

 op [a] disjunction?(t: ATerm a): Bool =
   case t of
     | Apply(Fun(Or,_,_), _,_) -> true
     | _ -> false

 op [a] getDisjuncts(t: ATerm a): List (ATerm a) =
   case t of
     | Apply(Fun(Or,_,_), Record([("1",p),("2",q)],_),_)
       -> getDisjuncts p ++ getDisjuncts q
     | _ -> [t]

  op addVarNames(vs: MSVars, name_set: StringSet.Set): StringSet.Set =
    foldl (fn (name_set, (n,_)) -> StringSet.add(name_set, n)) name_set vs

  %% Given a universal quantification return list of quantified variables, conditions and rhs
  op  forallComponents: MSTerm -> MSVars * MSTerms * MSTerm
  def forallComponents t =
    % let _ = writeLine("forallComponents:\n"^printTerm t) in
    let def aux(t, sbst, freeNames) =
          case t of
            | Bind(Forall, vs, bod, _) ->
              let (vs, sbst, freeNames) = substBoundVars(vs, sbst, freeNames) in
              let freeNames =  addVarNames(vs, freeNames) in
              let (rVs, rLhsCjs, rRhs) = aux(bod, sbst, freeNames) in
              (vs ++ rVs,  rLhsCjs, rRhs)
            | Apply(Fun(Implies, _, _),
                    Record([("1", lhs), ("2", rhs)],_),_) ->
              let (rVs, rLhsCjs, rRhs) = aux(rhs, sbst, freeNames) in
              (rVs, getConjuncts(substitute(lhs, sbst)) ++ rLhsCjs, rRhs)
            | _ -> ([], [], substitute(t, sbst))
     in
     let freeNames = StringSet.fromList(varNames(freeVars t)) in
     let result as (vs, condns, bod) = aux(t, [], freeNames) in
     % let _ = writeLine("Vars: "^ anyToString(map (fn (x,_) -> x) vs)) in
     % let _ = writeLine("Conds: "^foldl (fn (s,t) -> s ^" "^printTerm t) "" condns) in
     result

 op traceRemoveExcessAssumptions?: Bool = false

 op removeExcessAssumptions (t: MSTerm): MSTerm =
   let (vs, cjs, bod) = forallComponents t in
   let def findDepCjs(lvs, cjs, dep_cjs) =
         let n_dep_cjs = filter (fn cj -> hasRefTo?(cj, lvs)) cjs in
         let n_lvs = foldl (fn (lvs, cj) -> insertVars(freeVars cj, lvs)) lvs n_dep_cjs in
         let n_dep_cjs = n_dep_cjs ++ dep_cjs in
         if length n_lvs = length lvs
           then (lvs, n_dep_cjs)
           else findDepCjs(n_lvs, filter (fn cj -> ~(termIn?(cj, n_dep_cjs))) cjs, n_dep_cjs)
   in
   let (r_vs, r_cjs) = findDepCjs(freeVars bod, cjs, []) in
   if length vs ~= length r_vs || length cjs ~= length r_cjs
     then let new_t = mkSimpBind(Forall, r_vs, mkSimpImplies(mkSimpConj r_cjs, bod)) in
          let _ = if traceRemoveExcessAssumptions?
                    then writeLine(printTerm t^"\n --->\n"^printTerm new_t) else ()
          in
          new_t
     else t

  %% Given an existential quantification return list of quantified variables and conjuncts
  op  existsComponents: MSTerm -> MSVars * MSTerms
  def existsComponents t =
    let def aux(t, sbst, freeNames) =
          case t of
            | Bind(Exists,vs,bod,_) ->
              let (vs, sbst, freeNames) = substBoundVars(vs, sbst, freeNames) in
              let freeNames =  addVarNames(vs, freeNames) in
              let (rVs,rLhsCjs) = aux(bod, sbst, freeNames) in
              (vs ++ rVs,rLhsCjs)
            | Apply(Fun(And,_,_), Record([("1",lhs),("2",rhs)],_),_) ->
              let (lVs,lLhsCjs) = aux(lhs, sbst, freeNames) in
              let (rVs,rLhsCjs) = aux(rhs, sbst, freeNames) in
              (lVs ++ rVs,lLhsCjs ++ rLhsCjs)
            | _ -> ([],[substitute(t, sbst)])
    in
    let freeNames = StringSet.fromList(varNames(freeVars t)) in
    aux(t, [], freeNames)

  %% Given an existential (one) quantification return list of quantified variables and conjuncts
  op  exists1Components: MSTerm -> MSVars * MSTerms
  def exists1Components t =
    let def aux(t, sbst, freeNames) =
          case t of
            | Bind(Exists1,vs,bod,_) ->
              let (vs, sbst, freeNames) = substBoundVars(vs, sbst, freeNames) in
              let freeNames =  addVarNames(vs, freeNames) in
              let (rVs,rLhsCjs) = aux(bod, sbst, freeNames) in
              (vs ++ rVs,rLhsCjs)
            | Apply(Fun(And,_,_), Record([("1",lhs),("2",rhs)],_),_) ->
              let (lVs,lLhsCjs) = aux(lhs, sbst, freeNames) in
              let (rVs,rLhsCjs) = aux(rhs, sbst, freeNames) in
              (lVs ++ rVs,lLhsCjs ++ rLhsCjs)
            | _ -> ([],[substitute(t, sbst)])
    in
    let freeNames = StringSet.fromList(varNames(freeVars t)) in
    aux(t, [], freeNames)

  op  varTerm?: [a] ATerm a -> Bool
  def varTerm? t =
    case t of
      | Var _ -> true
      | _     -> false


  op [a] constantTerm? (t: ATerm a): Bool =
    case t of
      | Lambda    _           -> true
      | Fun       _           -> true
      | Record    (fields, _) -> forall? (fn (_,stm) -> constantTerm? stm) fields
      | TypedTerm (tm, _,  _) -> constantTerm? tm
      | Pi        (_, tm,  _) -> constantTerm? tm
      | And       (tm::_,  _) -> constantTerm? tm
      | _                     -> false

  op [a] containsOpRef?(term: ATerm a): Bool =
    existsSubTerm (fn t -> case t of
                             | Fun(Op _,_,_) -> true
                             | _ -> false)
      term

  op [a] containsRefToOp?(term: ATerm a, qid: QualifiedId): Bool =
    existsSubTerm (fn t -> case t of
                             | Fun(Op(qid1,_),_,_) -> qid = qid1
                             | _ -> false)
      term

  op [a] containsRefToOps?(term: ATerm a, qids: QualifiedIds): Bool =
    existsSubTerm (fn t -> case t of
                             | Fun(Op(qid1,_),_,_) -> qid1 in? qids
                             | _ -> false)
      term

  op [a] containsRefToType?(term: ATerm a, qid: QualifiedId): Bool =
    qid in? typesInTerm term

  op [a] opsInTerm(tm: ATerm a): QualifiedIds =
    foldTerm (fn opids -> fn t ->
                case t of
                  | Fun(Op(qid,_),_,_) | qid nin? opids ->
                    Cons(qid, opids)
                  | _ -> opids,
              fn result -> fn _ -> result,
              fn result -> fn _ -> result)
      [] tm

  op [a] opsInType(ty: AType a): QualifiedIds =
    foldType (fn result -> fn t ->
                case t of
                  | Fun(Op(qid,_),_,_) | qid nin? result -> qid::result
                  | _ -> result,
              fn result -> fn _ -> result,
              fn result -> fn _ -> result)

      [] ty

  op [a] typesInTerm(tm: ATerm a): QualifiedIds =
    foldTerm (fn result -> fn _ -> result,
              fn result -> fn t ->
                case t of
                  | Base(qid,_,_) | qid nin? result -> qid::result
                  | _ -> result,
              fn result -> fn _ -> result)

      [] tm

  op [a] typesInType(ty: AType a): QualifiedIds =
    foldType (fn result -> fn _ -> result,
              fn result -> fn t ->
                case t of
                  | Base(qid,_,_) | qid nin? result -> qid::result
                  | _ -> result,
              fn result -> fn _ -> result)

      [] ty

  op typeQIdUsedToDefineType?(qid: QualifiedId, ty: MSType, spc: Spec): Bool =
    let def aux(ty: MSType, seenTypeQIds: QualifiedIds) =
          existsInType? (fn tyi ->
                           case tyi
                             | Base(qidi, _, _) ->
                               qid = qidi || (qidi nin? seenTypeQIds
                                                && (case findTheType(spc, qidi)
                                                     | None -> false
                                                     | Some info -> aux(info.dfn, qidi::seenTypeQIds)))
                             | _ -> false)
            ty
    in
    aux(ty, [])

  op opsInOpDefFor(op_id: QualifiedId, spc: Spec): QualifiedIds =
    case findTheOp(spc, op_id) of
      | Some info -> opsInTerm info.dfn
      | None -> []

  op typesInTypeDefFor(ty_id: QualifiedId, spc: Spec): QualifiedIds =
    case findTheType(spc, ty_id) of
      | Some info -> typesInType info.dfn
      | None -> []

  op opsInSubTerms(tm: MSTerm): QualifiedIds =
    foldSubTerms (fn (t, opids) ->
                    case t of
                      | Fun(Op(qid,_),_,_) | qid nin? opids ->
                        qid :: opids
                      | _ -> opids)
      [] tm


  op  lambda?: [a] ATerm a -> Bool
  def lambda? t =
    case t of
      | Lambda _ -> true
      | _ -> false

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

 op  natVal: MSTerm -> Nat
 def natVal = fn (Fun(Nat i,_,_)) -> i
 op  natVals: List(Id * MSTerm) -> List Nat
 def natVals = map (fn (_,t) -> natVal t)

 op  charVal: MSTerm -> Char
 def charVal = fn (Fun(Char c,_,_)) -> c
 op  charVals: List(Id * MSTerm) -> List Char
 def charVals = map (fn (_,t) -> charVal t)

 op  stringVal: MSTerm -> String
 def stringVal = fn (Fun(String s,_,_)) -> s
 op  stringVals: List(Id * MSTerm) -> List String
 def stringVals = map (fn (_,t) -> stringVal t)

 op boolVal?(t: MSTerm): Bool =
   case t of
     | Fun(Bool _,_,_) -> true
     | Apply(Fun(Not, _, _), x, _) -> boolVal? x
     | Apply(Fun(And, _, _), Record([("1",p),("2",q)],_), _) -> boolVal? p && boolVal? q
     | Apply(Fun(Or, _, _), Record([("1",p),("2",q)],_), _) -> boolVal? p && boolVal? q
     | Apply(Fun(Implies, _, _), Record([("1",p),("2",q)],_), _) -> boolVal? p && boolVal? q
     | Apply(Fun(Iff, _, _), Record([("1",p),("2",q)],_), _) -> boolVal? p && boolVal? q
     | _ -> false

 op boolVal(t: MSTerm | boolVal? t): Bool =
   case t of
   | Fun(Bool val,_,_) -> val
   | Apply(Fun(Not, _, _), x, _) -> ~(boolVal x)
   | Apply(Fun(And, _, _), Record([("1",p),("2",q)],_), _) -> boolVal p && boolVal q
   | Apply(Fun(Or, _, _), Record([("1",p),("2",q)],_), _)  -> boolVal p || boolVal q
   | Apply(Fun(Implies, _, _), Record([("1",p),("2",q)],_), _) -> boolVal p => boolVal q
   | Apply(Fun(Iff, _, _), Record([("1",p),("2",q)],_), _) -> boolVal p = boolVal q
   %| _ -> false

 op trueValTerm?(t: MSTerm): Bool =
   boolVal? t && boolVal t
 op falseValTerm?(t: MSTerm): Bool =
   boolVal? t && ~(boolVal t)

 op  boolVals: List(Id * MSTerm) -> List Bool
 def boolVals = map (fn (_,t) -> boolVal t)


 op  typeFromField: List(Id * MSTerm) * MSType -> MSType
 def typeFromField(fields,defaultS) =
   case fields
     of (_,Fun(_,s,_)) :: _ -> s
      | _ -> defaultS

 def typeFromArg(arg: MSTerm,defaultS:MSType): MSType =
   case arg
     of Fun(_,s,_) -> s
      | _ -> defaultS

  op knownSideEffectFreeQualifiers: List Qualifier =
    ["Integer", "Nat", "Bool", "Char", "String", "Option", "Function", "List"]

  op  knownSideEffectFreeQIds: List(Qualifier * Id)
  def knownSideEffectFreeQIds =
    [("Integer",    "~"),  % TODO: deprecate
     ("IntegerAux", "-"),
     ("Integer",    "+"),
     ("Nat",        "+"),
     ("Integer",    "<"),
     ("Integer",    ">"),
     ("Integer",    "<="),
     ("Integer",    ">="),
     ("Integer",    "-"),
     ("Integer",    "div"),
     ("Integer",    "rem"),
     ("Integer",    "abs"),
     ("Integer",    "min"),
     ("Integer",    "max"),
     ("Integer",    "compare"),
     ("List",       "length")]

   op knownSideEffectFreeFns: List String =
    ["toString", "return"]

  op  knownSideEffectFreeFn?: MSFun -> Bool
  def knownSideEffectFreeFn? f =
    case f of
      | Op(Qualified(qid),_) ->
        qid.1 in? knownSideEffectFreeQualifiers
          || qid in? knownSideEffectFreeQIds
          || qid.2 in? knownSideEffectFreeFns
      % Not, And, Or, Implies, Iff, Equals, NotEquals -> true
      | _ -> true

 op assumeNoSideEffects?: Bool = false

 op assumingNoSideEffects: [a] a -> a

 op  sideEffectFree: MSTerm -> Bool
 def sideEffectFree(term) =
   assumeNoSideEffects? ||
     (case term
       of Var _ -> true
	| Record(fields,_) -> forall? (fn(_,t)-> sideEffectFree t) fields
	| Apply(Fun(f,_,_),t,_) -> knownSideEffectFreeFn? f && sideEffectFree t
        | Fun(Op(Qualified("Global", _), _),_,_) -> false
	| Fun _ -> true
	| IfThenElse(t1,t2,t3,_) -> 
		(sideEffectFree t1) 
	      && (sideEffectFree t2) 
	      && (sideEffectFree t3)
        | Bind _ -> true
	| _ -> false)

 op hasSideEffect?(term: MSTerm): Bool =
   existsSubTerm (fn s_tm ->
                    case s_tm of
                      | Fun(Op(Qualified("System", _), _), _, _) -> true
                      | _ -> false)
     term

 op  evalBinary: [a] (a * a -> MSFun) * (List(Id * MSTerm) -> List a)
                      * List(Id * MSTerm) * MSType
                     -> Option MSTerm
 def evalBinary(f, fVals, fields, ty) =
   case fVals fields
     of [i,j] -> Some(Fun(f(i,j),ty,noPos))
      | _ -> None

 op  evalBinaryNotZero: (Nat * Nat -> MSFun) * (List(Id * MSTerm) -> List Nat)
                      * List(Id * MSTerm) * MSType
                     -> Option MSTerm
 def evalBinaryNotZero(f, fVals, fields, ty) =
   case fVals fields
     of [i,j] ->
        if j=0 then None
	  else Some(Fun(f(i,j),ty,noPos))
      | _ -> None

 op nat:  [a] (a -> Nat)    -> a -> MSFun
 op char: [a] (a -> Char)   -> a -> MSFun
 op str:  [a] (a -> String) -> a -> MSFun
 op bool: [a] (a -> Bool)   -> a -> MSFun
 def nat  f x = Nat    (f x)
 def char f x = Char   (f x)
 def str  f x = String (f x)
 def bool f x = Bool   (f x)

 op  attemptEval1: String * MSTerm -> Option MSTerm
 def attemptEval1(opName,arg) =
   case (opName,arg) of
      | ("~", Fun (Nat i,_,aa)) -> Some(Fun (Nat (- i), natType,aa))
      | ("~", Fun (Bool b,_,aa)) -> Some(Fun (Bool (~b), boolType,aa))
      | ("pred", Fun (Nat i,_,aa)) -> Some(Fun (Nat (pred i), natType,aa))
      | ("toString", Fun (Nat i,_,aa)) -> Some (Fun (String (show i), stringType,aa))
      | ("succ",Fun (Nat i,_,aa)) -> Some(Fun (Nat (succ i), natType,aa))

      | ("length",Fun (String s,_,aa)) -> Some(Fun (Nat(length s),natType,aa))
      | ("stringToInt",Fun (String s,_,aa)) -> Some(Fun (Nat (stringToInt s),natType,aa))

      | ("isUpperCase",Fun (Char c,_,aa)) ->
          Some(Fun (Bool(isUpperCase c),boolType,aa))
      | ("isLowerCase",Fun (Char c,_,aa)) ->
          Some(Fun (Bool(isLowerCase c),boolType,aa))
      | ("isAlphaNum",Fun (Char c,_,aa)) ->
          Some(Fun(Bool(isAlphaNum c),boolType,aa))
      | ("isAlpha",Fun (Char c,_,aa)) -> Some(Fun (Bool(isAlpha c),boolType,aa))
      | ("isNum",Fun (Char c,_,aa)) -> Some(Fun (Bool(isNum c),boolType,aa))
      | ("isAscii",Fun (Char c,_,aa)) -> Some(Fun (Bool(isAscii c),boolType,aa))
      | ("toUpperCase",Fun (Char c,_,aa)) ->
          Some(Fun (Char(toUpperCase c),charType,aa))
      | ("toLowerCase",Fun (Char c,_,aa)) ->
          Some(Fun (Char(toLowerCase c),charType,aa))
      | ("ord",Fun (Char c,_,aa)) -> Some(Fun (Nat(ord c),natType,aa))
      | ("chr",Fun (Nat i,_,aa)) -> Some(Fun (Char(chr i),charType,aa))
      | _ -> None

 op  attemptEvaln: String * String * List(Id * MSTerm) ->  Option MSTerm
 def attemptEvaln(spName,opName,fields) =
   case opName of
      %% Nat operations
      | "+" ->
        Some(Fun(Nat((foldl +) 0 (natVals fields)),
		 typeFromField(fields,natType),noPos))
      | "*" ->
        Some(Fun(Nat((foldl * ) 1 (natVals fields)),
		 typeFromField(fields,natType),noPos))
      | "-"   -> evalBinary(nat -,natVals,fields,
			    typeFromField(fields,natType))
      | "<"   -> if spName = "String"
	          then evalBinary(bool <,stringVals,fields,boolType)
		  else evalBinary(bool <,natVals,fields,boolType)
      | "<="  -> if spName = "String"
	          then evalBinary(bool <=,stringVals,fields,boolType)
		  else evalBinary(bool <=,natVals,fields,boolType)
      | ">"   -> if spName = "String"
	          then evalBinary(bool >,stringVals,fields,boolType)
		  else evalBinary(bool >,natVals,fields,boolType)
      | ">="  -> if spName = "String"
	          then evalBinary(bool >=,stringVals,fields,boolType)
		  else evalBinary(bool >=,natVals,fields,boolType)
      | "min" -> evalBinary(nat min,natVals,fields,
			    typeFromField(fields,natType))
      | "max" -> evalBinary(nat max,natVals,fields,
			    typeFromField(fields,natType))
      | "modT" -> evalBinaryNotZero(nat modT,natVals,fields,natType)
      | "divE" -> evalBinaryNotZero(nat divE,natVals,fields,natType)

      %% string operations
      | "concat" -> evalBinary(str ^,stringVals,fields,stringType)
      | "++"  -> evalBinary(str ^,stringVals,fields,stringType)
      | "^"   -> evalBinary(str ^,stringVals,fields,stringType)
      | "substring" ->
	(case fields
	   of [(_,s),(_,i),(_,j)] ->
	      let sv = stringVal s in
	      let iv = natVal i in
	      let jv = natVal j in
	      if iv <= jv && jv <= length sv
		then Some(Fun(String(subFromTo(sv,iv,jv)),
			      stringType,noPos))
		else None
	    | _ -> None)
      | "leq" -> evalBinary(bool <=,stringVals,fields,boolType)
      | "lt"  -> evalBinary(bool <,stringVals,fields,boolType)

      | _ -> None

 op  attemptEval: Spec -> MSTerm -> MSTerm
 def attemptEval spc t = mapSubTerms (attemptEvalOne spc) t

 op  attemptEvalOne: Spec -> MSTerm -> MSTerm
 def attemptEvalOne spc t =
   case tryEvalOne spc t of
     | Some t1 -> t1
     | None    -> t

 op makeEquality (spc: Spec) (t1 : MSTerm, t2 : MSTerm) : MSTerm =
   mkEquality(inferType(spc, t1), t1, t2)

 op reduceEqual(t1: MSTerm, t2: MSTerm, eq?: Bool, spc: Spec): Option(MSTerm) =
   case (t1, t2) of
     | (Apply(Fun(Embed(id1, true), _, _), st1, _), Apply(Fun(Embed(id2, true), _, _), st2, _)) ->
       Some(if id1 = id2
              then if eq? then mkEquality(inferType(spc, st1), st1, st2)
                    else mkNotEquality(inferType(spc, st1), st1, st2)
              else mkBool(~eq?))
     | (Apply(Fun(Embed(_, true), _, _), st1, _), Fun(Embed(_, false), _, _)) ->
       Some(mkBool(~eq?))
     | (Fun(Embed(_, false), _, _), Apply(Fun(Embed(_, true), _, _), st1, _)) ->
       Some(mkBool(~eq?))
     %%  (x1, .., xn) = (y1, .., yn) --> x1 = y1 && .. && xn = yn
     | (Record(xs, _), Record(ys,_)) ->
       Some(mkSimpConj(map (fn ((_,xi), (_,yi)) -> mkEquality(inferType(spc, xi), xi, yi)) (zip(xs, ys))))
     | _ -> None

  op  fieldAcessTerm: MSTerm * String * Spec -> MSTerm
  def fieldAcessTerm(t,field,spc) =
    case t of
      | Record(fields,_) ->
	(case getField(fields,field) of
	  | Some fld -> fld
	  | _ -> mkProjection(field,t,spc))	% Shouldn't happen
      | _ -> mkProjection(field,t,spc)

  op  mkProjection  : Id * MSTerm * Spec -> MSTerm
  def mkProjection (id, term, spc) = 
    let super_type = termType(term) in
    case productOpt(spc,super_type) of
     | Some (fields) -> 
       (case findLeftmost (fn (id2, _) -> id = id2) fields of
	 | Some (_,sub_type) -> 
	   mkApply (mkProject (id, super_type, sub_type),term)
	 | _ -> System.fail ("Projection index "^id^" not found in product with fields "
                             ^(foldl (fn (res,(id2, _)) -> res^id2^" ") "" fields)
                             ^"at "^print(termAnn term)))
     | _ -> System.fail("Product type expected for mkProjectTerm: "^printTermWithTypes term)

  op projectionFun(f: MSFun, spc: Spec): Option Id =
    case f of
      | Project id -> Some id
      | Op(qid, _) ->
        (case findTheOp(spc, qid) of
           | None -> None
           | Some info ->
             let (_, ty, tm) = unpackFirstTerm info.dfn in
             case tm of
               | Fun(f, _, _) -> projectionFun(f, spc)
               | Lambda([(VarPat((v, _), _),_, Apply(Fun(f, _, _), Var((vr,_), _), _))], _) | v = vr ->
                 projectionFun(f, spc)
               | _ -> None)
      | _ -> None

  op projectionFun?(f: MSFun, spc: Spec): Bool =
    some?(projectionFun(f, spc))

  op projection?(e: MSTerm, spc: Spec): Bool =
    case e 
      | Apply(Fun(f,_,_), _, _) -> projectionFun?(f, spc)
      | _ -> false


%%  moved to RecordMerge.sw
%%
%% op  translateRecordMergeInSpec : Spec -> Spec
%% def translateRecordMergeInSpec spc =
%%   mapSpec (translateRecordMerge spc,id,id) spc
%%
%% op makeTupleUpdate?: Bool = true
%%
%% op makeRecordMerge (spc: Spec) (tm: MSTerm): MSTerm =
%%   case tm of
%%     | Record(fields as (id0, _) :: _, a) | id0 ~= "1" || makeTupleUpdate? ->
%%       (case maybeTermType tm of
%%          | None -> tm
%%          | Some rec_ty ->
%%        let (src_tms, new_fields) =
%%            foldr (fn ((id1, t), (src_tms, new_fields)) ->
%%                     case t of
%%                       | Apply(Fun(Project id2, _, _), src_tm, _)
%%                           | id1 = id2 && equivTypeSubType? spc (termType src_tm, rec_ty) true ->
%%                         (if termIn?(src_tm, src_tms) then src_tms else src_tm :: src_tms,
%%                          new_fields)
%%                       | _ -> (src_tms, (id1, t):: new_fields))
%%              ([], []) fields
%%        in
%%        (case src_tms of
%%         | [src_tm] ->
%%           if new_fields = [] then src_tm
%%             else mkRecordMerge(src_tm, mkRecord new_fields)
%%         | _ -> tm))
%%     | _ -> tm

 op translateRecordMerge (spc : Spec) (term : MSTerm) : MSTerm =
   translateRecordMerge1 spc true term

 op translateRecordMerge1 (spc : Spec) (intro_vars?: Bool) (term : MSTerm) : MSTerm =
  %% used by tryEvalOne, otherwise would move to RecordMerge.sw
  case term of
    | Apply (Fun (RecordMerge, typ, _), 
             Record ([("1",t1),("2",t2)], _), 
             _)
      ->
      (case arrowOpt (spc, typ) of
         | Some (dom, rng) ->
           (case (productOpt (spc, rng), productOpt (spc, inferType (spc, t2))) of
              | (Some resultFields, Some t2Fields) ->
                let rawResult = Record (map (fn (field,_) ->
                                               (field, 
                                                if exists? (fn (f,_) -> f = field) t2Fields then
                                                  fieldAcessTerm (t2, field, spc)
                                                else 
                                                  fieldAcessTerm (t1, field, spc)))
                                            resultFields,
                                        noPos)
                in
                if intro_vars?
                  then maybeIntroduceVarsForTerms (rawResult, [t1, t2], spc)
                else rawResult
              | _ -> term)
         | _ -> term)
    | _ -> term

 op maybeIntroduceVarsForTerms (mainTerm : MSTerm, 
                                vterms   : MSTerms, 
                                spc      : Spec) 
  : MSTerm =
  %% Introduces variables for vterms if they occur in mainTerm and they are non-trivial
  case filter (fn tm -> ~(simpleTerm tm) && (existsSubTerm (fn subtm -> subtm = tm) mainTerm)) vterms of
    | [] -> mainTerm
    | rvterms ->
      let (_,vbinds) =
          foldl (fn ((i, result), tm) -> 
                   (i+1,
                    result ++ [(tm, 
                                "tmp__" ^ show i, 
                                inferType (spc, tm))]))
                (0, []) 
                rvterms
      in
      let bindings = map (fn (tm,v,s) -> (mkVarPat (v,s),tm)) vbinds in
      let tsp = ((fn t -> 
                    case findLeftmost (fn (tm,_,_) -> t = tm) vbinds of
                      | Some(_,v,s) -> mkVar(v,s)
                      | None -> t),
                 id,
                 id)
      in
      let body = mapTerm tsp mainTerm in
      mkLet (bindings, body)

 op  tryEvalOne: Spec -> MSTerm -> Option MSTerm
 def tryEvalOne spc term =
   if boolVal? term
     then if embed? Fun term then None  % Already ground
           else Some(mkBool(boolVal term))
   else
   case term
     of Apply(Fun(Op(Qualified(spName,opName),_),s,_),arg,_) ->
        (if spName in? evalSpecNames
	 then (case arg
		 of Record(fields, _) ->
		    (if forall? (fn (_,tm) -> evalConstant?(tm)) fields
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
          (let eq? = equivTerm? spc (N1,N2) in % equalTerm? would reject 0:Nat = 0:Int
             if eq? || (~(containsOpRef? N1) && ~(containsOpRef? N2))
               then Some(mkBool eq?)
             else None)
        else reduceEqual(N1,N2,true,spc)
      | Apply(Fun(NotEquals,_,_),Record([(_,N1),(_,N2)], _),_) ->
	if evalConstant?(N1) && evalConstant?(N2) then
          %% CAREFUL: if N1 and N2 are equivalent, we can simplify to false,
          %%          but otherwise we cannot act, since they might be ops later equated to each other
          (let eq? = equivTerm? spc (N1,N2) in  % equalTerm? would reject 0:Nat = 0:Int
             if eq? || (~(containsOpRef? N1) && ~(containsOpRef? N2))
               then Some(mkBool(~eq?))
           else
             None)
        else reduceEqual(N1,N2,false,spc)
      | Apply(Fun(Not,  _,_),arg,_) -> 
	(case arg of
           | Fun (Bool b,_,aa) -> Some(mkBool (~ b))
           | Apply (Fun(Not,_,_), p,_) -> Some p
           | Apply(Fun(NotEquals,ty,a1),args,a2) ->
             Some(Apply(Fun(Equals,ty,a1),args,a2))
           | _ -> None)
      | Apply(Fun(And,  _,_),Record(fields as [(_,N1),(_,N2)], _),_) ->
        if boolVal? N1 || boolVal? N2 then Some (mkAnd(N1,N2)) else None
      | Apply(Fun(Or,   _,_),Record(fields as [(_,N1),(_,N2)], _),_) -> 
        if boolVal? N1 || boolVal? N2 then Some (mkOr(N1,N2)) else None
      | Apply(Fun(Implies, _,_),Record(fields as [(_,N1),(_,N2)], _),_) ->
        if boolVal? N1 || (boolVal? N2 && sideEffectFree N1) then Some (mkSimpImplies(N1,N2))
        else if equalTermAlpha?(N1,N2) && sideEffectFree N1
          then Some trueTerm else None
      | Apply(Fun(Iff, _,_),Record(fields as [(_,N1),(_,N2)], _),_) -> 
	if boolVal? N1 || boolVal? N2 then Some (mkSimpIff(N1,N2)) else None
      | IfThenElse(p,q,r,_) ->
        let simp_if = mkIfThenElse(p,q,r) in
        if equalTermAlpha?(term, simp_if) then None else Some simp_if
        %% {id1 = v1, ..., idn = vn}.idi = vi
      | Apply(Fun(Project i,_,_),Record(m,_),_) ->
        (case getField(m,i) of
           | Some fld -> Some fld
           | None -> None)
        %% (x << {i = v}).j  -->  x.j  (x << {i = v}).i  -->  v
      | Apply(proj_fn as Fun(Project i,_,_), Apply(Fun(RecordMerge, _, _), Record([(_,r1), (_,Record(m,_))], _),_),_) ->
        (case getField(m,i) of
           | Some fld -> Some fld
           | None -> tryEvalOne spc (mkApply(proj_fn, r1)))
      | Apply(Fun(RecordMerge,s,_),Record([("1", Record _),("2", Record _)],_),_) ->
        Some (translateRecordMerge spc term)
      | Fun(Op(Qualified ("Integer", "zero"),_),_,a) -> Some(mkFun(Nat 0, intType))
        %% let pat = e in bod --> bod  if variables in pat don't occur in bod
      | Let([(pat, tm)], bod, _) | sideEffectFree tm && disjointVars?(patternVars pat, freeVars bod) ->
        Some bod
      | Bind(_, vs, Fun (Bool false,_,_), _) -> Some falseTerm
      | Bind(_, vs, Fun (Bool true,_,_), _) | forall? (fn (_,tyi) -> knownNonEmpty?(tyi, spc)) vs -> Some trueTerm
      | Apply(Fun(Embedded(qid1), ty1, _), arg, _) ->
        (case constructorTerm spc arg
           | Some(qid2, _) -> Some(mkBool(qid1 = qid2))
           | _ -> None)
      | _ -> None

 op tryEval1(term: MSTerm): Option MSTerm =
    case term
     of Apply(Fun(Op(Qualified(spName,opName),_),s,_),arg,_) ->
        (if spName in? evalSpecNames
	 then (case arg
		 of Record(fields, _) ->
		    (if forall? (fn (_,tm) -> evalConstant?(tm)) fields
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
          (let eq? = equalTermAlpha?(N1,N2) in
             if eq? || (~(containsOpRef? N1) && ~(containsOpRef? N2))
               then Some(mkBool eq?)
             else None)
        else None
      | Apply(Fun(NotEquals,_,_),Record([(_,N1),(_,N2)], _),_) ->
	if evalConstant?(N1) && evalConstant?(N2) then
          %% CAREFUL: if N1 and N2 are equivalent, we can simplify to false,
          %%          but otherwise we cannot act, since they might be ops later equated to each other
          (let eq? = equalTermAlpha? (N1,N2) in
             if eq? || (~(containsOpRef? N1) && ~(containsOpRef? N2))
               then Some(mkBool(~eq?))
           else
             None)
        else None
      | Apply(Fun(Not,  _,_),arg,_) -> 
	(case arg of
           | Fun (Bool b,_,aa) -> Some(mkBool (~ b))
           | Apply (Fun(Not,_,_), p,_) -> Some p
           | Apply(Fun(NotEquals,ty,a1),args,a2) ->
             Some(Apply(Fun(Equals,ty,a1),args,a2))
           | _ -> None)
      | Apply(Fun(And,  _,_),Record(fields as [(_,N1),(_,N2)], _),_) ->
        if boolVal? N1 || boolVal? N2 then Some (mkAnd(N1,N2)) else None
      | Apply(Fun(Or,   _,_),Record(fields as [(_,N1),(_,N2)], _),_) -> 
        if boolVal? N1 || boolVal? N2 then Some (mkOr(N1,N2)) else None
      | Apply(Fun(Implies, _,_),Record(fields as [(_,N1),(_,N2)], _),_) ->
        if boolVal? N1 || (boolVal? N2 && sideEffectFree N1) then Some (mkSimpImplies(N1,N2)) else None
      | Apply(Fun(Iff, _,_),Record(fields as [(_,N1),(_,N2)], _),_) -> 
	if boolVal? N1 || boolVal? N2 then Some (mkSimpIff(N1,N2)) else None
      | IfThenElse(p,q,r,_) ->
        let simp_if = mkIfThenElse(p,q,r) in
        if equalTermAlpha?(term, simp_if) then None else Some simp_if
        %% {id1 = v1, ..., idn = vn}.idi = vi
      | Apply(Fun(Project i,_,_),Record(m,_),_) ->
        (case getField(m,i) of
           | Some fld -> Some fld
           | None -> None)
        %% (x << {i = v}).j  -->  x.j  (x << {i = v}).i  -->  v
      | Apply(proj_fn as Fun(Project i,_,_), Apply(Fun(RecordMerge, _, _), Record([(_,r1), (_,Record(m,_))], _),_),_) ->
        (case getField(m,i) of
           | Some fld -> Some fld
           | None -> tryEval1 (mkApply(proj_fn, r1)))
      | Fun(Op(Qualified ("Integer", "zero"),_),_,a) -> Some(mkFun(Nat 0, intType))
        %% let pat = e in bod --> bod  if variables in pat don't occur in bod
      | Let([(pat, tm)], bod, _) | sideEffectFree tm && disjointVars?(patternVars pat, freeVars bod) ->
        Some bod
      | Apply(Fun(Embedded(qid1), ty1, _), arg, _) ->
        (case arg
           | Fun(Embed(qid2, _), _, _) -> Some(mkBool(qid1 = qid2))
           | Apply(Fun(Embed(qid2, _), _, _), _, _) -> Some(mkBool(qid1 = qid2))
           | Fun(Op(qid2, _), _, _) | qid1 = qid2 -> Some(mkBool true)
           | Apply(Fun(Embedded(qid1), ty1, _), Apply(Fun(Op(qid2, _), _, _), _, _), _) | qid1 = qid2 -> Some(mkBool true)
           | _ -> None)
      | _ -> None

 op reduceTerm1(term: MSTerm): MSTerm =
   case tryEval1 term of
     | Some red_tm -> red_tm
     | None -> term

 op  disjointMatches: MSMatch -> Bool
 def disjointMatches = 
     fn [] -> true
      | (pat1,_,_)::matches -> 
         forall? 
           (fn(pat2,_,_) -> disjointPatterns(pat1,pat2)) 
             matches 
        && disjointMatches matches

 op  disjointPatterns: MSPattern * MSPattern -> Bool
 def disjointPatterns = 
     (fn (EmbedPat(con1,Some p1,_,_):MSPattern,
	  EmbedPat(con2,Some p2,_,_):MSPattern) -> 
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
	 disjointPatterns(p1,p3) || disjointPatterns(p2,p3)
       | (p1,AliasPat(p2,p3,_)) -> 
	 disjointPatterns(p1,p2) || disjointPatterns(p1,p3)
       | (NatPat(i1, _),NatPat(i2, _)) -> ~(i1 = i2)
       | (BoolPat(b1, _),BoolPat(b2, _)) -> ~(b1 = b2)
       | (CharPat(c1, _),CharPat(c2, _)) -> ~(c1 = c2)
       | (StringPat(s1, _),StringPat(s2, _)) -> ~(s1 = s2)
       | _ -> false
      )

 % Open up the definition of a named type (wrapped in a call of Base),
 % and repeat, if that is also a named type, etc.
 op unfoldBase (sp : Spec, ty : MSType) : MSType =
   unfoldBaseV (sp, ty, true)

 % Open up the definition of a named type (wrapped in a call of Base),
 % and repeat, if that is also a named type, etc.
 %V for verbose?
 % verbose parameter does not seem to be used.
 op unfoldBaseV (sp : Spec, ty : MSType, verbose : Bool) : MSType = 
  case ty of
    | Base (qid, tys, a) ->
      (case findTheType (sp, qid) of
	 | None -> ty %TODO Should this be an error?
	 | Some info ->
	   if definedTypeInfo? info then
	     let (tvs, ty_def) = unpackFirstTypeDef info in
             if length tvs ~= length tys
               then (% writeLine("Type arg# mismatch: "^printType ty);
                     %% This can arise because of inadequacy of patternType on QuotientPat
                     ty_def)
             else
	     let sty = substType (zip (tvs, tys), ty_def) in
	     unfoldBaseV (sp, sty, verbose)
	   else %Should this be an error?
	     ty)
    | _ -> ty

  op unfoldBase0 (spc: Spec) (ty: MSType): MSType =
    let exp_ty = unfoldBaseOne(spc, ty) in
    if embed? CoProduct exp_ty || embed? Quotient exp_ty || equalType?(exp_ty, ty)
         || recordType? exp_ty
      then ty
      else exp_ty

 op range_*(spc: Spec, ty: MSType, ign_subtypes?: Bool): MSType =
   case unfoldBase (spc, ty)
    of Arrow(_, rng, _) -> range_*(spc, rng, ign_subtypes?)
     | Subtype(st, _, _) | ign_subtypes? -> range_*(spc, st, ign_subtypes?)
     | _ -> ty

 op existsInFullType? (spc: Spec) (pred?: MSType -> Bool) (ty: MSType): Bool =
   pred? ty ||
   (case ty of
      | Base _ ->
        (case tryUnfoldBase spc ty of
           | None -> false
           | Some uf_ty -> existsInFullType? spc pred? uf_ty)
      | Arrow(x,y,_) -> existsInFullType? spc pred? x || existsInFullType? spc pred? y
      | Product(prs,_) -> exists? (fn (_,f_ty) -> existsInFullType? spc pred? f_ty) prs
      | CoProduct(prs,_)  -> exists? (fn (_,o_f_ty) ->
                                       case o_f_ty of
                                         | Some f_ty -> existsInFullType? spc pred? f_ty
                                         | None -> false)
                               prs
      | Quotient(x,_,_) -> existsInFullType? spc pred? x
      | Subtype(x,_,_) -> existsInFullType? spc pred? x
      | And(tys,_) -> exists? (existsInFullType? spc pred?) tys
      | _ -> false)

 op stripSubtypes (sp: Spec, ty: MSType): MSType = 
  let X = unfoldBase (sp, ty) in
  case X 
    of Subtype (ty, _, _) -> stripSubtypes (sp, ty)
     | ty -> ty

 % might we need to alternate repeatedly between unfolding base types and stripping off subtypes?
 op arrowOpt (sp : Spec, ty : MSType): Option (MSType * MSType) = 
  case stripSubtypes (sp, unfoldBase (sp,ty))
    of Arrow (dom, rng, _) -> Some (dom, rng)
     | _ -> None

 op ProcTypeOpt (sp : Spec, ty : MSType): Option (MSType * MSType) = 
  case stripSubtypes (sp, ty) of
    | Base (Qualified ("Accord", "ProcType"), [dom, rng, _], _) ->
      Some (dom, rng)
    | _ -> None

 op rangeOpt (sp: Spec, ty: MSType): Option MSType = 
  case arrowOpt (sp, ty) of
    | None ->
      (case ProcTypeOpt (sp, ty) of 
	 | Some (_, rng) -> Some rng
	 | _ -> None)
    | Some (_, rng) -> Some rng

 op productOpt (sp : Spec, ty : MSType): Option (List (Id * MSType)) = 
  case stripSubtypes (sp, unfoldBase (sp,ty))
    of Product (fields, _) -> Some fields
     | _ -> None

 op fieldTypes (sp : Spec, ty : MSType): MSTypes =
   case stripSubtypes (sp, unfoldBase (sp,ty))
    of Product (fields, _) -> map (fn (_, ty) -> ty) fields
     | _ -> [ty]

 op tupleType? (sp : Spec, ty : MSType): Bool =
   case productOpt(sp, ty) of
     | Some(("1",_)::_) -> true
     | _ -> false

 op tuplePattern? (pat: MSPattern): Bool =
   case pat of
     | RecordPat(("1",_)::_, _) -> true
     | AliasPat(_, p2, _) ->  tuplePattern? p2
     | RestrictedPat(p1, _, _) -> tuplePattern? p1
     | _ -> false

 op [a] tupleFields1? (fields: List(Id * a)): Bool =
   case fields of
     | [] -> true
     | ("1",_)::_ -> true
     | _ -> false

 op coproductOpt (sp : Spec, ty : MSType): Option (List (QualifiedId * Option MSType)) = 
  case stripSubtypes (sp, unfoldBase (sp,ty))
    of CoProduct (fields, _) -> Some fields
     | _ -> None

 op recordType?(ty: MSType): Bool =
  case ty of
    | Product(("1",_)::_, _)  -> false
    | Product _ -> true
    | Subtype(sty, _, _) -> recordType? sty
    | _ -> false

 %- --------------------------------------------------------------------------------

op maybeInferType (sp : Spec, term : MSTerm) : Option MSType =
 case term of
   | Apply      (t1, t2,            _) -> (case maybeInferType(sp, t1) of
                                             | Some typ ->
                                               (case arrowOpt (sp, typ) of
                                                  | Some (_, rng) -> Some rng
                                                  | _ -> None)
                                             | _ -> None)
   | ApplyN     ([t1,t2],          _)  -> (case maybeInferType(sp, t1) of
                                             | Some typ ->
                                               (case arrowOpt (sp, typ) of
                                                  | Some (_, rng) ->
                                                    % let _ = writeLine("tt2*: "^printTerm term^"\n"^anyToString t1) in
                                                    (case rng of
                                                       | MetaTyVar(tv,_) -> 
                                                         let {name=_,uniqueId=_,link} = ! tv in
                                                         (case link of
                                                            | None -> 
                                                              (case maybeInferType (sp, t2) of
                                                                 | Some typ2 ->
                                                                   (case (t1, productOpt(sp, typ2)) of
                                                                      | (Fun(Project id, _, _), Some fields) ->
                                                                        (case findLeftmost (fn (id2, _) -> id = id2) fields of
                                                                           | Some(_, f_ty) -> Some f_ty
                                                                           | None -> Some rng)
                                                                      | _ -> Some rng)
                                                                 | _ -> Some rng)
                                                            | _ -> Some rng)
                                                       | _ -> Some rng)
                                                  | _ -> None)
                                             | _ -> 
                                               %% how did this never happen in 10 years????
                                               None)
   | Bind       _                      -> Some boolType
   | Record     (fields,            _) -> (case foldr (fn ((id, t), result) ->
                                                         case result of
                                                           | None -> None
                                                           | Some fld_prs ->
                                                             case maybeInferType(sp, t) of
                                                               | None -> None
                                                               | Some ty -> Some((id, ty) :: fld_prs))
                                             (Some []) fields of
                                                               | None -> None
                                                               | Some fld_prs -> Some(mkRecordType fld_prs))
   | Let        (_, t,              _) -> maybeInferType(sp, t)
   | LetRec     (_, t,              _) -> maybeInferType(sp, t)
   | Var        ((_, srt),          _) -> Some srt
   | Fun        (fun, srt,          _) -> Some srt
   | Lambda     ((pat,_,body) :: _, _) ->  (case maybeInferType(sp, body) of
                                              | None -> None
                                              | Some body_ty -> Some(mkArrow (patternType pat, body_ty)))
   | Lambda     ([],                _) -> None
   | The        ((_,srt),_,         _) -> Some srt
   | IfThenElse (_, t2, t3,         _) -> maybeInferType(sp, t2)
   | Seq        (tms,               _) -> if tms = []
                                            then Some(mkProduct [])
                                          else maybeInferType(sp, last tms)
   | TypedTerm  (_, s,              _) -> Some s
   | Pi         (_, t,              _) -> maybeInferType   (sp, t)
   | And        (t :: _,            _) -> maybeInferType   (sp, t)
   | _                                 -> None
     
op inferType (sp: Spec, term : MSTerm) : MSType = 
  case term of
    | Apply      (t1, t2,           _) -> (let t1_type = inferType (sp, t1) in
                                            case rangeOpt (sp, t1_type) of
                                              | Some rng -> rng
                                              | _ ->
                                                let _ = case t1_type of
                                                          | Base (name, tys, a) ->
                                                            writeLine (show name ^
                                                                         (case findTheType (sp, name) of
                                                                            | Some info -> " defined\n" ^ printType info.dfn
                                                                            | _ -> " not defined "))
                                                          | _ -> 
                                                            let _ = writeLine("Infering type for " ^ printTerm term) in
                                                            let _ = writeLine("Applied term:  " ^ printTerm t1) in
                                                            let _ = writeLine("Argument term: " ^ printTerm t2) in
                                                            let _ = writeLine("Type of applied term is not an application: " ^ printType t1_type) in
                                                            ()
                                                in
                                                System.fail ("inferType: Could not extract type for\n"
                                                               ^ printTerm term
                                                               ^ "\nfn type\n: " ^ printType (unfoldBase (sp, t1_type))
                                                               ^ "\n" ^ printTermWithTypes t1))
    | Record     (fields,           _) -> Product (map (fn (id, t) -> 
                                                          (id, inferType (sp, t)))
                                                       fields,
                                                   noPos)
    | Bind       _                     -> boolType
    | The        ((_,ty), _,        _) -> ty
    | Let        (_, term,          _) -> inferType (sp, term)
    | LetRec     (_, term,          _) -> inferType (sp, term)
    | Var        ((_, ty),          _) -> ty
    | Fun        (_, ty,            _) -> ty
    | Lambda     ((pat,_,body)::_,  _) -> mkArrow (patternType pat, inferType (sp, body))
    | Lambda     ([],               _) -> System.fail "inferType: Ill formed lambda abstraction"
    | IfThenElse (_, t2, t3,        _) -> inferType (sp, t2)
    | Seq        ([],               _) -> Product ([], noPos)
    | Seq        (terms,            _) -> inferType (sp, last terms)
    | TypedTerm  (_, ty,            _) -> ty
    | Transform  _                     -> System.fail "inferType: Can't take type of a Transform term"
    | Pi         (_, t,             _) -> inferType (sp, t)
    | And        (t1::_,            _) -> inferType (sp, t1)
    | Any        _                     -> Any noPos
    | _ ->
      let _ = writeLine ("Infer type saw mystery term: " ^ anyToString term) in
      System.fail ("inferType: Non-exhaustive match")

 op subtype?(sp: Spec, ty: MSType): Bool =
   case ty of
     | Subtype _ -> true
     | _ ->
       let exp_ty =  unfoldBase (sp, ty) in
       if ty = exp_ty then false
         else subtype?(sp, exp_ty)

 op subtypeComps(sp: Spec, ty: MSType): Option (MSType * MSTerm) =
   case ty of
     | Subtype(sty,p,_) -> Some(sty,p)
     | _ ->
       let exp_ty =  unfoldBase (sp, ty) in
       if ty = exp_ty then None
         else subtypeComps(sp, exp_ty)

 op subtypeOf (ty: MSType, qid: QualifiedId, spc: Spec): Option MSType =
    case ty of
      | Base(qid1,tys,_) ->
        if qid1 = qid then Some ty
          else
	 (case findTheType (spc, qid1) of
            | None -> None
            | Some info ->
              if definedTypeInfo? info then
                let (tvs, ty) = unpackFirstTypeDef info in
                let sty = substType (zip (tvs, tys), ty) in
                subtypeOf(sty,qid,spc)
              else
                None)
      | Subtype(t1,_,_) -> subtypeOf(t1,qid,spc)
      | _ -> None

op subtypePred (ty: MSType, sup_ty: MSType, spc: Spec): Option MSTerm =
  if equalType?(ty, sup_ty) then Some(mkTruePred ty)
    else
    case ty of
      | Base(qid1,tys,_) ->
        (case findTheType (spc, qid1) of
           | None -> None
           | Some info ->
             if definedTypeInfo? info then
               let (tvs, ty) = unpackFirstTypeDef info in
               let sty = substType (zip (tvs, tys), ty) in
               subtypePred(sty,sup_ty,spc)
             else
               None)
      | Subtype(t1,pred,_) ->
        (case subtypePred(t1,sup_ty,spc) of
           | Some pred1 -> Some(composeConjPreds([pred, pred1], spc))
           | None -> None) 
      | _ -> None


   op subtypePreds(tys: MSTypes): MSTerms =
     mapPartial (fn ty ->
                 case ty of
                   | Subtype(_, p, _) -> Some p
                   | _ -> None)
       tys
 
   op subtypePred?(ty: MSType, p: MSTerm, spc: Spec): Bool =
     case subtypeComps(spc, ty) of
       | Some(_, pt) -> equalTermAlpha?(p, pt)
       | None -> false

   op possiblySubtypeOf?(ty1: MSType, ty2: MSType, spc: Spec): Bool =
     % let _ = writeLine(printType ty1^" <=? "^printType ty2^"\n"^show(equivType? spc (ty1, ty2))) in
     equivType? spc (ty1, ty2)
       || (case ty1 of
             | Base(qid1, tys, _) ->
               (case findTheType (spc, qid1) of
                  | None -> false
                  | Some info ->
                    if definedTypeInfo? info then
                      let (tvs, ty) = unpackFirstTypeDef info in
                      let n_tvs = length tvs in
                      let n_tys = length tys in
                      let (tvs, tys) =
                          if n_tvs = n_tys then (tvs, tys)
                          else
                           let min_len = min(n_tvs, n_tys) in
                           (warn("Mismatch in type: "^show n_tvs^" ~= "^show n_tys^"\n"^printType info.dfn^"\n"
                                   ^printType ty1);
                            (subFromTo(tvs, 0, min_len),
                             subFromTo(tys, 0, min_len)))
                      in
                      let sty = substType (zip (tvs, tys), ty) in
                      possiblySubtypeOf?(sty, ty2, spc)
                    else
                      false)
             | Subtype(t1, _, _) -> possiblySubtypeOf?(t1, ty2, spc)
             | _ -> false)

   op etaReduce(tm: MSTerm): MSTerm =
     case tm of
       | Lambda([(VarPat(v,_), Fun(Bool true,_,_),
                  Apply(lam as Lambda([(_, Fun(Bool true,_,_), _)], _), Var(v1,_), _))], _) | equalVar?(v, v1) ->
         lam
       | _ -> tm

   op varRecordTerm?(tm: MSTerm): Bool =
     %% Var or product
     case tm of
       | Var _ -> true
       | Record(fields, _) ->
         forall? (fn (_, fld_tm) -> varRecordTerm? fld_tm) fields
       | _ -> false

   op varRecordPattern?(pat: MSPattern): Bool =
     %% Var or product
     case pat of
       | VarPat _ -> true
       | RecordPat(fields, _) ->
         forall? (fn (_, fld_pat) -> varRecordPattern? fld_pat) fields
       | _ -> false

   op varCompatiblePatternTerm?(pat: MSPattern, tm: MSTerm): Bool =
     case (pat, tm) of
       | (VarPat _, Var _) -> true
       | (RecordPat(pat_fields, _), Record(tm_fields, _)) ->
         forall? (fn ((_, fld_pat), (_, fld_tm)) -> varCompatiblePatternTerm?(fld_pat, fld_tm))
           (zip(pat_fields, tm_fields))
       | _ -> false

   op substFromCompatiblePatternTerm(pat: MSPattern, tm: MSTerm): MSVarSubst =
     case (pat, tm) of
       | (RecordPat(pat_fields, _), Record(tm_fields, _)) ->
         foldr (fn (((_, fld_pat), (_, fld_tm)), sbst) -> substFromCompatiblePatternTerm(fld_pat, fld_tm) ++ sbst)
           [] (zip(pat_fields, tm_fields))
       | (VarPat(v, _), _) -> [(v, tm)]

   op flattenCompatiblePatternTerm(pat: MSPattern, tm: MSTerm): List(MSPattern * MSTerm) =
     case (pat, tm) of
       | (RecordPat(pat_fields, _), Record(tm_fields, _)) ->
         foldr (fn (((_, fld_pat), (_, fld_tm)), pairs) -> flattenCompatiblePatternTerm(fld_pat, fld_tm) ++ pairs)
           [] (zip(pat_fields, tm_fields))
       | _ -> [(pat, tm)]

   op simpleLambda?(tm: MSTerm): Bool =
     %% One case, true pred & variable of product of variable pattern
     case tm of
       | Lambda([(pat, Fun(Bool True, _, _), _)], _) ->
         varRecordPattern? pat
       | _ -> false

   op decomposeConjPred(pred: MSTerm): MSTerms =
     case pred of
       | Lambda([(VarPat(v,_), Fun(Bool True, _, _), conj as Apply(Fun(And,_,_), _, _))], _) ->
         let conjs = getConjuncts conj in
         if forall? (fn conj -> case conj of
                              | Apply(_, Var(vi,_), _) -> v = vi
                              | _ -> false)
              conjs
           then map (fn Apply(pi, _, _) -> pi) conjs
           else [pred]
       | Apply(Fun(Op(Qualified("Set", "/\\"), _),_,_), Record([("1", p1), ("2", p2)], _), _) ->
         removeDuplicateTerms(decomposeConjPred p1 ++ decomposeConjPred p2)
       | Apply(Fun(Op(Qualified("Bool", "&&&"), _),_,_), Record([("1", p1), ("2", p2)], _), _) ->
         removeDuplicateTerms(decomposeConjPred p1 ++ decomposeConjPred p2)
       | _ -> [etaReduce pred]

   op decomposeListConjPred(preds: MSTerms): List MSTerms =
     case preds of
       | [] -> [[]]
       | pred::r ->
         let rpredss = decomposeListConjPred r in
         let this_preds = decomposeConjPred pred in
         foldr (fn (preds, predss) ->
                  (map (fn pred -> pred::preds) this_preds)
                   ++ predss)
           [] rpredss

  op TruePred?(pred: MSTerm): Bool =
    case pred of
      | Fun(Op(Qualified("Bool","TRUE"), _), _, _) -> true
      | _ -> false

  op mkTruePred(ty: MSType): MSTerm =
    mkOp(Qualified("Bool","TRUE"), mkArrow(ty, boolType))

  op composeConjPreds(preds: MSTerms, spc: Spec): MSTerm =
    let preds = removeDuplicateTerms preds in
    let preds = filter (~~~ TruePred?) preds
    in
    case preds of
      | [pred] -> etaReduce pred
      | pred1::rpreds ->
        let pred_ty = foldl (fn (pred_ty, predi) ->
                               let pred_tyi = inferType(spc, predi) in
                               commonSuperType(pred_ty, pred_tyi, spc))
                        (inferType(spc, pred1)) rpreds
        in
        let op_exp = mkInfixOp(Qualified("Bool", "&&&"),
                               Infix(Right, 25),
                               mkArrow(mkProduct[pred_ty, pred_ty], pred_ty))
        in
        foldl (fn (result, pred) -> mkAppl(op_exp, [result, pred]))
          pred1 rpreds

  op mkSubtypePreds(sss_ty: MSType, preds: MSTerms, a: Position, spc: Spec): MSType =
    case preds of
      | [] -> sss_ty
      | _ -> Subtype(sss_ty, composeConjPreds(preds, spc), a)

  op composeSubtypes(sss_ty: MSType, p1: MSTerm, p2: MSTerm, a: Position, spc: Spec): MSType =
    % let _ = writeLine("composeStys: "^printTerm p1^" with "^printTerm p2) in
    let p1s = decomposeConjPred p1 in
    let p2s = decomposeConjPred p2 in
    mkSubtypePreds(sss_ty, p1s ++ p2s, a, spc)

  op maybeComposeSubtypes(ty: MSType, pr1: MSTerm, spc: Spec, a: Position): MSType =
    % let _ = writeLine("mcs: "^printType ty^" | "^printTerm pr1) in
    case ty of
      | Subtype(s_ty, pr2, _) -> composeSubtypes(s_ty, pr1, pr2, a, spc)
      | _ -> Subtype(ty, pr1, a)

  op unfoldOpRef(tm: MSTerm, spc: Spec): Option MSTerm =
    case tm of
      | Fun(Op(qid, _),ty,_) ->
        (case findTheOp(spc, qid) of
           | Some opinfo ->
             (let (tvs,ty1,defn) = unpackFirstOpDef opinfo in
              case typeMatch(ty1, ty, spc, true, true) of
                | Some subst -> Some(instantiateTyVarsInTerm(defn, subst))
                | None -> None)
           | None -> None)
      | _ -> None

  op opDefined?(spc: Spec, qid: QualifiedId): Bool =
   case findTheOp(spc, qid) of
     | Some info -> ~(anyTerm? info.dfn)
     | None -> false

  op unfoldable?(tm: MSTerm, spc: Spec): Bool =
    case tm of
      | Fun(Op(qid,_),_,_) -> opDefined?(spc, qid)
      | Apply(f, _, _) -> unfoldable?(f, spc)
      | _ -> false

  op unfoldableWithOp(tm: MSTerm, spc: Spec): Option QualifiedId =
    case tm of
      | Fun(Op(qid,_),_,_) ->
        if opDefined?(spc, qid) then Some qid else None
      | Apply(f, _, _) -> unfoldableWithOp(f, spc)
      | _ -> None

  op unfoldTerm(tm: MSTerm, spc: Spec): MSTerm =
    case tm of
      | Apply(f, a, p) -> Apply(unfoldTerm(f, spc), a, p)
      | _ ->
    case unfoldOpRef(tm, spc) of
      | Some tm -> tm
      | None -> tm

  type TermSubst = List(MSTerm * MSTerm)

  op mkFoldSubst(tms: MSTerms, spc: Spec): TermSubst =
    mapPartial (fn tm ->
                case unfoldOpRef(tm, spc) of
                  | Some defn -> Some(defn, tm)
                  | None -> None)
      tms

  op termSubst1 (sbst: TermSubst) (s_tm: MSTerm): Option MSTerm =
    case findLeftmost (fn (t1,_) -> equalTerm?(t1, s_tm)) sbst of
      | Some (_,t2) -> Some t2
      | None -> None

  op printTermSubst(sbst: TermSubst): () =
    (writeLine "TermSubst:";
     app (fn (t1, t2) -> writeLine(printTerm t1^" --> "^printTerm t2)) sbst)

  op termSubst(tm: MSTerm, sbst: TermSubst): MSTerm =
    if sbst = [] then tm
    else
    let free_vs = foldl (fn (fvs, (t1, t2)) -> removeDuplicateVars(freeVars t1 ++ freeVars t2 ++ fvs)) [] sbst in
    let def repl(tm) =
          replaceTerm(subst_tm, fn _ -> None, fn _ -> None) tm
        def subst_tm(stm) =
          let shared_vars = filter (fn v -> inVars?(v, free_vs)) (boundVars stm) in
          if shared_vars = [] then termSubst1 sbst stm
          else let rn_stm = renameBoundVars(stm, shared_vars) in
               let new_rn_stm = repl rn_stm in
               Some new_rn_stm
    in
    let result =  repl tm
    in
    result

  op termsSubst(tms: MSTerms, sbst: TermSubst): MSTerms =
    map (fn t -> termSubst(t, sbst)) tms

  op typeTermSubst(ty: MSType, sbst: TermSubst): MSType =
    if sbst = [] then ty
    else
%    let _ = writeLine(printType ty) in
%    let _ = printTermSubst sbst in
    let result =  replaceType (termSubst1 sbst, fn _ -> None, fn _ -> None) ty in
%    let _ = writeLine("= "^printType result) in
    result

  op maybeComposeFoldSubtypes(ty: MSType, pr1: MSTerm, sbst: TermSubst, spc: Spec, a: Position): MSType =
    % let _ = writeLine("mcs: "^printType ty^" | "^printTerm pr1) in
    let pr1 = termSubst(pr1, sbst) in
    case ty of
      | Subtype(s_ty, pr2, _) -> composeSubtypes(s_ty, pr1, termSubst(pr2, sbst), a, spc)
      | _ -> Subtype(ty, pr1, a)

  op raiseBase (spc: Spec) (ty: MSType): MSType =
     %let _ = writeLine("rb: "^printType(unfoldBase0 spc ty)) in
    case unfoldBase0 spc ty of
      | Subtype(_, pred, a) -> Subtype(ty, pred, a)
      | _ -> ty          

  op mergeRaisedBase(ty: MSType, r_ty: MSType, spc: Spec): MSType =
    % let _ = writeLine("mrb: "^printType ty^" u "^printType r_ty) in
    case raiseBase spc ty of
      | Subtype(_, prb, a) ->
        maybeComposeSubtypes(r_ty, prb, spc, a)
      | _ -> r_ty

%  op Simplify.simplify (spc: Spec) (term: MSTerm): MSTerm

  op filterSharedPred2(ty1: MSType, ty2: MSType, spc: Spec): MSType * MSType =
    case (ty1, ty2) of
      | (Subtype(_, p1, _), Subtype(sty2, p2, a2)) ->
        let p1s = decomposeConjPred p1 in
        let uf_p1s = mapPartial (fn t -> unfoldOpRef(t, spc)) p1s in
%        let _ = case uf_p1s of
%                | [p1] -> writeLine(printTerm(Simplify.simplify spc p1)^"\n =?=\n"
%                                      ^printTerm(Simplify.simplify spc p2))
%                | _ -> ()
%        in
        let forall?_p1s = p1s ++ uf_p1s in
        % let p2 = Simplify.simplify spc p2 in
        let p2s = decomposeConjPred p2 in
        let f_p2s = filter (fn p2i -> ~(equivTermIn? spc (p2i, forall?_p1s))) p2s in
        (ty1, mkSubtypePreds(sty2, f_p2s, a2, spc))
      | _ -> (ty1, ty2)

  op printSubtypeWithTypes(ty: MSType): () =
    case ty of
      | Subtype(sty, p, _) ->
        writeLine(printType sty^" | "^printTermWithTypes p)
      | _ -> writeLine(printType ty)

  op dontRaiseTypes: QualifiedIds = []   % [Qualified("Nat", "Nat")]
  op treatAsAtomicType?(ty: MSType): Bool =
    case ty of
      | Base(qid, _, _) -> qid in? dontRaiseTypes
      | _ -> false

  op namedTypesRaised?: Bool = false

  op raiseSubtypes(ty1: MSType, ty2: MSType, spc: Spec): MSType * MSType =
    % let _ = writeLine("\nrst: "^printType ty1^" <> "^printType ty2) in
    let (r_ty1, r_ty2) =  raiseSubtypes1(ty1, ty2, false, false, [], [], spc) in
    % let _ = writeLine("rtd: "^printType r_ty1^" <> "^printType r_ty2^"\n") in
    (r_ty1, r_ty2)      

  %% Want to expand given type and expected type consistently so subtype is transparent
  %% Not symmetric: remove conditions from ty2 greedily to avoid spurious obligations
  op raiseSubtypes1(ty1: MSType, ty2: MSType, uf1?: Bool, uf2?: Bool, real_as1: MSTypes, real_as2: MSTypes,
                    spc: Spec): MSType * MSType =
  %% Bring subtypes to the top-level
    let uf1? = ~(uf1? => typeIn?(ty1, real_as1)) in
    let uf2? = ~(uf2? => typeIn?(ty2, real_as2)) in
    % let _ = writeLine("rts< ("^show uf1?^","^show uf2?^") "^printType ty1^" <> "^printType ty2) in
    let def existsSubtypeArg?(args, uf?, real_as) =
          exists? (fn ty -> embed? Subtype ty && (uf? => typeIn?(ty, real_as))) args
        def tryRaiseFromArgs(ty, qid, args, uf?, real_as, a) =
          % let _ = writeLine("trfa: "^printType(Base(qid, args, a))) in
          if existsSubtypeArg?(args, uf?, real_as)
            then
            let Qualified(q,id) = qid in
            let pred_name = id^"_P" in
            let pred_qid = Qualified(q, pred_name) in
            (case findTheOp(spc, pred_qid) of
               | Some _ ->
                 let arg_comps = map (fn tyi ->
                                      case tyi of
                                        | Subtype(ty, pr, _) -> (ty, pr)
                                        | None -> (tyi, mkLambda(mkWildPat tyi, trueTerm)))
                                   args
                 in
                 let (bare_args, arg_preds) = unzip arg_comps in
                 let bare_ty = Base(qid, bare_args, a) in
                 let arg_preds_lst = decomposeListConjPred arg_preds in
                 let preds = map (fn arg_preds ->
                                    mkAppl(mkOp(pred_qid,
                                                mkArrow(mkProduct(map (fn ty -> mkArrow(ty, boolType))
                                                                    bare_args),
                                                        mkArrow(bare_ty, boolType))),
                                           arg_preds))
                               arg_preds_lst
                 in
                 % let _ = writeLine("--> "^printType(mkSubtypePreds(bare_ty, preds, a, spc))) in
                 Some(mkSubtypePreds(bare_ty, preds, a, spc))
               | None -> None)
          else None

        def maybeComposeWithRaisedBase ty =
          % let _ = writeLine("mcrwb: "^printType ty) in
          case ty of
            | Subtype(s_ty, pr1, a) ->
              maybeComposeSubtypes(raiseBase spc s_ty, pr1, spc, a)
            | _ -> raiseBase spc ty

        def tryRaiseFields(flds1, flds2, a) =
          let def addField(id, l_ty, (n_flds, arg_fld_vars, pred, i)) =
                case l_ty of
                  | Subtype(t, p, _) ->
                    let v = ("xf"^show i, t) in
                    (n_flds ++ [(id,t)],
                     arg_fld_vars ++ [(id, mkVarPat v)],
                     mkAnd(pred, mkApply(p, mkVar v)),
                     i+1)
                  | _ -> (n_flds ++ [(id, l_ty)],
                          arg_fld_vars ++ [(id, mkWildPat l_ty)],
                          pred,
                          i+1)
              def mkNonTrivSubtype(n_flds, arg_fld_vars, pred) =
                let prod = Product(n_flds, a) in
                if trueValTerm? pred then prod
                  else Subtype(prod, mkLambda(mkRecordPat arg_fld_vars, pred), a)
          in
          let ((n_flds1, arg_fld_vars1, pred1, _), (n_flds2, arg_fld_vars2, pred2, _)) =
              foldl (fn ((info1, info2), ((id1, tyi1), (id2, tyi2))) ->
                     let (r_tyi1, r_tyi2) = raiseSubtypes1(tyi1, tyi2, uf1?, uf2?, real_as1, real_as2, spc) in
                  %   let _ = writeLine("Raising field "^id1^", "^id2^"\n("^
%                                       printType tyi1^", "^printType tyi2^")\nto\n("^
%                                       printType r_tyi1^", "^printType r_tyi2^")\n") in
                     (addField(id1, r_tyi1, info1),
                      addField(id2, r_tyi2, info2)))
                (([],[],trueTerm,0), ([],[],trueTerm,0)) (zip(flds1, flds2))
          in
          (mkNonTrivSubtype(n_flds1, arg_fld_vars1, pred1),
           mkNonTrivSubtype(n_flds2, arg_fld_vars2, pred2))
    in
    let (ty1, ty2) =
    if uf1? && equalType?(ty1, ty2) then (ty1, ty2)
    else 
    case (ty1, ty2) of
      | (Base(qid1, [], _), Base(qid2, [], _)) | qid1 in? dontRaiseTypes && qid2 = qid1 ->
        (ty1, ty2)
      | (Base(qid1, args1, a1), Base(qid2, args2, a2)) | qid1 = qid2 && length args1 = length args2  ->
        let Qualified(q,id) = qid1 in
        let pred_name = id^"_P" in
        let (rargs1, rargs2) = unzip(map (fn (tyi1, tyi2) ->
                                            raiseSubtypes1(tyi1, tyi2, uf1?, uf2?, real_as1, real_as2, spc))
                                     (zip(args1, args2))) in
        let ty1r = Base(qid1, rargs1, a1) in
        let ty2r = Base(qid2, rargs2, a2) in
        let args1 = rargs1 in %originalForInternals(zip(args1, rargs1), uf1?, real_as1) in
        let args2 = rargs2 in %originalForInternals(zip(args2, rargs2), uf2?, real_as2) in
        if (existsSubtypeArg?(args1, uf1?, real_as1) || existsSubtypeArg?(args2, uf2?, real_as2))
          && embed? None (findTheOp(spc, Qualified(q, pred_name)))
          && embed? Some (tryUnfoldBase spc ty1r)
          then let (rty1, rty2) = raiseSubtypes1(unfoldBase0 spc ty1r, unfoldBase0 spc ty2r,
                                                 true, true,
                                                 if uf1? then real_as1 else args1,
                                                 if uf2? then real_as2 else args2, spc)
               in
               (if uf1? then rty1 else mergeRaisedBase(ty1, rty1, spc),
                if uf2? then rty2 else mergeRaisedBase(ty2, rty2, spc))
        else
        (case (tryRaiseFromArgs(ty1, qid1, args1, false, real_as1, a1),
               tryRaiseFromArgs(ty2, qid2, args2, false, real_as2, a2)) of
           | (Some st1, Some st2) ->
             (if uf1? then st1 else maybeComposeWithRaisedBase st1,
              if uf2? then st2 else maybeComposeWithRaisedBase st2)
           | (Some st1, None)     ->
             (if uf1? then st1 else maybeComposeWithRaisedBase st1,
              if uf2? then ty2r else raiseBase spc ty2)
           | (None,     Some st2) ->
             (if uf1? then ty1r else raiseBase spc ty1,
              if uf2? then st2 else maybeComposeWithRaisedBase st2)
           | (None, None) ->
             (if namedTypesRaised?
              then (if uf1? then ty1r else raiseBase spc ty1,
                    if uf2? then ty2r else raiseBase spc ty2)
              else
                case (tryUnfoldBase spc ty1, tryUnfoldBase spc ty2) of
                | (None, None)                 -> (ty1, ty2)
                | (Some exp_ty1, None)         ->
                   raiseSubtypes1(exp_ty1,ty2, true, uf2?, real_as1, real_as2, spc)
                | (None, Some exp_ty2)         ->
                   raiseSubtypes1(ty1, exp_ty2, uf1?, true, real_as1, real_as2, spc)
                | (Some exp_ty1, Some exp_ty2) ->
                   raiseSubtypes1(exp_ty1, exp_ty2, true, true, real_as1, real_as2, spc)))
      | (Base(qid1, args1, _), Base(_, args2, _)) ->
        %% If one is a subtype of the other then unfold it first
        (if subtypeOf?(ty2, qid1, spc)
          then case tryUnfoldBase spc ty2 of
                 | Some exp_ty2 ->
                   let (rty1, rty2) = raiseSubtypes1(ty1, exp_ty2, uf1?, false, real_as1,
                                                     if uf2? then real_as2 else args2,
                                                     spc)
                   in
                   (rty1, if uf2? then rty2 else mergeRaisedBase(ty2, rty2, spc))
                 | None -> (ty1, ty2)   % Shouldn't happen
          else case tryUnfoldBase spc ty1 of
                 | Some exp_ty1 ->
                   let (rty1, rty2) = raiseSubtypes1(exp_ty1, ty2, false, uf2?,
                                                     if uf1? then real_as1 else args1,
                                                     real_as2, spc)
                   in
                   (if uf1? then rty1 else mergeRaisedBase(ty1, rty1, spc), rty2)
                 | None -> (raiseSubtype(ty1, spc), raiseSubtype(ty2, spc)))
      | (Subtype(s_ty1, p1, a1), Subtype(s_ty2, p2, a2)) ->
        let (rty1, rty2) = raiseSubtypes1(s_ty1, s_ty2, uf1?, uf2?, real_as1, real_as2, spc) in
        let sbst = mkFoldSubst([p1, p2] ++ subtypePreds[rty1, rty2], spc) in
        (if uf1? then rty1 else maybeComposeFoldSubtypes(rty1, p1, sbst, spc, a1),
         if uf2? then rty2 else maybeComposeFoldSubtypes(rty2, p2, sbst, spc, a2))
      | (Subtype(s_ty1, p1, a1), _) ->
        let (rty1, rty2) = raiseSubtypes1(s_ty1, ty2, uf1?, uf2?, real_as1, real_as2, spc) in
        let sbst = mkFoldSubst(p1 :: subtypePreds[rty1, rty2], spc) in
        (if uf1? then rty1 else maybeComposeFoldSubtypes(rty1, p1, sbst, spc, a1),
         typeTermSubst(rty2, sbst))
      | (_, Subtype(s_ty2, p2, a2)) ->
        let (rty1, rty2) = raiseSubtypes1(ty1, s_ty2, uf1?, uf2?, real_as1, real_as2, spc) in
        let sbst = mkFoldSubst(p2 :: subtypePreds[rty1, rty2], spc) in
        (typeTermSubst(rty1, sbst),
         if uf2? then rty2 else maybeComposeFoldSubtypes(rty2, p2, sbst, spc, a2))
      | (_, Base(qid2, args2, a)) | qid2 nin? dontRaiseTypes ->
        (case tryRaiseFromArgs(ty2, qid2, args2, uf2?, real_as2, a) of
           | Some st2 -> raiseSubtypes1(ty1, st2, uf1?, uf2?, real_as1, real_as2, spc)
           | None ->
         case tryUnfoldBase spc ty2 of
           | Some exp_ty2 ->
             (let (rty1, rty2) = raiseSubtypes1(ty1, exp_ty2, uf1?, true, real_as1,
                                                if uf2? then real_as2 else args2, spc) in
              (rty1, if uf2? then rty2 else mergeRaisedBase(ty2, rty2, spc)))
           | None -> (raiseSubtype(ty1, spc), ty2))
      | (Base(qid1, args1, a), _) | qid1 nin? dontRaiseTypes ->
        (case tryRaiseFromArgs(ty1, qid1, args1, uf1?, real_as1, a) of   % Better way to handle this?
           | Some st1 -> raiseSubtypes1(st1, ty2, uf1?, uf2?, real_as1, real_as2, spc)
           | None ->
         case tryUnfoldBase spc ty1 of
           | Some exp_ty1 ->
             (let (rty1, rty2) = raiseSubtypes1(exp_ty1, ty2, true, uf2?,
                                                if uf1? then real_as1 else args1,
                                                real_as2, spc) in
              (if uf1? then rty1 else mergeRaisedBase(ty1, rty1, spc), rty2))
           | None -> (ty1, raiseSubtype(ty2, spc)))
      | (Product(flds1, a1), Product(flds2, a2)) ->
        tryRaiseFields(flds1, flds2, a1)
 %     | Arrow(dom, rng ,a) ->
%        (case raiseSubtype(dom,spc) of
%           | Subtype(d,d_p,_) ->
%             %% Using d would be more natural, but then you have to change the type of all variable refs
%             %% to avoid unnecessary type annotation in Isabelle output (or else freeVars needs to be
%             %% fixed to ignore types
%             let f_ty = Arrow(dom,rng,a) in
%             Subtype(f_ty, mkSubtypeFnPredicate(d_p, f_ty, d, rng), a)
%           | _ -> ty)
      | _ -> (raiseSubtype(ty1, spc), raiseSubtype(ty2, spc))
    in
    let (ty1, ty2) = filterSharedPred2(ty1, ty2, spc) in
    % let _ = writeLine("rts> "^printType ty1^" <> "^printType ty2) in
    (ty1, ty2)     

  op raiseSubtype(ty: MSType, spc: Spec): MSType =
    %% Bring subtypes to the top-level
    % let _ = writeLine("rt: "^printType ty) in
    case ty of
      | Base(qid, [], _) | qid in? dontRaiseTypes -> ty
      | Base(qid, args, a) ->
        let args = map (fn tyi -> raiseSubtype(tyi, spc)) args in
        if exists? (embed? Subtype) args
          then
          let Qualified(q,id) = qid in
          let pred_name = id^"_P" in
          let pred_qid = Qualified(q, pred_name) in
          (case findTheOp(spc, pred_qid) of
             | Some _ ->
               let arg_comps = map (fn tyi ->
                                      case tyi of
                                        | Subtype(ty, pr, _) -> (ty, pr)
                                        | None -> (tyi, mkLambda(mkWildPat tyi, trueTerm)))
                                 args
               in
               let (bare_args, arg_preds) = unzip arg_comps in
               let bare_ty = Base(qid, bare_args, a) in
               let arg_preds_lst = decomposeListConjPred arg_preds in
               let preds = map (fn arg_preds ->
                                  mkAppl(mkOp(pred_qid, mkArrow(mkProduct(map (fn ty -> mkArrow(ty, boolType)) bare_args),
                                                                mkArrow(bare_ty, boolType))),
                                         arg_preds))
                             arg_preds_lst
               in
               mkSubtypePreds(bare_ty, preds, a, spc)
             | None ->
               (case tryUnfoldBase spc ty of
                  | None -> ty
                  | Some exp_ty ->
                    let raise_ty = if namedTypesRaised? then exp_ty else raiseSubtype(exp_ty, spc) in
                    if embed? Subtype raise_ty
                      then raise_ty else ty))
        else
          (case tryUnfoldBase spc ty of
             | None -> ty
             | Some exp_ty ->
               if namedTypesRaised?
                 then (if embed? Subtype exp_ty
                         then exp_ty else ty)
               else raiseSubtype(exp_ty, spc))
      | Subtype(s_ty, p, a) ->
        (case raiseSubtype(s_ty, spc) of
           | Subtype(sss_ty, pr, _) ->
             composeSubtypes(sss_ty, p, pr, a, spc)
           | _ -> ty)
      | Product(flds, a) ->
        if exists? (fn (_,tyi) -> subtype?(spc, tyi)) flds
          then let (bare_flds, arg_fld_vars, pred,_) =
                foldl (fn ((bare_flds, arg_fld_vars, pred, i),(id,tyi)) ->
                         case subtypeComps(spc, tyi) of
                           | Some(t,p) -> let v = ("xp"^show i, t)  in
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
               Subtype(Product(bare_flds,a), mkLambda(mkRecordPat arg_fld_vars, pred), a)
          else ty
 %     | Arrow(dom, rng ,a) ->
%        (case raiseSubtype(dom,spc) of
%           | Subtype(d,d_p,_) ->
%             %% Using d would be more natural, but then you have to change the type of all variable refs
%             %% to avoid unnecessary type annotation in Isabelle output (or else freeVars needs to be
%             %% fixed to ignore types
%             let f_ty = Arrow(dom,rng,a) in
%             Subtype(f_ty, mkSubtypeFnPredicate(d_p, f_ty, d, rng), a)
%           | _ -> ty)
      | _ -> ty


  op subtypePredicate(ty: MSType, spc: Spec): MSTerm =
    case raiseSubtype(ty, spc) of
      | Subtype(sup_ty, pred, _) -> pred
      | _ -> mkLambda(mkWildPat ty, trueTerm)

  op  instantiateTyVars: MSType * TyVarSubst -> MSType
  def instantiateTyVars(s,tyVarSubst) =
    case s of
      | TyVar (name, _) ->
	(case findLeftmost (fn (nm,_) -> nm = name) tyVarSubst of
	   | Some(_,ss) -> ss
	   | _ -> s)
      | _ -> s

  op instantiateTyVarsInType(ty: MSType, subst: TyVarSubst): MSType =
    mapType (id, fn ty -> instantiateTyVars(ty,subst), id) ty

  op instantiateTyVarsInTerm(tm: MSTerm, subst: TyVarSubst): MSTerm =
    mapTerm (id, fn ty -> instantiateTyVars(ty,subst), id) tm

  op instantiateTyVarsInPattern(pat: MSPattern, subst: TyVarSubst): MSPattern =
    mapPattern (id, fn ty -> instantiateTyVars(ty,subst), id) pat

  op typeMatch(s1: MSType, s2: MSType, spc: Spec, ign_subtypes?: Bool, unfold?: Bool): Option TyVarSubst =
   let def match(ty1: MSType, ty2: MSType, pairs: TyVarSubst): Option TyVarSubst =
        % let _ = if printType ty1 = "Bool" then writeLine(show unfold?^anyToString ty1^"\n =?= \n"^ anyToString ty2) else () in
        let result =
            case (ty1,ty2) of
              | (TyVar(id1,_), ty2) -> 
                (case (findLeftmost (fn (id,_) -> id = id1) pairs) of
                   | Some(_,mty1) -> if equalType?(mty1,ty2) then Some pairs else None  % TODO: should equalType? be equivType? ??
                   | None -> Some(Cons((id1,ty2),pairs)))
              | _ ->
            if equalType? (ty1,ty2) then Some pairs  % equivType? spc
            else
            case (ty1,ty2) of
              | (Arrow(t1,t2,_),Arrow(s1,s2,_)) ->
                (case match(t1,s1,pairs) of
                   | Some pairs -> match(t2,s2,pairs)
                   | None -> None)
              | (Product(r1,_),Product(r2,_)) | length r1 = length r2 -> 
                typeMatchL(r1,r2,pairs,fn((id1,s1),(id2,s2),pairs) ->
                                        if id1 = id2 then match(s1,s2,pairs)
                                          else None) 
              | (CoProduct(r1,_),CoProduct(r2,_)) | length r1 = length r2 -> 
                typeMatchL(r1,r2,pairs,
                           fn((id1,s1),(id2,s2),pairs) ->
                             if id1 = id2 then
                               (case (s1,s2) of
                                  | (None,None) -> Some pairs 
                                  | ((Some ss1),(Some ss2)) -> match(ss1,ss2,pairs)
                                  | _ -> None)
                             else None)
              | (Quotient(ty,t1,_),Quotient(ty2,t2,_)) -> 
                if equalTermAlpha?(t1,t2) then % not equivTerm?
                  match(ty,ty2,pairs)
                else 
                  None
              | (Subtype(ty,t1,_),Subtype(ty2,t2,_)) | equalTermAlpha?(t1,t2) ->  % not equivTerm?
                match(ty,ty2,pairs)
              | (Subtype(ty,_,_), ty2) | ign_subtypes? ->
                match(ty,ty2,pairs)
              | (ty1, Subtype(ty,_,_)) | ign_subtypes? ->
                match(ty1,ty,pairs)
              | (Base(id,ts,pos1),Base(id2,ts2,pos2)) ->
                if id = id2
                  then typeMatchL(ts,ts2,pairs,match)
                else
                  (case tryUnfoldBase spc ty2 of
                   | Some exp_ty2 -> match(ty1, exp_ty2, pairs)
                   | None ->
                     (case tryUnfoldBase spc ty1 of
                      | Some exp_ty1 -> match(exp_ty1, ty2, pairs)
                      | None -> None))
              | (_,Base _) | unfold? ->
                (case tryUnfoldBase spc ty2 of
                 | Some exp_ty2 -> match(ty1, exp_ty2, pairs)
                 | None -> None)
              | (Base _,_) | unfold? ->
                (case tryUnfoldBase spc ty1 of
                 | Some exp_ty1 -> match(exp_ty1, ty2, pairs)
                 | None -> None)
              | (Boolean _, Boolean _) -> Some pairs
              | _ -> None
        in
        % let _ = if printType ty1 = "Bool" then writeLine("Result: "^(show (some? result))) else () in
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

  % Build a term for the op qid at type ty
  op mkOpFromDef(qid: QualifiedId, ty: MSType, spc: Spec): MSTerm =
    case findTheOp(spc, qid) of
      | Some opinfo ->
        (let (tvs,ty1,_) = unpackFirstOpDef opinfo in
         case typeMatch(ty1,ty,spc,true,true) of
           | Some subst ->
             let inst_ty = instantiateTyVarsInType(ty1, subst) in
             mkInfixOp(qid, opinfo.fixity, inst_ty)
           | None ->  mkOp(qid, ty)) 
      | _ -> mkOp(qid, ty)

  op termSize (t: MSTerm): Nat =
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
        let n = name ^ (show i) in
        if exists? (fn m -> n = m) names then
          loop (i + 1)
        else 
          n
    in
      loop 1

  op knownNonEmptyBaseTypes: QualifiedIds =
    [Qualified("Bool",    "Bool"),   
     Qualified("Integer", "Int"),   
     Qualified("Nat",     "Nat"), 
     Qualified("Char",    "Char"),
     Qualified("String",  "String"), 
     Qualified("List",    "List"), 
     Qualified("Option",  "Option")]

  op builtinBaseTypes: QualifiedIds =
    [Qualified("Integer", "Int"), 
     Qualified("Char",    "Char"),
     Qualified("String",  "String")]

  op existsOpWithType?(ty: MSType, spc: Spec): Bool =
    foldriAQualifierMap
      (fn (q, id, info, result) ->
         result
        || (possiblySubtypeOf?(firstOpDefInnerType info, ty, spc) ))
      false spc.ops

  op existsTrueExistentialAxiomForType?(ty: MSType, spc: Spec): Bool =
    foldlSpecElements (fn (result,el) ->
                         result || (case el of
                                      | Property(Axiom, _, _,
                                                 Bind(Exists, [(_,ex_ty)], Fun(Bool true,_,_), _),_) ->
                                        equalType?(ex_ty, ty)
                                      | _ -> false))
      false spc.elements

 op knownNonEmpty?(ty: MSType, spc: Spec): Bool =
    case ty of
      | Base(qid,tvs,_) ->
        qid in? knownNonEmptyBaseTypes
          || tvs ~= []                  % Not completely safe
          || (case findTheType(spc, qid) of
                | Some info ->
                  knownNonEmpty?(info.dfn, spc)
                | _ ->
                  % let _ = writeLine("Warning: knownNonEmpty? saw ref to undefined type: " ^ show qid) in
                  false)
          || existsOpWithType?(ty, spc)
         %% Leave out for now as it messes up emptyTypesToSubtypes
         %% || existsTrueExistentialAxiomForType?(ty, spc)
      | Boolean _ -> true
      | Quotient(sty,_,_) -> knownNonEmpty?(sty, spc)
      | Pi(_,sty,_) -> knownNonEmpty?(sty, spc)
      | And(sty::_,_) -> knownNonEmpty?(sty, spc)
      | Subtype(Base(qid,_,_), pred, _) | qid in? knownNonEmptyBaseTypes ->
        knownNotAlwaysFalse?(pred, spc)
      | Subtype _ -> false
      | TyVar _ -> false
      | Any _ -> false
      | _ -> true

 op knownNotAlwaysFalsePreds: QualifiedIds =
   []

 %% Currently ad-hoc
 op knownNotAlwaysFalse?(pred: MSTerm, spc: Spec): Bool =
   case pred of
     | Fun(Op(qid, _), _, _) -> qid in? knownNotAlwaysFalsePreds
     | Apply(Fun(Op(Qualified("Nat", fitsInNBits?), _), _, _), Fun(Nat i, _, _), _) -> i ~= 0
     | _ -> false

 op constructorTerm? (spc: Spec) (tm: MSTerm): Bool =
   some?(constructorTerm spc tm)

 op constructorTerm (spc: Spec) (tm: MSTerm): Option(QualifiedId * QualifiedIds) =
   case tm of
     | Fun(Embed (qid, _), _, _) -> Some(qid, [])
     | Apply(Fun(Embed(qid, _), _, _), _, _)  -> Some(qid, [])
     | Fun(f as Op(qid, Constructor0), ty, _) -> Some(qid, [])
     | Fun(f as Op(qid, Constructor1), ty, _) -> Some(qid, [])
     | Fun(f as Op(qid, _), ty, _) ->
       (case findTheOp(spc, qid) of
          | None -> None
          | Some info ->
        case constructorFun?(f, ty, spc) of
          | Some f -> Some(qid, [])
          | None -> 
        let (_, _, dfn) = unpackFirstTerm info.dfn in
        case constructorTerm spc dfn of
          | None -> None
          | Some(id, qids) -> Some(id, qid :: qids))
     | Apply(f as Fun(Op _, _, _), _, _) -> constructorTerm spc f
     | _ -> None

 op constructorOfType? (spc: Spec) (op_qid: QualifiedId) (ty: MSType): Bool =
   let def checkIfCoProduct ty_qid =
         case findTheType(spc, ty_qid) of
           | None -> false
           | Some ty_info ->
         case unpackType(ty_info.dfn) of
           | (_, CoProduct(fields, _)) ->
             some?(findLeftmost (fn (fld_qid, _) -> op_qid = fld_qid) fields) 
           | (_, Base(ty_qid1, _, _)) -> checkIfCoProduct ty_qid1
           | (_, Subtype(Base(ty_qid1, _, _), _, _)) -> checkIfCoProduct ty_qid1
           | _ -> false
   in
   case ty of
     | Base(qid, _, _) -> checkIfCoProduct qid
     | Arrow(_, Base(qid, _, _), _) -> checkIfCoProduct qid
     | _ -> false

 op constructorFun?(f: MSFun, ty: MSType, spc: Spec): Option(MSFun) =
  case f of
    | Op(op_qid, _) ->
      let def checkIfCoProductQId ty_qid =
            case findTheType(spc, ty_qid) of
              | None -> None
              | Some ty_info ->
            case unpackType(ty_info.dfn) of
              | (_, CoProduct(fields, _)) ->
                (case findLeftmost (fn (fld_qid, _) -> op_qid = fld_qid) fields of
                   | Some(_, o_arg) -> Some(Embed(op_qid, some? o_arg))
                   | None -> None)
              | (_, Base(ty_qid1, _, _)) -> checkIfCoProductQId ty_qid1
              | (_, Subtype(Base(ty_qid1, _, _), _, _)) -> checkIfCoProductQId ty_qid1
              | _ -> None
          def checkIfCoProduct ty =
            case ty of
              | Base(qid, _, _) -> checkIfCoProductQId qid
              | Arrow(_, s_ty, _) -> checkIfCoProduct s_ty
              | Subtype(s_ty, _, _) -> checkIfCoProduct s_ty
              | _ -> None
      in
      checkIfCoProduct ty
    | (Embed _) -> Some f
    | _ -> None

%% True for nullary polymorphic constructors such as Nil
op nullPolyConstructorFun?(f: MSFun, ty: MSType, spc: Spec): Bool =
  let def checkIfNullPolyQId (op_qid, ty_qid) =
        case findTheType(spc, ty_qid) of
          | None -> false
          | Some ty_info ->
        case unpackType(ty_info.dfn) of
          | (_::_, CoProduct(fields, _)) ->
            (case findLeftmost (fn (fld_qid, _) -> op_qid = fld_qid) fields of
               | Some(_, None) -> true
               | None -> false)
          | (_::_, Base(ty_qid1, _, _)) -> checkIfNullPolyQId(op_qid, ty_qid1)
          | (_::_, Subtype(Base(ty_qid1, _, _), _, _)) -> checkIfNullPolyQId(op_qid, ty_qid1)
          | _ -> false
      def checkIfNullPoly(op_qid, ty) =
        case ty of
          | Base(qid, _, _) -> checkIfNullPolyQId(op_qid, qid)
          | Arrow(_, s_ty, _) -> checkIfNullPoly(op_qid, s_ty)
          | Subtype(s_ty, _, _) -> checkIfNullPoly(op_qid, s_ty)
          | _ -> false
  in
  case f of
    | Op(op_qid, _) -> checkIfNullPoly(op_qid, ty)
    | Embed(qid, false) -> checkIfNullPoly(qid, ty)
    | _ -> false

 op explicateEmbed (spc: Spec) (tm: MSTerm): MSTerm =
   case tm of
    | Fun(Op(op_qid, _), ty, a) ->
      let def checkIfCoProduct ty_qid =
            case findTheType(spc, ty_qid) of
              | None -> tm
              | Some ty_info ->
            case unpackType(ty_info.dfn) of
              | (_, CoProduct(fields, _)) ->
                (case findLeftmost (fn (fld_qid, _) -> op_qid = fld_qid) fields of
                   | Some(_, o_arg) -> Fun(Embed(op_qid, some? o_arg), ty, a)
                   | None -> tm)
              | (_, Base(ty_qid1, _, _)) -> checkIfCoProduct ty_qid1
              | (_, Subtype(Base(ty_qid1, _, _), _, _)) -> checkIfCoProduct ty_qid1
              | _ -> tm
      in
      (case ty of
         | Base(qid, _, _) -> checkIfCoProduct qid
         | Arrow(_, Base(qid, _, _), _) -> checkIfCoProduct qid
         | _ -> tm)
    | _ -> tm

 op explicateEmbeds (spc: Spec): Spec =
   mapSpec (explicateEmbed spc, id, id) spc

 op constructorOp? (spc: Spec) (qid: QualifiedId): Bool =
   case findTheOp(spc, qid)of
     | None -> false
     | Some info ->
       let (_, ty, _) = unpackFirstTerm info.dfn in
       constructorOfType? spc qid ty

 op removeImplicitConstructorOps (spc: Spec): Spec =
   setElements(spc, filter (fn el ->
                            case el of
                              | Op(qid, _, _) ->
                                ~(constructorOp? spc qid)
                              | _ -> true)
                      spc.elements)

 op constructorFn?(spc: Spec) (tm: MSTerm): Bool =
   case tm of
     | Fun(f, ty, _) -> some?(constructorFun? (f, ty, spc))
     | _ -> false

 type MatchResult = | Match MSVarSubst | NoMatch | DontKnow

 op patternMatch(pat: MSPattern, N: MSTerm, S: MSVarSubst, constrs: QualifiedIds): MatchResult = 
     case pat
       of VarPat(x, _) -> Match(Cons((x,N),S))
	| WildPat _ -> Match S
	| RecordPat(fields, _) -> 
	  let fields2 = map (fn (l,p) -> (l,patternType p,p)) fields in
	  let ty = Product(map (fn (l,s,_) -> (l,s)) fields2,noPos) in
	  let 
	      def loop(fields,S) : MatchResult = 
	          case fields
		    of (l,s,p)::fields ->
			let N =
			    (case N
			       of Record(NFields,_) -> findField(l,NFields)
		                | _ -> Apply(Fun(Project l,Arrow(ty,s,noPos),noPos),N,noPos)) in
		        (case patternMatch(p, N, S, constrs)
			   of Match S -> loop(fields,S)
			    | r -> r)
		     | [] -> Match S
	  in
	  loop(fields2,S)
	| EmbedPat(lbl,None,ty,_) -> 
	  (case N
	     | Fun(Embed(lbl2,_),_,_) -> if lbl = lbl2 then Match S else NoMatch
	     | Apply(Fun(Embed(_,true),_,_),_,_) -> NoMatch
	     | Fun(Op(lbl2,_),_,_) ->
               if lbl = lbl2 then Match S
               else if lbl2 in? constrs then NoMatch
               else DontKnow
	     | Apply(Fun(Op(lbl2,_),_,_),_,_) | lbl2 in? constrs -> NoMatch
	     | _ -> DontKnow)
	| EmbedPat(lbl,Some p,ty,_) -> 
	  (case N
             | Fun(Embed(lbl2,_),_,_) -> NoMatch
             | Apply(Fun(Embed(lbl2,true),_,_),N2,_) -> 
               if lbl = lbl2 
                 then patternMatch(p, N2, S, constrs)
               else NoMatch
             | Fun(Op(lbl2,_),_,_) |  lbl2 in? constrs -> NoMatch
             | Apply(Fun(Op(lbl2,_),_,_),N2,_) -> 
               if lbl = lbl2 
                 then patternMatch(p, N2, S, constrs)
               else if lbl2 in? constrs then NoMatch
               else DontKnow
             | _ -> DontKnow)
        | RestrictedPat(p,_,_) ->
          (case patternMatch(p, N, S, constrs) of
             %% Assume we can't decide predicate
             | NoMatch -> NoMatch
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
        | TypedPat(p1, _, _) -> patternMatch(p1, N, S, constrs)
	| _ -> DontKnow

 op constrsInPattern(pat: MSPattern): QualifiedIds =
   foldSubPatterns (fn | (EmbedPat(qid,_,_,_), qids) | qid nin? qids -> qid :: qids
                       | (_, qids) -> qids)
     [] pat

 op  patternMatchRules : MSMatch * MSTerm -> Option (MSVarSubst * MSTerm)
 def patternMatchRules(rules,N) =
   let constrs = foldl (fn (constrs, (pat,_,_)) ->
                        constrsInPattern pat ++ constrs)
                   [] rules
   in
   let def aux rules =
         case rules 
           of [] -> None
            | (pat,Fun(Bool true,_,_),body)::rules -> 
              (case patternMatch(pat, N, [], constrs)
                 of Match S -> Some(S,body)
                  | NoMatch -> aux rules
                  | DontKnow -> None)
            | _ :: rules -> None
   in
   aux rules

  op [a] mergeSomeLists(ol1: Option(List a), ol2: Option(List a)): Option(List a) =
    case (ol1, ol2) of
      | (Some l1, Some l2) -> Some(l1 ++ l2)
      | _ -> None

  %% ignores types
  op matchPatterns(p1: MSPattern, p2: MSPattern): Option MSVarSubst =
    if equalPatternStruct?(p1, p2) then Some []
      else
      case (p1, p2) of
        | (VarPat(v1, a), VarPat(v2, _)) ->
          Some(if equalVarStruct?(v1, v2) then []
               else [(v2, Var(v1, a))])
        | (RecordPat(xs1,_), RecordPat(xs2,_)) ->
          foldl (fn (result, ((label1, x1), (label2, x2))) ->
                  case result of
                    | None -> None
                    | Some sb ->
                  if label1 = label2 then mergeSomeLists(result, matchPatterns(x1, x2))
                   else None)
            (Some []) (zip(xs1, xs2))
        | (_, WildPat _) -> Some []
        | (RestrictedPat(x1, t1, _), _) -> matchPatterns(x1, p2)
        | (_, RestrictedPat(x2, t2, _)) -> matchPatterns(p1, x2)
        | (TypedPat(x1, _, _), _) -> matchPatterns(x1, p2)
        | (_, TypedPat(x2, _, _)) -> matchPatterns(p1, x2)
        | _ -> None

  op topLevelOpNames(spc: Spec): QualifiedIds =
    mapPartial (fn el ->
                  case el of
                    | Op(qid, _, _) -> Some qid
                    | OpDef(qid, _, _, _) -> Some qid
                    | _ -> None)
     spc.elements

  op topLevelTypeNames(spc: Spec): QualifiedIds =
    mapPartial (fn el ->
                  case el of
                    | Type(qid, _) -> Some qid
                    | TypeDef(qid, _) -> Some qid
                    | _ -> None)
     spc.elements

 op boolType?(spc: Spec, ty: MSType): Bool =
   case ty of
     | Boolean _ -> true
     | Base _ ->
       (case tryUnfoldBase spc ty of
          | Some uf_ty -> boolType?(spc, uf_ty)
          | None -> false)
     | _ -> false

 op unconditionalPattern?(pat: MSPattern): Bool =
   case pat of
     | WildPat _ -> true
     | VarPat _  -> true
     | RecordPat(prs, _) -> forall? (fn (_,p) -> unconditionalPattern? p) prs
     | AliasPat(p1, p2, _) -> unconditionalPattern? p1 && unconditionalPattern? p2
     | _ -> false

 op exhaustivePatterns?(pats: MSPatterns, ty: MSType, spc: Spec): Bool =
   pats ~= []
    && ( unconditionalPattern?(last pats)
     || (case (pats, subtypeComps(spc, ty)) of
           | ([RestrictedPat(pat, ty_tm,_)], Some(_, pat_pred)) -> 
             let ty_pred = mkLambda(pat, ty_tm) in
             let equiv? = equivTerm? spc (ty_pred, pat_pred) in
             % let _ = writeLine(printTerm ty_pred^(if equiv? then " == " else " =~= ")^printTerm pat_pred) in
             equiv?
           | _ ->
         case coproductOpt(spc, ty) of
           | Some(id_prs) ->
             forall? (fn (id_ty, o_id_arg_ty) ->
                        exists? (fn p ->
                                   case p of
                                     | EmbedPat(id_p, None, _, _) ->
                                       id_ty = id_p
                                     | EmbedPat(id_p, Some p_s, _, _) ->
                                       id_ty = id_p && unconditionalPattern? p_s
                                     | _ -> false)
                          pats
                       || (case o_id_arg_ty of
                             | None -> false
                             | Some id_arg_ty ->
                           exhaustivePatterns?(mapPartial (fn p ->
                                                             case p of
                                                               | EmbedPat(id_p, Some p_s, _, _) | id_ty = id_p ->
                                                                 Some p_s
                                                               | _ -> None)
                                                 pats,
                                               id_arg_ty, spc)))
               id_prs
           | None ->
          if boolType?(spc, ty)
           then length pats = 2
               && exists? (fn p -> case p of
                                   | BoolPat(true, _) -> true
                                   | _ -> false)
                    pats
               && exists? (fn p -> case p of
                                   | BoolPat(false, _) -> true
                                   | _ -> false)
                    pats
           else false))
    

  op makeQualifierFromPat(old_qual: String, new_pat: String): String =
    %% Syntax doesn't allow a * on its own in general
    let new_pat = replaceString(new_pat, "*_", "*") in
    let new_pat = replaceString(new_pat, "_*", "*") in
    if old_qual = UnQualified
      then replaceString(new_pat, "*", "")
      else replaceString(new_pat, "*", old_qual)

  op makeDerivedQId (spc: Spec) (Qualified (qual,id): QualifiedId) (newOptQual : Option String): QualifiedId =
    case newOptQual of
      | None -> Qualified (qual, id ^ "'")
      | Some newQual -> Qualified (makeQualifierFromPat(qual, newQual),id)

 op idPatternMatch(qual: Id, pattern: String): Option String =
   let qual_len = length qual in
   let pat_len =  length pattern in
   case search("_*_", pattern) of       % foo_*_fum foofiefum  i=3
     | Some i ->
       if subseqEqual?(pattern, qual, 0, i, 0) && subseqEqual?(pattern, qual, i+3, pat_len, qual_len - (pat_len - (i + 3)))
         then let final = qual_len - (pat_len - (i + 3)) in
              Some(if i = final then UnQualified else subFromTo(qual, i, final))
         else None
     | None ->
   case search("_*", pattern) of        % foo_* foofie   i=3
     | Some i ->
       if subseqEqual?(pattern, qual, 0, i, 0)
         then Some(if i = qual_len then UnQualified else subFromTo(qual, i, qual_len))
         else None
     | None ->
   case search("*_", pattern) of        % *_foo fiefoo   i=0
     | Some i ->
       if testSubseqEqual?(pattern, qual, i+2, qual_len - (pat_len - 2))
         then let final = qual_len - (pat_len - (i + 2)) in
              Some(if final = 0 then UnQualified else subFromTo(qual, 0, final))
         else None
     | None -> if qual = pattern then Some "" else None

 op derivedQId?(Qualified (qual,id): QualifiedId, newOptQual: Option String, spc: Spec): Bool =
   case newOptQual of
     | None ->
       let len = length id in
       id@(len - 1) = #' && some?(findTheOp(spc, Qualified (qual, subFromTo(id, 0, len - 1))))
     | Some newQual ->
   case idPatternMatch(qual, newQual) of
     | None -> false
     | Some(old_qual) -> old_qual = ""    % Don't know what old qualifier was
                       || some?(findTheOp(spc, Qualified(old_qual, id)))

 op varSubstFromTerms(old_tm: MSTerm, new_tm: MSTerm): MSVarSubst =
   let def match(old_tm, new_tm, sbst) =
         case (old_tm, new_tm) of
           | (Lambda([(old_pat, _, old_ptm)], _), Lambda([(new_pat, _, new_ptm)], _)) ->
             (case matchPatterns(new_pat, old_pat) of
               | None -> sbst
               | Some sbst1 ->
                 match(old_ptm, new_ptm, sbst ++ sbst1))
           | _ -> sbst
   in
   match(old_tm, new_tm, []) 

op combineSubTypes(old_ty: MSType, new_ty: MSType, old_tm: MSTerm, new_tm: MSTerm): MSType =
   let sbst = varSubstFromTerms(old_tm, new_tm) in
   let old_ty = mapType (fn t -> substitute(t, sbst), id, id) old_ty in
   let def combineTypes(old_ty, new_ty, add_preds?) =
         if equalType?(old_ty, new_ty) then new_ty
         else
         % let _ = writeLine("combine:\n"^printType old_ty^"\n"^printType new_ty) in
         case (old_ty, new_ty) of
           | (_, MetaTyVar _) -> old_ty
           | (Arrow(old_d, old_r, _), Arrow(new_d, new_r, a)) ->
              Arrow(combineTypes(old_d, new_d, false), combineTypes(old_r, new_r, add_preds?), a)
             % Arrow(new_d, combineTypes(old_r, new_r), a)
           | (Subtype(old_sup, old_p, _), Subtype(new_sup, new_p, a)) ->
             Subtype(new_sup, combinePreds(old_p, new_p, add_preds?), a)
           | (Subtype _, _) -> old_ty
           | _ -> if existsInType? (embed? MetaTyVar) new_ty
                    then old_ty else new_ty
       def combinePreds(old_p, new_p, add_preds?) =
         case (old_p, new_p) of
           | (Lambda([(old_pat, _, old_ptm)], _), Lambda([(new_pat, c, new_ptm)], a)) ->
             (case matchPatterns(new_pat, old_pat) of
               | None -> new_p
               | Some sb ->
              let comb_bool = if add_preds? then combineBool(substitute(old_ptm, sb), new_ptm) else new_ptm in
              Lambda([(new_pat, c, comb_bool)], a))
           | (Lambda _, _) -> old_p
           | _ -> new_p
       def combineBool(old_b, new_b) =
         case old_b of
           | IfThenElse(p, q, r, a) ->
             IfThenElse(p, combineBool(q, new_b), combineBool(r, new_b), a)
           | _ -> mkSimpConj(getConjuncts old_b ++ getConjuncts new_b)
    in
    combineTypes(old_ty, new_ty, true) 

op substVarNames(old_tm: MSTerm, new_tm: MSTerm): MSTerm =
  let def subst(old_tm, new_tm, sbst) =
         case (old_tm, new_tm) of
           | (Lambda([(old_pat, _, old_ptm)], _), Lambda([(new_pat, cnd, new_ptm)], _)) ->
             (case matchPatterns(new_pat, old_pat) of
               | None -> substitute(old_tm, sbst)
               | Some sbst1 ->
                 mkLambda(new_pat, subst(old_ptm, new_ptm, sbst ++ sbst1)))
           | _ -> substitute(old_tm, sbst)
   in
   subst(old_tm, new_tm, []) 

op getPostCondn(ty: MSType, spc: Spec): Option(MSPattern * MSTerm) =
  case range_*(spc, ty, false) of
    | Subtype(result_ty, Lambda([(pat, _, condn)], _), _) -> Some(pat, condn)
    | _ -> None

 def evaluableQualifiers = ["Nat", "Integer", "IntegerAux", "String", "Char", "System", "Bool"]

%% Initialized by initializeInterpreterBaseAux in toplevel.lisp
op MSInterpreter.interpreterBaseSpec: Spec = emptySpec

op findTheOpInterp(spc: Spec, qid: QualifiedId): Option OpInfo =
  case findTheOp (interpreterBaseSpec, qid) of
    | None -> findTheOp (spc, qid)
    | v -> v

op nonExecutableTerm1? (tm: MSTerm): Bool =
  existsSubTerm  (fn t ->
                    case t of
                      | Bind _ -> true
                      | The _ -> true
                      | Any _ -> true
                      %% This case really should be generalized (see below) but needs spc argument
                      | Fun(f, Arrow(Product([("1", Arrow _), _], _), _, _), _)
                          | embed? Equals f || embed? NotEquals f ->
                        true
                      | _ -> false)
    tm

op nonExecutableTerm? (spc: Spec) (tm: MSTerm): Bool =
  let def nonEx?(t: MSTerm, seen: QualifiedIds): Bool =
        % let _ = writeLine(printTerm t) in
        existsSubTerm2 false
                       (fn t ->
                         case t of
                           | Bind _ -> true
                           | The _ -> true
                           | Any _ -> true
                           | Fun(f, ty, _) | embed? Equals f || embed? NotEquals f ->
                             (case arrowOpt(spc, ty) of
                                | Some(Product([("1", e_ty), _], _), _) ->
                                  some?(arrowOpt(spc, e_ty))
                                | _ -> false)
                           | Fun(Op(qid as Qualified(qual, _), _), _, _)
                               | qual in? evaluableQualifiers && some?(findTheOp(getBaseSpec(), qid)) -> false
                           | Fun(Op(qid, _), _, _) ->
                             if qid in? seen then false
                               else (case findTheOpInterp(spc, qid) of
                                       | Some info ->
                                         let (_, _, d_tm) = unpackFirstTerm info.dfn in
                                         let r = 
                                           nonEx?(d_tm, qid::seen)
                                           && printPackageId(qid, "") nin? SuppressGeneratedDefuns
                                         in
                                         %let _ =
                                         %  if r then writeLine("non-executable " ^ printPackageId(qid, "")) else () in
                                         r
                                       | None -> false    % Assume defined in Lisp?
                                         )
                           | _ -> false)
          t
  in
  let result = nonEx?(tm, []) in
  % let _ = writeLine("Term is "^(if result then "not " else "")^"executable.\n"^printTerm tm) in
  result

 type PathTerm.PathTerm     % Defined in /Languages/MetaSlang/AbstractSyntax/PathTerm.sw
 type Proof.Tactic          % Defined in /Languages/MetaSlang/Specs/Proof
 type TraceFlag = Bool
 type TransOpName = QualifiedId
 type TransTerm = MSTerm

(* Support for /Languages/MetaSlang/Transformations/MetaTransform: These are needed for dumping info about transform fns *)
 type MetaTransform.AnnTypeValue =
    | SpecV Spec
    | MorphismV Morphism
    | TermV MSTerm
    | TransTermV TransTerm
    | PathTermV PathTerm
    | ArrowsV (List AnnTypeValue)
    | StrV String
    | NumV Int
    | BoolV Bool
    | TraceFlagV Bool
    | OpNameV QualifiedId
    | TransOpNameV QualifiedId
    | RuleV RuleSpec
    | ProofV Proof
    | TacticV Tactic
    | OptV (Option AnnTypeValue)
    | ListV (List AnnTypeValue)
    | TupleV (List AnnTypeValue)
    | RecV List(String * AnnTypeValue)
    | MonadV (Env AnnTypeValue)

 op MetaTransform.extractSpec(SpecV x: AnnTypeValue): Spec = x
 op MetaTransform.extractMorphism(MorphismV x: AnnTypeValue): Morphism = x
 op MetaTransform.extractTerm(TermV x: AnnTypeValue): MSTerm = x
 op MetaTransform.extractTransTerm(TransTermV x: AnnTypeValue): TransTerm = x
 op MetaTransform.extractPathTerm(PathTermV x: AnnTypeValue): PathTerm = x
 op MetaTransform.extractStr(StrV x: AnnTypeValue): String = x
 op MetaTransform.extractNum(NumV x: AnnTypeValue): Int = x
 op MetaTransform.extractBool(BoolV x: AnnTypeValue): Bool = x
 op MetaTransform.extractTraceFlag(TraceFlagV x: AnnTypeValue): TraceFlag = x
 op MetaTransform.extractOpName(OpNameV x: AnnTypeValue): QualifiedId = x
 op MetaTransform.extractTransOpName(TransOpNameV x: AnnTypeValue): TransOpName = x
 op MetaTransform.extractRule(RuleV x: AnnTypeValue): RuleSpec = x
 op MetaTransform.extractRefinementProof(ProofV x: AnnTypeValue): Proof = x
 op MetaTransform.extractProofTactic(TacticV x: AnnTypeValue): Tactic = x
 op [a] MetaTransform.extractOpt(extr_val: AnnTypeValue -> a) (OptV x: AnnTypeValue): Option a = mapOption extr_val x
 op [a] MetaTransform.extractList(extr_val: AnnTypeValue -> a) (ListV x: AnnTypeValue): List a = map extr_val x
 %op [a] extractOpt(extr_val: AnnTypeValue -> a) (OptV x: AnnTypeValue): Option a = mapOption extr_val x

 op dummyQualifiedId: QualifiedId = Qualified("", "")
 op dummyMSTerm: MSTerm = Any noPos
 op dummySpec: Spec = emptySpec

 % Make a fresh name for a refined op
 op refinedQID (refine_num: Nat) (qid as Qualified(q, nm): QualifiedId): QualifiedId =
   if refine_num = 0 then qid
     else Qualified(q,nm^"__"^show refine_num)

#translate lisp
-verbatim
(defmacro Utilities::assumingNoSideEffects (fm)
  `(let ((Utilities::assumeNoSideEffects? t))
     (declare (special Utilities::assumeNoSideEffects?))
     ,fm))

-end
-morphism
op Utilities.assumingNoSideEffects -> Utilities::assumingNoSideEffects

#end

end-spec
