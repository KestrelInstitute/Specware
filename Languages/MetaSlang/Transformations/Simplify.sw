%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

(*
 *  Simplify term with respect to simple optimizations.
 *  Assume that all variables occur uniquely, that is, 
 *  they have unique names.

    These are very ad hoc simplifications and should be accomodated more systematically.


    Var to var definitions:
	let x = y in e 			

		is simplified to e[y/x]

    Restrict(var) to var definitions:

	let x = restrict(y) in e 	

		is simplified to e[restrict(y)/x]

----------- New ---------------------

    Dead code elimination:

	let x = e in e'			

		is simplified to e' if x is not free in e' and e does not have effects.

    Tuple instantiation:

	let z = (x,y) in [... e[project(1)z,project(2)(z)] ...]		
					

		is simplified to 

	let x_1 = x in 
	let y_1 = y in 
	let z = (x_1,y_1) in [ ... e[x_1,y_1] ...]


    Single threaded in-lining

	let x = e in e'[x]		

		is simplified to e'[e] if x occurs only once and does not have side effects.



  rewrite1: rewrite(`let ^(Varpat x) = ^(Var y) in z`, mapTerm(replace,Id,Id) `z`)
  rewrite2: rewrite(`let ....`)  



 *)

Simplify qualifying
spec
 import ../Specs/Environment
 import ../Specs/Utilities

 op  countVarRefs: MS.Term * Var -> Nat
 def countVarRefs(term,v) =
   let occ = Ref 0 : Ref Nat in
   let
     def occurs(term) = 
       case term
	 of Var (v2,_) -> 
	   (occ := (! occ) + (if equalVar?(v, v2) then 1 else 0); term)
	  | _ -> term
   in
     let _ = mapSubTerms occurs term in
     ! occ

 op  removeUnnecessaryVariable: Spec -> MS.Term -> MS.Term
 def removeUnnecessaryVariable spc term =
     % let _ = if traceSimplify? then writeLine("ruv: "^printTerm term) else () in
     case term
       of Let([(VarPat (v,_),e)],body,_) ->
	  let noSideEffects = sideEffectFree(e) || embed? Lambda e in
	  (case countVarRefs(body,v)
	     of 0 -> if noSideEffects then body else term
	      | 1 -> if noSideEffects
	                 || noInterveningSideEffectsBefore?
			      (body,fn (Var (v2,_)) -> v = v2
			             | _ -> false)
	               then %let _ = if embed? Lambda e then writeLine("ruv: \n"^printTerm term) else () in
                            let result = simplifyOne spc (substitute(body,[(v,e)])) in
                            %let _ = if embed? Lambda e then writeLine("--> \n"^printTerm (substitute(body,[(v,e)]))
                            %                                            ^"\n"^printTerm result) else () in
                            result
		       else term
	      | _ -> term)
        | Let ([(WildPat _,e)], body, _) ->
          if sideEffectFree(e) then body else term
	| _ -> term

  op noInterveningSideEffectsBefore?: MS.Term * (MS.Term -> Boolean) -> Boolean 
  def noInterveningSideEffectsBefore?(tm,p) =
    %% examine terms in execution order until either p is true or a possibly side-effection
    %% term is encountered
    let result =
        foldSubTermsEvalOrder
          (fn (t,result as (noSideEffectsYet?,done?)) ->
	     if done? then result
	     else if p t then (true,true)
	     else
	     case t of
	       | Apply(Fun(Embed _,_,_),_,_) -> result
	       % case
	       | Apply(Lambda _,_,_) -> result
	       %% We don't know in general when an application can cause a side-effect 
	       | Apply(Fun (f,_,_),_,_) ->
	         if knownSideEffectFreeFn? f then result else (false,true)
	       | Apply _ -> (false,true)
	       %% We don't know when the body of a lambda will be evaluated
	       | Lambda _ -> (false,true)
	       | _ -> result)
	  (true,false)
	  tm
    in result.1

% We implement a version of tuple instantiation that works on terms after pattern 
% matching compilation such that all references to let (u,v) = z in .. are of the
% form let u = project(1) z, v = project(2) z in ..
%
 op  tupleInstantiate: Spec -> MS.Term -> MS.Term
 op tupleInstantiate (spc: Spec) (term:  MS.Term): MS.Term =
   let
      def elimTuple(zId,srt,fields,body) =
        let (zId,body) =
            if member(zId,boundVarNamesIn body)
              then
                let new_zid = zId^"__sb" in  % Avoid variable capture!
                (new_zid, substitute(body,[((zId,srt), mkVar(new_zid,srt))]))
              else (zId,body)
        in
        let
            def mkField(id,srt) = 
                let name = zId^"_field_"^id in
                let v = (name,srt) in
                (v,mkVar v)
        in
        let varFields = 
            case productOpt(spc,srt)
              of Some fields -> map mkField fields 
               | _ -> fail ("Product sort expected for let bound variable. Found "^printSort srt)
        in
        let allFields = zip(fields,varFields) in
        let
           def findField(id,fields) = 
               case fields
                 of [] -> System.fail ("Field identifier "^id^" was not found")
                  | ((id2,_),(v,vTerm))::fields -> 
                    if id = id2 then vTerm else findField(id,fields)
        in
        let
           def substField(term) = 
               case term
                 of Apply(Fun(Project id,_,_), Var((zzId,_),_),_) -> 
                    if zId = zzId
                       then findField(id,allFields)
                    else term
                  | _ -> term
        in
        let varDecls = List.map (fn((id,t),(v,vTerm))-> (mkVarPat v,t)) allFields in
        let zDecl    = (mkVarPat(zId,srt),
                        mkRecord(List.map (fn((id,_),(_,vTerm))-> (id,vTerm)) allFields)) 
        in
        let newBody = mapSubTerms substField body in
        let newTerm = mkLet([zDecl],newBody) in
        let newTerm = removeUnnecessaryVariable spc newTerm  in
        %let _ = writeLine("newTerm2:\n"^printTerm newTerm) in
        mkLet(varDecls,newTerm)
   in
   case term
     of Let([((VarPat((zId,srt),_)),Record(fields,_))],body,_)
          | existsSubTerm (fn t -> case t of
                                     | Apply(Fun(Project id,_,_), Var((zzId,_),_),_) -> 
                                       zId = zzId
                                     | _ -> false)
              body
        -> 
        %let _ = writeLine(printTerm term) in
        simplifyOne spc (elimTuple(zId,srt,fields,body))
      | Let([(VarPat((zId,srt),_),
              Apply(Fun(Op(Qualified("TranslationBuiltIn","mkTuple"),_),_,_),
                    Record(fields,_),_))],body,_) -> 
        simplifyOne spc (elimTuple(zId,srt,fields,body))
      | _ -> term

 op  simplifyOne: Spec -> MS.Term -> MS.Term
 def simplifyOne spc term =
     % let _ = if traceSimplify? then writeLine("s1: "^printTerm term) else () in
     case tryEvalOne spc term of
       | Some cterm -> cterm
       | _ ->
     case term of
       | Let(all_decls as decl1::decl2::decls,body,_) ->
         let bndvars  = foldl (fn (pvs, (p, _)) -> patternVars p ++ pvs) [] all_decls in
         if exists? (fn (_, t) -> hasVarNameConflict?(t, bndvars)) all_decls
           then  %% Rename to avoid name overload 
             simplifyOne spc (substitute(term, map (fn v -> (v, mkVar v)) bndvars))
         else
	 simplifyOne spc (mkLet([decl1],simplifyOne spc (mkLet(Cons(decl2,decls),body))))
       %% let (x,y) = (w,z) in f(x,y) -> f(w,z)
       | Let([(pat as RecordPat(pflds, _), tm as Record(tflds, _))], body, pos)
           | varRecordPattern? pat && varRecordTerm? tm ->
         let new_decls = map (fn ((_,p), (_,t)) -> (p,t)) (zip(pflds, tflds)) in
         simplifyOne spc (Let(new_decls, body, pos))
       %% let y = x in f y  --> f x
       | Let([(VarPat(v,_),wVar as (Var(w,_)))],body,pos) ->
	 substitute(body,[(v,wVar)])
       %% Normalize simple lambda application to let
       | Apply(Lambda([(VarPat vp,_,body)],_),t,pos) ->
	 simplifyOne spc (Let([(VarPat vp,t)],body,pos))
       %% case y of _ -> z  -->  z if y side-effect free
       | Apply(Lambda([(WildPat(_,_),_,body)],_),tm,_) ->
	 if sideEffectFree tm then body else term
%       %% case e of p -> body --> let p = e in body
%       | Apply(Lambda([(p,Fun(Bool true,_,_),body)],_),e,pos) ->
%         simplifyOne spc (Let([(p,e)],body,pos))
       | Let([(VarPat(v,_),letTerm as (Apply(Fun(Restrict,_,_),(Var _),_)))],
	     body,_) ->
	 simplifyOne spc (substitute(body,[(v,letTerm)])) 
       %% Distribution of terms over application
       %% (if p then x else y) z --> if p then x z else y z
       | Apply(IfThenElse(t1,t2,t3,a),tm,_) ->
	 if simpleTerm? tm
	   then IfThenElse(t1,simplifiedApply(t2,tm,spc),simplifiedApply(t3,tm,spc),a)
	   else term
       %% (let x = y in f) z --> let x = y in f z
       | Apply(Let(binds,body,a),tm,_) ->
	 if simpleTerm? tm
	   then Let(binds,simplifiedApply(body,tm,spc),a)
	   else term
       %% (letrec x = y in f) z --> let x = y in f z
       | Apply(LetRec(binds,body,a),tm,_) ->
	 if simpleTerm? tm
	   then LetRec(binds,simplifiedApply(body,tm,spc),a)
	   else term
       %% (case x of p1 -> e1 p2 -> e2 ...) z  --> case x of p1 -> e1 z p2 -> e2 .z ..
       | Apply(Apply(Lambda(cases,a1),x,a2),tm,_) ->
	 if simpleTerm? tm
	   then Apply(Lambda(map (fn (p,pred,ei) -> (p,pred,simplifiedApply(ei,tm,spc))) cases,a1),
		      x,a2)
	   else term	%% let y = <exp> in f y  --> f <exp> where y occurs once in f and no side-effects
%	| Let([(VarPat((id,_),_),tm)],body,_) -> 
%	  let
%	     def replace(term) = 
%		 case term
%		   of (Var((id2,_),_)) -> if id = id2 then wVar else term 
%		    | _ -> term
%	  in
%	     mapTerm(replace,fn x -> x,fn p -> p) body
       | Apply(Fun(Op(Qualified("Nat","natural?"), _),_,_), e, a) ->
         mkAppl((Fun(Op (Qualified("Integer",">="),Infix(Left,20)),
                     Arrow(mkProduct[integerSort,integerSort],boolSort,a),
                     a),
                 [e, mkNat 0]))
%       %% Eta fn v -> case v of p -> e --> fn p -> e
%       | Lambda([(VarPat(v,_), Fun(Bool true,_,_),
%                  Apply(lam as Lambda([(_, Fun(Bool true,_,_), _)], _), Var(v1,_), _))], _) | equalVar?(v, v1) ->
%         lam
       %% Quantification simplification
       %% fa(x,y) x = a & p(x,y) => q(x,y) --> fa(x,y) p(a,y) => q(a,y)
       | Bind(Forall,_,_,_) -> simplifyForall spc (forallComponents term)
       | Bind(Exists,_,_,_) -> simplifyExists spc (existsComponents term)
       | Bind(Exists1,_,_,_) -> simplifyExists1(exists1Components term)
       | Apply(Fun(Project i,_,_),Record(m,_),_) ->
	 (case getField(m,i) of
	   | Some fld -> fld
	   | None -> term)
       | Apply(Fun (Implies, _, _), Record([("1",t1),("2",t2)],_),_) ->
         if  (trueTerm? t2 || equalTerm?(t1, t2)) && sideEffectFree t1
           then mkTrue()
           else mkSimpImplies(t1,t2)
       %% x + n - n \_longrightarrow x  (Could generalize, but useful for IsaPrinter)
       | Apply(Fun(Op(Qualified("Integer","-"),_),_,_),
               Record([("1",Apply(Fun(Op(Qualified("Integer","+"),_),_,_),
                                  Record([("1",t1),
                                          ("2",Fun(Nat n1,_,_))],_),_)),
                       ("2",Fun(Nat n2,_,_))],_), _)
           | n1 = n2 ->
         t1
       %% (x:Nat) >= 0 --> true
       | Apply(Fun(Op(Qualified("Integer",">="),_),_,_),
               Record([("1", x), ("2", Fun(Nat 0, _, _))], _), _)
           | subtypeOf?(inferType(spc, x), Qualified("Nat", "Nat"), spc) ->
         trueTerm
       | Apply(Apply(Fun(Op(Qualified("Bool","&&&"),_),_,_),
                     Record([("1", pred1), ("2", pred2)],_), _),
               arg_tm, _) | termSize arg_tm < 40 ->
         mkSimpConj [simplifiedApply(pred1, arg_tm, spc),
                     simplifiedApply(pred2, arg_tm, spc)]
       | Apply(Fun(Op(Qualified("Bool","&&&"),_),_,_), _, a) ->
         let preds = decomposeConjPred term in
         (case find simpleLambda? preds of
            | Some (lam as Lambda ([(pat, _, bod)], _)) ->
              let other_preds = delete lam preds in
              let Some arg_tm = patternToTerm pat in
              mkLambda(pat, mkConj(bod::map (fn pred -> simplifiedApply(pred, arg_tm, spc)) other_preds))
            | _ -> composeConjPreds(preds, spc))
       | IfThenElse(t1,t2,t3,a) ->
         (case t1 of
            | Fun(Bool true, _,_) -> t2
            | Fun(Bool false,_,_) -> t1
            | _ -> term)
       %% There are contexts where this is undesirable, e.g. at one stage in Isabelle translator
       %% | Apply(p, Var((_,ty), _), _) | subtypePred?(ty, p, spc) -> trueTerm
       | _ ->
     case simplifyCase spc term of
       | Some tm -> tm
       | None ->
     let term = removeUnnecessaryVariable spc term in
     let term = tupleInstantiate spc term in
     term

  op countDeReferencesIn(v: Var, tms: List MS.Term): Nat =
    foldl (fn (i,t) ->
             foldSubTerms (fn (st,i) ->
                             case st of
                               | Apply(Fun(Project _,_,_), Var (sv,_), _)
                               | equalVar?(v,sv) ->
                                 i + 1
                               | _ -> i)
               i t)
      0 tms

  op  simplifyForall: Spec -> List Var * List MS.Term * MS.Term -> MS.Term
  def simplifyForall spc (vs, cjs, bod) =
    % let _ = writeLine("\nsfa: "^printTerm(mkConj cjs)^"\n => "^ printTerm bod) in
    let name_set = varNamesSet(vs, bod::cjs) in
    case normForallBody (bod, name_set, spc) of
      | Some(new_vs, new_cjs, new_bod) ->
        simplifyForall spc (vs++new_vs, cjs++new_cjs, new_bod)
      | _ ->
    case find (fn cj ->
                case cj of
                  | Let([(VarPat ((vn,_),_),e)], _, _) -> true
                  | _ -> false)
           cjs of
      | Some(cj as Let([(VarPat (v as (vn, ty),_),e)], let_body, _)) ->
        %% turn let bound var in conjunct to a universally quantified var
        let new_vn = freshName(vn, name_set) in
        let new_v = (new_vn, ty) in
        let let_body = substitute(let_body, [(v, mkVar new_v)]) in
        let new_cjs = foldr (fn (cji, cjs) ->
                               if cji = cj then mkEquality(ty, mkVar new_v, e)::let_body::cjs
                                 else cji::cjs)
                        [] cjs
        in
        simplifyForall spc (new_v::vs, new_cjs, bod)
      | _ ->
    case find (fn cj ->
	        case bindEquality (cj,vs) of
		 | None -> false
		 | Some(v,e) ->
		   simpleOrConstrTerm? e
                     || (let num_refs = foldl (fn (r,cji) -> r + countVarRefs(cji,v))
                                         (countVarRefs(bod,v)) cjs
                         in
                         num_refs - 1 = 1 % This one and the one we want to replace
                           || embed? Record e
                             && num_refs - 1 = countDeReferencesIn(v, Cons(bod, cjs))))
           cjs
      of Some cj ->
	 (case bindEquality (cj,vs) of
	    | Some (pr as (sv as (_, sv_ty), s_tm)) ->
	      let sbst = [pr] in
              % let sv_ty = raiseSubtypeFn(sv_ty, spc) in
              let pred_tm = case subtypeComps(spc, sv_ty) of
                              | Some(_, pred) -> simplifiedApply(pred, s_tm, spc)
                              | None -> trueTerm
              in
	      simplifyForall spc
	        (filter (fn v -> ~(equalVar?(v, sv))) vs,
                 pred_tm ::
		   (mapPartial (fn c -> if c = cj then None
                                        else Some(simpSubstitute(spc,c,sbst)))
                      cjs),
		 simpSubstitute(spc,bod,sbst)))
       | _ ->
        %% x = f y && p(f y) => q(f y) --> x = f y && p x => q x
        let bind_cjs = filter (fn cj -> some?(bindEquality(cj,vs))) cjs in
        let (cjs, bod) = foldl (fn ((cjs, bod), cj) ->
                                  let Some bnd = bindEquality (cj,vs) in
                                  (map (fn cji -> if cj = cji then cji
                                                   else invertSubst(cji, [bnd]))
                                     cjs,
                                   invertSubst(bod, [bnd])))
                           (cjs, bod) bind_cjs
        in
        let simplCJs = foldr (fn (cj,new_cjs) -> simplifyConjunct(cj,spc) ++ new_cjs) [] cjs in
        let simpVs = filter (fn v -> (exists (fn cj -> isFree(v,cj)) ([bod] ++ simplCJs))
                                    || ~(knownNonEmpty?(v.2, spc)))
                       vs
        in
        let bod_cjs = getConjuncts bod in
        % let _ = writeLine("Simplifying "^printTerm bod^"\nwrt:\n"^printTerm(mkConj simplCJs)) in
        let bod = mkConj(filter (fn c -> ~(equivTermIn? spc (c,simplCJs))) bod_cjs) in
        if trueTerm? bod
          then if true   % all (fn (_,ty) -> knownNonEmpty?(ty,spc)) vs
                 then trueTerm
                 else let poss_empty_tys = filter (fn (_,ty) -> ~(knownNonEmpty?(ty,spc))) vs in
                      mkBind(Forall, poss_empty_tys, trueTerm)
          else if simplCJs = cjs && simpVs = vs
          then mkSimpBind(Forall, vs, mkSimpImplies(mkSimpConj cjs, bod))
          else simplifyForall spc (simpVs, simplCJs, bod)

  op  simplifyConjunct: MS.Term * Spec -> List MS.Term 
  def simplifyConjunct (cj,spc) =
    case cj of
      | Apply(Fun(Equals,_,_),Record([("1",Record(lhs_flds,_)),("2",Record(rhs_flds,_))],_),_) ->
        map (fn ((_,lhs_e),(_,rhs_e)) -> mkEquality(inferType(spc,lhs_e),lhs_e,rhs_e))
	  (zip(lhs_flds,rhs_flds))
      | _ -> [cj]

  op  varNamesSet: List Var * List MS.Term -> StringSet.Set
  def varNamesSet(vs,tms) =
    foldl (fn (nm_set,(nm,_)) -> StringSet.add(nm_set,nm))
      StringSet.empty
      (vs ++ foldl (fn (fvs,t) -> freeVars t ++ fvs) [] tms)
    

  op  normForallBody: MS.Term * StringSet.Set * Spec -> Option(List Var * List MS.Term * MS.Term)
  %% fa(x) p => let y = m in n --> fa(x,y) p & y = m => n
  def normForallBody(body, used_names, spc) =
    case body of
      | Let([(pat, val)], let_body, _) ->	% fa(x) p => let y = m in n --> fa(x,y) p & y = m => n
        (case patternToTerm pat of
	   | Some pat_tm ->
	     let new_vs = freeVars pat_tm in
	     let (unique_vs, sb) = getRenamingSubst(new_vs, used_names) in
	     if sb = []
	       then Some(unique_vs, [mkEquality(inferType(spc, pat_tm), pat_tm, val)], let_body)
	       else Some(unique_vs, [mkEquality(inferType(spc, pat_tm), substitute(pat_tm, sb), val)],
			 simpSubstitute(spc, let_body, sb))
	   | _ -> None)
      | Apply(Fun(And,_,_), _, _) ->
        (let cjs = getConjuncts body in
         case foldr (fn (cj, (vs, lhs_cjs, rhs_cjs)) ->
                      case normForallBody(cj, used_names, spc) of
                        | Some(new_vs, new_lhs_cjs, new_rhs_cj) ->
                          (new_vs ++ vs, new_lhs_cjs ++ lhs_cjs, new_rhs_cj :: rhs_cjs)
                        | None -> (vs, lhs_cjs, cj :: rhs_cjs))
               ([], [], []) cjs of
          | ([], [], _) -> None
          | (vs, lhs_cjs, rhs_cjs) -> Some (vs, lhs_cjs, mkConj rhs_cjs))
      | _ -> None

  op  getRenamingSubst: List Var * StringSet.Set -> List Var * List (Var * MS.Term)
  def getRenamingSubst(vs, used_names) =
    foldr (fn (v as (nm, ty), (vs, sb)) ->
	   let new_nm = StringUtilities.freshName(nm, used_names) in
	   if nm = new_nm
	    then (Cons(v, vs), sb)
	    else let new_v = (new_nm, ty) in
	         (Cons(new_v, vs), Cons((v, mkVar new_v), sb)))
      ([], []) vs

  op  simpSubstitute: Spec * MS.Term *  List (Var * MS.Term) -> MS.Term
  def simpSubstitute(spc, t, sbst) =
    % let _ = toScreen("\nBefore subst:\n" ^ printTerm t ^ "\n") in
    let stm = substitute(t, sbst) in
    % let _ = toScreen("After subst:\n" ^ printTerm stm ^ "\n") in
    let result = simplify spc stm in
    % let _ = toScreen("Simp:\n" ^ printTerm result ^ "\n\n") in
    result

  op  bindEquality: MS.Term * List Var -> Option(Var * MS.Term)
  def bindEquality (t, vs) =
    case t of
      | Apply(Fun(Equals, _, _), Record([(_, e1), (_, e2)],  _), _) ->
        (case e1 of
	  | Var(v, _) | inVars?(v, vs) && ~(isFree(v, e2)) -> Some(v, e2)
	  | _ ->
	 case e2 of
	  | Var(v, _) | inVars?(v, vs) && ~(isFree(v, e1)) -> Some(v, e1)
	  | _ -> None)
      | _ -> None

  op  simplifyExists: Spec -> List Var * List MS.Term -> MS.Term
  def simplifyExists spc (vs, cjs) =
    let vs = filter (fn v -> (exists (fn cj -> isFree(v, cj)) cjs)
                            || ~(knownNonEmpty?(v.2,  spc)))
               vs
    in
    mkSimpBind(Exists, vs, mkSimpConj cjs)    

  op  simplifyExists1: List Var * List MS.Term -> MS.Term
  def simplifyExists1(vs, cjs) =
    mkSimpBind(Exists1, vs, mkSimpConj cjs)    

  op simplifyRecordBind(spc: Spec, pats: List (Id * Pattern), acts: List (Id * MS.Term), body: MS.Term)
     : Option MS.Term =
    if all (fn(_,VarPat _) -> true | (_,WildPat _) -> true | _ -> false) pats 
      then (if all (fn(_,Var _) -> true | _ -> false) acts
              then Some(substitute(body,makeSubstFromRecord(pats,acts)))
              else
              %% Sequentializing binds: rename to avoid variable capture
              let (binds,sbst,_)
                 = foldr (fn (((_,vp as VarPat(v,a)),(_,val)),(binds,sbst,fvs)) ->
                            let new_fvs = (map (fn (vn,_) -> vn) (freeVars val)) ++ fvs in
                            if member(v.1,fvs)
                              then let nv = (v.1 ^ "__" ^ (Nat.toString (length binds)),v.2) in
                                (Cons((VarPat(nv,a),val),binds),
                                 Cons((v,Var(nv,a)),sbst),
                                 new_fvs)
                            else (Cons((vp,val),binds),sbst,new_fvs)
                          | (((_,vp as WildPat _),(_,val)),(binds,sbst,fvs)) ->
                            if sideEffectFree val then (binds,sbst,fvs)
                            else
                            let new_fvs = (map (fn (vn,_) -> vn) (freeVars val)) ++ fvs in
                            (Cons((vp,val),binds),sbst,new_fvs))
                     ([],[],[]) (zip(pats,acts))
              in
              let body = substitute(body,sbst) in
              Some(foldr (fn ((v,val),body) ->
                            simplifyOne spc (mkLet([(v,val)],body)))
                     body binds))
      else None

  op simplifyCase (spc: Spec) (term: MS.Term): Option MS.Term =
    case term of
      %% case (a,b,c) of (x,y,z) -> g(x,y,z) --> g(a,b,c)
      | Apply(Lambda([(RecordPat(pats,_),_,body)],_),Record(acts,_),_) ->
        simplifyRecordBind(spc, pats, acts, body)
      %% let (x,y,z) = (a,b,c) in g(x,y,z) --> g(a,b,c)
      | Let ([(RecordPat(pats,_), Record(acts,_))], body, _) ->
        simplifyRecordBind(spc, pats, acts, body)
      %% case v of (x,y) -> ... --> let x = v.1 and y = v.2 in ...
      | Apply(Lambda([(RecordPat(pats,_),_,body)],_),v as Var(vr,_),_) ->
        Some (simplifyOne spc
                (mkLet(map (fn (id,p) -> (p, mkProjection(id, v, spc))) pats, body)))
      | _ -> None

  op  makeSubstFromRecord: List(Id * Pattern) * List(Id * MS.Term) -> List(Var * MS.Term)
  def makeSubstFromRecord(pats,acts) =
    foldl (fn (result,(id,VarPat(v,_)))
             -> Cons((v,findField(id,acts)),result)
             | (result,_) -> result)
      []
      pats

  def simplifiedApply(t1,t2,spc) =
    simplifyOne spc (mkApply(t1,t2))

  op  simpleTerm?: MS.Term -> Boolean
  def simpleTerm?(term) = 
    case term of 
      | Record(fields,_) ->
        all (fn (_,t) -> simpleTerm t) fields
      | Lambda _ \_rightarrow true
      | _ -> simpleTerm term

 op simpleOrConstrTerm?(term: MS.Term): Boolean =
   simpleTerm? term
     || (case term of
           | Apply(Fun(Embed _,_,_), arg, _) ->
             all simpleOrConstrTerm? (termToList arg)
           | _ -> false)

 op traceSimplify?: Boolean = false

 def simplify spc term =
   let simp_term = mapSubTerms(simplifyOne spc) term in
   let trace? = traceSimplify? && ~(equalTerm?(simp_term, term)) in
   let _ = if trace? then toScreen("Before:\n" ^ printTerm term ^ "\n") else () in
   let _ = if trace? then toScreen("Simp:\n" ^ printTerm simp_term ^ "\n\n") else () in
   simp_term

 op  simplifySpec: Spec -> Spec
 def simplifySpec(spc) = 
   % let _ = toScreen("Before:\n" ^ printSpec spc ^ "\n\n") in
   let simp_spc = mapSpec (simplify spc,fn s -> s,fn p -> p) spc in
   % let _ = toScreen("After:\n" ^ printSpec simp_spc ^ "\n\n") in
   simp_spc
    
 op simplifyTopSpec(spc: Spec): Spec =
   let (new_elts, new_ops) =
       foldr (fn (elt, (elts, ops)) ->
                case elt of
                  | Property(ty, qid, tvs, tm, a) ->
                    (Cons(Property(ty, qid, tvs, simplify spc tm, a), elts), ops)
                  | Op(qid as Qualified(q,id), true, _) ->
                    let Some info = findTheOp(spc, qid) in
                    (elt :: elts,
                     insertAQualifierMap(ops, q, id, info << {dfn = simplify spc info.dfn}))
                  | OpDef(qid as Qualified(q,id), refine_num, _) ->
                    (case findTheOp(spc, qid) of
                       | None -> fail("Can't find def of op "^printQualifiedId qid)
                       | Some info ->
                     (elt :: elts,
                      let (tvs, ty, full_dfn) = unpackTerm info.dfn in
                      let dfn = refinedTerm(full_dfn, refine_num) in
                      let simp_dfn = simplify spc dfn in
                      let full_dfn = replaceNthTerm(full_dfn, refine_num, simp_dfn) in
                      let new_dfn = maybePiTerm (tvs, SortedTerm (full_dfn, ty, termAnn dfn)) in
                      insertAQualifierMap(ops, q, id, info << {dfn = new_dfn})))
                  | _ -> (elt :: elts, ops))
         ([], spc.ops) spc.elements
   in
   spc << {ops = new_ops, elements = new_elts}

endspec

