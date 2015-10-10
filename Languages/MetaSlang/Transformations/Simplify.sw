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
 import Interpreter
% import ../Specs/Environment
% import ../Specs/Utilities

 op traceSimplify?: Bool = false
 op simplifyUsingSubtypes?: Bool = false


 op  countVarRefs: MSTerm * MSVar -> Nat
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

 op  removeUnnecessaryVariable: Spec -> MSTerm -> MSTerm
 def removeUnnecessaryVariable spc term =
      let _ = if traceSimplify? then writeLine("ruv: "^printTerm term) else () in
     case term
       of Let([(vp as VarPat (v,_),e)],body,pos) ->
	  let noSideEffects = sideEffectFree(e) || embed? Lambda e in
          let new_body = if noSideEffects then termSubst(body, [(e, mkVar v)]) else body in
          let term = if body ~= new_body then Let([(vp, e)],new_body,pos) else term in
	  (case countVarRefs(new_body,v)
	     of 0 -> if noSideEffects then new_body else term
	      | 1 -> if noSideEffects
	                 || noInterveningSideEffectsBefore?
			      (new_body,fn (Var (v2,_)) -> v = v2
			             | _ -> false)
	               then %let _ = if embed? Lambda e then writeLine("ruv: \n"^printTerm term) else () in
                            let result = simplifyOne spc (substitute(new_body,[(v,e)])) in
                            %let _ = if embed? Lambda e then writeLine("--> \n"^printTerm (substitute(new_body,[(v,e)]))
                            %                                            ^"\n"^printTerm result) else () in
                            result
		       else term
	      | _ -> term)
        | Let ([(WildPat _,e)], body, _) ->
          if sideEffectFree(e) then body else term
	| _ -> term

  op noInterveningSideEffectsBefore?: MSTerm * (MSTerm -> Bool) -> Bool 
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
 op tupleInstantiate: Spec -> MSTerm -> MSTerm
 op tupleInstantiate (spc: Spec) (term:  MSTerm): MSTerm =
   let
      def elimTuple(zId,srt,fields,body) =
        let (zId,body) =
            if zId in? boundVarNamesIn body
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
               | _ -> fail ("Product type expected for let bound variable. Found "^printType srt)
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

 op simpleLetRecBody?(tm: MSTerm): Bool =
   case tm of
     | Lambda([(_, _, bod)], _) ->  simpleLetRecBody? bod
     | _ -> simpleTerm tm

 op  simplifyOne: Spec -> MSTerm -> MSTerm
 def simplifyOne spc term =
     let _ = if traceSimplify? then writeLine("s1< "^printTerm term) else () in
     let result =
         case tryEvalOne spc term of
           | Some cterm -> simplifyOne spc cterm
           | _ ->
         case term of
           | Let([], tm, _) -> tm
           | Let(all_decls as decl1::decl2::decls,body,_) ->
             let bndvars  = foldl (fn (pvs, (p, _)) -> patternVars p ++ pvs) [] all_decls in
             if exists? (fn (_, t) -> hasVarNameConflict?(t, bndvars)) all_decls
               then  %% Rename to avoid name overload 
                 simplifyOne spc (renameBoundVars(term, bndvars))
             else
             simplifyOne spc (mkLet([decl1],simplifyOne spc (mkLet(Cons(decl2,decls),body))))
           %% let (x,y) = (w,z) in f(x,y) -> f(w,z)
           | Let([(pat as RecordPat(pflds, _), tm as Record(tflds, _))], body, pos)
               | varCompatiblePatternTerm?(pat, tm) ->
             let new_decls = flattenCompatiblePatternTerm(pat, tm) in
             simplifyOne spc (Let(new_decls, body, pos))
           %% let y = x in f y  --> f x
           | Let([(VarPat(v,_), w)],body,pos) | simpleTerm w ->
             simplifyOne spc (substitute(body,[(v,w)]))
           %% case e of pat => bod   --> let pat = e in bod
           | Apply(Lambda([(pat, Fun(Bool true,_,_), body)],_),t,pos) ->
             simplifyOne spc (Let([(pat, t)], body, pos))
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
           %% let def f(x,y,z) = g in h(f(a,b,c)) --> h g
           | LetRec(binds, body, a) ->
             let sbst = mapPartial (fn (v, f) -> if simpleLetRecBody? f then Some(v, f) else None) binds in
             if sbst = [] then term
               else let new_body = simplify spc (substitute(body, sbst)) in
                    if length sbst = length binds then new_body
                      else
                      let new_binds = filter (fn (_, f) -> ~(simpleLetRecBody? f)) binds in
                      LetRec(new_binds, new_body, a)
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
           | Apply(Fun(Op(Qualified("Nat","natural?"), _),_,_), e, a) | simplifyUsingSubtypes? ->
             mkAppl((Fun(Op (Qualified("Integer",">="),Infix(Left,20)),
                         Arrow(mkProduct[intType,intType],boolType,a),
                         a),
                     [e, mkNat 0]))
    %       %% Eta fn v -> case v of p -> e --> fn p -> e
    %       | Lambda([(VarPat(v,_), Fun(Bool true,_,_),
    %                  Apply(lam as Lambda([(_, Fun(Bool true,_,_), _)], _), Var(v1,_), _))], _) | equalVar?(v, v1) ->
    %         lam
           | Apply(Fun(And,  _,_),Record(fields as [(_,N1),(_,N2)], _),_) -> Utilities.mkAnd(N1,N2)
           %% Quantification simplification
           %% fa(x,y) x = a && p(x,y) => q(x,y) --> fa(x,y) p(a,y) => q(a,y)
           | Bind(Forall,_,_,_) ->
             let result = simplifyForall spc (forallComponents term) in
             % let _ = writeLine("\nSFA0:\n"^printTerm term^"\n --->\n"^printTerm result) in
             result
           | Bind(Exists,_,_,_) -> simplifyExists spc (existsComponents term)
           | Bind(Exists1,_,_,_) -> simplifyExists1(exists1Components term)
           | Apply(Fun(Project i,_,_),Record(m,_),_) ->
             (case getField(m,i) of
               | Some fld -> fld
               | None -> term)
           | Apply(Fun (Implies, _, _), Record([("1",t1),("2",t2)],_),_) ->
             if  (trueTerm?(simplifyOne spc t2) || equalTermAlpha?(t1, t2)) && sideEffectFree t1
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
               | simplifyUsingSubtypes? && subtypeOf?(inferType(spc, x), Qualified("Nat", "Nat"), spc) ->
             trueTerm
           %% Isabelle specific: int x >= 0
           | Apply(Fun(Op(Qualified("Integer", ">="),_),_,_),
                   Record([("1", Apply(Fun(Op(Qualified("ToIsa-Internal", "int"),_),_,_), _, _)),
                           ("2", Fun(Nat 0, _, _))], _), _) ->
             trueTerm
           | Apply(Apply(Fun(Op(Qualified("Bool","&&&"),_),_,_),
                         Record([("1", pred1), ("2", pred2)],_), _),
                   arg_tm, _) | termSize arg_tm < 40 ->
             mkSimpConj [simplifiedApply(pred1, arg_tm, spc),
                         simplifiedApply(pred2, arg_tm, spc)]
           | Apply(Fun(Op(Qualified("Bool","&&&"),_),_,_), _, a) ->
             let preds = decomposeConjPred term in
             (case findLeftmost simpleLambda? preds of
                | Some (lam as Lambda ([(pat, _, bod)], _)) ->
                  let other_preds = delete lam preds in
                  let Some arg_tm = patternToTerm pat in
                  mkLambda(pat, mkConj(bod::map (fn pred -> simplifiedApply(pred, arg_tm, spc)) other_preds))
                | _ ->
                  let result = composeConjPreds(preds, spc) in
                  result)
           %% Specific to Isabelle translator, but cheap
           | Apply(Fun(Op(Qualified("ToIsa-Internal","int"),_),_,_), Fun(Nat i, _, a), _) ->
             Fun(Nat i, intType, a)
           %| Apply(Fun(Op(Qualified("Function", "id"),_), Arrow(dom, ran, _),_), x, _) | ~(equalType?(dom, ran))
           %  -> x
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
    in
    let _ = if traceSimplify? && ~ (equalTerm?(term, result))
               then writeLine("s1: "^printTerm term^"\n--> "^printTerm result) else () in
    result

  op countDeReferencesIn(v: MSVar, tms: MSTerms): Nat =
    foldl (fn (i,t) ->
             foldSubTerms (fn (st,i) ->
                             case st of
                               | Apply(Fun(Project _,_,_), Var (sv,_), _)
                               | equalVar?(v,sv) ->
                                 i + 1
                               | _ -> i)
               i t)
      0 tms

  op  simplifyForall: Spec -> MSVars * MSTerms * MSTerm -> MSTerm
  def simplifyForall spc (vs, cjs, bod) =
    % let _ = writeLine("\nsfa: "^printTerm(mkConj cjs)^"\n => "^ printTerm bod) in
    let name_set = varNamesSet(vs, bod::cjs) in
    case normForallBody (bod, name_set, spc) of
      | Some(new_vs, new_cjs, new_bod) ->
        simplifyForall spc (vs++new_vs, cjs++new_cjs, new_bod)
      | _ ->
    case findLeftmost (fn cj ->
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
     case findLeftmost (fn cj ->
                         case cj of
                           | Let([_], _, _) -> true
                           | _ -> false)
           cjs of
      | Some(cj as Let([_], _, _)) ->
        %% turn let bound pattern into conjuncts with universally quantified vars
        let cj1 = substitute2(cj,[],name_set) in    % Rename variables to avoid capture
        let Let([(pat, e)], let_body, _) = cj1 in
        let (pat_tm, new_conds, new_vs) = patternToTermPlusExConds pat in
        let eq_tm = mkEquality(inferType(spc, pat_tm), pat_tm, e) in
        simplifyForall spc (new_vs ++ vs, eq_tm :: let_body :: new_conds ++ delete cj cjs , bod)
      | _ ->
    case findLeftmost (fn cj ->
                         case bindEquality (cj,vs,false) of
                           | None -> false
                           | Some([v],_,e) ->
                             simpleOrConstrTerm? e
                           || (let num_refs = foldl (fn (r,cji) -> r + countVarRefs(cji,v))
                                 (countVarRefs(bod,v)) cjs
                               in
                                 num_refs - 1 = 1 % This one and the one we want to replace
                                                               || embed? Record e
                                                                  && num_refs - 1 = countDeReferencesIn(v, Cons(bod, cjs)))
                           | _ -> false)
           cjs
      of Some cj ->
	 (case bindEquality (cj,vs,false) of
	    | Some (([sv as (_, sv_ty)], _, s_tm)) ->
	      let sbst = [(sv, s_tm)] in
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
        let bind_cjs = filter (fn cj -> case bindEquality(cj,vs,false) of Some([_], _, _) -> true | _ -> false) cjs in
        let (cjs, bod) = List.foldl (fn ((cjs, bod), cj) ->
                                  let Some ([v], _, e) = bindEquality (cj,vs,false) in
                                  let sb = [(v, e)] in
                                  (map (fn cji -> if cj = cji then cji
                                                   else invertSubst(cji, sb))
                                     cjs,
                                   invertSubst(bod, sb)))
                           (cjs, bod) bind_cjs
        in
        let cjs = simplifyConjuncts cjs in
        let simplCJs = foldr (fn (cj,new_cjs) -> simplifyConjunct(cj,spc) ++ new_cjs) [] cjs in
        let simpVs = filter (fn v -> (exists? (fn cj -> isFree(v,cj)) ([bod] ++ simplCJs))
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

  op  simplifyConjunct: MSTerm * Spec -> MSTerms
  def simplifyConjunct (cj,spc) =
    case cj of
      | Apply(Fun(Equals,_,_),Record([("1",Record(lhs_flds,_)),("2",Record(rhs_flds,_))],_),_) ->
        map (fn ((_,lhs_e),(_,rhs_e)) -> mkEquality(inferType(spc,lhs_e),lhs_e,rhs_e))
	  (zip(lhs_flds,rhs_flds))
      | _ -> [cj]

  op simplifyConjuncts(cjs: MSTerms): MSTerms =
    map (fn cj ->
           case cj of
             | Apply(Fun(Implies, _, _),
                     Record([("1", lhs), ("2", rhs)],_),_) ->
               let lhs_cjs = getConjuncts lhs in
               let lhs_cjs1 = filter (fn t -> ~(termIn?(t, cjs))) lhs_cjs in
               if length lhs_cjs1 = length lhs_cjs then cj
                 else mkSimpImplies(mkSimpConj lhs_cjs1, rhs)
             | _ -> cj)
      cjs

  op  varNamesSet: MSVars * MSTerms -> StringSet.Set
  def varNamesSet(vs,tms) =
    foldl (fn (nm_set,(nm,_)) -> StringSet.add(nm_set,nm))
      StringSet.empty
      (vs ++ foldl (fn (fvs,t) -> freeVars t ++ fvs) [] tms)
    

  op  normForallBody: MSTerm * StringSet.Set * Spec -> Option(MSVars * MSTerms * MSTerm)
  %% fa(x) p => let y = m in n --> fa(x,y) p && y = m => n
  def normForallBody(body, used_names, spc) =
    case body of
      | Let([(pat, val)], let_body, _) ->	% fa(x) p => let y = m in n --> fa(x,y) p && y = m => n
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

  op  getRenamingSubst: MSVars * StringSet.Set -> MSVars * MSVarSubst
  def getRenamingSubst(vs, used_names) =
    foldr (fn (v as (nm, ty), (vs, sb)) ->
	   let new_nm = StringUtilities.freshName(nm, used_names) in
	   if nm = new_nm
	    then (Cons(v, vs), sb)
	    else let new_v = (new_nm, ty) in
	         (Cons(new_v, vs), Cons((v, mkVar new_v), sb)))
      ([], []) vs

  op  simpSubstitute: Spec * MSTerm *  MSVarSubst -> MSTerm
  def simpSubstitute(spc, t, sbst) =
    % let _ = toScreen("\nBefore subst:\n" ^ printTerm t ^ "\n") in
    let stm = substitute(t, sbst) in
    % let _ = toScreen("After subst:\n" ^ printTerm stm ^ "\n") in
    let result = simplify spc stm in
    % let _ = toScreen("Simp:\n" ^ printTerm result ^ "\n\n") in
    result

  op  bindEquality: MSTerm * MSVars * Bool -> Option (MSVars * MSTerm * MSTerm)
  def bindEquality (t, vs, rhs_free?: Bool) =
    %% rhs_free? means that we require the expression that the variables is equal to not have any refs to other vs
    let def exprOfVs(e: MSTerm): Option MSVars =
          case e of
            | Var(v, _) | inVars?(v, vs) -> Some [v]
            | Record((_, t1) :: r_binds, _) ->
              foldl (fn (result, (_, s_tm)) ->
                       case result of
                         | None -> None
                         | Some vs1 ->
                       case exprOfVs s_tm of
                         | Some vs2 | disjointVars?(vs1, vs2) -> Some (vs1 ++ vs2)
                         | _ -> None)
                (exprOfVs t1) r_binds
            | _ -> None
        def bindE(e1, e2) =
          case exprOfVs e1 of
           | Some bvs | disjointVars?(if rhs_free? then vs else bvs, freeVars e2) -> Some(bvs, e1, e2)
           | _ ->
         case exprOfVs e2 of
           | Some bvs | disjointVars?(if rhs_free? then vs else bvs, freeVars e1) -> Some(bvs, e2, e1)
           | _ -> 
         case (e1, e2) of
           | (Apply(Fun(Embed(id1, _), _, _), t1, _), Apply(Fun(Embed(id2, _), _, _), t2, _)) | id1 = id2 ->
              bindE(t1, t2)
           | _ -> None
    in
    case t of
      | Apply(Fun(Equals, _, _), Record([(_, e1), (_, e2)],  _), _) -> bindE(e1, e2)
      | _ -> None

  op  simplifyExists: Spec -> MSVars * MSTerms -> MSTerm
  def simplifyExists spc (vs, cjs) =
    let vs = filter (fn v -> (exists? (fn cj -> isFree(v, cj)) cjs)
                            || ~(knownNonEmpty?(v.2,  spc)))
               vs
    in
    case findLeftmost (fn cj ->
                         case bindEquality (cj,vs,false) of
                           | None -> false
                           | Some([v],_,e) ->
                             simpleOrConstrTerm? e
                           || (let num_refs = foldl (fn (r,cji) -> r + countVarRefs(cji,v))
                                                0 cjs
                               in
                                 num_refs - 1 = 1 % This one and the one we want to replace
                                   || embed? Record e
                                      && num_refs - 1 = countDeReferencesIn(v, cjs))
                           | _ -> false)
           cjs
      of Some cj ->
	 (case bindEquality (cj,vs,false) of
	    | Some (([sv as (_, sv_ty)], _, s_tm)) ->
	      let sbst = [(sv, s_tm)] in
              let pred_tm = case subtypeComps(spc, sv_ty) of
                              | Some(_, pred) | ~(equivType? spc (sv_ty, inferType(spc, s_tm))) ->
                                simplifiedApply(pred, s_tm, spc)
                              | _ -> trueTerm
              in
              simplifyExists spc (filter (fn v -> ~(equalVar?(v, sv))) vs,
                                    (map (fn c -> if c = cj then pred_tm
                                                  else simpSubstitute(spc,c,sbst))
                                       cjs)))
      | None -> mkSimpBind(Exists, vs, mkSimpConj cjs)    

  op  simplifyExists1: MSVars * MSTerms -> MSTerm
  def simplifyExists1(vs, cjs) =
    mkSimpBind(Exists1, vs, mkSimpConj cjs)    

  op simplifyRecordBind(spc: Spec, pat: MSPattern, tm: MSTerm, body: MSTerm)
     : Option MSTerm =
    let pairs = flattenCompatiblePatternTerm(pat, tm) in
    if forall? (fn(VarPat _, _) -> true | (WildPat _,_) -> true | _ -> false) pairs 
      then (if forall? (fn(_,Var _) -> true | _ -> false) pairs
              then Some(substitute(body,makeSubstFromBindPairs pairs))
              else
              %% Sequentializing binds: rename to avoid variable capture
              let (binds,sbst,_)
                 = foldr (fn ((vp as VarPat(v,a),val), (binds,sbst,fvs)) ->
                            let new_fvs = (map (fn (vn,_) -> vn) (freeVars val)) ++ fvs in
                            if v.1 in? fvs
                              then let nv = (v.1 ^ "__" ^ (Nat.show (length binds)),v.2) in
                                ((VarPat(nv,a),val) :: binds,
                                 (v,Var(nv,a)) :: sbst,
                                 new_fvs)
                            else ((vp,val) :: binds, sbst, new_fvs)
                          | ((vp as WildPat _,val), (binds,sbst,fvs)) ->
                            if sideEffectFree val then (binds,sbst,fvs)
                            else
                            let new_fvs = (map (fn (vn,_) -> vn) (freeVars val)) ++ fvs in
                            ((vp,val) :: binds, sbst, new_fvs))
                     ([],[],[]) pairs
              in
              let body = substitute(body,sbst) in
              Some(foldr (fn ((vp,val),body) ->
                            % let _ = writeLine("srb: "^printTerm (mkLet([(vp,val)],body))) in
                            let simp_let_tm = simplifyOne spc (mkLet([(vp,val)],body)) in
                            % let _ = writeLine("---> "^printTerm simp_let_tm) in
                            simp_let_tm)
                     body binds))
      else None

  op simplifyCase (spc: Spec) (term: MSTerm): Option MSTerm =
    case term of
      %% case (a,b,c) of (x,y,z) -> g(x,y,z) --> g(a,b,c)
      | Apply(Lambda([(pat as RecordPat _,_,body)],_),tm as Record _,_) ->
        simplifyRecordBind(spc, pat, tm, body)
      %% let (x,y,z) = (a,b,c) in g(x,y,z) --> g(a,b,c)
      | Let ([(pat as RecordPat _, tm as Record _)], body, _) ->
        % let (pats, acts) = unzip(flattenCompatiblePatternTerm(pat, tm)) in
        simplifyRecordBind(spc, pat, tm, body)
      %% case v of (x,y) -> ... --> let x = v.1 and y = v.2 in ...
      | Apply(Lambda([(RecordPat(pats,_),_,body)],_),v as Var(vr,_),_) ->
        Some (simplifyOne spc
                (mkLet(map (fn (id,p) -> (p, mkProjection(id, v, spc))) pats, body)))
      | _ -> None

  op  makeSubstFromBindPairs: List(MSPattern * MSTerm) -> MSVarSubst
  def makeSubstFromBindPairs(pairs) =
    foldl (fn (result,(VarPat(v,_), tm)) -> (v,tm) :: result
            | (result,_) -> result)
      []
      pairs

  def simplifiedApply(t1,t2,spc) =
    % let _ = writeLine("simp apply: "^printTerm t1^" ("^printTerm t2^")") in
    let result = renameShadowedVars(simplifyOne spc (mkApply(t1,t2))) in
    % let _ = writeLine(" --> "^printTerm result) in
    result

  op  simpleTerm?: MSTerm -> Bool
  def simpleTerm?(term) = 
    case term of 
      | Record(fields,_) ->
        forall? (fn (_,t) -> simpleTerm t) fields
      | Lambda _ \_rightarrow true
      | _ -> simpleTerm term

 op simpleOrConstrTerm?(term: MSTerm): Bool =
   simpleTerm? term
     || (case term of
           | Apply(Fun(Embed _,_,_), arg, _) ->
             forall? simpleOrConstrTerm? (termToList arg)
           | _ -> false)

 op simplify (spc: Spec) (term: MSTerm): MSTerm =
   let simp_term = mapSubTerms(simplifyOne spc) term in
   let trace? = traceSimplify? && ~(equalTerm?(simp_term, term)) in
   let _ = if trace? then toScreen("Before:\n" ^ printTerm term ^ "\n") else () in
   let _ = if trace? then toScreen("Simp:\n" ^ printTerm simp_term ^ "\n\n") else () in
   simp_term

 op MSTermTransform.simpStandard  (spc: Spec) (term: TransTerm): MSTerm =
   simplify spc term

 op SpecTransform.simplifySpec (spc : Spec) : Spec =
   % let _ = toScreen("Before:\n" ^ printSpec spc ^ "\n\n") in
   let simp_spc = mapSpec (simplifyOne spc, fn typ -> typ, fn pat -> pat) spc in
   % let _ = toScreen("After:\n" ^ printSpec simp_spc ^ "\n\n") in
   simp_spc
    
 op simplifyTopSpec (spc: Spec): Spec =
   let (new_elts, new_ops) =
       foldr (fn (elt, (elts, ops)) ->
                case elt of
                  | Property(ty, qid, tvs, tm, a) ->
                    (Cons(Property(ty, qid, tvs, simplify spc tm, a), elts), ops)
                  | Op(qid as Qualified(q,id), true, _) ->
                    let Some info = findTheOp(spc, qid) in
                    (elt :: elts,
                     insertAQualifierMap(ops, q, id, info << {dfn = simplify spc info.dfn}))
                  | OpDef(qid as Qualified(q,id), refine_num, _, _) ->
                    (case findTheOp(spc, qid) of
                       | None -> fail("Can't find def of op "^printQualifiedId qid)
                       | Some opinfo ->
                     (elt :: elts,
                      let trps = unpackTypedTerms (opinfo.dfn) in
                      let (tvs, ty, dfn) = nthRefinement(trps, refine_num) in
                      let simp_dfn = simplify spc dfn in
                      let new_dfn = maybePiAndTypedTerm(replaceNthRefinement(trps, refine_num, (tvs, ty, simp_dfn))) in
                      insertAQualifierMap(ops, q, id, opinfo << {dfn = new_dfn})))
                  | _ -> (elt :: elts, ops))
         ([], spc.ops) spc.elements
   in
   spc << {ops = new_ops, elements = new_elts}

endspec

