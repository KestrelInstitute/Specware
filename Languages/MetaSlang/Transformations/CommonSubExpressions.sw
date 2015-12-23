(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

CSE qualifying
spec
 import /Languages/MetaSlang/Transformations/Simplify
 import /Languages/MetaSlang/Transformations/CurryUtils

(*
Look for common terms bottom up. 
Introduce lets for common terms as high up as possible within an unconditional context.
Key to variables:
  cse#: hold terms that have been found to be common but haven't been let bound.
  single_tms#: terms that have occurred once
  poss_tms#: terms that have occurred once, but within a conditional
For common expressions involving multiple levels, the lower levels may be recognized first
there is a final clean-up phase to get rid of introduced variables that are only used once 
(in the more complex common expression)
*)

  op newCSEs(cse1: MSTerms, cse2: MSTerms, tms1: MSTerms, tms2: MSTerms,
             poss_tms1: MSTerms, poss_tms2: MSTerms)
    : MSTerms * MSTerms * MSTerms =
    let cse12 = termsUnion(termsIntersect(tms1, tms2),
                           termsUnion(termsIntersect(tms1, poss_tms2),
                                      termsIntersect(poss_tms1, tms2)))
    in
    let new_ces = termsUnion(cse12, termsUnion(cse1, cse2)) in
    let single_tms = termsDiff(termsUnion(tms1, tms2), new_ces) in
    let poss_tms = termsDiff(termsUnion(poss_tms1, poss_tms2), new_ces) in
    (new_ces, single_tms, poss_tms)

  op removeLocal(tms: MSTerms, vs: MSVars): MSTerms =
    filter (fn t -> ~(hasRefTo?(t,vs))) tms

  op maybeAbstract(t: MSTerm, cse: MSTerms, names: List String, bindable?: Bool,
                   single_tms: MSTerms, poss_tms: MSTerms, spc: Spec)
    : MSTerm * MSTerms * MSTerms * MSTerms * List String =
      % let _ = (writeLine("maybeAbstract "^show bindable?^":\n"^printTerm t^"\ncse:");
      %          app (fn t -> writeLine(printTerm t)) cse;
      %          writeLine("single_tms: ");
      %          app (fn t -> writeLine(printTerm t)) single_tms;
      %          writeLine("Poss_tms: ");
      %          app (fn t -> writeLine(printTerm t)) poss_tms;
      %          writeLine "")
      % in
    let bvs = boundVars t in
    let cse = removeLocal(cse,bvs) in
    case cse of
      | _::_ | bindable? ->
        let Some big_cse = maximal termSize cse in
        let nm = newName("cse",names) in
        let ty = inferType(spc, big_cse) in
        let v = (nm, ty) in
        let vr = mkVar v in
        let new_bod = mapTerm (fn st -> if equalTerm?(big_cse,st) then vr else st, id,id) t in
        let new_t = mkLet([(mkVarPat v, big_cse)], new_bod) in
        let new_t = mapTerm (fn st ->
                               case st of
                                 | Let([(VarPat(v,_),wVar as (Var(w,_)))],body,pos) ->
                                   substitute(body,[(v,wVar)])
                                 | _ -> st,
                              id,id)
                      new_t
        in                              
        recAbstractCSE(new_t, Cons(nm, names), true, spc)        
      | _ ->
        let single_tms = removeLocal(single_tms,bvs) in
        let poss_tms = removeLocal(poss_tms,bvs) in
        let single_tms = if dontAbstract? t
                          then single_tms
                          else t :: single_tms
        in
        (t, cse, single_tms, poss_tms, names)

  op recAbstractCSE(t: MSTerm, names: List String, bindable?: Bool, spc: Spec)
    : MSTerm * MSTerms * MSTerms * MSTerms * List String =
    case getCurryArgs t of
      | Some(f,c_args) ->
        %% Don't wan't to abstract partial applications
        let (new_c_args,names,cse,single_tms,poss_tms) =
            foldr (fn (st,(new_c_args,names,cse,single_tms,poss_tms)) ->
                      let (st1, cse1, tms1, ptms1, names) = recAbstractCSE(st, names, false, spc) in
                      let (new_cse, single_tms, poss_tms) = newCSEs(cse1, cse, tms1, single_tms,
                                                                    ptms1, poss_tms)
                      in
                      (Cons(st1, new_c_args),
                       names, new_cse, single_tms, poss_tms))
               ([],names,[],[],[])
               c_args
        in
        let new_t = mkCurriedApply(f, new_c_args) in
        maybeAbstract(new_t, cse, names, bindable?, single_tms, poss_tms, spc)

      | None ->
    case t of
      | Apply(setf_fn as Fun(Op(Qualified("System", "setf"), _), _, _),
              Record([("1", term_to_modify as Apply _), ("2", val_term)], a1), a0) ->
        let (new_val_term, cse2, tms2, ptms2, names) = recAbstractCSE(val_term, names, false, spc) in
        let args = getArgs term_to_modify in
        let (new_args, namses, cse_args, single_tms_args, poss_tms_args) =
            foldr (fn (arg, (new_args, names, cse_args, single_tms_args, poss_tms_args)) ->
                     let (arg1, cse1, tms1, ptms1, names) = recAbstractCSE(arg, names, false, spc) in
                     let (new_cse, single_tms, poss_tms) = newCSEs(cse1, cse_args, tms1, single_tms_args, ptms1, poss_tms_args) in
                     (arg1::new_args, names, new_cse, single_tms, poss_tms))
              ([],names,[],[],[])
              args
        in
        let (new_cse, single_tms, poss_tms) = newCSEs(cse2, cse_args, tms2, single_tms_args, ptms2, poss_tms_args) in
        let sbst = filter (fn (x,y) -> ~(equalTerm?(x,y))) (zip(args, new_args)) in   % likely empty
        let new_term_to_modify = replace(term_to_modify, sbst) in
        let new_t = Apply(setf_fn, Record([("1", new_term_to_modify), ("2", new_val_term)], a1), a0) in
        maybeAbstract(new_t, new_cse, names, bindable?, single_tms, poss_tms, spc)                     
        
      | Apply(x,y,a) ->
        %% Careful about abstracting fns
        let (x1, cse1, tms1, ptms1, names) = recAbstractCSE(x, names, false, spc) in
        let tms1 = case tms1 of
                     | (Lambda _)::r_tms1 -> r_tms1
                     | _ -> tms1
        in
        let (y1, cse2, tms2, ptms2, names) = recAbstractCSE(y, names, false, spc) in
        let tms2 = case tms2 of
                     | (Record _)::r_tms2 -> r_tms2
                     | _ -> tms2
        in
        let (new_cse, single_tms, poss_tms) = newCSEs(cse1, cse2, tms1, tms2, ptms1, ptms2) in
        let new_t = Apply(x1,y1,a) in
        maybeAbstract(new_t, new_cse, names, bindable?, single_tms, poss_tms, spc)

      | Record(fields,a) ->
        let (new_fields,names,b_cse,b_single_tms,b_poss_tms)
           = foldr (fn ((pid,st),(new_binds,names,b_cse,b_single_tms,b_poss_tms)) ->
                      let (st1, cse1, tms1, ptms1, names) = recAbstractCSE(st, names, false, spc) in
                      let (new_cse, single_tms, poss_tms) = newCSEs(cse1, b_cse, tms1, b_single_tms,
                                                                    ptms1, b_poss_tms)
                      in
                      ((pid, st1) :: new_binds, names, new_cse, single_tms, poss_tms))
               ([],names,[],[],[])
               fields
        in
        let new_t = Record(new_fields,a) in
        maybeAbstract(new_t, b_cse, names, bindable?, b_single_tms, b_poss_tms, spc)

      | IfThenElse(x,y,z,a) ->
        let (x1, csex, tmsx, ptmsx, names) = recAbstractCSE(x, names, false, spc) in
        %% Don't want expressions only appearing in y or z lifted
        let (y1, csey, tmsy, ptmsy, names) = recAbstractCSE(y, names, true, spc) in
        let (z1, csez, tmsz, ptmsz, names) = recAbstractCSE(z, names, true, spc) in
        let poss_tms = termsUnion(ptmsx,
                       termsUnion(tmsy,
                       termsUnion(tmsz,
                       termsUnion(ptmsy, ptmsz))))
        in
        let cse = termsUnion(csex,
                  termsUnion(termsIntersect(tmsx, poss_tms),
                             termsIntersect(tmsy, tmsz)))
        in
        let tms = termsDiff(tmsx, cse) in
        let poss_tms = termsDiff(poss_tms, cse) in
        let new_t = IfThenElse(x1,y1,z1,a) in
        maybeAbstract(new_t, cse, names, bindable?, tms, poss_tms, spc)
        
      | Let(binds,body,a) ->
        let (new_binds,names,b_cse,b_single_tms,b_poss_tms)
           = foldr (fn ((p,st),(new_binds,names,b_cse,b_single_tms,b_poss_tms)) ->
                      let (st1, cse1, tms1, ptms1, names) = recAbstractCSE(st, names, false, spc) in
                      let (new_cse, single_tms, poss_tms) = newCSEs(cse1, b_cse, tms1, b_single_tms,
                                                                    ptms1, b_poss_tms)
                      in
                      (Cons((p,st1), new_binds),
                       names, new_cse, single_tms, poss_tms))
               ([],names,[],[],[])
               binds
        in
        let bvs = boundVars t in
        let (body2, [], tms2, ptms2, names) = recAbstractCSE(body, names, true, spc) in
        let (body3, cse3, tms3, ptms3, names) = (body2, [], tms2, ptms2, names)
%             (case filter (fn ct -> hasRefTo?(ct,bvs)) cse2 of
%                | [] -> (body2, cse2, tms2, ptms2, names)
%                | cse2a -> maybeAbstract(body2,cse2a,names,true,tms2, ptms2, spc))
        in
        let (new_cse, single_tms, poss_tms) = newCSEs(b_cse, cse3, b_single_tms, tms3,
                                                      b_poss_tms, ptms3)
        in
        let new_t = Let(new_binds,body3,a) in
        maybeAbstract(new_t, new_cse, names, bindable?, single_tms, poss_tms, spc)

      | Lambda((p0,c0,b0)::r_matches,a) ->
        let (b0, _, tms0, ptms0, names) = recAbstractCSE(b0, names, true, spc) in
        let bvs0 = patternVars p0 in
        let tms0  = removeLocal( tms0,bvs0) in
        let ptms0 = removeLocal(ptms0,bvs0) in
        let (new_binds,names,b_cse,b_single_tms,b_poss_tms)
           = if r_matches = [] then ([(p0,c0,b0)],names,[],tms0,ptms0)
             else
             foldl (fn ((new_binds,names,b_cse,_,b_poss_tms),(p1,c1,b1)) ->
                      let (b1, _, tms1, ptms1, names) = recAbstractCSE(b1, names, true, spc) in
                      let bvs1 = patternVars p1 in
                      let tms1  = filter (fn ct -> ~(hasRefTo?(ct,bvs1)))  tms1 in
                      let ptms1 = filter (fn ct -> ~(hasRefTo?(ct,bvs1))) ptms1 in
                      (Cons((p1,c1,b1), new_binds),
                       names, termsIntersect(b_cse, tms1),
                       [], termsUnion(b_poss_tms,
                                      termsUnion(tms1,ptms1)))
                      )
               ([(p0,c0,b0)],names,tms0,[],termsUnion(tms0,ptms0))
               r_matches
        in
        let new_t = Lambda(reverse new_binds,a) in
        maybeAbstract(new_t, b_cse, names, bindable?,
                      %% When do you want to abstract lambdas?
                      %% Cons(new_t, b_single_tms)
                      b_single_tms, b_poss_tms, spc)

      | Seq(act1 :: r_acts, a) ->
        let (nr_acts, names) = foldr (fn (act_i, (nr_acts, names)) ->
                                       let (n_act_i, _, _, _, names) = recAbstractCSE(act_i, names, true, spc) in
                                       (n_act_i :: nr_acts, names))
                                 ([], names) r_acts
        in
        let (n_act1, new_cse, single_tms, poss_tms, names) = recAbstractCSE(act1, names, false, spc) in
        let new_t = Seq(n_act1 :: nr_acts, a) in
        maybeAbstract(new_t, new_cse, names, bindable?, single_tms, poss_tms, spc)
      
      %% To add!
      %% | Bind(b,vs,bod) ->
      
      | _ -> (t,[],[],[],names)

  op cseVar?(vn: Id): Bool =
    testSubseqEqual?("cse", vn, 0, 0)

  op dontAbstract?(tm: MSTerm): Bool =
    case tm of
      | Lambda _ -> true
      | Apply(Fun(Project _, _, _), _, _) -> true
      | Record(fld_vals as (("1", _) :: _), _) ->
        forall? (fn (_, tm) -> embed? Var tm) fld_vals
      | _ -> false

  op abstractCommonSubExpressions(t: MSTerm, spc: Spec): MSTerm =
    let all_names = map (fn (nm,_) ->  nm) (boundVarsIn t) in
    let result = (recAbstractCSE(t, all_names, true, spc)).1 in
    let cseVarSubst = foldSubTerms (fn (t, sb) ->
                                      case  t of
                                        | Let([(VarPat (v,_),e)],_,_) | cseVar? v.1 ->
                                          (v,e) :: sb
                                        | _ -> sb)
                        [] result
    in
    let result = mapTerm (fn t ->
                            case t of
                              | Let([(VarPat (v,_),e)],body,_) | cseVar? v.1 && countVarRefs(body, v) = 1 ->
                                substitute(body,[(v,e)])
                              | Apply(setf_fn as Fun(Op(Qualified("System", "setf"), _), _, _),
                                      Record([("1", term_to_modify as Var(v,_)), ("2", val_term)], a1), a0) | cseVar? v.1 ->
                                Apply(setf_fn, Record([("1", substitute(term_to_modify, cseVarSubst)), ("2", val_term)], a1), a0)
                              | _ -> t,
                          id, id)
                   result
    in
    result

end-spec
