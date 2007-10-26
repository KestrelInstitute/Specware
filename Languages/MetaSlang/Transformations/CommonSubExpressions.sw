CSE qualifying
spec
  import /Languages/MetaSlang/Specs/Utilities, CurryUtils

  op newCSEs(cse1: List MS.Term, cse2: List MS.Term, tms1: List MS.Term, tms2: List MS.Term,
             poss_tms1: List MS.Term, poss_tms2: List MS.Term)
    : List MS.Term * List MS.Term * List MS.Term =
    let cse12 = termsUnion(termsIntersect(tms1, tms2),
                           termsUnion(termsIntersect(tms1, poss_tms2),
                                      termsIntersect(poss_tms1, tms2)))
    in
    let new_ces = termsUnion(cse12, termsUnion(cse1, cse2)) in
    let single_tms = termsDiff(termsUnion(tms1, tms2), new_ces) in
    let poss_tms = termsDiff(termsUnion(poss_tms1, poss_tms2), new_ces) in
    (new_ces, single_tms, poss_tms)

  op removeLocal(tms: List MS.Term, vs: List Var): List MS.Term =
    filter (fn t -> ~(hasRefTo?(t,vs))) tms

  op maybeAbstract(t: MS.Term, cse: List MS.Term, names: List String, bindable?: Boolean,
                   single_tms: List MS.Term, poss_tms: List MS.Term, spc: Spec)
    : MS.Term * List MS.Term * List MS.Term * List MS.Term * List String =
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
        let single_tms = case t of
                           | Lambda _ -> single_tms
                           | _ -> Cons(t, single_tms)
        in
        (t, cse, single_tms, poss_tms, names)

  op mkCurriedApply(f: MS.Term, terms: List MS.Term): MS.Term =
    foldl (fn (t,r) -> mkApply(r,t)) f terms

  op recAbstractCSE(t: MS.Term, names: List String, bindable?: Boolean, spc: Spec)
    : MS.Term * List MS.Term * List MS.Term * List MS.Term * List String =
    case getCurryArgs t of
      | Some(f,c_args) ->
        %% Don't wan't to abstract partial applications
        let (new_c_args,names,ces,single_tms,poss_tms) =
            foldr (fn (st,(new_c_args,names,ces,single_tms,poss_tms)) ->
                      let (st1, ces1, tms1, ptms1, names) = recAbstractCSE(st, names, false, spc) in
                      let (new_ces, single_tms, poss_tms) = newCSEs(ces1, ces, tms1, single_tms,
                                                                    ptms1, poss_tms)
                      in
                      (Cons(st1, new_c_args),
                       names, new_ces, single_tms, poss_tms))
               ([],names,[],[],[])
               c_args
        in
        let new_t = mkCurriedApply(f, new_c_args) in
        maybeAbstract(new_t, ces, names, bindable?, single_tms, poss_tms, spc)

      | None ->
    case t of
      | Apply(x,y,a) ->
        %% Careful about abstracting fns
        let (x1, ces1, tms1, ptms1, names) = recAbstractCSE(x, names, false, spc) in
        let tms1 = case tms1 of
                     | (Lambda _)::r_tms1 -> r_tms1
                     | _ -> tms1
        in
        let (y1, ces2, tms2, ptms2, names) = recAbstractCSE(y, names, false, spc) in
        let tms2 = case tms2 of
                     | (Record _)::r_tms2 -> r_tms2
                     | _ -> tms2
        in
        let (new_ces, single_tms, poss_tms) = newCSEs(ces1, ces2, tms1, tms2, ptms1, ptms2) in
        let new_t = Apply(x1,y1,a) in
        maybeAbstract(new_t, new_ces, names, bindable?, single_tms, poss_tms, spc)

      | Record(fields,a) ->
        let (new_fields,names,b_ces,b_single_tms,b_poss_tms)
           = foldr (fn ((pid,st),(new_binds,names,b_ces,b_single_tms,b_poss_tms)) ->
                      let (st1, ces1, tms1, ptms1, names) = recAbstractCSE(st, names, false, spc) in
                      let (new_ces, single_tms, poss_tms) = newCSEs(ces1, b_ces, tms1, b_single_tms,
                                                                    ptms1, b_poss_tms)
                      in
                      (Cons((pid, st1), new_binds),
                       names, new_ces, single_tms, poss_tms))
               ([],names,[],[],[])
               fields
        in
        let new_t = Record(new_fields,a) in
        maybeAbstract(new_t, b_ces, names, bindable?, b_single_tms, b_poss_tms, spc)

      | IfThenElse(x,y,z,a) ->
        let (x1, cesx, tmsx, ptmsx, names) = recAbstractCSE(x, names, false, spc) in
        %% Don't want expressions only appearing in y or z lifted
        let (y1, csey, tmsy, ptmsy, names) = recAbstractCSE(y, names, true, spc) in
        let (z1, csez, tmsz, ptmsz, names) = recAbstractCSE(z, names, true, spc) in
        let poss_tms = termsUnion(tmsy,
                       termsUnion(tmsz,
                       termsUnion(ptmsy, ptmsz)))
        in
        let ces = termsUnion(termsIntersect(tmsx, poss_tms),
                             termsIntersect(tmsy, tmsz))
        in
        let tms = termsDiff(tmsx, ces) in
        let poss_tms = termsDiff(poss_tms, ces) in
        let new_t = IfThenElse(x1,y1,z1,a) in
        maybeAbstract(new_t, ces, names, bindable?, tms, poss_tms, spc)
        
      | Let(binds,body,a) ->
        let (new_binds,names,b_ces,b_single_tms,b_poss_tms)
           = foldr (fn ((p,st),(new_binds,names,b_ces,b_single_tms,b_poss_tms)) ->
                      let (st1, ces1, tms1, ptms1, names) = recAbstractCSE(st, names, false, spc) in
                      let (new_ces, single_tms, poss_tms) = newCSEs(ces1, b_ces, tms1, b_single_tms,
                                                                    ptms1, b_poss_tms)
                      in
                      (Cons((p,st1), new_binds),
                       names, new_ces, single_tms, poss_tms))
               ([],names,[],[],[])
               binds
        in
        let bvs = boundVars t in
        let (body2, [], tms2, ptms2, names) = recAbstractCSE(body, names, true, spc) in
        let (body3, ces3, tms3, ptms3, names) = (body2, [], tms2, ptms2, names)
%             (case filter (fn ct -> hasRefTo?(ct,bvs)) ces2 of
%                | [] -> (body2, ces2, tms2, ptms2, names)
%                | cse2a -> maybeAbstract(body2,cse2a,names,true,tms2, ptms2, spc))
        in
        let (new_ces, single_tms, poss_tms) = newCSEs(b_ces, ces3, b_single_tms, tms3,
                                                      b_poss_tms, ptms3)
        in
        let new_t = Let(new_binds,body3,a) in
        maybeAbstract(new_t, new_ces, names, bindable?, single_tms, poss_tms, spc)

      | Lambda((p0,c0,b0)::r_matches,a) ->
        let (b0, _, tms0, ptms0, names) = recAbstractCSE(b0, names, true, spc) in
        let bvs0 = patternVars p0 in
        let tms0  = removeLocal( tms0,bvs0) in
        let ptms0 = removeLocal(ptms0,bvs0) in
        let (new_binds,names,b_ces,b_single_tms,b_poss_tms)
           = if r_matches = [] then ([(p0,c0,b0)],names,[],tms0,ptms0)
             else
             foldl (fn ((p1,c1,b1),(new_binds,names,b_ces,_,b_poss_tms)) ->
                      let (b1, _, tms1, ptms1, names) = recAbstractCSE(b1, names, true, spc) in
                      let bvs1 = patternVars p1 in
                      let tms1  = filter (fn ct -> ~(hasRefTo?(ct,bvs1)))  tms1 in
                      let ptms1 = filter (fn ct -> ~(hasRefTo?(ct,bvs1))) ptms1 in
                      (Cons((p1,c1,b1), new_binds),
                       names, termsIntersect(b_ces, tms1),
                       [], termsUnion(b_poss_tms,
                                      termsUnion(tms1,ptms1)))
                      )
               ([(p0,c0,b0)],names,tms0,[],termsUnion(tms0,ptms0))
               r_matches
        in
        let new_t = Lambda(rev new_binds,a) in
        maybeAbstract(new_t, b_ces, names, bindable?,
                      %% When do you want to abstract lambdas?
                      %% Cons(new_t, b_single_tms)
                      b_single_tms, b_poss_tms, spc)
      
      %% To add!
      %% | Bind(b,vs,bod) ->

      | _ -> (t,[],[],[],names)


  op abstractCommonSubExpressions(t: MS.Term, spc: Spec): MS.Term =
    let all_names = map (fn (nm,_) ->  nm) (boundVarsIn t) in
    (recAbstractCSE(t, all_names, true, spc)).1

endspec
