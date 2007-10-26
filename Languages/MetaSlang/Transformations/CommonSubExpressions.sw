CSE qualifying
spec
  import /Languages/MetaSlang/Specs/Utilities, CurryUtils

  op newCSEs(tms1: List MS.Term, tms2: List MS.Term, cse1: List MS.Term, cse2: List MS.Term)
    : List MS.Term * List MS.Term =
    let cse12 = termsIntersect(tms1, tms2) in
    let new_ces = termsUnion(cse12, termsUnion(cse1, cse2)) in
    let single_tms = termsDiff(termsUnion(tms1, tms2), new_ces) in
    (new_ces, single_tms)

  op hasRefsTo?(t: MS.Term, vs: List Var): Boolean =
    exists (fn v -> inVars?(v, vs)) (freeVars t)

  op removeLocal(tms: List MS.Term, vs: List Var): List MS.Term =
    filter (fn t -> ~(hasRefsTo?(t,vs))) tms

  op maybeAbstract(t: MS.Term, cse: List MS.Term, names: List String,
                   bindable?: Boolean, single_tms: List MS.Term, spc: Spec)
    : MS.Term * List MS.Term * List MS.Term * List String =
    let bvs = boundVars t in
    let cse = removeLocal(cse,bvs) in
    let single_tms = removeLocal(single_tms,bvs) in
    case cse of
      | _::_ | bindable? ->
        let Some big_cse = maximal termSize cse in
        let nm = newName("cse",names) in
        let ty = inferType(spc, t) in
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
      | _ -> (t, cse, single_tms, names)

  op mkCurriedApply(f: MS.Term, terms: List MS.Term): MS.Term =
    foldl (fn (t,r) -> mkApply(r,t)) f terms

  op recAbstractCSE(t: MS.Term, names: List String, bindable?: Boolean, spc: Spec)
    : MS.Term * List MS.Term * List MS.Term * List String =
    case getCurryArgs t of
      | Some(f,c_args) ->
        %% Don't wan't to abstract partial applications
        let (new_c_args,names,ces,single_tms) =
            foldr (fn (st,(new_c_args,names,ces,single_tms)) ->
                      let (st1, ces1, tms1, names) = recAbstractCSE(st, names, false, spc) in
                      let (new_ces, single_tms) = newCSEs(tms1, single_tms, ces1, ces) in
                      (Cons(st1, new_c_args),
                       names, new_ces, single_tms))
               ([],names,[],[])
               c_args
        in
        let new_t = mkCurriedApply(f, new_c_args) in
        maybeAbstract(new_t, ces, names, bindable?, Cons(new_t, single_tms), spc)

      | None ->
    case t of
      | Apply(x,y,a) ->
        %% Careful about abstracting fns
        let (x1, ces1, tms1, names) = recAbstractCSE(x, names, false, spc) in
        let (y1, ces2, tms2, names) = recAbstractCSE(y, names, false, spc) in
        let tms1 = if embed? Lambda x then tms1 else [] in
        let (new_ces, single_tms) = newCSEs(tms1, tms2, ces1, ces2) in
        let new_t = Apply(x1,y1,a) in
        maybeAbstract(new_t, new_ces, names, bindable?, Cons(new_t, single_tms), spc)

      | Record(fields,a) ->
        let (new_fields,names,b_ces,b_single_tms)
           = foldr (fn ((pid,st),(new_binds,names,b_ces,b_single_tms)) ->
                      let (st1, ces1, tms1, names) = recAbstractCSE(st, names, false, spc) in
                      let (new_ces, single_tms) = newCSEs(tms1, b_single_tms, ces1, b_ces) in
                      (Cons((pid, st1), new_binds),
                       names, new_ces, single_tms))
               ([],names,[],[])
               fields
        in
        let new_t = Record(new_fields,a) in
        maybeAbstract(new_t, b_ces, names, bindable?,
                      if bindable?      % Mainly to avoid abstracting function args
                        then Cons(new_t, b_single_tms)
                        else b_single_tms, spc)

      | IfThenElse(x,y,z,a) ->
        let (x1, cesx, tmsx, names) = recAbstractCSE(x, names, false, spc) in
        %% Don't want expressions only appearing in y or z lifted
        let (y1, csey, tmsy, names) = recAbstractCSE(y, names, true, spc) in
        let (z1, csez, tmsz, names) = recAbstractCSE(z, names, true, spc) in
        let ces = termsUnion(termsIntersect(tmsx,tmsy),
                             termsUnion(termsIntersect(tmsx, tmsz),
                                        termsIntersect(tmsy, tmsz)))
        in
        let tms = termsDiff(tmsx, ces) in
        let new_t = IfThenElse(x1,y1,z1,a) in
        maybeAbstract(new_t, ces, names, bindable?, Cons(new_t, tms), spc)
        
      | Let(binds,body,a) ->
        let (new_binds,names,b_ces,b_single_tms)
           = foldr (fn ((p,st),(new_binds,names,b_ces,b_single_tms)) ->
                      let (st1, ces1, tms1, names) = recAbstractCSE(st, names, false, spc) in
                      let (new_ces, single_tms) = newCSEs(tms1, b_single_tms, ces1, b_ces) in
                      (Cons((p,st1), new_binds),
                       names, new_ces, single_tms))
               ([],names,[],[])
               binds
        in
        let bvs = boundVars t in
        let (body2, ces2, tms2, names) = recAbstractCSE(body, names, true, spc) in
        let (body3, ces3, tms3, names) =
            (case filter (fn ct -> hasRefTo?(ct,bvs)) ces2 of
               | [] -> (body2, ces2, tms2, names)
               | cse2a -> maybeAbstract(body2,cse2a,names,true,tms2, spc))
        in
        let (new_ces, single_tms) = newCSEs(b_single_tms, tms3, b_ces, ces3) in
        let new_t = Let(new_binds,body3,a) in
        maybeAbstract(new_t, new_ces, names, bindable?, Cons(new_t, single_tms), spc)

      | Lambda(matches,a) ->
        let (new_binds,names,b_ces,b_single_tms)
           = foldr (fn ((p1,c1,b1),(new_binds,names,b_ces,b_single_tms)) ->
                      let (b2, ces1, tms1, names) = recAbstractCSE(b1, names, true, spc) in
                      let bvs = patternVars p1 in
                      let (b3, tms3, ces3, names) =
                          (case filter (fn ct -> hasRefTo?(ct,bvs)) ces1 of
                             | [] -> (b2, tms1, ces1, names)
                             | cse2a -> maybeAbstract(b2,cse2a,names,true,tms1, spc))
                      in
%                       let (new_ces, single_tms) = newCSEs(tms3, b_single_tms, ces3, b_ces) in
%                       (Cons((p1,c1,b3), new_binds),
%                        names, new_ces, single_tms)
                      (Cons((p1,c1,b3), new_binds),
                       names, termsUnion(ces3, b_ces), termsUnion(tms3, b_single_tms))
                      )
               ([],names,[],[])
               matches
        in
        let new_t = Lambda(new_binds,a) in
        maybeAbstract(new_t, b_ces, names, bindable?,
                      %% When do you want to abstract lambdas?
                      %% Cons(new_t, b_single_tms)
                      b_single_tms, spc)
      
      %% To add!
      %% | Bind(b,vs,bod) ->

      | _ -> (t,[],[], names)


  op abstractCommonSubExpressions(t: MS.Term, spc: Spec): MS.Term =
    let all_names = map (fn (nm,_) ->  nm) (boundVarsIn t) in
    (recAbstractCSE(t, all_names, true, spc)).1

endspec
