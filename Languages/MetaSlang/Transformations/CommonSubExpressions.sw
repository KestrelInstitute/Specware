CSE qualifying
spec
  import /Languages/MetaSlang/Specs/Utilities

  op newCSEs(tms1: List MS.Term, tms2: List MS.Term, cse1: List MS.Term, cse2: List MS.Term)
    : List MS.Term * List MS.Term =
    let cse12 = termsIntersect(tms1, tms2) in
    let new_ces = termsUnion(cse12, termsUnion(cse1, cse2)) in
    let single_tms = termsDiff(termsUnion(tms1, tms2), new_ces) in
    (new_ces, single_tms)

  op hasRefsTo?(t: MS.Term, vs: List Var): Boolean =
    exists (fn v -> inVars?(v, vs)) (freeVars t)

  op maybeAbstract(t: MS.Term, cse: List MS.Term, names: List String,
                   bindable?: Boolean, single_tms: List MS.Term)
    : MS.Term * List MS.Term * List MS.Term * List String =
    case cse of
      | _::_ | bindable? ->
        let Some big_cse = maximal termSize cse in
        let nm = newName("cse",names) in
        let ty = termSort t in
        let v = (nm, ty) in
        let vr = mkVar v in
        let new_bod = mapTerm (fn st -> if equalTerm?(big_cse,st) then vr else st, id,id) t in
        let new_t = mkLet([(mkVarPat v, big_cse)], new_bod) in
        recAbstractCSE(new_t, Cons(nm, names), true)        
      | _ -> (t, cse, single_tms, names)

  op recAbstractCSE(t: MS.Term, names: List String, bindable?: Boolean)
    : MS.Term * List MS.Term * List MS.Term * List String =
    case t of
      | Apply(x,y,a) ->
        %% Careful about abstracting fns
        let (x1, ces1, _, names) = recAbstractCSE(x, names, false) in
        let (y1, ces2, tms2, names) = recAbstractCSE(y, names, false) in
        let (new_ces, single_tms) = newCSEs([], tms2, ces1, ces2) in
        let new_t = Apply(x1,y1,a) in
        maybeAbstract(new_t, new_ces, names, bindable?, Cons(new_t, single_tms))

      | Record(fields,a) ->
        let (new_fields,names,b_ces,b_single_tms)
           = foldr (fn ((pid,st),(new_binds,names,b_ces,b_single_tms)) ->
                      let (st1, ces1, tms1, names) = recAbstractCSE(st, names, false) in
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
                        else b_single_tms)

      | IfThenElse(x,y,z,a) ->
        let (x1, cesx, tmsx, names) = recAbstractCSE(x, names, false) in
        %% Don't want expressions only appearing in y or z lifted
        let (y1, csey, tmsy, names) = recAbstractCSE(y, names, true) in
        let (z1, csez, tmsz, names) = recAbstractCSE(z, names, true) in
        let ces = termsUnion(termsIntersect(tmsx,tmsy),
                             termsUnion(termsIntersect(tmsx, tmsz),
                                        termsIntersect(tmsy, tmsz)))
        in
        let tms = termsDiff(tmsx, ces) in
        let new_t = IfThenElse(x1,y1,z1,a) in
        maybeAbstract(new_t, ces, names, bindable?, Cons(new_t, tms))
        
      | Let(binds,body,a) ->
        let (new_binds,names,b_ces,b_single_tms)
           = foldr (fn ((p,st),(new_binds,names,b_ces,b_single_tms)) ->
                      let (st1, ces1, tms1, names) = recAbstractCSE(st, names, false) in
                      let (new_ces, single_tms) = newCSEs(tms1, b_single_tms, ces1, b_ces) in
                      (Cons((p,st1), new_binds),
                       names, new_ces, single_tms))
               ([],names,[],[])
               binds
        in
        let bvs = boundVars t in
        let (body2, ces2, tms2, names) = recAbstractCSE(body, names, true) in
        let (body3, ces3, tms3, names) =
            (case filter (fn ct -> hasRefTo?(ct,bvs)) ces2 of
               | [] -> (body2, ces2, tms2, names)
               | cse2a -> maybeAbstract(body2,cse2a,names,true,tms2))
        in
        let (new_ces, single_tms) = newCSEs(b_single_tms, tms3, b_ces, ces3) in
        let new_t = Let(new_binds,body3,a) in
        maybeAbstract(new_t, new_ces, names, bindable?, Cons(new_t, single_tms))

      | Lambda(matches,a) ->
        let (new_binds,names,b_ces,b_single_tms)
           = foldr (fn ((p1,c1,b1),(new_binds,names,b_ces,b_single_tms)) ->
                      let (b2, ces1, tms1, names) = recAbstractCSE(b1, names, true) in
                      let bvs = patternVars p1 in
                      let (b3, tms3, ces3, names) =
                          (case filter (fn ct -> hasRefTo?(ct,bvs)) ces1 of
                             | [] -> (b2, tms1, ces1, names)
                             | cse2a -> maybeAbstract(b2,cse2a,names,true,tms1))
                      in
                      let (new_ces, single_tms) = newCSEs(tms1, b_single_tms, ces1, b_ces) in
                      (Cons((p1,c1,b3), new_binds),
                       names, new_ces, single_tms))
               ([],names,[],[])
               matches
        in
        let new_t = Lambda(new_binds,a) in
        maybeAbstract(new_t, b_ces, names, bindable?, Cons(new_t, b_single_tms))
      
      %% To add!
      %% | Bind(b,vs,bod) ->

      | _ -> (t,[],[], names)


  op abstractCommonSubExpressions(t: MS.Term): MS.Term =
    let all_names = map (fn (nm,_) ->  nm) (boundVarsIn t) in
    (recAbstractCSE(t, all_names, true)).1

endspec
