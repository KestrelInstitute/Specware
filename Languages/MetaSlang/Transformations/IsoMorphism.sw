(* Takes isomorphism function iso_qid and its inverse inv_iso_qid,
   Extracts State and State'
   Find all functions f that take State as an argument or returned value and create
   f' with State' instead of State. The body is a call to f with state parameters wrapped in
   inv_iso_qid and result state wrapped in iso_qid.

   Simplify all
     Distributive rules
     fa(x': State') iso_qid(inv_iso_qid x')) = x'

   Simplify
*)

Isomorphism qualifying
spec
  import Script
  import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements

  op mkMapApply(fn_arg: MS.Term, list_arg: MS.Term, dom_ty: Sort, rng_ty): MS.Term =
    mkApply(mkApply(mkInfixOp
                      (Qualified("List","map"),
                       Unspecified,
                       mkArrow(mkArrow(dom_ty,rng_ty),
                               mkArrow(mkBase(Qualified("List","List"), [dom_ty]),
                                       mkBase(Qualified("List","List"),
                                              [rng_ty])))),
                    fn_arg),
            list_arg)

  op createPrimeDef(spc: Spec, orig_op_ref: MS.Term, old_dfn: MS.Term,
                    def_ty: Sort, src_ty: Sort, trg_ty: Sort,
                    iso_ref: MS.Term, inv_iso_ref: MS.Term)
     : MS.Term =
    let
      def makePrimedPat p =
        case p of
          | VarPat((vn,v_ty),a) \_rightarrow
            if equalType?(v_ty,src_ty)
              then VarPat((vn^"'",trg_ty),a)
              else
               (case v_ty of
                 | Base(Qualified("List","List"),[el_ty],a1) | equalType?(el_ty, src_ty) \_rightarrow
                   VarPat((vn^"'",Base(Qualified("List","List"),[trg_ty],a1)),a)
                 | _ \_rightarrow p)
          | RecordPat(idprs,a) \_rightarrow
            RecordPat(map (fn (id,p) \_rightarrow (id,makePrimedPat p)) idprs, a)
          | RestrictedPat(p1,pred,a) \_rightarrow RestrictedPat(makePrimedPat p1,pred,a)
          | _ \_rightarrow p
      def paramsToPrimedArgs p =
        case p of
          | VarPat((vn,v_ty),a) \_rightarrow
            if equalType?(v_ty,src_ty)
              then mkApply(inv_iso_ref,Var((vn^"'",trg_ty),a))
              else
                (case v_ty of
                 | Base(Qualified("List","List"),[el_ty],a1) | equalType?(el_ty, src_ty) \_rightarrow
                   mkMapApply(inv_iso_ref, Var((vn^"'",trg_ty),a), trg_ty, src_ty)
                 | _ \_rightarrow Var((vn,v_ty),a))
          | RecordPat(idprs,a) \_rightarrow
            Record(map (fn (id,p) \_rightarrow (id,paramsToPrimedArgs p)) idprs, a)
          | RestrictedPat(p1,_,_) \_rightarrow paramsToPrimedArgs p1
          | _ \_rightarrow (warn("createPrimeFnBody: parameter case not handled"^printPattern p);
                  falseTerm)
      def makePrimeBody (old_def_tm,new_bod) =
        case old_def_tm of
         | Lambda(binds,a) \_rightarrow
           let new_binds = map (fn (p,condn,body) \_rightarrow
                                  (makePrimedPat p,condn,
                                   makePrimeBody(body,mkApply(new_bod,paramsToPrimedArgs p))))
                             binds
           in
           Lambda(new_binds,a)
         | _ \_rightarrow
           %% !! Generalize to handle tuple containing src_ty as a component
           let result_ty = termSort new_bod in
           if equalType?(result_ty, src_ty)
             then mkApply(iso_ref, new_bod)
             else
               case result_ty of
                 | Base(Qualified("List","List"),[el_ty],a) | equalType?(el_ty, src_ty) \_rightarrow
                   %% map iso_ref new_bod
                   mkMapApply(iso_ref, new_bod, src_ty, trg_ty)
                 | _ \_rightarrow new_bod
    in
   makePrimeBody(old_dfn, orig_op_ref)    

  op makePrimedOps(spc: Spec, src_ty: Sort, trg_ty: Sort,
                   iso_ref: MS.Term, inv_iso_ref: MS.Term, ign_qids: List QualifiedId)
     : List (QualifiedId * OpInfo) =
    foldriAQualifierMap
      (fn (q, nm, info, result) ->
       let qid = Qualified(q,nm) in
       let (tvs, op_ty, dfn) = unpackTerm info.dfn in
       case dfn  of
         | Any _ \_rightarrow result
         | _ \_rightarrow
       let def ty_to_ty' ty =
             if equalType?(ty,src_ty)
               then trg_ty
               else ty
       in
       let op_ty' = mapSort (id,ty_to_ty',id) op_ty in
       if member(qid,ign_qids)
         \_or equalType?(op_ty',op_ty)
         then result
        else
          let qid_ref = mkInfixOp(qid,info.fixity,op_ty) in
          let qid' = Qualified(q,nm^"'") in
          let dfn' = createPrimeDef(spc, qid_ref, dfn, op_ty, src_ty, trg_ty,
                                    iso_ref, inv_iso_ref)
          in
          let qid'_ref = mkInfixOp(qid',info.fixity,op_ty') in
  %        let new_def = createPrimeDef(spc, qid'_ref, dfn', op_ty, trg_ty, src_ty,
%                                       inv_iso_ref, iso_ref)
%          in
          Cons((qid,
                info \_guillemotleft {names = [qid'],
                        dfn = maybePiTerm(tvs, SortedTerm(dfn', op_ty', noPos))}),
               result))
      []
      spc.ops

  op printDef(spc: Spec, qid: QualifiedId): () =
    case findTheOp(spc,qid) of
      | None \_rightarrow (warn("Can't find op "^anyToString qid);
                 ())
      | Some opinfo \_rightarrow
    let (tvs, ty, dfn) = unpackTerm opinfo.dfn in
    let _ = writeLine(printQualifiedId qid^":") in
    writeLine(printTerm dfn)

  def Isomorphism.makeIsoMorphism(spc: Spec, iso_qid: QualifiedId, inv_iso_qid: QualifiedId): Spec =
    case findTheOp(spc,iso_qid) of
      | None \_rightarrow (warn("Can't find op "^anyToString iso_qid);
                 spc)
      | Some iso_opinfo \_rightarrow
    let (tvs, iso_ty, _) = unpackTerm iso_opinfo.dfn in
    case findTheOp(spc,inv_iso_qid) of
      | None \_rightarrow (warn("Can't find op "^anyToString inv_iso_qid);
                 spc)
      | Some inv_iso_opinfo \_rightarrow
    case arrowOpt(spc,iso_ty) of
      | None  \_rightarrow (warn(anyToString iso_qid^" is not a function!");
                 spc)
      | Some(src_ty,trg_ty) \_rightarrow
    let (inv_tvs, inv_iso_ty, _) = unpackTerm inv_iso_opinfo.dfn in
    case arrowOpt(spc,inv_iso_ty) of
      | None  \_rightarrow (warn(anyToString inv_iso_qid^" is not a function!");
                 spc)
      | Some(inv_src_ty,inv_trg_ty) \_rightarrow
    if ~(length tvs = length inv_tvs
           && equalType?(src_ty,inv_trg_ty)
           && equalType?(trg_ty,inv_src_ty))
      then (warn(anyToString iso_qid^" and "^anyToString inv_iso_qid^" types not inverse!");
                 spc)
    else
    let iso_ref = mkInfixOp(iso_qid, iso_opinfo.fixity, iso_ty) in
    let inv_iso_ref = mkInfixOp(inv_iso_qid, inv_iso_opinfo.fixity, inv_iso_ty) in

    %% Thm fa(x) iso(inv_iso x) = x
    let x'_var = ("x'",trg_ty) in
    let inv_thm = mkBind(Forall,[x'_var],
                         mkEquality(trg_ty,
                                    mkApply(iso_ref,mkApply(inv_iso_ref, mkVar x'_var)),
                                    mkVar x'_var))
    in
    let iso_inv_iso_qid = Qualified("generated","iso_inv_iso") in
    let spc = addTheorem((iso_inv_iso_qid, tvs,inv_thm, noPos), spc) in

    let primed_defs = makePrimedOps(spc, src_ty, trg_ty, iso_ref, inv_iso_ref,
                                    [iso_qid,inv_iso_qid]) in
    let spc = foldl (fn ((_,opinfo),spc) \_rightarrow
                     let qid = hd opinfo.names in
                     let spc =  appendElement(spc,Op(qid,true,noPos)) in
                     setOpInfo(spc,qid,opinfo))
                spc primed_defs
    in    
    let x'_var = ("x'",trg_ty) in
    let inv_thm = mkBind(Forall,[x'_var],
                         mkApply(iso_ref,mkApply(inv_iso_ref, mkVar x'_var)))
    in
    let folds = map (fn (_,opinfo) \_rightarrow Fold(hd opinfo.names)) primed_defs in
    let main_script = Simplify([Unfold(mkUnQualifiedId "inv_iso"),
                                LeftToRight(iso_inv_iso_qid),
                                %LeftToRight(mkUnQualifiedId "f_if_then_else"),
                                %% Should be in specs
                                LeftToRight(mkUnQualifiedId "iso_set_fold"),
                                LeftToRight(mkUnQualifiedId "map_empty"),
                                LeftToRight(mkUnQualifiedId "map_doubleton")]
                                 ++ folds)
    in
    let simp_primed_defs
       = map (fn (orig_qid, opinfo) \_rightarrow
                let _ = printDef(spc,orig_qid) in
                let qid = hd opinfo.names in
                let _ = printDef(spc,qid) in
                let (tvs, ty, dfn) = unpackTerm opinfo.dfn in
                let unfold_dfn = interpretTerm(spc, Apply[Unfold orig_qid],
                                               dfn)
                in
                let simp_dfn = interpretTerm(spc, main_script, unfold_dfn) in
                let new_dfn = maybePiTerm(tvs, SortedTerm (simp_dfn, ty, noPos)) in
                let _ = writeLine(printQualifiedId qid^":") in
                let _ = writeLine(printTerm new_dfn^"\n") in
                opinfo \_guillemotleft {dfn = new_dfn})
            primed_defs
    in
    let spc = foldl (fn (opinfo,spc) \_rightarrow
                     let qid = hd opinfo.names in
                     setOpInfo(spc,qid,opinfo))
                spc simp_primed_defs
    in
    spc
    

endspec