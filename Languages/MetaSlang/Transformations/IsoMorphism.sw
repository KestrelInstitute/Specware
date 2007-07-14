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
                                       mkBase(Qualified("List","List"), [rng_ty])))),
                    fn_arg),
            list_arg)

  op makeIsoTheorems(spc: Spec, iso_ref: MS.Term, inv_iso_ref: MS.Term,
                     src_ty: Sort, trg_ty: Sort)
     : Spec * List QualifiedId =
    %% Thm fa(x) iso(inv_iso x) = x
    let x_pr_var = ("x'",trg_ty) in
    let inv_thm1 = mkBind(Forall,[x_pr_var],
                          mkEquality(trg_ty,
                                     mkApply(iso_ref,mkApply(inv_iso_ref, mkVar x_pr_var)),
                                     mkVar x_pr_var))
    in
    let iso__inv_iso_qid = Qualified("generated","iso__inv_iso") in
    let spc = addTheorem((iso__inv_iso_qid, [], inv_thm1, noPos), spc) in

    %% Thm fa(x) inv_iso(iso x) = x
    let x_var = ("x",src_ty) in
    let inv_thm1 = mkBind(Forall,[x_var],
                          mkEquality(trg_ty,
                                     mkApply(inv_iso_ref,mkApply(iso_ref, mkVar x_var)),
                                     mkVar x_var))
    in
    let inv_iso__iso_qid = Qualified("generated","inv_iso__iso") in
    let spc = addTheorem((inv_iso__iso_qid, [], inv_thm1, noPos), spc) in

    %% Thm fa(x) map iso (map inv_iso x) = x
    let x_pr_var = ("x'", mkBase(Qualified("List","List"), [trg_ty])) in
    let inv_thm1 = mkBind(Forall,[x_pr_var],
                          mkEquality(mkBase(Qualified("List","List"), [trg_ty]),
                                     mkMapApply(iso_ref, mkMapApply(inv_iso_ref, mkVar x_pr_var,
                                                                    trg_ty, src_ty),
                                                src_ty, trg_ty),
                                     mkVar x_pr_var))
    in
    let map__iso__inv_iso_qid = Qualified("generated","map__iso__inv_iso") in
    let spc = addTheorem((iso__inv_iso_qid, [], inv_thm1, noPos), spc) in

    %% Thm fa(x) map inv_iso(map iso x) = x
    let x_var = ("x", mkBase(Qualified("List","List"), [src_ty])) in
    let inv_thm1 = mkBind(Forall,[x_var],
                          mkEquality(mkBase(Qualified("List","List"), [src_ty]),
                                     mkMapApply(inv_iso_ref, mkMapApply(iso_ref, mkVar x_var,
                                                                        src_ty, trg_ty),
                                                trg_ty, src_ty),
                                     mkVar x_var))
    in
    let map__inv_iso__iso_qid = Qualified("generated","map__inv_iso__iso") in
    let spc = addTheorem((inv_iso__iso_qid, [], inv_thm1, noPos), spc) in

    (spc, [iso__inv_iso_qid, inv_iso__iso_qid, map__iso__inv_iso_qid, map__inv_iso__iso_qid])


(*
    % inverse iso = inv_inv_iso
    let inv_thm = mkEquality(mkArrow(trg_ty,src_ty),
                             mkApply(mkInfixOp(Qualified("Functions", "inverse"), Unspecified,
                                               mkArrow(mkArrow(src_ty,trg_ty),
                                                       mkArrow(trg_ty,src_ty))),
                                     iso_ref),
                             inv_iso_ref)
    in
    let inv_thm_qid1 = Qualified("generated", "inverse_iso") in
    let spc = addTheorem((inv_thm_qid1, [], inv_thm, noPos), spc) in

    % inverse inv_inv_iso  = iso
    let inv_thm = mkEquality(mkArrow(src_ty,trg_ty),
                             mkApply(mkInfixOp(Qualified("Functions", "inverse"), Unspecified,
                                               mkArrow(mkArrow(trg_ty,src_ty),
                                                       mkArrow(src_ty,trg_ty))),
                                     inv_iso_ref),
                             iso_ref)
    in
    let inv_thm_qid2 = Qualified("generated", "inverse_rev_iso") in
    let spc = addTheorem((inv_thm_qid2, [], inv_thm, noPos), spc) in

*)


  op createPrimeDef(spc: Spec, old_dfn: MS.Term, op_ty: Sort, src_ty: Sort, trg_ty: Sort,
                    iso_ref: MS.Term, inv_iso_ref: MS.Term)
     : MS.Term =
    let
      def makePrimedPat (p: Pattern, sb: List(Var * MS.Term)): Pattern * List(Var * MS.Term) =
        case p of
          | VarPat(v as (vn,v_ty),a) \_rightarrow
            if equalType?(v_ty,src_ty)
              then let v_pr = (vn^"'",trg_ty) in
                   (VarPat(v_pr,a),
                    Cons((v, mkApply(inv_iso_ref,Var(v_pr,a))), sb))
              else
               (case v_ty of
                 | Base(Qualified("List","List"),[el_ty],a1) | equalType?(el_ty, src_ty) \_rightarrow
                   let v_pr = (vn^"'",Base(Qualified("List","List"),[trg_ty],a1)) in
                   (VarPat(v_pr,a),
                    Cons((v, mkMapApply(inv_iso_ref, Var(v_pr,a), trg_ty, src_ty)), sb))
                 | _ \_rightarrow (p, sb))
          | RecordPat(idprs,a) \_rightarrow
            let (idprs_pr,sb) =
                foldr (fn ((id,p),(idprs_pr,sb)) \_rightarrow
                         let (p_pr,sb) = makePrimedPat(p,sb) in
                         (Cons((id,p_pr), idprs_pr), sb))
                  ([],sb) idprs
            in
            (RecordPat(idprs_pr, a), sb)
          | RestrictedPat(p1,pred,a) \_rightarrow
            let (p1_pr, sb) = makePrimedPat(p1, sb) in
            (RestrictedPat(p1_pr, substitute(pred,sb) ,a),
             sb)
          | _ \_rightarrow (p, sb)
      def makePrimeBody (old_def_tm, sb, result_ty) =
        case old_def_tm of
         | Lambda(binds,a) \_rightarrow
           let new_binds = map (fn (p, condn, body) \_rightarrow
                                  let (p_pr, sb) = makePrimedPat(p, sb) in
                                  let body_ty = case arrowOpt(spc,result_ty) of
                                                  | Some(_,r) -> r
                                                  | None -> fail("Illegal type")
                                  in
                                  (p_pr, condn, makePrimeBody(body, sb, body_ty)))
                             binds
           in
           Lambda(new_binds,a)
         | _ \_rightarrow
           let new_bod = substitute(old_def_tm, sb) in
           %% !! Generalize to handle tuple containing src_ty as a component
           if equivType? spc (result_ty, src_ty)
             then mkApply(iso_ref, new_bod)
             else
               case result_ty of
                 | Base(Qualified("List","List"),[el_ty],a) | equivType? spc (el_ty, src_ty) \_rightarrow
                   %% map iso_ref new_bod
                   mkMapApply(iso_ref, new_bod, src_ty, trg_ty)
                 | Base(Qualified("Option","Option"),[el_ty],a) | equivType? spc (el_ty, src_ty) \_rightarrow
                   mkApply(mkApply(mkInfixOp(Qualified("Option","mapOption"),
                                             Unspecified,
                                             mkArrow(mkArrow(src_ty,trg_ty),
                                                     mkArrow(mkBase(Qualified("Option","Option"), [src_ty]),
                                                             mkBase(Qualified("Option","Option"), [trg_ty])))),
                                   iso_ref),
                           new_bod)
                 | _ \_rightarrow new_bod
    in
    makePrimeBody(old_dfn, [], op_ty)    

  %% fn x \_rightarrow fn (x,y) \_rightarrow \_dots  \_longrightarrow  fn x \_rightarrow fn (x,y) \_rightarrow f (x) (y,z)
  op makeTrivialDef(spc: Spec, dfn: MS.Term, qid_pr_ref: MS.Term): MS.Term =
    let def constructDef(tm, new_bod) =
          case tm of
            | Lambda(binds,a) \_rightarrow
              let new_binds = map (fn (p,condn,body) \_rightarrow
                                     let Some args = patternToTerm p in
                                     (p,condn,
                                      constructDef(body, mkApply(new_bod, args))))
                             binds
           in
           Lambda(new_binds,a)
         | _ \_rightarrow new_bod 
    in
    constructDef(dfn, qid_pr_ref)

  op makePrimedOps(spc: Spec, src_ty: Sort, trg_ty: Sort,
                   iso_ref: MS.Term, inv_iso_ref: MS.Term, ign_qids: List QualifiedId)
     : List (OpInfo * OpInfo) =
    foldriAQualifierMap
      (fn (q, nm, info, result) ->
       let qid = Qualified(q,nm) in
       let (tvs, op_ty, dfn) = unpackTerm info.dfn in
       case dfn  of
         | Any _ \_rightarrow result
         | _ \_rightarrow
       let def ty_to_ty_pr ty =
             if equivType? spc (ty,src_ty)
               then trg_ty
               else ty
       in
       let op_ty_pr = mapSort (id,ty_to_ty_pr,id) op_ty in
       if member(qid,ign_qids)
         \_or equivType? spc (op_ty_pr,op_ty)
         then result
        else
          let qid_ref = mkInfixOp(qid,info.fixity,op_ty) in
          let qid_pr = Qualified(q,nm^"'") in
          let dfn_pr = createPrimeDef(spc, dfn, op_ty, src_ty, trg_ty, iso_ref, inv_iso_ref) in
 let _ = if nm = "mkInitialState"then writeLine(nm^": \n"^printTerm dfn_pr)else () in
          let qid_pr_ref = mkInfixOp(qid_pr,info.fixity,op_ty_pr) in
          let id_def_pr = makeTrivialDef(spc, dfn_pr, qid_pr_ref) in
          let new_dfn = createPrimeDef(spc, id_def_pr, op_ty_pr, trg_ty, src_ty, inv_iso_ref, iso_ref) in
          Cons((info \_guillemotleft {dfn = maybePiTerm(tvs, SortedTerm(new_dfn, op_ty, noPos))},
                info \_guillemotleft {names = [qid_pr],
                        dfn = maybePiTerm(tvs, SortedTerm(dfn_pr, op_ty_pr, noPos))}),
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
           && equivType? spc (src_ty,inv_trg_ty)
           && equivType? spc (trg_ty,inv_src_ty))
      then (warn(anyToString iso_qid^" and "^anyToString inv_iso_qid^" types not inverse!");
                 spc)
    else
    let iso_ref = mkInfixOp(iso_qid, iso_opinfo.fixity, iso_ty) in
    let inv_iso_ref = mkInfixOp(inv_iso_qid, inv_iso_opinfo.fixity, inv_iso_ty) in

    let (spc, iso_thm_qids) = makeIsoTheorems(spc, iso_ref, inv_iso_ref, src_ty, trg_ty) in

    let new_defs = makePrimedOps(spc, src_ty, trg_ty, iso_ref, inv_iso_ref,
                                 [iso_qid,inv_iso_qid])
    in
    let spc = foldl (fn ((opinfo,opinfo_pr),spc) \_rightarrow
                     let qid  = hd opinfo.names in
                     let qid_pr = hd opinfo_pr.names in
                     let spc =  appendElement(spc,Op(qid_pr,true,noPos)) in
                     let spc = setOpInfo(spc,qid,opinfo) in
                     let spc = setOpInfo(spc,qid_pr,opinfo_pr) in
                     spc)
                spc new_defs
    in    
    let unfolds = map (fn (opinfo,_) \_rightarrow Unfold(hd opinfo.names)) new_defs in
    let iso_rewrites = map (fn qid \_rightarrow LeftToRight qid) iso_thm_qids in
    let main_script = Steps [SimpStandard,
                             Simplify([Unfold(mkUnQualifiedId "inv_iso"),
                                       %LeftToRight(mkUnQualifiedId "f_if_then_else"),
                                       %% Should be in specs
                                       LeftToRight(mkUnQualifiedId "iso_set_fold"),
                                       LeftToRight(mkUnQualifiedId "iterate_inv_iso"),
                                       LeftToRight(mkUnQualifiedId "map_empty"),
                                       LeftToRight(mkUnQualifiedId "map_doubleton"),
                                       LeftToRight(mkUnQualifiedId "case_map"),
                                       LeftToRight(mkUnQualifiedId "unfold_let_inv_iso"),
                                       Unfold(mkQualifiedId("Option","mapOption"))]
                                        ++ iso_rewrites
                                        ++ unfolds)%,
                            % AbstractCommonExpressions
                             ]
    in
    let simp_ops
       = mapOpInfos
           (fn (opinfo) \_rightarrow
              if exists (fn (hidden_opinfo,_) \_rightarrow opinfo = hidden_opinfo) new_defs
                then opinfo
              else
              let (tvs, ty, dfn) = unpackTerm opinfo.dfn in
              let simp_dfn = interpretTerm(spc, main_script, dfn) in
              if equalTerm?(dfn,simp_dfn)
                then opinfo
              else
              let qid = hd opinfo.names in
              let _ = printDef(spc,qid) in
              let new_dfn = maybePiTerm(tvs, SortedTerm (simp_dfn, ty, noPos)) in
              let _ = writeLine(printQualifiedId qid^":") in
              let _ = writeLine(printTerm simp_dfn^"\n") in
              opinfo \_guillemotleft {dfn = new_dfn})
           spc.ops
    in
    let spc = spc \_guillemotleft {ops = simp_ops} in
    spc
    

endspec