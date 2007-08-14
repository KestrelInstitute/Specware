(* Takes isomorphism function iso_qid and its inverse osi_qid,
   Extracts State and State'
   Find all functions f that take State as an argument or returned value and create
   f' with State' instead of State. The body is a call to f with state parameters wrapped in
   osi_qid and result state wrapped in iso_qid.

   Simplify all
     Distributive rules
     fa(x': State') iso_qid(osi_qid x')) = x'

   Simplify
*)

Isomorphism qualifying
spec
  import Script
  import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements

  op makeNewPrimedQid(Qualified(q,id): QualifiedId, exists?: QualifiedId -> Boolean): QualifiedId =
    let primed_qid = Qualified(q,id^"'") in
    if exists? primed_qid
      then makeNewPrimedQid(primed_qid, exists?)
      else primed_qid

  op makePrimedOpQid(qid: QualifiedId, spc: Spec): QualifiedId =
    makeNewPrimedQid(qid, fn nqid -> some?(findTheOp(spc, nqid)))

  op makePrimedTypeQid(qid: QualifiedId, spc: Spec): QualifiedId =
    makeNewPrimedQid(qid, fn nqid -> some?(findTheSort(spc, nqid)))

  type IsoFnInfo = List(QualifiedId * QualifiedId)
  %% Look for fns of the form Bijection(a,a') -> Bijection(L a,L a')
  op findComplexIsoFns(spc: Spec): IsoFnInfo =
    foldOpInfos (fn (info, result) ->
                   case firstOpDefInnerSort info of
                     | Arrow(Base(Qualified("Functions","Bijection"),_,_),
                             Base(Qualified("Functions","Bijection"),
                                  [Base(qid1,_,_), Base(qid2,_,_)],
                                  _), _)
                         | qid1 = qid2 ->
                       Cons((qid1, primaryOpName info), result)
                     | _ -> result)
      []
      spc.ops

  op mkHOIsoFn(ty_qid: QualifiedId, fn_qid: QualifiedId, fn_arg: MS.Term, dom_ty: Sort, rng_ty: Sort): MS.Term =
    mkApply(mkInfixOp (fn_qid, Unspecified,
                       mkArrow(mkArrow(dom_ty,rng_ty),
                               mkArrow(mkBase(ty_qid, [dom_ty]),
                                       mkBase(ty_qid, [rng_ty])))),
            fn_arg)

  op mkMapApply(fn_arg: MS.Term, list_arg: MS.Term, dom_ty: Sort, rng_ty): MS.Term =
    mkApply(mkApply(mkInfixOp
                      (Qualified("List","map"),
                       Unspecified,
                       mkArrow(mkArrow(dom_ty,rng_ty),
                               mkArrow(mkBase(Qualified("List","List"), [dom_ty]),
                                       mkBase(Qualified("List","List"), [rng_ty])))),
                    fn_arg),
            list_arg)

  op makeIsoTheorems(spc: Spec, iso_ref: MS.Term, osi_ref: MS.Term, tvs: TyVars,
                     src_ty: Sort, trg_ty: Sort, prev: List QualifiedId)
     : Spec * List QualifiedId =
    %% Thm inverse iso = osi
    let inv_thm1 = mkEquality(mkArrow(trg_ty,src_ty),
                              mkApply(mkInfixOp(Qualified("Functions","inverse"), Unspecified,
                                                mkArrow(mkArrow(src_ty,trg_ty),
                                                        mkArrow(trg_ty,src_ty))),
                                      iso_ref),
                              osi_ref)
    in
    let inverse_iso_is_osi_qid = Qualified("generated","inverse_iso_is_osi") in
    let spc = addTheorem((inverse_iso_is_osi_qid, tvs, inv_thm1, noPos), spc) in

    let inv_thm2 = mkEquality(mkArrow(src_ty,trg_ty),
                              mkApply(mkInfixOp(Qualified("Functions","inverse"), Unspecified,
                                                mkArrow(mkArrow(trg_ty,src_ty),
                                                        mkArrow(src_ty,trg_ty))),
                                      osi_ref),
                              iso_ref)
    in
    let inverse_osi_is_iso_qid = Qualified("generated","inverse_osi_is_iso") in
    let spc = addTheorem((inverse_osi_is_iso_qid, tvs, inv_thm2, noPos), spc) in

    %% Thm fa(x) iso(osi x) = x
     let x_pr_var = ("x'",trg_ty) in
     let inv_thm1 = mkBind(Forall,[x_pr_var],
                           mkEquality(trg_ty,
                                      mkApply(iso_ref,mkApply(osi_ref, mkVar x_pr_var)),
                                      mkVar x_pr_var))
     in
     let iso__osi_qid = Qualified("generated","iso__osi") in
     let spc = addTheorem((iso__osi_qid, tvs, inv_thm1, noPos), spc) in

     %% Thm fa(x) osi(iso x) = x
     let x_var = ("x",src_ty) in
     let inv_thm1 = mkBind(Forall,[x_var],
                           mkEquality(trg_ty,
                                      mkApply(osi_ref,mkApply(iso_ref, mkVar x_var)),
                                      mkVar x_var))
     in
     let osi__iso_qid = Qualified("generated","osi__iso") in
     let spc = addTheorem((osi__iso_qid, tvs, inv_thm1, noPos), spc) in

    %% Thm fa(x) map iso (map osi x) = x
 %    let x_pr_var = ("x'", mkBase(Qualified("List","List"), [trg_ty])) in
%     let inv_thm1 = mkBind(Forall,[x_pr_var],
%                           mkEquality(mkBase(Qualified("List","List"), [trg_ty]),
%                                      mkMapApply(iso_ref, mkMapApply(osi_ref, mkVar x_pr_var,
%                                                                     trg_ty, src_ty),
%                                                 src_ty, trg_ty),
%                                      mkVar x_pr_var))
%     in
%     let map__iso__osi_qid = Qualified("generated","map__iso__osi") in
%     let spc = addTheorem((iso__osi_qid, tvs, inv_thm1, noPos), spc) in

%     %% Thm fa(x) map osi(map iso x) = x
%     let x_var = ("x", mkBase(Qualified("List","List"), [src_ty])) in
%     let inv_thm1 = mkBind(Forall,[x_var],
%                           mkEquality(mkBase(Qualified("List","List"), [src_ty]),
%                                      mkMapApply(osi_ref, mkMapApply(iso_ref, mkVar x_var,
%                                                                         src_ty, trg_ty),
%                                                 trg_ty, src_ty),
%                                      mkVar x_var))
%     in
%     let map__osi__iso_qid = Qualified("generated","map__osi__iso") in
%     let spc = addTheorem((osi__iso_qid, tvs, inv_thm1, noPos), spc) in

    (spc, [inverse_iso_is_osi_qid, inverse_osi_is_iso_qid, iso__osi_qid, osi__iso_qid] ++ prev)

  %% fn x -> fn (x,y) -> \_dots  \_longrightarrow  fn x -> fn (x,y) -> f (x) (y,z)
  op makeTrivialDef(spc: Spec, dfn: MS.Term, qid_pr_ref: MS.Term): MS.Term =
    let def constructDef(tm, new_bod) =
          case tm of
            | Lambda(binds,a) ->
              let new_binds = map (fn (p,condn,body) ->
                                     case patternToTerm p of
                                       | Some args ->
                                          (p,condn,
                                           constructDef(body, mkApply(new_bod, args)))
                                       | None -> (p,condn,body))
                             binds
              in
                Lambda(new_binds,a)
            | _ -> new_bod 
    in
    constructDef(dfn, qid_pr_ref)

  op printDef(spc: Spec, qid: QualifiedId): () =
    case findTheOp(spc,qid) of
      | None -> (warn("Can't find op "^anyToString qid);
                 ())
      | Some opinfo ->
    let (tvs, ty, dfn) = unpackTerm opinfo.dfn in
    let _ = writeLine(printQualifiedId qid^":") in
    writeLine(printTerm dfn)

  op lookupIsoFnInfo(qid: QualifiedId, iso_fn_info: IsoFnInfo): Option QualifiedId =
    case iso_fn_info of
      | [] -> None
      | (qid1,qid2)::_ | qid = qid1 -> Some qid2
      | _::r -> lookupIsoFnInfo(qid,r)

  type IsoInfo = MS.Term * TyVars * Sort * Sort
  type IsoInfoList = List(IsoInfo * IsoInfo)

  op lookupIsoInfo(qid: QualifiedId, iso_info: IsoInfoList): Option(IsoInfo * IsoInfo) =
    case iso_info of
      | [] -> None
      | (info as ((_,_,Base(ty_qid,_,_),_),_)) :: _ | qid = ty_qid ->
        Some info
      | _::rst -> lookupIsoInfo(qid,rst)

  op invertIsoInfo(iso_info: IsoInfoList): IsoInfoList =
    map (fn (x,y) -> (y,x)) iso_info

  op typeInIsoInfoList(qid: QualifiedId, iso_info: IsoInfoList): Boolean =
    case iso_info of
      | [] -> false
      | (info as ((_,_,Base(ty_qid,_,_),Base(ty'_qid,_,_)),_) :: _) | qid = ty_qid || qid = ty'_qid -> 
        true
      | _::rst -> typeInIsoInfoList(qid,rst)

  op findOpInfo(spc: Spec, qid: QualifiedId): Option(IsoInfo) =
    case findAllOps(spc,qid) of
      | [] \_rightarrow (warn("No op with name: " ^ printQualifiedId qid);
                         None)
      | [opinfo] \_rightarrow
        let (tvs, ty, tm) = unpackTerm opinfo.dfn in
        let qid = primaryOpName opinfo in
        let qid_ref = mkInfixOp(qid, opinfo.fixity, ty) in
        (case arrowOpt(spc, ty) of
           | None -> (warn(printQualifiedId qid^" is not a function!");
                      None)
           | Some(src_ty, trg_ty) ->
             Some(qid_ref, tvs, src_ty, trg_ty))
      | _ -> (warn("Ambiguous op name: " ^ printQualifiedId qid);
              None)

  op dependsOnIsoInfo?(qid: QualifiedId, iso_info: IsoInfoList, spc: Spec, seen: List QualifiedId)
       : Boolean =
    let seen = Cons(qid, seen) in
    case findTheSort(spc, qid) of
      | None -> false
      | Some info ->
    let (_,def_ty) = unpackSort info.dfn in
    existsInType? (fn ty ->
                     case ty of
                       | Base(s_qid,_,_) ->
                         typeInIsoInfoList(s_qid, iso_info)
                           || (~(member(s_qid, seen))
                                  && dependsOnIsoInfo?(s_qid, iso_info, spc, seen))
                       | _ -> false)
       def_ty

  op identityFn(ty: Sort): MS.Term = mkInfixOp(Qualified("Functions","id"),Unspecified,mkArrow(ty,ty))
  op identityFn?(tm: MS.Term): Boolean =
    case tm of
      | Fun(Op(Qualified("Functions","id"),_),_,_) -> true
      | _ -> false

  op mkCompose(f1: MS.Term, f2: MS.Term, spc: Spec): MS.Term =
    if identityFn? f1 then f2
      else if identityFn? f2 then f1
      else
        let f1_ty = inferType(spc,f1) in
        let f2_ty = inferType(spc,f2) in
        let Some (dom,_) = arrowOpt(spc,f2_ty) in
        let Some (_,ran) = arrowOpt(spc,f1_ty) in
        let compose_ty = mkArrow(mkProduct[f1_ty,f2_ty], mkArrow(dom, ran)) in
        let compose_fn = mkInfixOp(Qualified("Functions","o"), Infix(Left,24), compose_ty) in
        mkAppl(compose_fn, [f1,f2])

  op isoTypeFn (spc: Spec, iso_info: IsoInfoList, iso_fn_info: IsoFnInfo)
               (ty: Sort): MS.Term =
    case ty of
      | Base(qid,params,a) ->
        (case lookupIsoFnInfo(qid,iso_fn_info) of
           | Some qid' ->
             (case params of
                | [p_ty] ->
                  let p_ty' = isoType (spc, iso_info, iso_fn_info) p_ty in
                  let arg_iso_fn = isoTypeFn (spc, iso_info, iso_fn_info) p_ty in
                  mkHOIsoFn(qid, qid', arg_iso_fn, p_ty, p_ty')
                | _ -> fail("Multi-parameter types not yet handled: "^printQualifiedId qid))
           | None ->
             case lookupIsoInfo(qid, iso_info) of
               | Some((iso_fn,_,_,_),_) -> iso_fn
               | None -> identityFn ty)
      | Arrow(dom,ran,_) ->
        let fnarg = ("f",ty) in
        mkLambda(mkVarPat fnarg, 
                 mkCompose(isoTypeFn (spc, iso_info, iso_fn_info) ran,
                           mkCompose(mkVar fnarg, osiTypeFn (spc, iso_info, iso_fn_info) dom, spc),
                           spc))
      %% Need to add rest of the cases
      | _ -> identityFn ty

  op osiTypeFn (spc: Spec, iso_info: IsoInfoList, iso_fn_info: IsoFnInfo)
               (ty: Sort): MS.Term =
    isoTypeFn (spc, invertIsoInfo iso_info, iso_fn_info) (isoType (spc, iso_info, iso_fn_info) ty)

  op osiTerm (spc: Spec, iso_info: IsoInfoList, iso_fn_info: IsoFnInfo)
             (ty: Sort)
             (tm: MS.Term): MS.Term =
    isoTerm (spc, invertIsoInfo iso_info, iso_fn_info) (isoType (spc, iso_info, iso_fn_info) ty) tm

  op isoTerm (spc: Spec, iso_info: IsoInfoList, iso_fn_info: IsoFnInfo)
             (ty: Sort)
             (tm: MS.Term): MS.Term =
    let
      def makePrimedPat (p: Pattern, body: MS.Term, p_ty: Sort, sb: List(Var * MS.Term))
          : Pattern * MS.Term * List(Var * MS.Term) =
        case p of
          | VarPat(v as (vn,v_ty),a) ->
            let v_ty' = isoType (spc, iso_info, iso_fn_info) v_ty in
            if equalType?(v_ty,v_ty')
              then (p, body, sb)
              else let v' = (vn^"'",v_ty') in
                   (VarPat(v',a), body,
                    Cons((v, osiTerm (spc, iso_info, iso_fn_info) (v_ty') (Var(v',a))), sb))
          | RestrictedPat(p1,pred,a) ->
            let (p1_pr, body, sb) = makePrimedPat(p1, body, p_ty, sb) in
            (RestrictedPat(p1_pr, substitute(pred,sb) ,a),
             body, sb)
          | _ | embed? Base p_ty ->
            let v = ("x",p_ty) in
            makePrimedPat(mkVarPat v, mkSimpApply(mkLambda(p,body), mkVar v), p_ty, sb)
          | RecordPat(idprs,a) ->
            (case productOpt(spc, p_ty) of
               | None -> fail("Shouldn't happen!")
               | Some fields ->
             let (idprs_pr,body,sb) =
                 foldr (fn ((id,p),(idprs_pr,body,sb)) ->
                          case getTermField(fields, id) of
                            | None -> fail("Shouldn't happen!")
                            | Some f_ty ->
                          let (p_pr, body, sb) = makePrimedPat(p,body,f_ty,sb) in
                          (Cons((id,p_pr), idprs_pr), body, sb))
                   ([],body,sb) idprs
             in
             (RecordPat(idprs_pr, a), body, sb))
          | _ -> (p, body, sb)
      def makePrimeBody (old_def_tm, sb, result_ty) =
        case old_def_tm of
          | Lambda([(p, condn, body)],a) | ~(embed? Base result_ty)
                           % && (embed? Base (domain(spc, result_ty))
                           %      => embed? VarPat)
                            ->
            (case arrowOpt(spc,result_ty) of
               | None -> fail("Illegal type")
               | Some(d_ty,body_ty) -> 
                 let (p_pr, body, sb) = makePrimedPat(p, body, d_ty, sb) in
                 let new_body = makePrimeBody(body, sb, body_ty) in
                 Lambda([(p_pr, condn, new_body)],a))
          | _ ->
            let new_bod = substitute(old_def_tm, sb) in
            let result_ty' = isoType (spc, iso_info, iso_fn_info) result_ty in
            if equalType?(result_ty, result_ty')
              then new_bod
            else simplifiedApply(isoTypeFn (spc, iso_info, iso_fn_info) result_ty, new_bod, spc)
    in
    makePrimeBody(tm, [], ty)    

  op isoTypeRec (spc: Spec, iso_info: IsoInfoList, iso_fn_info: IsoFnInfo)
                (ty: Sort): Sort =
    let def isoType1 ty =
          case ty of
            | Base(qid,params,a) ->
              (case lookupIsoInfo(qid, iso_info) of
                 | Some((_,_,_,Base(osi_qid,_,_)), _) -> Base(osi_qid,params,a)
                 | _ ->
               if dependsOnIsoInfo?(qid,iso_info,spc,[])
                 then Base(makePrimedTypeQid(qid, spc), params, a)
                 else ty)
            | Quotient(s,tm,a) ->
              let tm_ty = mkArrow(mkProduct[s,s], boolSort) in 
              Quotient(s, isoTerm (spc, iso_info, iso_fn_info) tm_ty tm, a)
            | Subsort (s,tm,a) ->
              let tm_ty = mkArrow(s, boolSort) in 
              Subsort (s, isoTerm (spc, iso_info, iso_fn_info) tm_ty tm, a)
            | _ -> ty
    in
    mapSort (id, isoType1, id) ty

  op isoType (spc: Spec, iso_info: IsoInfoList, iso_fn_info: IsoFnInfo)
             (ty: Sort): Sort =
    let def isoType1 ty =
          case ty of
            | Base(qid,params,a) ->
              (let iso_params =  map (isoType (spc, iso_info, iso_fn_info)) params in
               case lookupIsoInfo(qid, iso_info) of
                 | Some((_,_,_,Base(osi_qid,_,_)), _) -> Base(osi_qid, iso_params, a)
                 | _ -> Base(qid, iso_params, a))
            | Quotient(s,tm,a) ->
              let tm_ty = mkArrow(mkProduct[s,s], boolSort) in 
              Quotient(s, isoTerm (spc, iso_info, iso_fn_info) tm_ty tm, a)
            | Subsort (s,tm,a) ->
              let tm_ty = mkArrow(s, boolSort) in 
              Subsort (s, isoTerm (spc, iso_info, iso_fn_info) tm_ty tm, a)
            | _ -> ty
    in
    mapSort (id, isoType1, id) ty

  op addIsoDefForIso(spc: Spec, iso_info: IsoInfoList, iso_fn_info: IsoFnInfo) (iso_ref: MS.Term): Spec =
    spc

  op addOsiDefForIso(spc: Spec, iso_info: IsoInfoList, iso_fn_info: IsoFnInfo) (osi_ref: MS.Term): Spec =
    spc
 
  op newPrimedTypes(init_spc: Spec, iso_info: IsoInfoList, iso_fn_info: IsoFnInfo)
     : IsoInfoList * Spec =
    foldSortInfos
      (fn (info, result as (new_iso_info, spc)) ->
         let qid = primarySortName info in
         let Qualified(q,id) = qid in
         if typeInIsoInfoList(qid, iso_info) then result
         else
         let (tvs,ty) = unpackFirstSortDef info in
         %% Use init_spec because priming algorithm assumes primed types haven't been added yet
         let ty' = isoTypeRec(init_spc, iso_info, iso_fn_info) ty in
         if equalType?(ty,ty') then result
         else
         let qid' = makePrimedTypeQid(qid, spc) in
         let qid_ref = mkBase(qid,map mkTyVar tvs) in
         let qid'_ref = mkBase(qid',map mkTyVar tvs) in
         let iso_qid = makePrimedTypeQid(Qualified(q,"iso"^id), spc) in
         let osi_qid = makePrimedTypeQid(Qualified(q,"osi"^id), spc) in
         let iso_fn = mkInfixOp(iso_qid, Unspecified, mkArrow(qid_ref, qid'_ref)) in
         let osi_fn = mkInfixOp(osi_qid, Unspecified, mkArrow(qid'_ref, qid_ref)) in
         (Cons(((iso_fn, tvs, qid_ref, qid'_ref),
                (osi_fn, tvs, qid'_ref, qid_ref)),
               new_iso_info),
          addTypeDef(spc, qid', maybePiSort(tvs, ty'))))
       ([], init_spc)
       init_spc.sorts

  op createPrimeDef(spc: Spec, old_dfn: MS.Term, op_ty: Sort, src_ty: Sort, trg_ty: Sort,
                    iso_ref: MS.Term, osi_ref: MS.Term)
     : MS.Term =
    let
      def makePrimedPat (p: Pattern, sb: List(Var * MS.Term)): Pattern * List(Var * MS.Term) =
        case p of
          | VarPat(v as (vn,v_ty),a) ->
            if equalType?(v_ty,src_ty)
              then let v_pr = (vn^"'",trg_ty) in
                   (VarPat(v_pr,a),
                    Cons((v, mkApply(osi_ref,Var(v_pr,a))), sb))
              else
               (case v_ty of
                 | Base(Qualified("List","List"),[el_ty],a1) | equalType?(el_ty, src_ty) ->
                   let v_pr = (vn^"'",Base(Qualified("List","List"),[trg_ty],a1)) in
                   (VarPat(v_pr,a),
                    Cons((v, mkMapApply(osi_ref, Var(v_pr,a), trg_ty, src_ty)), sb))
                 | _ -> (p, sb))
          | RecordPat(idprs,a) ->
            let (idprs_pr,sb) =
                foldr (fn ((id,p),(idprs_pr,sb)) ->
                         let (p_pr,sb) = makePrimedPat(p,sb) in
                         (Cons((id,p_pr), idprs_pr), sb))
                  ([],sb) idprs
            in
            (RecordPat(idprs_pr, a), sb)
          | RestrictedPat(p1,pred,a) ->
            let (p1_pr, sb) = makePrimedPat(p1, sb) in
            (RestrictedPat(p1_pr, substitute(pred,sb) ,a),
             sb)
          | _ -> (p, sb)
      def makePrimeBody (old_def_tm, sb, result_ty) =
        case old_def_tm of
          | Lambda(binds,a) ->
            let new_binds = map (fn (p, condn, body) ->
                                   let (p_pr, sb) = makePrimedPat(p, sb) in
                                   let body_ty = case arrowOpt(spc,result_ty) of
                                                   | Some(_,r) -> r
                                                   | None -> fail("Illegal type")
                                   in
                                     (p_pr, condn, makePrimeBody(body, sb, body_ty)))
                              binds
            in
              Lambda(new_binds,a)
           | _ ->
             let new_bod = substitute(old_def_tm, sb) in
             %% !! Generalize to handle tuple containing src_ty as a component
             if equivType? spc (result_ty, src_ty)
               then mkApply(iso_ref, new_bod)
             else
               case result_ty of
                 | Base(Qualified("List","List"),[el_ty],a) | equivType? spc (el_ty, src_ty) ->
                   %% map iso_ref new_bod
                   mkMapApply(iso_ref, new_bod, src_ty, trg_ty)
                 | Base(Qualified("Option","Option"),[el_ty],a) | equivType? spc (el_ty, src_ty) ->
                   mkApply(mkApply(mkInfixOp(Qualified("Option","mapOption"),
                                             Unspecified,
                                             mkArrow(mkArrow(src_ty,trg_ty),
                                                     mkArrow(mkBase(Qualified("Option","Option"), [src_ty]),
                                                             mkBase(Qualified("Option","Option"), [trg_ty])))),
                                   iso_ref),
                           new_bod)
                 | _ -> new_bod
    in
    makePrimeBody(old_dfn, [], op_ty)    

%% (search-forward-regexp specware-definition-regexp) (match-string 0) (match-string 2)
  op makePrimedOps(spc: Spec,
                   iso_info: IsoInfoList,
                   iso_fn_info: IsoFnInfo)
     : List (OpInfo * OpInfo) =
    let ign_qids = foldl (fn (((Fun(Op(iso_qid,_),_,_),_,_,_), (Fun(Op(osi_qid,_),_,_),_,_,_)), result) ->
                            [iso_qid, osi_qid] ++ result)
                     [] iso_info
    in
    foldriAQualifierMap
      (fn (q, nm, info, result) ->
       let qid = Qualified(q,nm) in
       let (tvs, op_ty, dfn) = unpackTerm info.dfn in
       case dfn  of
         | Any _ -> result
         | _ ->
       let op_ty_pr = isoType (spc, iso_info, iso_fn_info) op_ty in
       if member(qid,ign_qids)
         \_or equivType? spc (op_ty_pr,op_ty)
         then result
        else
          let qid_ref = mkInfixOp(qid,info.fixity,op_ty) in
          let qid_pr = makePrimedOpQid(qid, spc) in
          let dfn_pr = isoTerm (spc, iso_info, iso_fn_info) op_ty dfn in
          let qid_pr_ref = mkInfixOp(qid_pr,info.fixity,op_ty_pr) in
          let id_def_pr = makeTrivialDef(spc, dfn_pr, qid_pr_ref) in
          let new_dfn = osiTerm (spc, iso_info, iso_fn_info) op_ty_pr id_def_pr in
          % createPrimeDef(spc, id_def_pr, op_ty_pr, trg_ty, src_ty, osi_ref, iso_ref) in
          Cons((info \_guillemotleft {dfn = maybePiTerm(tvs, SortedTerm(new_dfn, op_ty, noPos))},
                info \_guillemotleft {names = [qid_pr],
                        dfn = maybePiTerm(tvs, SortedTerm(dfn_pr, op_ty_pr, noPos))}),
               result))
      []
      spc.ops

  def Isomorphism.makeIsoMorphism(spc: Spec, iso_qid_prs: List(QualifiedId * QualifiedId),
                                  extra_rules: List RuleSpec)
      : Spec =
    if exists (fn (iso_qid, osi_qid) ->
               none?(findOpInfo(spc,iso_qid)) || none?(findOpInfo(spc,osi_qid)))
         iso_qid_prs
       then spc
    else                 
    let base_iso_info = map (fn (iso_qid, osi_qid) ->
                                let (Some iso_info, Some osi_info)
                                   = (findOpInfo(spc,iso_qid), findOpInfo(spc,osi_qid))
                                in (iso_info, osi_info))
                          iso_qid_prs
    in  %% Check compatibility of iso and osi
    if exists (fn ((iso,tvs,src_ty,trg_ty), (osi,inv_tvs,inv_src_ty,inv_trg_ty)) ->
                if ~(length tvs = length inv_tvs
                       && equivType? spc (src_ty,inv_trg_ty)
                       && equivType? spc (trg_ty,inv_src_ty))
                  then (warn(printTerm iso^" and "^printTerm osi^" types not inverse!");
                        true)
                  else false)
        base_iso_info
      then spc
    else
    let iso_fn_info = findComplexIsoFns spc in
    let (prime_type_iso_info, spc) = newPrimedTypes(spc, base_iso_info, iso_fn_info) in
    let iso_info = base_iso_info ++ prime_type_iso_info in
    %% Add definitions for newly introduced iso fns
    let spc = foldl (fn (((iso_ref,tvs,src_ty,trg_ty), (osi_ref,_,_,_)), spc) ->
                       let spc = addIsoDefForIso(spc,iso_info,iso_fn_info) iso_ref in
                       let spc = addOsiDefForIso(spc,invertIsoInfo iso_info,iso_fn_info) osi_ref in
                       spc)
                spc
                prime_type_iso_info
    in
    let (spc, iso_thm_qids) =
        foldl (fn (((iso_ref,tvs,src_ty,trg_ty), (osi_ref,_,_,_)), (spc, iso_thm_qids)) ->
                 makeIsoTheorems(spc, iso_ref, osi_ref, tvs, src_ty, trg_ty, iso_thm_qids))
          (spc, []) iso_info
    in
    let new_defs = makePrimedOps(spc, iso_info, iso_fn_info) in
    let spc = foldl (fn ((opinfo,opinfo_pr),spc) ->
                     let qid  = hd opinfo.names in
                     let qid_pr = hd opinfo_pr.names in
                     let spc = appendElement(spc,Op(qid_pr,true,noPos)) in
                     let spc = setOpInfo(spc,qid,opinfo) in
                     let spc = setOpInfo(spc,qid_pr,opinfo_pr) in
                     spc)
                spc new_defs
    in    
    let unfolds = map (fn (opinfo,_) -> Unfold(hd opinfo.names)) new_defs in
    let iso_rewrites = map (fn qid -> LeftToRight qid) iso_thm_qids in
    let osi_unfolds = map (fn (_,(Fun(Op(osi_qid,_),_,_),_,_,_)) -> Unfold osi_qid) iso_info in
    let complex_iso_fn_unfolds = map (fn (_,qid) -> Unfold qid) iso_fn_info in
    let main_script = Steps [%SimpStandard,
                             Simplify([
                                       %LeftToRight(mkUnQualifiedId "f_if_then_else"),
                                       %% Should be in specs
                                       %% LeftToRight(mkUnQualifiedId "inverse_apply"),
                                       Unfold(mkQualifiedId("Functions","o")),
                                       LeftToRight(mkUnQualifiedId "map_map_inv"),
                                       %% LeftToRight(mkUnQualifiedId "iso_set_fold"),
                                       %% LeftToRight(mkUnQualifiedId "iterate_inv_iso"),
                                       LeftToRight(mkUnQualifiedId "map_empty"),
                                       LeftToRight(mkUnQualifiedId "map_doubleton"),
                                       LeftToRight(mkUnQualifiedId "case_map"),
                                       %LeftToRight(mkUnQualifiedId "unfold_let_osi"),
                                       Unfold(mkQualifiedId("Option","mapOption"))]
                                        ++ iso_rewrites
                                        %++ osi_unfolds
                                        ++ complex_iso_fn_unfolds
                                        ++ unfolds
                                        ++ extra_rules),
                             Simplify osi_unfolds
                            % AbstractCommonExpressions
                             ]
    in
    let simp_ops
       = mapOpInfos
           (fn (opinfo) ->
              if exists (fn (hidden_opinfo,_) -> opinfo = hidden_opinfo) new_defs
                then opinfo
              else
              let (tvs, ty, dfn) = unpackTerm opinfo.dfn in
              let (simp_dfn,_) = interpretTerm(spc, main_script, dfn, dfn) in
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