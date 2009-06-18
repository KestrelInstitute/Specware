SpecNorm qualifying spec
  import DefToAxiom
  import Coercions

  op eagerRegularization?: Boolean = false
  op regularizeSets?: Boolean = true
  op regularizeBooleanToFalse?: Boolean = false    % Can do this effectively in IsabelleExtensions


  %% Polymorphic ops have versions that have a predicate for each polymorphic variable
  type PolyOpTable = AQualifierMap(QualifiedId * List TyVar)

  op mkTruePred(ty: Sort): MS.Term =
    mkOp(Qualified("Bool","TRUE"), mkArrow(ty, boolSort))
    % mkLambda(mkWildPat ty, trueTerm)

  op substTyVarsWithSubtypes(tv_map: List(TyVar * MS.Term), tm: MS.Term): MS.Term =
    let result = instantiateTyVarsInTerm(tm, map (fn (tv,v) ->
                                                    (tv, Subsort(mkTyVar tv, v, noPos)))
                                               tv_map)
    in
    %let _ = writeLine("r: "^printTermWithSorts result) in
    result

  op subtypeC?(spc: Spec, ty: Sort, coercions: TypeCoercionTable): Boolean =
    case ty of
     | Subsort _ -> true
     | Base(qid, _, _) | exists (fn tb \_rightarrow qid = tb.subtype) coercions -> false
     | Product(flds, _) ->
       exists (fn (_,tyi) -> subtypeC?(spc, tyi, coercions)) flds
     | Arrow(dom, rng, _) ->
       subtypeC?(spc, dom, coercions) || subtypeC?(spc, rng, coercions)
     | Base(_, ty_args, _) ->
       exists (fn tyi -> subtypeC?(spc, tyi, coercions)) ty_args
       || (let exp_ty =  unfoldBaseOne(spc, ty) in
           if ty = exp_ty then false
            else subtypeC?(spc, exp_ty, coercions))
     | _ -> false
 
  op polyCallsTransformers (spc: Spec, tb: PolyOpTable, types?: Boolean, coercions: TypeCoercionTable)
     : TSP_Maps_St =
    let def doTerm (t: MS.Term): MS.Term =
          case t of
            | Fun(Op(qid as Qualified(q, id), fix?), ty, a) ->
              (case findAQualifierMap(tb, q, id) of
                 | None -> t
                 | Some(r_qid, used_tvs) ->
               case AnnSpec.findTheOp(spc, qid) of
                 | None -> t
                 | Some opinfo ->
               let (tvs, ty1, defn) = unpackFirstOpDef opinfo in
               % let _ = writeLine("\nRelativizing ref to: "^printQualifiedId qid^": "^printSort ty) in
               % let _ = writeLine("Matching with: "^printSort ty1) in
               case typeMatch(ty1, ty, spc, false) of
                 | None -> t
                 | Some tvsubst ->
               let tvsubst = filter (fn (tv,_) -> member(tv, used_tvs)) tvsubst in
               % let _ = (writeLine "Subst";
               %          app (fn (tv, ty) -> writeLine(tv^": "^printSort ty)) tvsubst) in
               if exists (fn (_, s_ty) -> subtypeC?(spc, s_ty, coercions)) tvsubst
                 then let predArgs = map (fn tv -> let Some(_, s_ty) =
                                                         find (fn (tvi,_) -> tv = tvi) tvsubst
                                                   in
                                                   let s_ty1 = raiseSubtypeFn(s_ty, spc) in
                                                   % let _ = if equalType?(s_ty1, s_ty) then ()
                                                   %      else writeLine("pct: "^printSort s_ty^" --> "^printSort s_ty1)
                                                   % in
                                                   case s_ty1 of
                                                     | Subsort(_, pred, _) -> pred
                                                     | _ -> mkTruePred s_ty)
                                       used_tvs
                      in
                      % let _ = app (fn pred -> writeLine(printTerm pred)) predArgs in
                      let predTypes = map (fn pred -> inferType(spc, pred)) predArgs in
                      let new_t = mkAppl(Fun(Op(r_qid, Nonfix),
                                             mkArrow(mkProduct predTypes, ty), a),
                                         predArgs)
                      in
                      % let _ = writeLine("New t: "^printTerm new_t) in
                      new_t
                 else t)
            | _ -> t

        def doType (ty: Sort): Sort =
          case ty of
            | Base(qid, args, _) | args ~= [] && types? ->
              let new_ty = unfoldBase(spc, ty) in
              if equalType?(new_ty, ty) || embed? CoProduct new_ty then ty
              else
              let tr_ty = mapSort (doTerm, doType, id) new_ty in
              if equalType?(tr_ty, new_ty) then ty
                else tr_ty
            | _ -> ty
    in
    (doTerm, doType, id)

  op maybeRelativize?(t: MS.Term, tb: PolyOpTable): Boolean =
    if eagerRegularization? then true
    else
    existsSubTerm (fn tm ->
                     case tm of
                       | Fun(Op(Qualified(q,id),_),_,_) ->
                         some?(findAQualifierMap(tb,q,id))
                       | Fun(Equals, _, _) -> true
                       | Fun(NotEquals, _, _) -> true
                       | Bind _ -> true
                       | The _ -> true
                       | _ -> false)
      t

  op subtypePredFreeVars (t: MS.Term, spc: Spec): List Var =
    foldSubTerms (fn (t,fvs) ->
                    case t of
                      | Bind(_,bndVars,_,_) ->
                        foldl (fn (fvs,(vn,ty)) ->
                                 freeVars(srtPred(spc, ty, mkVar(vn,ty))) ++ fvs)
                           fvs bndVars
                      | The((vn,ty),_,_) ->
                        freeVars(srtPred(spc, ty, mkVar(vn,ty))) ++ fvs
                      | _ -> fvs)
      [] t

  op makeStpName(nm: String): String = nm ^ "__stp" 

  op hasStpFun?(spc: Spec, Qualified(q, id): QualifiedId): Boolean =
    some? (AnnSpec.findTheOp(spc, Qualified(q, makeStpName id)))

  op stpFun?(id: String): Boolean =
    testSubseqEqual?("__stp", id, 0, length id - 5)

  op reduceStpFnArgs?: Boolean = true

  op tryRelativizeTerm(tvs: TyVars, tm: MS.Term, tb: PolyOpTable, ty: Sort, ho_eqfns: List QualifiedId, spc: Spec,
                       coercions: TypeCoercionTable)
      : List(Id * MS.Term) =
    % let _ = writeLine("tm: "^printTerm tm) in
    if tvs = [] || ~(maybeRelativize?(tm, tb))then []
    else
    let tv_map = map (fn tv -> (tv, mkVar("P__"^tv, mkArrow(mkTyVar tv, boolSort)))) tvs in
    % let _ = writeLine("tv_map: "^anyToString tv_map) in
    let st_tm = substTyVarsWithSubtypes(tv_map,tm) in
    let rel_tm = mapTerm (polyCallsTransformers(spc, tb, false, coercions)) st_tm in
    let rel_tm = regTerm(rel_tm, ty, ~(arrow?(spc,ty)), ho_eqfns, spc) in
    % let _ = writeLine("rel_tm: "^printTerm rel_tm) in
    let fvs = freeVars rel_tm ++ subtypePredFreeVars(rel_tm, spc) in
    % let _ = writeLine("fvs: "^anyToString(subtypePredFreeVars(rel_tm, spc))) in
    let opt_tv_map =
         if reduceStpFnArgs?
           then filter (fn (_,Var(v,_)) -> inVars?(v, fvs)) tv_map
           else tv_map
    in
    % let _ = writeLine("opt_tv_map: "^anyToString opt_tv_map) in
    opt_tv_map

  op addRelativizedOps(spc: Spec, coercions: TypeCoercionTable): Spec * PolyOpTable =
    let ho_eqfns = findHOEqualityFuns spc in
    let def relativizeElts(elts, top?, op_map, tb) =
          foldl (fn ((new_elts, op_map, tb), el) ->
                 case el of
                   | Import(s_tm, i_sp, im_elts, a) ->
                     let (im_elts, op_map, tb) = relativizeElts(im_elts, false, op_map, tb) in
                     (new_elts ++ [Import(s_tm, i_sp, im_elts, a)], op_map, tb)
                   | Op(qid as Qualified(q,id), _, a) ->
                     % let _ = writeLine("Trying "^printQualifiedId qid) in
                     (case AnnSpec.findTheOp(spc, qid) of
                      | Some opinfo ->
                        let (tvs, ty, dfn) = unpackTerm opinfo.dfn in
                        (case tryRelativizeTerm(tvs, dfn, tb, ty, ho_eqfns, spc, coercions) of
                         | [] -> (new_elts ++ [el], op_map, tb)
                         | tv_map ->
                           let new_id = makeStpName id in
                           let new_tb = insertAQualifierMap(tb, q, id,
                                                            (Qualified(q,new_id),
                                                             map (fn (tv,_) -> tv) tv_map))
                           in
                           let rel_ty_tm = substTyVarsWithSubtypes (tv_map, SortedTerm(dfn,ty,noPos)) in
                           let SortedTerm(rel_dfn,ty,_) = rel_ty_tm in
                           let rel_tm = mkLambda(mkTuplePat(map (fn (_,Var v) -> VarPat v) tv_map),
                                                 rel_dfn)
                           in
                           let new_ty = mkArrow(mkProduct(map (fn (_,Var((_,ty),_)) -> ty) tv_map), ty) in
                           let new_opinfo = {names = [Qualified(q,new_id)],
                                             dfn = Pi(tvs, SortedTerm(rel_tm, new_ty, noPos), noPos),
                                             fixity = Nonfix,
                                             fullyQualified? = opinfo.fullyQualified?}
                           in
                           let new_op_map = insertAQualifierMap(op_map,q,new_id,new_opinfo) in
                           let new_el = Op(Qualified(q,new_id), true, a) in
                           (new_elts ++ [new_el, el], new_op_map, new_tb))
                      | _ -> (new_elts ++ [el], op_map, tb))
               | Property(knd, qid as Qualified(q,id), tvs, bod, a) | tvs ~= [] & knd ~= Conjecture ->
                     % let _ = writeLine("Trying "^printQualifiedId qid^": "^printTerm bod) in
                     (case tryRelativizeTerm(tvs, bod, tb, boolSort, ho_eqfns, spc, coercions) of
                        | [] -> (new_elts ++ [el], op_map, tb)
                        | tv_map ->
                          let new_id = id ^ "__stp" in
                          let rel_bod = substTyVarsWithSubtypes (tv_map, bod) in
                          let new_bod = Bind(Forall, map (fn (_,Var(v,_)) -> v) tv_map, rel_bod, a) in
                          let new_prop = Property(knd, Qualified(q,new_id), tvs, new_bod, a)in
                          (new_elts ++ [new_prop, el], op_map, tb))
                   | _ -> (new_elts ++ [el], op_map, tb))
             ([], op_map, tb)
             elts
    in
    let (new_elts, new_op_map, tb) = relativizeElts(spc.elements, true, spc.ops, emptyAQualifierMap) in
    let spc = spc << {elements = new_elts, ops = new_op_map} in
    (spc, tb)

  op  addSubtypePredicateParams: Spec \_rightarrow TypeCoercionTable \_rightarrow Spec * PolyOpTable
  def addSubtypePredicateParams spc coercions =
    % let _ = writeLine(printSpec spc) in
    let (spc, tbl) = addRelativizedOps(spc, coercions) in
    %let _ = writeLine(printSpec spc) in
    % let _ = writeLine(anyToString tbl) in
    let spc = mapSpec (polyCallsTransformers(spc, tbl, false, coercions)) spc in
    let spc = mapSpec (polyCallsTransformers(spc, tbl, true,  coercions)) spc in
    % let _ = writeLine(printSpec spc) in
    (spc, tbl)


  %% For internal use. Choose unparseable name
  def toIsaQual = "ToIsa-Internal"

  op mkArbitrary(ty: Sort): MS.Term =
    mkOp(Qualified(toIsaQual, "regular_val"), ty)

  op mkSubtypeFnPredicate(dom_ty: Sort, ran_ty: Sort, f_ty: Sort): Option MS.Term =
    if ~(embed? Subsort dom_ty || embed? Subsort ran_ty) then None
    else
    case (dom_ty, ran_ty) of
      | (Subsort(dom_ty, domPred, _), Subsort(ran_ty, ranPred, _)) ->
        Some(mkApply(mkOp(Qualified(toIsaQual, "Fun_P"),
                          mkArrow(mkProduct[mkArrow(dom_ty, boolSort),
                                            mkArrow(ran_ty, boolSort)],
                                  mkArrow(f_ty, boolSort))),
                     mkTuple [domPred, ranPred]))
      | (Subsort(dom_ty, domPred, _), Boolean _) | regularizeBooleanToFalse? -> 
        Some(mkApply(mkOp(Qualified(toIsaQual, "Fun_PDB"),
                          mkArrow(mkArrow(dom_ty, boolSort),
                                  mkArrow(f_ty, boolSort))),
                     domPred))
      | (Subsort(dom_ty, domPred, _), _) ->
        Some(mkApply(mkOp(Qualified(toIsaQual, "Fun_PD"),
                          mkArrow(mkArrow(dom_ty, boolSort),
                                  mkArrow(f_ty, boolSort))),
                     domPred))
      | (_, Subsort(ran_ty, ranPred, _)) ->
        Some(mkApply(mkOp(Qualified(toIsaQual, "Fun_PR"),
                          mkArrow(mkArrow(ran_ty, boolSort),
                                  mkArrow(f_ty, boolSort))),
                     ranPred))
      | _ -> None

  op changePatternType(pat: Pattern, ty: Sort, spc: Spec): Pattern =
    case pat of
      | VarPat((v, _), a) -> VarPat((v, ty), a)
      | WildPat(_, a) -> WildPat(ty, a)
      | RecordPat(pat_prs, a) ->
        let ty_prs = product(spc, ty) in
        let new_pat_prs = map (fn ((id, pat_pat), (_, tyi)) -> (id, changePatternType(pat_pat, tyi, spc)))
                            (zip(pat_prs, ty_prs))
        in
        RecordPat(new_pat_prs, a)
      | AliasPat(p1, p2, a) ->
        AliasPat(changePatternType(p1, ty, spc), changePatternType(p2, ty, spc), a)
      | _ -> pat
    

  %% Not currently used
  op changeDomainType(fn_tm: MS.Term, dom_ty: Sort, spc: Spec): MS. Term =
    % let _ = writeLine("cdt: "^printTermWithSorts fn_tm^"  c  "^printSort dom_ty) in
    let result =
    case fn_tm of
      | Fun(f, fn_ty, a) ->
        (case rangeOpt(spc, fn_ty) of
         | Some rng -> Fun(f, Arrow(dom_ty, rng, a), a)
         | None -> fn_tm)
      | Var((v, fn_ty), a) ->
        (case rangeOpt(spc, fn_ty) of
         | Some rng -> Var((v, Arrow(dom_ty, rng, a)), a)
         | None -> fn_tm)
      | Lambda(matches, a) ->
        let n_matches = map (fn (pat, c, bod) ->
                               let new_pat = changePatternType(pat, dom_ty, spc) in
                               let sb = map (fn (old_v, new_v) -> (old_v, mkVar new_v))
                                          (zip(patternVars pat, patternVars new_pat))
                               in
                               (new_pat, c, substitute(bod, sb)))
                          matches
        in
        Lambda(n_matches, a)
      | Let(decls, bod, a) ->
        Let(decls, changeDomainType(bod, dom_ty, spc), a)
      | _ -> fn_tm
    in
    %let _ = writeLine("returned: "^ printTermWithSorts result) in
    result

  op raiseSubtypeFn(ty: Sort, spc: Spec): Sort =
    %% Bring subtypes to the top-level
    %% Like raiseSubtype, but doesn't look inside Nat (because it should already have
    %% been expanded) The two functions should be merged
    % let _ = writeLine("rstf: "^printSort ty) in
    case ty of
      | Base(qid, args, a) | qid nin? dontRaiseTypes ->
        let args = map (fn tyi -> raiseSubtypeFn(tyi, spc)) args in
        if exists (fn tyi -> embed? Subsort tyi) args
          then
          let Qualified(q,id) = qid in
          let pred_name = id^"_P" in
          let pred_qid = Qualified(q, pred_name) in
          (case AnnSpec.findTheOp(spc, pred_qid) of
             | Some _ ->
               let arg_comps = map (fn tyi ->
                                    case tyi of
                                      | Subsort(styi, pr, _) -> (styi, pr)
                                      | _ -> (tyi, mkLambda(mkWildPat tyi, trueTerm)))
                                 args
               in
               let (bare_args, arg_preds) = unzip arg_comps in
               let bare_ty = Base(qid, bare_args, a) in
               let arg_preds_lst =  decomposeListConjPred arg_preds in
               let preds = map (fn arg_preds ->
                                  mkAppl(mkOp(pred_qid, mkArrow(mkProduct(map (fn ty -> mkArrow(ty, boolSort)) bare_args),
                                                                mkArrow(bare_ty, boolSort))),
                                         arg_preds))
                             arg_preds_lst
               in
               mkSubtypePreds(bare_ty, preds, a)
             | None ->
               (case tryUnfoldBase spc ty of
                  | None -> ty
                  | Some exp_ty ->
                    let raise_ty = raiseSubtypeFn(exp_ty, spc) in
                    if embed? Subsort raise_ty
                      then raise_ty else ty))
        else
          (case tryUnfoldBase spc ty of
             | None -> ty
             | Some exp_ty ->
               let raise_ty = raiseSubtypeFn(exp_ty, spc) in
               if embed? Subsort raise_ty
                 then raise_ty else ty)
      | Subsort(s_ty, p, a) ->
        (case raiseSubtypeFn(s_ty, spc) of
           | Subsort(sss_ty, pr, _) -> composeSubtypes(sss_ty, p, pr, a)
           | _ -> ty)
      | Product(flds, a) ->
        let flds = map (fn (id, ty) -> (id, raiseSubtypeFn(ty, spc))) flds in
        if exists (fn (_,tyi) -> embed? Subsort tyi) flds
          then let (bare_flds, arg_id_vars, pred,_) =
                foldl (fn ((bare_flds, arg_id_vars, pred, i),(id,tyi)) ->
                         case tyi of
                           | Subsort(t,p,_) -> let v = ("x"^toString i, t)  in
                                               (bare_flds ++ [(id,t)],
                                                arg_id_vars ++ [(id, mkVarPat v)],
                                                Utilities.mkAnd(pred, mkApply(p, mkVar v)),
                                                i+1)
                           | _ -> (bare_flds ++ [(id,tyi)],
                                   arg_id_vars ++ [(id, mkWildPat tyi)],
                                   pred,
                                   i+1))
                  ([],[],trueTerm,0) flds
               in
               Subsort(Product(bare_flds,a),
                       mkLambda(mkRecordPat arg_id_vars, pred), a)
          else ty
      | Arrow(dom, rng ,a) ->
        (case mkSubtypeFnPredicate(raiseSubtypeFn(dom,spc), raiseSubtypeFn(rng,spc), ty) of
           | Some pred -> Subsort(ty, pred, a)
           | None -> ty)
      | _ -> ty
 
  op relativizeQuantifiers(spc: Spec) (t: MS.Term): MS.Term =
    case t of
      | Bind(bndr,bndVars,bod,a) \_rightarrow
        let (bndVars,bndVarsPred) =
            foldr (fn ((vn,ty0), (bndVars,res)) ->
                     let ty = raiseSubtypeFn(ty0, spc) in
                     % let _ = writeLine("relQ: "^printSort ty0^" ---> "^printSort ty) in
                     let pred_tm = srtPred(spc, ty, mkVar(vn,ty)) in
                     let pred_tm = mapTerm (relativizeQuantifiers spc,id,id) pred_tm in
                     (Cons((vn,ty),bndVars), Utilities.mkAnd(pred_tm, res)))
              ([],mkTrue()) bndVars
        in
        let new_bod = case bndr of
                        | Forall -> Utilities.mkSimpImplies(bndVarsPred, bod)
                        | Exists -> Utilities.mkAnd(bndVarsPred, bod)
                        | Exists1 -> Utilities.mkAnd(bndVarsPred, bod)
        in
        Bind(bndr,bndVars,new_bod,a)
      | The(theVar as (vn,ty),bod,a) \_rightarrow
        let ty = raiseSubtypeFn(ty,spc) in
        let theVarPred = srtPred(spc, ty, mkVar(vn,ty)) in
        let new_bod = Utilities.mkAnd(theVarPred, bod) in
        The((vn,ty),new_bod,a)
      | _ \_rightarrow t

  op refToHo_eqfns(f: Fun, qids: List QualifiedId): Boolean =
    case f of
      | Op(qid,_) -> member(qid, qids)
      | _ -> false

  op hoTypesIn(spc: Spec) (ty: Sort): List Sort =
    case unfoldBeforeCoProduct(spc, ty) of
      | Arrow _ -> [ty]
      | TyVar _ -> [ty]
      | Product(flds,_) -> foldl (fn (result,(_,tyi)) -> hoTypesIn spc tyi ++ result) [] flds
      | Subsort(s_ty,_,_) -> hoTypesIn spc s_ty
      | _ -> []

  op hoFunTypes(spc: Spec) (f_ty: Sort): List Sort =
    case arrowOpt(spc, f_ty) of
      | Some(dom, rng) ->
        hoTypesIn spc dom ++ hoFunTypes spc rng
      | None -> []

  op hasArgTypeIn?(spc: Spec) (tys: List Sort) (a_ty: Sort): Boolean =
    case unfoldBeforeCoProduct(spc, a_ty) of
      | Product(flds,_)   -> exists (fn (_,tyi) -> hasArgTypeIn? spc tys tyi) flds
      | Subsort(s_ty,_,_) -> hasArgTypeIn? spc tys s_ty
      | _ -> member(a_ty, tys)

  op hasFunTypeIn?(spc: Spec) (tys: List Sort)(f_ty: Sort): Boolean =
    case arrowOpt(spc, f_ty) of
      | Some(dom, rng) ->
        hasArgTypeIn? spc tys dom
         || hasFunTypeIn? spc tys rng
      | None -> false

  op findHOEqualityFuns(spc: Spec): List QualifiedId =
    let def iterate1(qids,initial?) =
          foldOpInfos
            (fn (info, qids) ->
               if member(primaryOpName info, qids) then qids
               else
               let (tvs,ty,defn) = unpackFirstOpDef info in
               let ho_fn_types = hoFunTypes spc ty in
               if ho_fn_types ~= []
                 && existsSubTerm (fn t -> case t of
                                             | Fun(f,f_ty,_)
                                                 | ((initial? && (f = Equals || f = NotEquals))
                                                     || refToHo_eqfns(f, qids))
                                                    && hasFunTypeIn? spc ho_fn_types f_ty
                                                 -> true
                                             | _ -> false)
                     defn
                 then info.names ++ qids
                 else qids)
            qids spc.ops
        def iterateUntilNoChange qids =
          let new_qids = iterate1(qids, false) in
          if new_qids = qids then qids
            else iterateUntilNoChange new_qids
    in
    iterateUntilNoChange(iterate1([], true))

  op possibleHoEqualTestableArg?(f: MS.Term, ho_eqfns: List QualifiedId): Boolean =
    case f of
      | Fun(f, _,_) ->
        (case f of
           | Equals -> true
           | NotEquals -> true
           | Embed _ -> true
           | _ -> refToHo_eqfns(f, ho_eqfns))
      | Apply(f, _, _) -> possibleHoEqualTestableArg?(f, ho_eqfns)
      | _ -> false

  op regTermTop (info: OpInfo, ho_eqfns: List QualifiedId, spc: Spec): MS.Term =
    let (tvs,ty,tm) = unpackFirstOpDef info in
    let recursive? = containsRefToOp?(tm, primaryOpName info) in
    let result = regTerm(tm, ty, ~(arrow?(spc,ty)), ho_eqfns, spc) in
    let result = if recursive?
                  then   % May need condition to prove termination
                    regularizeIfPFun(result, ty, inferType(spc,result), spc)
                  else result
    in
    if equalTerm?(result, tm)
      then maybePiTerm(tvs, SortedTerm(tm,ty,termAnn tm)) 
    else
    % let _ = writeLine("Def:\n"^printTerm tm^"\n  changed to\n"^printTerm result) in
    maybePiTerm(tvs, SortedTerm(result,ty,termAnn tm)) 

  op regularizeIfPFun(t: MS.Term, ty: Sort, rm_ty: Sort, spc: Spec): MS.Term =
    % ty is expected type, rm_ty is provided types
    % let _ = writeLine("Regularize: "^printTerm t^": "^printSort ty^" to "^printSort rm_ty) in
    case (arrowOpt(spc,ty), arrowOpt(spc,rm_ty)) of
      | (Some(dom, rng), Some(rm_dom, rm_rng)) ->
        if embed? Var t && equalType?(dom, rm_dom) then t
        else
        let rfun = if embed? Boolean (stripSubsorts(spc, rng))
                     then case ty of
                            | Base(Qualified("Set", "Set"),_,_) | regularizeSets? -> "RSet"
                            | _ -> if regularizeBooleanToFalse? then "RFunB" else "RFun"
                   else "RFun"
        in
        let def mkRFun(pred, t) =
              let pred = simplify spc pred in
              %% We are only coercing domain so pass expectation for range down
              let exp_ty = if equalType?(rng, rm_rng) then rm_ty else mkArrow(rm_dom, rng) in
              let reg_t =
                  case (pred, t) of
                    | (Lambda([(pred_pat, Fun(Bool true,_,_), pred_bod)],_),
                       Lambda([(fn_pat, Fun(Bool true,_,_), fn_bod)],_))
                        | rfun = "RFun" ->
                      (case matchPatterns(fn_pat, pred_pat) of
                         | Some sb ->
                           mkLambda(fn_pat, Utilities.mkIfThenElse(substitute(pred_bod, sb),
                                                                   fn_bod, mkArbitrary ty))
                         | None ->
                       case patternToTerm fn_pat of
                         | Some var_tm ->
                           mkLambda(fn_pat, Utilities.mkIfThenElse(simplifiedApply(pred, var_tm, spc),
                                                                   fn_bod, mkArbitrary ty))
                         | None ->
                           mkApply(mkApply(mkOp(Qualified(toIsaQual, rfun),
                                                mkArrow(inferType(spc, pred),
                                                        mkArrow(exp_ty, ty))),
                                           pred),
                                   t))
                    | (_, Lambda([(fn_pat, Fun(Bool true,_,_), fn_bod)],_)) ->
                      (case patternToTerm fn_pat of
                         | Some var_tm ->
                           mkLambda(fn_pat, Utilities.mkIfThenElse(simplifiedApply(pred, var_tm, spc),
                                                                   fn_bod, mkArbitrary ty))
                         | None ->
                           mkApply(mkApply(mkOp(Qualified(toIsaQual, rfun),
                                                mkArrow(inferType(spc, pred),
                                                        mkArrow(exp_ty, ty))),
                                           pred),
                                   t))
                    | _ ->
                      mkApply(mkApply(mkOp(Qualified(toIsaQual, rfun),
                                           mkArrow(inferType(spc, pred),
                                                   mkArrow(exp_ty, ty))),
                                      pred),
                              t)
              in
              % let _ = writeLine("Regularize: "^printTerm t^" to\n"^printTermWithSorts reg_t) in
              reg_t
        in
        (case subtypeComps(spc, raiseSubtypeFn(dom, spc)) of
           | None ->
             (case subtypeComps(spc, raiseSubtypeFn(rm_dom, spc)) of
                | Some(sup_ty, pred) | eagerRegularization? ->
                  mkRFun(pred, t)
                | _ -> t)
           | Some(sup_ty, pred) -> mkRFun(pred, t))
      | _ -> t

  op regTerm (t, ty, equal_testable?, ho_eqfns: List QualifiedId, spc: Spec): MS.Term =
    let rm_ty = inferType(spc,t) in
    let t = if equal_testable? && ~eagerRegularization?
              then regularizeIfPFun(t, ty, rm_ty, spc)
            else t
    in
    case t of
      | Apply(f, x, a) ->
        let (dom, rng) = arrow(spc, inferType(spc, f)) in
        Apply(regTerm(f, mkArrow(inferType(spc, x), ty), false, ho_eqfns, spc),
              regTerm(x, dom, possibleHoEqualTestableArg?(f, ho_eqfns), ho_eqfns, spc), a)
      | Record(row, a) ->
        % let _ = writeLine("regTerm "^printTerm t^":\n"^printSort ty) in
        let srts = map (fn (_,x) -> x) (product (spc,ty)) in
        Record(map (fn ((idi,tmi), tyi) \_rightarrow (idi, regTerm(tmi, tyi, equal_testable?, ho_eqfns, spc)))
                 (zip(row,srts)), a) 
      | Bind(b, vs, bod, a) ->
        Bind(b, vs, regTerm(bod, boolSort, false, ho_eqfns, spc), a)
      | The(v, bod, a) ->
        The(v, regTerm(bod, boolSort, false, ho_eqfns, spc), a)
      | Let(decls, bod, a) ->
        Let (map (fn (pat,trm) \_rightarrow (pat, regTerm(trm, patternSort pat, equal_testable?, ho_eqfns, spc)))
               decls,
             regTerm(bod, ty, equal_testable?, ho_eqfns, spc), a)
      | LetRec(decls, bod, a) ->
        LetRec (map (fn ((id,srt), trm) \_rightarrow ((id,srt), regTerm(trm, srt, false, ho_eqfns, spc))) decls,
                regTerm(bod, ty, equal_testable?, ho_eqfns, spc), a)
      | Lambda(match, a) ->
        let lam_tm = 
            Lambda (map (fn (pat,condn,trm) \_rightarrow
                           (pat, regTerm(condn, boolSort, false, ho_eqfns, spc),
                            regTerm(trm, range(spc,ty), false, ho_eqfns, spc))) % ?
                      match,
                    a)
        in
        if eagerRegularization?
          then regularizeIfPFun(lam_tm, ty, rm_ty, spc)
          else lam_tm
      | IfThenElse(x,y,z, a) ->
        IfThenElse(regTerm(x, boolSort, false, ho_eqfns, spc),
                   regTerm(y, ty, equal_testable?, ho_eqfns, spc),
                   regTerm(z, ty, equal_testable?, ho_eqfns, spc), a)
      %| Seq(tms, a) ->
      | SortedTerm(tm, tm_ty, a) ->
        SortedTerm(regTerm(tm, tm_ty, equal_testable?, ho_eqfns, spc), tm_ty, a)
      | _ -> t
         
  op regularizeFunctions(spc: Spec): Spec =
    let ho_eqfns = findHOEqualityFuns spc in
    % let _ = writeLine(anyToString ho_eqfns) in
    % let _ = writeLine(printSpec spc) in
    let spc =
        spc << {ops = foldl (fn (ops,el) \_rightarrow
                             case el of
                               | Op (qid as Qualified(q,id), true, _) \_rightarrow
                                 %% true means decl includes def
                                 (case AnnSpec.findTheOp(spc,qid) of
                                   | Some info \_rightarrow
                                     insertAQualifierMap (ops, q, id,
                                                          info << {dfn = regTermTop(info, ho_eqfns, spc)})
                                   | None \_rightarrow ops)
                               | OpDef (qid as Qualified(q,id), _) \_rightarrow
                                 (case AnnSpec.findTheOp(spc,qid) of
                                   | Some info \_rightarrow
                                     insertAQualifierMap (ops, q, id,
                                                          info << {dfn = regTermTop(info, ho_eqfns, spc)})
                                   | None \_rightarrow ops)
                               | _ \_rightarrow ops)
                        spc.ops
                        spc.elements,
                %% mapOpInfos (fn info \_rightarrow info << {dfn = mapTermTop info}) spc.ops,
                elements = map (fn el \_rightarrow
                                  case el of
                                    | Property(pt, nm, tvs, term,a) \_rightarrow
                                      Property(pt, nm, tvs, regTerm(term, boolSort, false, ho_eqfns, spc),a)
                                    | _ \_rightarrow el)
                             spc.elements}
    in
    % let _ = writeLine(printSpec spc) in
    spc

  op typePred(spc: Spec, ty: Sort, tm: MS.Term): MS.Term =
    % let _ = writeLine("tp: "^printTerm tm^": "^printSort ty) in
    case raiseSubtypeFn(ty, spc) of
      | Subsort(_, pred, _) ->
        % let _ = writeLine("tpp: "^printTerm pred) in
        let pred = maybeUnfoldSubTypePred(spc, pred) in
        (case pred of
           | Lambda([(pat, Fun(Bool true,_,_), sub_ty_bod)], _) | varRecordPattern? pat ->
             simplifyOne spc (mkLet([(pat, tm)], sub_ty_bod))
           | _ -> simplifiedApply(pred, tm, spc))
      | _ -> trueTerm

  op argName(i: Nat): String =
    case i of
      | 0 -> "d__x"
      | 1 -> "d__y"
      | 2 -> "d__z"
      | _ -> "d__"^toString i

  op tryUnpackLambda(tm: Option MS.Term): Option(Pattern * MS.Term) =
    case tm of
      | Some(Lambda([(pat, Fun(Bool true,_,_), bod)], _)) | varRecordPattern? pat -> Some(pat, bod)
      | _ -> None

  op termSubtypeCondn(spc: Spec, term: MS.Term, ty: Sort, defn?: Option MS.Term, depth: Nat): MS.Term =
    % let _ = writeLine("\ntsc: "^printTerm term^": "^printSort ty^"\n"^(case defn? of
    %                                                                     Some defn -> printTerm defn | _ -> "")) in
    case unfoldBase(spc, ty) of
      | Arrow(dom, rng, _) ->
	(case unfoldBase(spc, dom) of
          | Subsort(_, Lambda([(pat, Fun(Bool true,_,_), sub_ty_bod)], _), _) | varRecordPattern? pat ->
            let Some arg_tm = patternToTerm pat in
            let vs = patternVars pat in
            let rangeTerm = mkApply(term, arg_tm) in
            let rangePred = termSubtypeCondn(spc, rangeTerm, rng, None, depth + 1) in
            mkBind(Forall, vs, mkSimpImplies(sub_ty_bod, rangePred))
          | dom ->
         case tryUnpackLambda(defn?) of
          | Some(pat, bod) ->
            %% Gives dependent-type capability
            let Some arg_tm = patternToTerm pat in
            let vs = patternVars pat in
            let rangeTerm = mkApply(term, arg_tm) in
            let rangePred = termSubtypeCondn(spc, rangeTerm, rng, Some bod, depth + 1) in
            mkBind(Forall, vs, rangePred)
          | _ ->
         case dom of
	  | Product(fields, _) ->
            let name = argName depth in
	    let domVars = map (fn (id: Id, ty) -> (name ^ "_" ^ id, ty))
                              fields in
	    let domVarTerms = map (fn (var) -> mkVar(var)) domVars in
	    let rangeTerm = mkAppl(term, domVarTerms) in
	    let rangePred = termSubtypeCondn(spc, rangeTerm, rng, None, depth + 1) in
	    mkBind(Forall, domVars, rangePred)
	  | _ ->
            let name = argName depth in
	    let domVar = (name, dom) in
	    let domVarTerm = mkVar(domVar) in
	    let rangeTerm = mkApply(term, domVarTerm) in
	    let rangePred = termSubtypeCondn(spc, rangeTerm, rng, None, depth + 1) in
	    mkBind(Forall, [domVar], rangePred))
       | _ -> typePred(spc, ty, term)

  op range_*(spc: Spec, ty: Sort): Sort =
    case unfoldBase(spc, ty) of
      | Arrow(_, rng, _) -> range_*(spc, rng)
      | _ -> ty        

  op opSubtypeTheorem(spc: Spec, opname as (Qualified(q,id)): QualifiedId, fx: Fixity,
                      tvs: TyVars, ty: Sort, defn: MS.Term,
                      coercions: TypeCoercionTable, stp_tbl: PolyOpTable): MS.Term =
    let base_thm = termSubtypeCondn(spc, mkInfixOp(opname, fx, ty), ty, Some defn, 0) in
    if stpFun? id || tvs = [] || hasStpFun?(spc, opname) then base_thm
      else
      let result_ty = range_*(spc, ty) in
      let range_tvs = freeTyVars result_ty in
      if range_tvs = [] then base_thm
      else
      let tv_pred_map = map (fn tv -> (tv, mkVar("P__"^tv, mkArrow(mkTyVar tv, boolSort)))) range_tvs in
      let tv_ty_map = map (fn (tv, pred) -> (tv, mkSubsort(mkTyVar tv, pred))) tv_pred_map in
      let ty_with_preds = instantiateTyVarsInType(ty, tv_ty_map) in
      let defn_with_preds = substTyVarsWithSubtypes(tv_pred_map, defn) in
      let pred_thm = termSubtypeCondn(spc, mkInfixOp(opname, fx, ty_with_preds),
                                      ty_with_preds, Some defn_with_preds, 0)
      in
      let pred_thm = mapTerm (polyCallsTransformers(spc, stp_tbl, true, coercions)) pred_thm in
      mkConj[base_thm, pred_thm]

  op separateRhsConjuncts(tm: MS.Term): List MS.Term =
    case tm of
      | Bind(Forall, vs, bod, a) ->
        map (fn b -> Bind(Forall, vs, b, a)) (separateRhsConjuncts bod)
      | Apply(Fun (Implies, _, _), Record([(_, lhs), (_, rhs)], _), _) ->
        map (fn b -> mkImplies(lhs, b)) (separateRhsConjuncts rhs)
      | Let(decls, bod, a) ->
        map (fn b -> Let(decls, b, a)) (separateRhsConjuncts bod)
      | Apply(Lambda([(pat, Fun(Bool true, _, _) ,bod)], _), e, a) | varRecordPattern? pat ->
        map (fn b -> Let([(pat, e)], b, a)) (separateRhsConjuncts bod)
      | Apply(Fun(And,_,_), _, _) -> flatten(map separateRhsConjuncts (getConjuncts tm))
      | _ -> [tm]


  op  removeSubTypes: Spec \_rightarrow TypeCoercionTable \_rightarrow PolyOpTable \_rightarrow Spec
  def removeSubTypes spc coercions stp_tbl =
    %% Remove subsort definition for directly-implemented subtypes
    let spc = spc << {sorts = mapSortInfos
                                (fn info \_rightarrow
                                 let qid = primarySortName info in
                                 if (exists (\_lambda tb \_rightarrow tb.subtype = qid) coercions)
                                   && embed? Subsort (firstSortDef info)
                                   then info << {dfn = And([],noPos)}
                                   else info)
                                spc.sorts}
    in
    %% Regularize functions that may be used in equality tests
    let spc = regularizeFunctions spc in
    %% Add subtype assertions from op declarations
    let spc =
        spc << {elements =
                  foldr (fn (el,r) \_rightarrow
                         case el of
                         | Op(qid as (Qualified(q,id)), def?, a)
                             | ~(stpFun? id) \_rightarrow
                           let Some info = AnnSpec.findTheOp(spc,qid) in
                           let (tvs, ty, defn) = unpackFirstOpDef info in
                           % let _ = writeLine ("\nstc: "^id^": "^printSort ty) in
                           % let _ = writeLine(printSort(raiseSubtypeFn(ty, spc))) in
                           let subTypeFmla = opSubtypeTheorem(spc, qid, info.fixity, tvs, ty, defn,
                                                              coercions, stp_tbl)
                           in
                           % let _ = writeLine (printTerm subTypeFmla) in
                           % ?? let liftedFmlas = removePatternTop(spc, subTypeFmla) in
                           (case simplify spc subTypeFmla of
                            | Fun(Bool true,_,_) \_rightarrow Cons(el,r)
                            | s_fm \_rightarrow
                              % let _ = writeLine (" --> "^printTerm s_fm) in
                              let fms = separateRhsConjuncts s_fm in
                              let thms = map (fn (i, fm) ->
                                              Property(if def? then Theorem else Axiom, 
                                                       mkQualifiedId
                                                         (q, id^"_subtype_constr"
                                                            ^(if i = 0 then "" else toString i)), 
                                                       [], fm, a))
                                           (tabulate (length fms, fn i -> (i, fms@i)))
                              in
                              case r of
                                | (p as Pragma_)::rs -> [el, p] ++ thms ++ rs
                                | _ -> el :: (thms ++ r))
                             | _ \_rightarrow el :: r)
                  [] spc.elements}
    in
    %let _ = writeLine(anyToString tbl) in
    %let _ = writeLine(printSpec spc) in
    let spc = mapSpec (relativizeQuantifiers spc, id, id) spc in
    %let _ = writeLine(printSpec spc) in
    %% Replace subtypes by supertypes
    mapSpec (id,fn s \_rightarrow
		   case s of
		     | Subsort(supTy,_,_) \_rightarrow supTy
		     | _ \_rightarrow s,
             id)
      spc

  op removeSubtypesInTerm (spc: Spec) (t: MS.Term): MS.Term =
    let t = mapTerm(relativizeQuantifiers spc, id, id) t in
    mapTerm (id,fn s \_rightarrow
		   case s of
		     | Subsort(supTy,_,_) \_rightarrow supTy
		     | _ \_rightarrow s,
             id)
      t

  op hoSubtypePredicateForType(qid as Qualified(q,id): QualifiedId, tys: List Sort, param_ty: Sort, spc: Spec)
     : Option MS.Term =
    let pred_qid = Qualified(q,id^"_P") in
    case AnnSpec.findTheOp(spc, pred_qid) of
      | None -> None
      | Some info ->
        let pred_args = map (fn ty -> mkOptLambda(typePattern(ty, spc))) tys in
        Some(mkAppl(mkOp(pred_qid, mkArrow(mkProduct(map (fn ty -> mkArrow(ty, boolSort)) tys),
                                           mkArrow(param_ty, boolSort))),
                    pred_args))

  op typePattern(ty: Sort, spc: Spec): Pattern * MS.Term =
    let def aux(ty, i: Nat) =
          case ty of
            | TyVar(tv,a) ->
              let nm = "x"^toString i in
              (mkVarPat(nm, ty), mkApply(mkVar("P_"^tv, Arrow(TyVar(tv, a), boolSort, a)),
                                         mkVar(nm, ty)))
            | Base(qid, a_tys, a) | a_tys ~= [] ->
              (case hoSubtypePredicateForType(qid, a_tys, ty, spc) of
                 | Some pred ->
                   let nm = "x"^toString i in
                   (mkVarPat(nm, ty),
                    mkApply(pred, mkVar(nm, ty)))
                 | None ->
                   (case tryUnfoldBase spc ty of
                      | None -> (mkWildPat(ty), trueTerm)
                      | Some exp_ty -> aux(exp_ty, i)))
            | Product(prs, a) ->
              let (pats, preds, _) = foldl (fn ((pats,preds,i),(id,e_ty)) ->
                                            let (pat,pred) = aux(e_ty,i) in
                                            (Cons((id,pat), pats), Cons(pred, preds), i+1))
                                       ([], [], i*10) prs
              in
              (RecordPat(rev pats, a), foldl Utilities.mkAnd trueTerm preds)
            | _ -> (mkWildPat(ty), trueTerm)
    in
    aux(ty, 0)

  %% For named type T a create HO predicate T_P that takes a subtype on a and produces subtype on T a
  op addSubtypePredicateLifters(spc: Spec): Spec =
    let def addPredDecl((qid as Qualified(q,id),a), el, n_elts, spc) =
          let Some info = AnnSpec.findTheSort(spc, qid) in
          let (tvs,ty_def) = unpackFirstSortDef info in
          if tvs = [] || (case ty_def of
                            | Any _ -> false
                            | CoProduct _ -> false
                            | Product _ -> false
                            | Quotient _ -> true % ?
                            | _ -> true)
            then (Cons(el, n_elts), spc)
          else
          let pred_name = id^"_P" in
          % let _ = writeLine("making "^pred_name^" with "^toString def?) in
          let pred_qid = Qualified(q, pred_name) in
          (case AnnSpec.findTheOp(spc, pred_qid) of
             | Some _ -> (Cons(el, n_elts), spc) % already exists. Should check type is correct!
             | None ->
           let param_ty = Base(qid, map (fn tv -> TyVar(tv, a)) tvs, a) in
           let pred_ty = Arrow(mkProduct(map (fn tv -> Arrow(TyVar(tv, a), boolSort, a)) tvs),
                               Arrow(param_ty, boolSort, a), a)
           in
           let x_dfn = Pi(tvs, SortedTerm(Any a, pred_ty, a), a) in
           let op_map = insertAQualifierMap(spc.ops, q, pred_name,
                                            {names = [pred_qid], dfn = x_dfn,
                                             fixity = Nonfix, fullyQualified? = false})
           in
           ([Op(pred_qid, ~(embed? Any ty_def), a), el] ++ n_elts, spc << {ops = op_map}))
        def addPredDeclss (elts, op_map) =
          foldl (fn ((n_elts, op_map),el) ->
                 case el of
                   | Sort sd -> addPredDecl(sd, el, n_elts, op_map)
                   | SortDef sd -> addPredDecl(sd, el, n_elts, op_map)
                   | Import(s_tm, i_sp, i_elts, a) ->
                     let (r_elts, op_map) = addPredDeclss(i_elts, op_map) in
                     (Cons(Import(s_tm, i_sp, rev r_elts, a), n_elts), op_map)
                   |  _ -> (Cons(el, n_elts), op_map))
            ([], op_map) elts
        def addPredDef((ty_qid as Qualified(q,id), a), spc) =
          let Some info = AnnSpec.findTheSort(spc, ty_qid) in
          let (tvs, ty_def) = unpackFirstSortDef info in
          if tvs = [] || (case ty_def of
                            | Any _ -> false
                            | CoProduct _ -> false
                            | Product _ -> false
                            | Quotient _ -> true % ?
                            | _ -> true)
            then spc
          else
          let pred_name = id^"_P" in
          let pred_qid = Qualified(q, pred_name) in
          case AnnSpec.findTheOp(spc, pred_qid) of
             | Some info ->
               let (tvs, pred_ty, _) = unpackFirstOpDef info in
               let param_ty = Base(ty_qid, map (fn tv -> TyVar(tv, a)) tvs, a) in
               let dfn = case ty_def of
                           | CoProduct(constrs,_) ->
                             mkLambda(mkTuplePat(map (fn tv ->
                                                        mkVarPat("P_"^tv,
                                                                 Arrow(TyVar(tv, a),
                                                                       boolSort, a)))
                                                   tvs),
                                      mkLambda
                                        (mkVarPat("x__c", param_ty),
                                         mkApply(Lambda
                                                   (map (fn (id,o_ty) ->
                                                           case o_ty of
                                                             | None ->
                                                               (EmbedPat(id, None, param_ty, a),
                                                                trueTerm, trueTerm)
                                                             | Some ty ->
                                                               let (p, p_t) = typePattern(ty, spc) in
                                                               (EmbedPat(id, Some p, param_ty, a), 
                                                                trueTerm, p_t))
                                                      constrs, a),
                                                 mkVar("x__c", param_ty))))
                           | Product _ ->
                             let (p,p_t) = typePattern(ty_def, spc) in
                             mkLambda(mkTuplePat(map (fn tv -> mkVarPat("P_"^tv, Arrow(TyVar(tv, a), boolSort, a)))
                                                   tvs),
                                      mkLambda(p, p_t))
                           | _ -> Any a
               in
               let x_dfn = Pi(tvs, SortedTerm(dfn, pred_ty, a), a) in
               let ops = insertAQualifierMap(spc.ops, q, pred_name, info << {dfn = x_dfn}) in
               spc << {ops = ops}
             | None -> spc
    in
    let (new_elts, spc) = addPredDeclss (spc.elements, spc) in
    let spc = spc << {elements = rev new_elts} in
    let spc = foldlSpecElements
                (fn (spc, el) ->
                 case el of
                   | SortDef ty_qid -> addPredDef(ty_qid, spc)
                   | _ -> spc)
                spc spc.elements
    in
    spc

endspec
