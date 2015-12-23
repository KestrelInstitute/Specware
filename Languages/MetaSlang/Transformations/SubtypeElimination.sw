(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

SpecNorm qualifying spec
  import Pragma, DefToAxiom, Coercions, EmptyTypesToSubtypes

  op eagerRegularization?: Bool = false
  op regularizeSets?: Bool = true
  op regularizeBoolToFalse?: Bool = false    % Can do this effectively in IsabelleExtensions
  op removeExcessAssumptions?: Bool = false

  op isaPragmaKinds: List String = ["Isa", "isa", "All", "Simplification"]
  op  isaPragma?(s: String): Bool =
    isOneOfPragmaKinds(s, isaPragmaKinds)

  op makeSubtypeConstrTheoremsString: String   =    "-subtype_constrs"
  op noMakeSubtypeConstrTheoremsString: String = "-no-subtype_constrs"
  op makeFreeTheoremsString: String      = "-free-theorems"
  op noMakeFreeTheoremsString: String = "-no-free-theorems"
  op subtypePredicateOpsObligationsString: String      = "-stp-op-obligations"
  op noSubtypePredicateOpsObligationsString: String = "-no-stp-op-obligations"
  op makeSubtypePredicateTheoremsString: String =      "-stp-theorems"
  op noMakeSubtypePredicateTheoremsString: String = "-no-stp-theorems"
  op makeStpTheoremsDefault?: Bool = false

  %% Polymorphic ops have versions that have a predicate for each polymorphic variable
  type PolyOpTable = AQualifierMap(QualifiedId * List TyVar)

    % mkLambda(mkWildPat ty, trueTerm)

  op substTyVarsWithSubtypes(tv_map: List(TyVar * MSTerm), tm: MSTerm): MSTerm =
    let result = instantiateTyVarsInTerm(tm, map (fn (tv,v) ->
                                                    (tv, Subtype(mkTyVar tv, v, noPos)))
                                               tv_map)
    in
    %let _ = writeLine("r: "^printTermWithTypes result) in
    result

  op subtypeC?(spc: Spec, ty: MSType, coercions: TypeCoercionTable): Bool =
    case ty of
     | Subtype _ -> true
     | Base(qid, _, _) | opaqueTypeQId? coercions qid -> false
     | Product(flds, _) ->
       exists? (fn (_,tyi) -> subtypeC?(spc, tyi, coercions)) flds
     | Arrow(dom, rng, _) ->
       subtypeC?(spc, dom, coercions) || subtypeC?(spc, rng, coercions)
     | Base(_, ty_args, _) ->
       exists? (fn tyi -> subtypeC?(spc, tyi, coercions)) ty_args
       || (let exp_ty =  unfoldBaseOne(spc, ty) in
           if ty = exp_ty then false
            else subtypeC?(spc, exp_ty, coercions))
     | _ -> false
 
  op polyCallsTransformers (spc: Spec, tb: PolyOpTable, types?: Bool, coercions: TypeCoercionTable)
     : TSP_Maps_St =
    let def doTerm (t: MSTerm): MSTerm =
          case t of
            | Fun(Op(qid as Qualified(q, id), fix?), ty, a) ->
              (case findAQualifierMap(tb, q, id) of
                 | None -> t
                 | Some(r_qid, used_tvs) ->
               case AnnSpec.findTheOp(spc, qid) of
                 | None -> t
                 | Some opinfo ->
               let (tvs, ty1, defn) = unpackFirstOpDef opinfo in
               % let _ = writeLine("\nRelativizing ref to: "^printQualifiedId qid^": "^printType ty) in
               % let _ = writeLine("Matching with: "^printType ty1) in
               case typeMatch(ty1, ty, spc, false, true) of
               % case (case typeMatch(ty1, ty, spc, false, true) of
               %         | None -> typeMatch(ty1, ty, spc, true, true)
               %         | ss -> ss) of
                 | None -> t
                 | Some tvsubst ->
               let tvsubst = filter (fn (tv,_) -> tv in? used_tvs) tvsubst in
               % let _ = (writeLine "Subst";
               %          app (fn (tv, ty) -> writeLine(tv^": "^printType ty)) tvsubst) in
               if exists? (fn (_, s_ty) -> subtypeC?(spc, s_ty, coercions)) tvsubst
                 then let (predArgs, predTypes) =
                          unzip
                            (map (fn tv -> let Some(_, s_ty) = findLeftmost
                                                                (fn (tvi,_) -> tv = tvi)
                                                                tvsubst
                                           in
                                           let s_ty1 = raiseSubtypeFn(s_ty, spc) in
                                           % let _ = if equalType?(s_ty1, s_ty) then ()
                                           %         else writeLine("pct: "^printType s_ty^" --> "^printType s_ty1)
                                           % in
                                           case s_ty1 of
                                             | Subtype(s_ty2, pred, _) -> (pred, mkArrow(s_ty2, boolType))
                                             | _ -> (mkTruePred s_ty, mkArrow(s_ty, boolType)))
                               used_tvs)
                      in
                      % let _ = app (fn pred -> writeLine(printTermWithTypes pred)) predArgs in
                      let predTypes = map (fn pred -> inferType(spc, pred)) predArgs in
                      let new_t = mkAppl(Fun(Op(r_qid, Nonfix),
                                             mkArrow(mkProduct predTypes, ty), a),
                                         predArgs)
                      in
                      % let _ = writeLine("New t: "^printTerm new_t) in
                      new_t
                 else t)
            | _ -> t

        def doType (ty: MSType): MSType =
          case ty of
            | Base(qid, args, _) | args ~= [] && types? ->
              let new_ty = unfoldBase(spc, ty) in
              if equalType?(new_ty, ty) || embed? CoProduct new_ty then ty
              else
              let tr_ty = mapType (doTerm, doType, id) new_ty in
              if equalType?(tr_ty, new_ty) then ty
                else tr_ty
            | _ -> ty
    in
    (doTerm, doType, id)

  op domSubtypePred(ty: MSType, spc: Spec): MSTerms =
    case arrowOpt(spc, ty) of
      | None -> []
      | Some(dom_ty, _) ->
    if setType?(spc, ty) && regularizeSets? then []
    else
    let r_dom_ty = raiseSubtypeFn(dom_ty, spc) in
    case r_dom_ty of
      | Subtype(dom_ty, domPred, _) ->
        let ho_ty = mkArrow(mkArrow(dom_ty, boolType), mkArrow(ty, boolType)) in
        [mkApply(mkOp(Qualified(toIsaQual, "Fun_PD"), ho_ty), domPred)]
      | _ -> []

  op maybeTypePredTerm(ty0: MSType, tm: MSTerm, spc: Spec): Option MSTerm =
    let ty = raiseSubtypeFn(ty0, spc) in
    let preds1 = case ty of
                 | Subtype(_, pred, _) ->
                   let uf_pred = maybeUnfoldSubTypePred(spc, pred) in
                   % let _ = if equalTerm?(pred, uf_pred) then () else
                   %          writeLine("maybeUnfoldSubTypePred:\n"^printTerm pred^"\n--> "^printTerm uf_pred)
                   % in
                   [uf_pred]
                 | _ -> []
    in
    let preds2 = domSubtypePred(ty, spc) in
    case preds1 ++ preds2 of
      | [] -> None
      | preds ->
    %let _ = writeLine("typePredTerm:\n"^printTerm tm^"\n: "^printType ty0^"\n^ "^printType ty) in
        let pred = composeConjPreds(preds, spc) in
    %let _ = writeLine("Pred: "^printTermWithTypes pred) in
        Some (simplifiedApply(pred, tm, spc))

  op typePredTerm(ty0: MSType, tm: MSTerm, spc: Spec): MSTerm =
      extractOption trueTerm (maybeTypePredTerm(ty0,tm,spc))

  % Getting subtype predicates without a spec: the only difference is
  % that no definitions are unfolded
  op typePredTermNoSpec(ty0: MSType, tm: MSTerm): MSTerm =
    typePredTerm (ty0, tm, emptySpec)

  op maybeRelativize?(t: MSTerm, tb: PolyOpTable): Bool =
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

  op subtypePredFreeVars (t: MSTerm, spc: Spec): MSVars =
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

  op hasStpFun?(spc: Spec, Qualified(q, id): QualifiedId): Bool =
    some? (AnnSpec.findTheOp(spc, Qualified(q, makeStpName id)))

  op stpFun?(id: String): Bool =
    testSubseqEqual?("__stp", id, 0, length id - 5)

  op reduceStpFnArgs?: Bool = true

  op tryRelativizeTerm(tvs: TyVars, tm: MSTerm, tb: PolyOpTable, ty: MSType,
                       ho_eqfns: List QualifiedId, spc: Spec,
                       coercions: TypeCoercionTable)
      : List(Id * MSTerm) * MSTerm =
    % let _ = writeLine("tm: "^printTerm tm) in
    if tvs = [] || ~(maybeRelativize?(tm, tb))then ([],tm)
    else
    let tv_map = map (fn tv -> (tv, mkVar("P__"^tv, mkArrow(mkTyVar tv, boolType)))) tvs in
    % let _ = writeLine("tv_map: "^anyToString tv_map) in
    let st_tm = substTyVarsWithSubtypes(tv_map,tm) in
    let rel_tm = mapTerm (polyCallsTransformers(spc, tb, false, coercions)) st_tm in
    % let _ = writeLine("rel_tm: "^printTerm rel_tm) in
    let rel_tm = regTerm(rel_tm, ty, ~(arrow?(spc,ty)), ho_eqfns, spc) in
    % let _ = writeLine("rel_tm: "^printTerm rel_tm) in
    let fvs = freeVars rel_tm ++ subtypePredFreeVars(rel_tm, spc) in
    % let _ = writeLine("fvs: "^anyToString(fvs)) in
    let opt_tv_map =
         if reduceStpFnArgs?
           then filter (fn (_,Var(v,_)) -> inVars?(v, fvs)) tv_map
           else tv_map
    in
    % let _ = writeLine("opt_tv_map: "^anyToString opt_tv_map) in
    (opt_tv_map, rel_tm)

  op insertElPreservingNextPragma(el: SpecElement, new_el: SpecElement, next_elts: SpecElements)
       : SpecElements =
    case next_elts of
      | (prg_el as Pragma prg) :: next_elts1 | unnamedPragma? prg->
        [el, prg_el, new_el] ++ next_elts1
      | _ -> [el, new_el] ++ next_elts

  op addRelativizedOps(spc: Spec, coercions: TypeCoercionTable): Spec * PolyOpTable =
    let ho_eqfns = findHOEqualityFuns spc in
    let def relativizeElts(elts, top?, make_stp_thms?, op_map, tb) =
          case elts of
            | [] -> ([], op_map, tb)
            | el :: r_elts ->
          case el of
            | Import(s_tm, i_sp, im_elts, a) ->
              let (im_elts, op_map, tb) = relativizeElts(im_elts, false, makeStpTheoremsDefault?,
                                                            op_map, tb) in
              let (new_elts, op_map, tb) = relativizeElts(r_elts, top?, make_stp_thms?, op_map, tb) in
              (Import(s_tm, i_sp, im_elts, a) :: new_elts, op_map, tb)
            | Pragma("proof", prag_str, "end-proof", _) ->
              let make_stp_thms? =
                   case controlPragmaString prag_str of
                     | Some strs ->
                       if makeSubtypePredicateTheoremsString in? strs
                         then true
                       else if noMakeSubtypePredicateTheoremsString in? strs
                         then false
                       else make_stp_thms?
                     | None -> make_stp_thms?
              in
              let (new_elts, op_map, tb) = relativizeElts(r_elts, top?, make_stp_thms?, op_map, tb) in
              (el :: new_elts, op_map, tb)
            | Op(qid as Qualified(q,id), _, a) ->
              % let _ = writeLine("Trying "^printQualifiedId qid) in
              (case AnnSpec.findTheOp(spc, qid) of
               | Some opinfo ->
                 let (tvs, ty, dfn) = unpackNthTerm(opinfo.dfn, 0) in
                 % let dfn = refinedTerm(dfn, 0) in
                 (case tryRelativizeTerm(tvs, dfn, tb, ty, ho_eqfns, spc, coercions) of
                  | ([],_) ->
                    let (new_elts, op_map, tb) = relativizeElts(r_elts, top?, make_stp_thms?, op_map, tb) in
                    (el :: new_elts, op_map, tb)
                  | (tv_map,_) ->
                    let new_id = makeStpName id in
                    let new_tb = insertAQualifierMap(tb, q, id,
                                                     (Qualified(q,new_id),
                                                      map (fn (tv,_) -> tv) tv_map))
                    in
                    let rel_ty_tm = substTyVarsWithSubtypes (tv_map, TypedTerm(dfn,ty,noPos)) in
                    let TypedTerm(rel_dfn,ty,_) = rel_ty_tm in
                    let rel_tm = mkLambda(mkTuplePat(map (fn (_,Var v) -> VarPat v) tv_map),
                                          rel_dfn)
                    in
                    let new_ty = mkArrow(mkProduct(map (fn (_,Var((_,ty),_)) -> ty) tv_map), ty) in
                    let new_opinfo = {names = [Qualified(q,new_id)],
                                      dfn = Pi(tvs, TypedTerm(rel_tm, new_ty, noPos), noPos),
                                      fixity = Nonfix,
                                      fullyQualified? = opinfo.fullyQualified?}
                    in
                    let new_op_map = insertAQualifierMap(op_map,q,new_id,new_opinfo) in
                    let new_el = Op(Qualified(q,new_id), true, a) in
                    let (new_elts, op_map, tb) = relativizeElts(r_elts, top?, make_stp_thms?,
                                                                new_op_map, new_tb) in
                    (insertElPreservingNextPragma(el, new_el, new_elts), op_map, tb))
               | _ ->
                 let (new_elts, op_map, tb) = relativizeElts(r_elts, top?, make_stp_thms?, op_map, tb) in
                 (el :: new_elts, op_map, tb))
            | Property(knd, qid as Qualified(q,id), tvs, bod, a)
                | make_stp_thms? && tvs ~= [] && knd ~= Conjecture ->
              let (new_elts, op_map, tb) = relativizeElts(r_elts, top?, make_stp_thms?, op_map, tb) in
              % let _ = writeLine("Trying "^printQualifiedId qid^": "^printTerm bod) in
              (case tryRelativizeTerm(tvs, bod, tb, boolType, ho_eqfns, spc, coercions) of
                 | ([],_) -> (el :: new_elts, op_map, tb)
                 | (tv_map,_) ->
                   let new_id = id ^ "__stp" in
                   let rel_bod = substTyVarsWithSubtypes (tv_map, bod) in
                   let new_bod = Bind(Forall, map (fn (_,Var(v,_)) -> v) tv_map, rel_bod, a) in
                   let new_prop = Property(knd, Qualified(q,new_id), tvs, new_bod, a)in
                   (insertElPreservingNextPragma(el, new_prop, new_elts), op_map, tb))
            | _ ->
              let (new_elts, op_map, tb) = relativizeElts(r_elts, top?, make_stp_thms?, op_map, tb) in
              (el :: new_elts, op_map, tb)
    in
    let (new_elts, new_op_map, tb) = relativizeElts(spc.elements, false, makeStpTheoremsDefault?,
                                                    spc.ops, emptyAQualifierMap) in
    let spc = spc << {elements = new_elts, ops = new_op_map} in
    (spc, tb)

  op  addSubtypePredicateParams: Spec -> TypeCoercionTable -> Spec * PolyOpTable
  def addSubtypePredicateParams spc coercions =
    % let _ = writeLine(printSpec spc) in
    let (spc, stp_tbl) = addRelativizedOps(spc, coercions) in
    % let _ = writeLine(printSpec spc) in
    % let _ = writeLine(anyToString stp_tbl) in
    let spc = mapSpec (polyCallsTransformers(spc, stp_tbl, false, coercions)) spc in
    let spc = mapSpec (polyCallsTransformers(spc, stp_tbl, true,  coercions)) spc in
    % let _ = writeLine(printSpec spc) in
    (spc, stp_tbl)


  %% For internal use. Choose unparseable name
  def toIsaQual = "ToIsa-Internal"

  op mkArbitrary(ty: MSType): MSTerm =
    mkOp(Qualified(toIsaQual, "regular_val"), ty)

  op mkSubtypeFnPredicate(dom_ty: MSType, ran_ty: MSType, f_ty: MSType): Option MSTerm =
    if ~(embed? Subtype dom_ty || embed? Subtype ran_ty) then None
    else
    case (dom_ty, ran_ty) of
      | (Subtype(dom_ty, domPred, _), Subtype(ran_ty, ranPred, _)) ->
        Some(mkApply(mkOp(Qualified(toIsaQual, "Fun_P"),
                          mkArrow(mkProduct[mkArrow(dom_ty, boolType),
                                            mkArrow(ran_ty, boolType)],
                                  mkArrow(f_ty, boolType))),
                     mkTuple [domPred, ranPred]))
      | (Subtype(dom_ty, domPred, _), Boolean _) | regularizeBoolToFalse? -> 
        Some(mkApply(mkOp(Qualified(toIsaQual, "Fun_PDB"),
                          mkArrow(mkArrow(dom_ty, boolType),
                                  mkArrow(f_ty, boolType))),
                     domPred))
       %% Not used because of lazy regulization
%      | (Subtype(dom_ty, domPred, _), _) ->
%        Some(mkApply(mkOp(Qualified(toIsaQual, "Fun_PD"),
%                          mkArrow(mkArrow(dom_ty, boolType),
%                                  mkArrow(f_ty, boolType))),
%                     domPred))
      | (_, Subtype(ran_ty, ranPred, _)) ->
        Some(mkApply(mkOp(Qualified(toIsaQual, "Fun_PR"),
                          mkArrow(mkArrow(ran_ty, boolType),
                                  mkArrow(f_ty, boolType))),
                     ranPred))
      | _ -> None

  op changePatternType (pat: MSPattern, ty: MSType, spc: Spec): MSPattern =
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
  op changeDomainType (fn_tm: MSTerm, dom_ty: MSType, spc: Spec): MSTerm =
    % let _ = writeLine("cdt: "^printTermWithTypes fn_tm^"  c  "^printType dom_ty) in
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
    %let _ = writeLine("returned: "^ printTermWithTypes result) in
    result

  op tryUnfoldBase1 (spc: Spec) (ty: MSType): Option MSType =
    let exp_ty = unfoldBaseOne(spc, ty) in
    case exp_ty of
      | CoProduct _ -> None
      | Quotient _ -> None
      | Product _ | recordType? exp_ty -> None
      | Subtype(st, _, _) | none?(tryUnfoldBase1 spc st) -> None
      | _ ->
        if equalType?(exp_ty, ty) then None else Some exp_ty

  op tryUnfoldBase2 (spc: Spec) (ty: MSType): Option MSType =
    let exp_ty = unfoldBaseOne(spc, ty) in
    case exp_ty of
      | CoProduct _ -> None
      | Quotient _ -> None
      | Product _ | recordType? exp_ty -> None
      %| Subtype(st, _, _) | none?(tryUnfoldBase1 spc st) -> None
      | _ ->
        if equalType?(exp_ty, ty) then None else Some exp_ty

  op unfoldBase1 (spc: Spec) (ty: MSType): MSType =
    let exp_ty = unfoldBaseOne(spc, ty) in
    case exp_ty of
      | CoProduct _ -> ty
      | Quotient _ -> ty
      | Product _ | recordType? exp_ty -> ty
      | Subtype(st, _, _) | none?(tryUnfoldBase1 spc st) -> ty
      | _ ->
        if equalType?(exp_ty, ty) then ty else exp_ty

  op raiseSubtypeFn(ty: MSType, spc: Spec): MSType =
    %% Bring subtypes to the top-level
    %% Like raiseSubtype, but doesn't look inside Nat (because it should already have
    %% been expanded) The two functions should be merged
    %% Also assumes that the definitions of named types have been raised already
    % let _ = writeLine("rstf< "^printType ty) in
    let result =
        case ty of
          | Base(qid, args, a) | qid nin? dontRaiseTypes ->
            let args = map (fn tyi -> raiseSubtypeFn(tyi, spc)) args in
            if exists? (fn tyi -> embed? Subtype tyi) args
              then
              let Qualified(q,id) = qid in
              let pred_name = id^"_P" in
              let pred_qid = Qualified(q, pred_name) in
              (case AnnSpec.findTheOp(spc, pred_qid) of
                 | Some _ ->
                   let arg_comps = map (fn tyi ->
                                        case tyi of
                                          | Subtype(styi, pr, _) -> (styi, pr)
                                          | _ -> (tyi, mkLambda(mkWildPat tyi, trueTerm)))
                                     args
                   in
                   let (bare_args, arg_preds) = unzip arg_comps in
                   let bare_ty = Base(qid, bare_args, a) in
                   % let _ = writeLine("pred_qid: "^pred_name^"\nbarety: "^printType bare_ty) in
                   let arg_preds_lst = decomposeListConjPred arg_preds in
                   let preds = map (fn arg_preds ->
                                      mkAppl(mkOp(pred_qid, mkArrow(mkProduct(map (fn ty -> mkArrow(ty, boolType))
                                                                                bare_args),
                                                                    mkArrow(bare_ty, boolType))),
                                             arg_preds))
                                 arg_preds_lst
                   in
                   mkSubtypePreds(bare_ty, preds, a, spc)
                 | None ->   % Need to unfold to get predicate lifter function
               case tryUnfoldBase2 spc ty of
                 | Some exp_ty -> mergeRaisedBase(ty, raiseSubtypeFn(exp_ty, spc), spc)
                 | None -> raiseBase spc ty)
            else if args = [] || raisePolyTypes? then raiseBase spc ty
            else (case tryUnfoldBase2 spc ty of
                    | None -> raiseBase spc ty
                    | Some exp_ty -> raiseSubtypeFn(exp_ty, spc))
          | Subtype(s_ty, p, a) ->
            (case raiseSubtypeFn(s_ty, spc) of
               | Subtype(sss_ty, pr, _) ->
                 % let _ = writeLine("rsf ss: "^printType s_ty^"\n"^printType sss_ty^" | "^printTerm pr) in
                 composeSubtypes(sss_ty, p, pr, a, spc)
               | _ -> ty)
          | Product(flds, a) ->
            let flds = map (fn (id, ty) -> (id, raiseSubtypeFn(ty, spc))) flds in
            if exists? (fn (_,tyi) -> embed? Subtype tyi) flds
              then let (bare_flds, arg_id_vars, pred,_) =
                    foldl (fn ((bare_flds, arg_id_vars, pred, i),(id,tyi)) ->
                             case tyi of
                               | Subtype(t,p,_) -> let v = ("x_"^id, t)  in
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
                   Subtype(Product(bare_flds,a),
                           mkLambda(mkRecordPat arg_id_vars, pred), a)
              else ty
          | CoProduct(constrs0, a) ->
            %% Lifting a CoProduct is dangerous in that it makes the CoProduct not be at the top level, 
            %% but at the point it is done it may be benign.
            let constrs1 = map (fn (constr_qid, opt_ty) -> (constr_qid, mapOption (fn ty -> raiseSubtypeFn(ty, spc)) opt_ty)) constrs0 in
            if exists? (fn (_,opt_tyi) -> case opt_tyi of
                                            | Some(Subtype _) -> true
                                            | _ -> false)
                 constrs1
              then
                let (bare_constrs, cases) =
                    foldl (fn ((bare_constrs, cases), (constr_qid as Qualified(_, constr_id), opt_tyi)) ->
                             case opt_tyi of
                               | Some(Subtype(t,p,_)) ->
                                 (case p of
                                    | Lambda([(pat, _, bod)], _) ->
                                      (bare_constrs ++ [(constr_qid, Some t)],
                                       cases ++ [(EmbedPat(constr_qid, Some(pat), ty, a), trueTerm, bod)])
                                    | _ ->
                                      let v = ("y_"^constr_id, t)  in
                                      (bare_constrs ++ [(constr_qid, Some t)],
                                       cases ++ [(EmbedPat(constr_qid, Some(mkVarPat v), ty, a), trueTerm, simplifiedApply(p, mkVar v, spc))]))
                               | Some tyi -> (bare_constrs ++ [(constr_qid, opt_tyi)],
                                              cases ++ [(EmbedPat(constr_qid, Some(mkWildPat tyi), ty, a), trueTerm, trueTerm)])
                               | _ -> (bare_constrs ++ [(constr_qid, opt_tyi)],
                                       cases ++ [(EmbedPat(constr_qid, None, ty, a), trueTerm, trueTerm)]))
                      ([],[]) constrs1
                   in
                   let lifted_ty = Subtype(CoProduct(bare_constrs, a),
                                           Lambda(cases, a), a)
                   in
                   % let _ = writeLine("Raising coproduct:\n"^printType ty^"\n  -->\n"^printType lifted_ty) in
                   lifted_ty
              else ty
          | Arrow(dom, rng ,a) ->
            (case mkSubtypeFnPredicate(raiseSubtypeFn(dom,spc), raiseSubtypeFn(rng,spc), ty) of
               | Some pred -> Subtype(ty, pred, a)
               | None -> ty)
          | _ -> ty
     in
     % let _ = writeLine("rstf> "^printType result) in
     result
 
  op encapsulateSubtypePred?(pred: MSTerm, sup_ty: MSType): Bool =
    termSize pred < Prover.unfoldSizeThreshold && ~(embed? CoProduct sup_ty)
 
  op raisePolyTypes?: Bool = false

  op raiseNamedTypes(spc: Spec): Spec =
    let def raiseTypeDefs(elts: SpecElements, spc: Spec, sbst: TermSubst)
              : SpecElements * Spec * TermSubst =
          foldl (fn ((elts, spc, sbst), el) ->
                 case el of
                 | Import(s_tm, i_sp, s_elts, a) ->
                   let (s_elts, spc, sbst) = raiseTypeDefs(s_elts, spc, sbst) in
                   (Import(s_tm, i_sp, reverse s_elts, a)::elts, spc, sbst)
                 | TypeDef(qid, a) ->
                   (case AnnSpec.findTheType(spc, qid) of
                    | Some  {names, dfn} ->
                      let (tvs, ty) = unpackType dfn in
                      % let _ = writeLine(printQualifiedId qid) in
                      let raised_ty? = if tvs ~= [] && ~raisePolyTypes?
                                         then ty 
                                       else raiseSubtypeFn(ty, spc)
                      in
                      (case raised_ty? of
                       | r_ty as Subtype(sup_ty, pred, a1) ->
                         % let _ = writeLine("rnt: "^printQualifiedId qid^"\n"^
                         %                   printType ty^"\n-->\n"
                         %                     ^printType sup_ty^" | "^printTerm pred) in
                         let Qualified(q, ty_name) = qid in
                         let pred = termSubst(pred, sbst) in
                         if encapsulateSubtypePred?(pred, sup_ty)
                           then let sup_ty = if equalType?(ty, r_ty) || embed? Base sup_ty
                                               then sup_ty
                                             else case ty of
                                                    | Subtype(s_ty, _, _) -> s_ty
                                                    | _ -> ty
                                in
                                let typeinfo = {names = names,
                                                dfn = maybePiType(tvs, Subtype(sup_ty, pred, a1))}
                                in
                                let spc = spc << {types = insertAQualifierMap(spc.types,q,ty_name,typeinfo)} in
                                (el::elts, spc, sbst)
                         else
                         let base_ty = mkBase(qid, map mkTyVar tvs) in
                         let pred_nm = ty_name^"__subtype_pred" in
                         let pred_id = Qualified(q, pred_nm) in
                         let pred_ty = mkArrow(sup_ty, boolType) in
                         let pred_tm = mkOp(pred_id, pred_ty) in
                         let pred_el = Op(pred_id, true, a) in
                         let pred =
                             case pred of
                             | Lambda([(RecordPat((id1,_)::_, _), _,_)], _) | false ->
                               let param = ("rec1", base_ty) in
                               mkLambda(mkVarPat param, mkApply(pred, mkVar param))
                             | _ -> pred
                         in
                         let opinfo = {names = [pred_id],
                                       fixity = Nonfix,
                                       dfn = maybePiTerm(tvs,
                                                         TypedTerm(pred, pred_ty, a1)),
                                       fullyQualified? = false}
                         in
                         let typeinfo = {names = names,
                                         dfn = maybePiType(tvs, Subtype(sup_ty, pred_tm, a1))}
                         in
                         let spc = spc << {ops   = insertAQualifierMap(spc.ops,  q,pred_nm,opinfo),
                                           types = insertAQualifierMap(spc.types,q,ty_name,typeinfo)}
                         in
                         %% This is in reverse order of what is legal for Specware but works in Isabelle
                         %% as the type does not refer to the predicate
                         (pred_el::el::elts, spc, (pred, pred_tm)::sbst)
                       | _ -> (el::elts, spc, sbst))
                    | None -> (el::elts, spc, sbst))
                 | _ -> (el::elts, spc, sbst))
            ([], spc, sbst) elts
    in
    let (r_elts, spc, _) = raiseTypeDefs(spc.elements, spc, []) in
    let spc = spc << {elements = reverse r_elts} in
    % let _ = writeLine("raiseNamedTypes:\n"^printSpec spc) in
    spc

  op bindingEquality?(v: MSVar, tm: MSTerm): Option(MSTerm * MSTerm) =
    let def bindable?(e1: MSTerm): Bool =
          case e1 of
            | Var(vi, _) -> equalVar?(vi, v) 
            | Record(prs, _) -> exists? (fn (_, s_tm) -> bindable? s_tm) prs
            | _ -> false
    in
    case tm of
      | Apply(Fun(Equals, _, _), Record([(_, e1), (_, e2)],  _), _) ->
        if bindable? e1 then Some(e1, e2)
        else if bindable? e2 then Some(e2, e1)
        else None
      | _ -> None
 
  %% possiblySubtypeOf? isn't sufficient because type definitions have been normalized
  op possiblySubtypeOfPostNorm?(ty1: MSType, ty2: MSType, spc: Spec): Bool =
    possiblySubtypeOf?(ty1, ty2, spc)
      || (let env = initialEnv (spc, "internal") in
          case (expandType(env, ty1), expandType(env, ty2)) of
            | (Subtype(s_ty1, p1, _), Subtype(s_ty2, p2, _)) ->
              equalTermAlpha?(p1, p2)
            | _ -> false)

  op hasDefiningConjunctImplyingSubtype(v as (vn,v_ty): MSVar, binding_cjs: MSTerms, ignore_projections?: Bool, spc: Spec): Bool =
   exists? (fn cj ->
               case bindingEquality? (v, cj) 
                   %% The projection exception is necessary because we don't have theorems about the values of record fields
                 | Some(e1, e2) | ~(embed? Var e2) && (ignore_projections? => ~(projection?(e2, spc))) ->
                   let e2_ty = inferType(spc, e2) in
                   let def implied_by_assigned_val(e1, e2_ty) =
                         % let _ = writeLine(printTerm e1^" implied by(?) "^printType e2_ty) in
                         case e1 of
                           | Var((v_id, _), _) ->
                             vn = v_id && possiblySubtypeOfPostNorm?(e2_ty, v_ty, spc)
                           | Record(prs, _) ->
                             let given_tys = recordTypes(spc, e2_ty) in
                             length prs = length given_tys
                             && exists? (fn ((_, s_tm), s_e2_ty) -> implied_by_assigned_val(s_tm, s_e2_ty))
                             (zip(prs, given_tys))
                     | _ -> false
                   in
                   implied_by_assigned_val(e1, e2_ty)
                 | _ -> false)
      binding_cjs

  op getNonImpliedTypePredicates(bndVars: MSVars, binding_cjs: MSTerms, ignore_projections?: Bool, spc: Spec): MSTerms =
    %% For bndVars with subtypes return the subtype predicate applied to the var except when
    %% when the subtype is implied by a binding conjunct.
    %% Could add more cases the implication
    mapPartial (fn v as (_,v_ty) ->
                  case maybeTypePredTerm(v_ty, mkVar v, spc) of
                    | None -> None
                    | Some pred_tm ->
                      % let _ = writeLine("Considering "^printTerm pred_tm) in
                      if hasDefiningConjunctImplyingSubtype(v, binding_cjs, ignore_projections?, spc)
                        || (case binding_cjs of
                              | [cj1 as Apply(Fun(Or,_,_), _, _)]->
                                forall? (fn disj ->
                                           (~(hasRefTo?(disj, [v])) && knownNonEmptyType?(v_ty, spc))
                                           || hasDefiningConjunctImplyingSubtype(v, conjunctTerms(disj, Exists),
                                                                                 ignore_projections?, spc))
                                (getDisjuncts cj1)
                              | _ -> false)
                     then
                       % let _ = writeLine("relativized predicate not needed:\n"^printTerm pred_tm) in
                       None
                     else
                       % let _ = writeLine("relativized predicate needed!:\n"^printTerm pred_tm) in
                       Some pred_tm)
      bndVars
    
  op conjunctTerms(tm: MSTerm, kind: Binder): MSTerms =
    case tm of
      | Apply(Fun(And,_,_), Record([("1",lhs),("2",rhs)],_),_) ->
        conjunctTerms(lhs, kind) ++ conjunctTerms(rhs, kind)
      | Let(_, bod, _) -> conjunctTerms(bod, kind)
      | Bind(kind1,_,bod,_) | kind1 = kind -> conjunctTerms(bod, kind)
      | _ -> [tm]

  op lhsTerms(tm: MSTerm): MSTerms =
    let cjs = (forallComponents tm).2 in
    flatten (map (fn cj -> conjunctTerms(cj, Exists)) cjs)

  op getBindingConjuncts(tm: MSTerm): MSTerms =
     case tm of
       | Bind(Forall, _, bod, _) -> lhsTerms bod
       | Bind(Exists, _, bod, _) -> conjunctTerms(bod, Exists)
       | Bind(Exists1, _, bod, _) -> conjunctTerms(bod, Exists1)
       | _ -> []

  % This function pushes subtype constraints on quantified variables
  % for formulae into the body of the formula, removing the subtype
  % constraint on the variable's type.
  op relativizeQuantifiersSimpOption(simplify?:Bool)(spc: Spec) (t: MSTerm): MSTerm =
    case t of
      | Bind(bndr,bndVars,bod,a) ->
        let binding_cjs = getBindingConjuncts t in
        let preds = getNonImpliedTypePredicates(bndVars, binding_cjs, bndr = Forall, spc) in
        let preds = map (mapTerm (relativizeQuantifiersSimpOption simplify? spc,id,id)) preds in
        (if empty? preds
          then t
          else
            let bndVarsPred = List.foldr1 MS.mkAnd preds in
            let new_bod = case bndr of
                    | Forall ->
                        if simplify?
                          then Utilities.mkSimpImplies(bndVarsPred, bod)
                        else MS.mkImplies(bndVarsPred,bod)
                    | Exists -> 
                        if simplify?
                          then Utilities.mkAnd(bndVarsPred, bod)
                        else MS.mkAnd(bndVarsPred,bod)
                      
                    | Exists1 -> 
                        if simplify?
                          then Utilities.mkAnd(bndVarsPred, bod)
                        else MS.mkAnd(bndVarsPred,bod)
                      
            in
            % let _ = if equalTerm?(bod, new_bod) then () else writeLine("relquant:\n"^printTerm new_bod) in
            Bind(bndr,bndVars,new_bod,a))
      | The(theVar as (vn,ty),bod,a) ->
        let theVarPred = typePredTerm(ty, mkVar(vn,ty), spc) in
        let new_bod = Utilities.mkAnd(theVarPred, bod) in
        The((vn,ty),new_bod,a)
      | _ -> t

  op relativizeQuantifiers(spc: Spec) (t: MSTerm): MSTerm =
       relativizeQuantifiersSimpOption true spc t

        
  op refToHo_eqfns(f: MSFun, qids: List QualifiedId): Bool =
    case f of
      | Op(qid,_) -> qid in? qids
      | _ -> false

  op hoTypesIn(spc: Spec) (ty: MSType): MSTypes =
    case unfoldBeforeCoProduct(spc, ty) of
      | Arrow _ -> [ty]
      | TyVar _ -> [ty]
      | Product(flds,_) -> foldl (fn (result,(_,tyi)) -> hoTypesIn spc tyi ++ result) [] flds
      | Subtype(s_ty,_,_) -> hoTypesIn spc s_ty
      | _ -> []

  op hoFunTypes(spc: Spec) (f_ty: MSType): MSTypes =
    case arrowOpt(spc, f_ty) of
      | Some(dom, rng) ->
        hoTypesIn spc dom ++ hoFunTypes spc rng
      | None -> []

  op hasArgTypeIn?(spc: Spec) (tys: MSTypes) (a_ty: MSType): Bool =
    case unfoldBeforeCoProduct(spc, a_ty) of
      | Product(flds,_)   -> exists? (fn (_,tyi) -> hasArgTypeIn? spc tys tyi) flds
      | Subtype(s_ty,_,_) -> hasArgTypeIn? spc tys s_ty
      | _ -> a_ty in? tys

  op hasFunTypeIn?(spc: Spec) (tys: MSTypes) (f_ty: MSType): Bool =
    case arrowOpt(spc, f_ty) of
      | Some(dom, rng) ->
        hasArgTypeIn? spc tys dom
         || hasFunTypeIn? spc tys rng
      | None -> false

  op initialHOEqualityFuns: List QualifiedId = []

  op findHOEqualityFuns(spc: Spec): List QualifiedId =
    let def iterate1(qids,initial?) =
          foldOpInfos
            (fn (info, qids) ->
               if primaryOpName info in? qids then qids
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
                                             % | Any _ -> true
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
    iterateUntilNoChange(iterate1(initialHOEqualityFuns, true))

  op hoFun2s: List String = ["Fun_P", "Fun_PD", "Fun_PR"]

  op possibleEqTestableFun?(f: MSFun, ho_eqfns: QualifiedIds): Bool =
    case f of
      | Equals -> true
      | NotEquals -> true
      | _ -> refToHo_eqfns(f, ho_eqfns)

  op possibleEqTestableFunTerm?(ho_eqfns: List QualifiedId, spc: Spec) (tm: MSTerm): Bool =
    let result =
    case tm of
      | Fun(f, Product([("1", ty), ("2", _)], _), _) | f = Equals || f = NotEquals ->
        some?(arrowOpt(spc, ty))
      | Fun(f, _, _) -> refToHo_eqfns(f, ho_eqfns)
      | Apply(Fun(Embed _, _, _), t, _) -> freeVars t ~= []
      | _ -> false
    in
    % let _ = if result then writeLine(printTerm tm) else () in
    result

  op possibleEqTestableFunTermIn?(ho_eqfns: List QualifiedId, spc: Spec) (tm: MSTerm): Bool =
    let result =
    existsSubTerm (possibleEqTestableFunTerm? (ho_eqfns, spc)) tm
    in
    % let _ = if result then writeLine(printTerm tm) else () in
    result

  op possibleHoEqualTestableArg?(f: MSTerm, ho_eqfns: List QualifiedId, spc: Spec): Bool =
    case f of
      | Fun(f, _, _) ->
        possibleEqTestableFun?(f, ho_eqfns) || embed? Embed f
      | Apply(f, _, _) ->
        possibleHoEqualTestableArg?(f, ho_eqfns, spc)
          || (case f of
              | Fun(Op(Qualified(q, nm),_),_,_) -> q = toIsaQual && nm in? hoFun2s
              | _ -> false)
      | Lambda _ -> possibleEqTestableFunTermIn? (ho_eqfns, spc) f
      | _ -> false

  op simpleTermIn?(term: MSTerm, vs: MSVars): Bool = 
    case term of 
      | Record(fields,_) ->
        forall? (fn (_,t) -> simpleTermIn?(t, vs)) fields
      | Var(v, _) -> inVars?(v, vs)
      | Fun _ -> true
      | _ -> false

  %% This could be more sophisticated as there are cases it doesn't catch.
  %% Note that its imprecision doesn't effect correctness as it only used to determine whether
  %% to add the subtype predicate into the definition.
  %% A false negative means an unnecessarily complex defn which might need extra user
  %% annotation to prove termination.
  %% A false negative means is only a problem if the missing subtype predicate is necessary
  %% to prove termination
  op simpleRecursion?(dfn: MSTerm, qid: QualifiedId): Bool =
    let def checkBody?(tm, params) =
          case tm of
            | Apply(Lambda(binds, _), arg, _) | simpleTermIn?(arg, params) ->
              forall?(fn (pat, _, bod) -> checkBody?(bod, patVars pat ++ params)) binds
            %% Could add a case for simple lets
            | _ ->
              ~(existsSubTerm
                 (fn stm ->
                  case stm of
                    | Apply(Fun(Op(qidi, _), _, _), arg, _) | qid = qidi ->
                      ~(simpleTermIn?(arg, params))
                    | Apply _ ->        % Curried version
                      (case getCurryArgs stm of
                         | Some(Fun(Op(qidi, _), _, _), args) | qid = qidi ->
                           exists? (fn arg -> ~(simpleTermIn?(arg, params))) args
                         | _ -> false)
                    | _ -> false)
                  tm)
        def checkLambdas(tm, params) =
          case tm of
            | Lambda(binds, _) ->
              forall? (fn (pat, _, bod) -> checkLambdas(bod, patVars pat ++ params)) binds
            | _ -> checkBody?(tm, params)
    in
    checkLambdas(dfn, [])

  op regTermTop (opinfo: OpInfo, ho_eqfns: List QualifiedId, refine_num: Nat, spc: Spec): MSTerm =
    let trps = unpackTypedTerms (opinfo.dfn) in
    let (tvs, ty, tm) = nthRefinement(trps, refine_num) in
    let def reg1 tm =
         let qid = %refinedQID refine_num
         (primaryOpName opinfo) in
         let recursive? = containsRefToOp?(tm, qid) in
         let result = regTerm(tm, ty, ~(arrow?(spc,ty)), ho_eqfns, spc) in
         let result = if recursive? && ~(simpleRecursion?(tm, qid))
                       then   % May need condition to prove termination
                         regularizeIfPFun(result, ty, inferType(spc,result), spc)
                       else result
         in
         result
    in
    let result = reg1 tm in
    if equalTerm?(result, tm)
      then opinfo.dfn 
    else
    % let _ = writeLine("Def:\n"^printTerm tm^"\n  changed to\n"^printTerm result) in
    maybePiAndTypedTerm(replaceNthRefinement(trps, refine_num, (tvs, ty, result)))

  op setType?(spc: Spec, ty: MSType): Bool =
    case ty of
     | Base(Qualified("Set", "Set"), _, _) -> true
     | Base(Qualified("ISet", "ISet"), _, _) -> true
     | Base _ ->
       (case tryUnfoldBase spc ty of
          | Some uf_ty -> setType?(spc, uf_ty)
          | None -> false)
     | Subtype(st, _, _) -> setType?(spc, st)
     | _ -> false


  op regularizeIfPFun(tm: MSTerm, ty: MSType, rm_ty: MSType, spc: Spec): MSTerm =
    % ty is expected type, rm_ty is provided types
    % let _ = writeLine("Regularize0: "^printTerm tm^": \n"^printType ty^" to \n"^printType rm_ty) in
    case (arrowOpt(spc,ty), arrowOpt(spc,rm_ty)) of
      | (Some(dom, rng), Some(rm_dom, rm_rng)) ->
        if embed? Var tm && equalType?(dom, rm_dom) then tm
        else
        let rfun = if setType?(spc, ty) && regularizeSets?
                    then  "RSet"
                   else if boolType?(spc, rng)
                     then if regularizeBoolToFalse?
                            then "RFunB"
                          else "RFun"
                   else "RFun"
        in
        let def mkRFun(pred, tm) =
              let pred = simplify spc pred in
              %% We are only coercing domain so pass expectation for range down
              let exp_ty = if equalType?(rng, rm_rng) then rm_ty else mkArrow(rm_dom, rng) in
              let reg_tm =
                  case (pred, tm) of
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
                                   tm))
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
                                   tm))
                    | (_, Apply(Apply(Fun(Op(Qualified(toIsaQual, rfun),_),_,_), prd, _),_,_)) | equalTermAlpha?(prd, pred)->
                      %% Don't regularize twice!
                      tm
                    | _ ->
                      mkApply(mkApply(mkOp(Qualified(toIsaQual, rfun),
                                           mkArrow(inferType(spc, pred),
                                                   mkArrow(exp_ty, ty))),
                                      pred),
                              tm)
              in
              % let _ = writeLine("Regularize1: "^printTerm tm^" to\n"^printTerm reg_tm) in
              reg_tm
        in
        (case subtypeComps(spc, raiseSubtypeFn(dom, spc)) of
           | None ->
             (case subtypeComps(spc, raiseSubtypeFn(rm_dom, spc)) of
                | Some(sup_ty, pred) | eagerRegularization? ->
                  mkRFun(pred, tm)
                | _ -> tm)
           | Some(sup_ty, pred) -> mkRFun(pred, tm))
      | _ -> tm

  op regTerm (t, ctxt_ty, equal_testable?, ho_eqfns: List QualifiedId, spc: Spec): MSTerm =
    let rm_ty = inferType(spc,t) in
    % let _ = writeLine("reg: "^show equal_testable?^"\n"^printTerm t
    %                     ^"\n: "^printType ctxt_ty) in
    let t = if equal_testable? && ~eagerRegularization? && ~(embed? And t)
              then regularizeIfPFun(t, ctxt_ty, rm_ty, spc)
            else t
    in
    case t of
      | Apply(f, x, a) ->
        let (dom, rng) = arrow(spc, inferType(spc, f)) in
        Apply(regTerm(f, mkArrow(inferType(spc, x), ctxt_ty), false, ho_eqfns, spc),
              regTerm(x, dom, possibleHoEqualTestableArg?(f, ho_eqfns, spc), ho_eqfns, spc), a)
      | Record(row, a) ->
        % let _ = writeLine("regTerm "^printTerm t^":\n"^printType ctxt_ty) in
        let srts = map (fn (_,x) -> x) (product (spc,ctxt_ty)) in
        Record(map (fn ((idi,tmi), tyi) -> (idi, regTerm(tmi, tyi, equal_testable?, ho_eqfns, spc)))
                 (zip(row,srts)), a) 
      | Bind(b, vs, bod, a) ->
        Bind(b, vs, regTerm(bod, boolType, false, ho_eqfns, spc), a)
      | The(v, bod, a) ->
        The(v, regTerm(bod, boolType, false, ho_eqfns, spc), a)
      | Let(decls, bod, a) ->
        Let (map (fn (pat,trm) -> (pat, regTerm(trm, patternType pat,
                                                possibleEqTestableFunTermIn? (ho_eqfns, spc) bod,
                                                ho_eqfns, spc)))
               decls,
             regTerm(bod, ctxt_ty, equal_testable?, ho_eqfns, spc), a)
      | LetRec(decls, bod, a) ->
        LetRec (map (fn ((id,srt), trm) -> ((id,srt), regTerm(trm, srt, false, ho_eqfns, spc))) decls,
                regTerm(bod, ctxt_ty, equal_testable?, ho_eqfns, spc), a)
      | Lambda(match, a) ->
        let lam_tm = 
            Lambda (map (fn (pat,condn,trm) ->
                           let reg_trm = case arrowOpt(spc, ctxt_ty) of
                                           | Some(_, rng) -> regTerm(trm, rng, false, ho_eqfns, spc)
                                           | None ->
                                          %% This happens because addCoercions only works on local ops!
                                         (%% warn("Can't find range of context for "^printTerm t^"\nUsing range of lambda...");
                                          case arrowOpt(spc, rm_ty) of
                                           | Some(_, rng) -> regTerm(trm, rng, false, ho_eqfns, spc)
                                           | None ->
                                          (warn("Can't find range of "^printTerm t^"\nUsing body");
                                           regTerm(trm, inferType(spc, trm), false, ho_eqfns, spc)))
                           in
                           (pat, regTerm(condn, boolType, false, ho_eqfns, spc), reg_trm)) % ?
                      match,
                    a)
        in
        if eagerRegularization?
          then regularizeIfPFun(lam_tm, ctxt_ty, rm_ty, spc)
          else lam_tm
      | IfThenElse(x,y,z, a) ->
        IfThenElse(regTerm(x, boolType, false, ho_eqfns, spc),
                   regTerm(y, ctxt_ty, equal_testable?, ho_eqfns, spc),
                   regTerm(z, ctxt_ty, equal_testable?, ho_eqfns, spc), a)
      %| Seq(tms, a) ->
      | TypedTerm(tm, tm_ty, a) ->
        TypedTerm(regTerm(tm, tm_ty, equal_testable?, ho_eqfns, spc), tm_ty, a)
      | And(tms, a) ->
        And(map (fn tm -> regTerm(tm, ctxt_ty, equal_testable?, ho_eqfns, spc)) tms, a)
      | _ -> t
         
  op regularizeFunctions(spc: Spec): Spec =
    let ho_eqfns = findHOEqualityFuns spc in
    % let _ = writeLine(anyToString ho_eqfns) in
    % let _ = writeLine(printSpec spc) in
    let spc =
        spc << {ops = foldl (fn (ops,el) ->
                             case el of
                               | Op (qid as Qualified(q,id), true, _) ->
                                 %% true means decl includes def
                                 (case AnnSpec.findTheOp(spc,qid) of
                                   | Some info ->
                                     insertAQualifierMap (ops, q, id,
                                                          info << {dfn = regTermTop(info, ho_eqfns, 0, spc)})
                                   | None -> ops)
                               | OpDef (qid as Qualified(q,id), refine_num, _, _) ->
                                 (case AnnSpec.findTheOp(spc,qid) of
                                   | Some info ->
                                     insertAQualifierMap (ops, q, id,
                                                          info << {dfn = regTermTop(info, ho_eqfns, refine_num, spc)})
                                   | None -> ops)
                               | _ -> ops)
                        spc.ops
                        spc.elements,
                %% mapOpInfos (fn info -> info << {dfn = mapTermTop info}) spc.ops,
                elements = map (fn el ->
                                  case el of
                                    | Property(pt, nm, tvs, term,a) ->
                                      Property(pt, nm, tvs, regTerm(term, boolType, false, ho_eqfns, spc),a)
                                    | _ -> el)
                             spc.elements}
    in
    % let _ = writeLine(printSpec spc) in
    spc

  op typePred(spc: Spec, ty: MSType, tm: MSTerm): MSTerm =
    % let _ = writeLine("tp: "^printTerm tm^": "^printType ty) in
    case raiseSubtypeFn(ty, spc) of
      | Subtype(_, pred, _) ->
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
      | _ -> "d__"^show i

  op tryUnpackLambda (tm: Option MSTerm): Option (MSPattern * MSTerm) =
    case tm of
      | Some(Lambda([(pat, Fun(Bool true,_,_), bod)], _)) | varRecordPattern? pat -> Some(pat, bod)
      | _ -> None

  op stripRFun(tm: MSTerm): MSTerm =
    case tm of
      | Apply(Apply(Fun(Op(Qualified(_, "RFun"),_),_,_), _, _), r_tm, _) -> r_tm
      | _ -> tm

  op termSubtypeCondn(spc: Spec, term: MSTerm, ty: MSType, defn?: Option MSTerm, depth: Nat): MSTerm =
    % let _ = writeLine("\ntsc: "^printTerm term^": "^printType ty^"\n"^(case defn? of Some defn -> printTerm defn | _ -> "")) in
    case unfoldBase(spc, ty) of
      | Arrow(dom, rng, _) ->
	(let dom_exp = case tryUnfoldBase spc dom of
                         | Some d -> d
                         | None -> dom
         in
         case dom_exp of
          | Subtype(_, Lambda([(pat, Fun(Bool true,_,_), sub_ty_bod)], _), _) | varRecordPattern? pat ->
            let Some arg_tm = patternToTerm pat in
            let vs = patternVars pat in
            let rangeTerm = mkApply(stripRFun term, arg_tm) in
            let rangePred = termSubtypeCondn(spc, rangeTerm, rng, None, depth + 1) in
            mkBind(Forall, vs, mkSimpImplies(sub_ty_bod, rangePred))
          | _ ->
         case tryUnpackLambda(defn?) of
          | Some(pat, bod) ->
            %% Gives dependent-type capability
            let Some arg_tm = patternToTerm pat in
            let vs = patternVars pat in
            let rangeTerm = mkApply(stripRFun term, arg_tm) in
            let rangePred = termSubtypeCondn(spc, rangeTerm, rng, Some bod, depth + 1) in
            mkBind(Forall, vs, rangePred)
          | _ ->
         case productOpt (spc, dom_exp) of
	  | Some fields ->
            let name = argName depth in
	    let domIdVars = map (fn (id: Id, ty) -> (id, (name ^ "_" ^ id, ty))) fields in
            let domVars = List.map (fn (_, v) -> v) domIdVars in
	    let domVarTerms = map (fn (id, var) -> (id, mkVar(var))) domIdVars in
	    let rangeTerm = mkApply(term, mkRecord domVarTerms) in
	    let rangePred = termSubtypeCondn(spc, rangeTerm, rng, None, depth + 1) in
	    mkBind(Forall, domVars, rangePred)
	  | _ ->
            let name = argName depth in
	    let domVar = (name, dom) in
	    let domVarTerm = mkVar(domVar) in
	    let rangeTerm = mkApply(stripRFun term, domVarTerm) in
	    let rangePred = termSubtypeCondn(spc, rangeTerm, rng, None, depth + 1) in
	    mkBind(Forall, [domVar], rangePred))
       | _ -> typePred(spc, ty, term)

  op dontLiftSubtypeTheorem?: Bool = false     % Not sure if this is necessary

  op opSubtypeTheorem(spc: Spec, opname as (Qualified(q,id)): QualifiedId, fx: Fixity,
                      tvs: TyVars, ty: MSType, defn: MSTerm, ho_eqfns: List QualifiedId,
                      coercions: TypeCoercionTable, stp_tbl: PolyOpTable,
                      freeThms?: Bool): MSTerm =
    let fn_tm = mkInfixOp(opname, fx, ty) in
    % let fn_tm = regularizeIfPFun(fn_tm, ty, inferType(spc, defn), spc) in 
    let base_thm = termSubtypeCondn(spc, fn_tm, ty, Some defn, 0) in
    if dontLiftSubtypeTheorem? || stpFun? id || tvs = [] || hasStpFun?(spc, opname)
      then base_thm
      else
      let result_ty = range_*(spc, ty, false) in
      let range_tvs = freeTyVars result_ty in
      if range_tvs = [] then base_thm
      else if freeThms?
      then
        let tv_pred_map = map (fn tv -> (tv, mkVar("P__"^tv, mkArrow(mkTyVar tv, boolType)))) range_tvs in
        let tv_ty_map = map (fn (tv, pred) -> (tv, mkSubtype(mkTyVar tv, pred))) tv_pred_map in
        let ty_with_preds = instantiateTyVarsInType(ty, tv_ty_map) in
        let defn_with_preds = substTyVarsWithSubtypes(tv_pred_map, defn) in
        % let _ = writeLine("defn_with_preds:\n"^printTerm defn_with_preds) in
        let fn_tm = mkInfixOp(opname, fx, ty_with_preds) in
        let fn_tm = regularizeIfPFun(fn_tm, ty_with_preds, inferType(spc, defn_with_preds), spc) in 
        let pred_thm = termSubtypeCondn(spc, fn_tm, ty_with_preds, Some defn_with_preds, 0) in
        % let _ = writeLine("constr thm:\n"^printTerm pred_thm) in
        let pred_thm = mapTerm (polyCallsTransformers(spc, stp_tbl, true, coercions)) pred_thm in
        mkConj[base_thm, pred_thm]
      else
        (case tryRelativizeTerm(tvs, base_thm, stp_tbl, boolType, ho_eqfns, spc, coercions) of
           | ([],_) -> base_thm
           | (tv_map, pred_tm) ->
         % let pred_tm = substTyVarsWithSubtypes(tv_map, pred_tm) in
         % let _ = writeLine("ost: "^id^"\n"^printTerm pred_tm) in
         let pred_tm = mapTerm (polyCallsTransformers(spc, stp_tbl, true, coercions)) pred_tm in
         % let _ = writeLine("tr:\n"^printTerm pred_tm) in
         let pred_thm = mkBind(Forall, map (fn (_,Var(v,_)) -> v) tv_map, pred_tm) in
         mkConj[base_thm, pred_thm]) 

  op separateRhsConjuncts (spc: Spec) (tm: MSTerm): MSTerms =
    case tm of
      | Bind(Forall, vs, bod, a) ->
        map (fn b -> Bind(Forall, vs, b, a)) (separateRhsConjuncts spc bod)
      | Apply(Fun (Implies, _, _), Record([(_, lhs), (_, rhs)], _), _) ->
        map (fn b -> mkImplies(lhs, b)) (separateRhsConjuncts spc rhs)
      | Let(decls, bod, a) ->
        map (fn b -> Let(decls, b, a)) (separateRhsConjuncts spc bod)
      | Apply(Lambda([(pat, Fun(Bool true, _, _) ,bod)], _), e, a) | varRecordPattern? pat ->
        map (fn b -> Let([(pat, e)], b, a)) (separateRhsConjuncts spc bod)
      | Apply(Fun(And,_,_), _, _) -> flatten(map (separateRhsConjuncts spc) (getConjuncts tm))
      | Apply(Apply(Fun(Op(Qualified(_, "Fun_PD"),_),_,_), p1, _),
              f, _) ->
        % let _ = writeLine("src: "^printTerm p1) in
        (case arrowOpt(spc, inferType(spc, f)) of
           | Some(rm_dom, _) ->
             (case subtypeComps(spc, raiseSubtypeFn(rm_dom, spc)) of
               | Some(_, pred) | equivTerm? spc (p1, pred) -> []
               | _ -> [tm])
           | None -> [tm])
      | _ -> [tm]


  % Bool option determines whether the formulae created in subtype
  % removal will be simplified.
  op  removeSubTypes: Bool -> Spec -> TypeCoercionTable -> PolyOpTable -> Spec
  def removeSubTypes simplify? spc coercions stp_tbl =
    %% Remove subtype definition for directly-implemented subtypes after saving defs
    let ho_eqfns = findHOEqualityFuns spc in
    %% Add subtype assertions from op declarations
    let def makeSubtypeConstrThms(elts, new_elts, subtypeConstrThms?, freeThms?) =
              case elts of
               | [] -> reverse new_elts
               | (el as Pragma("proof", prag_str, "end-proof", _)) :: r_elts ->
                 (case controlPragmaString prag_str of
                  | Some strs ->
                    let subtypeConstrThms? =
                        if makeSubtypeConstrTheoremsString in? strs
                          then true
                        else if noMakeSubtypeConstrTheoremsString in? strs
                          then false
                          else subtypeConstrThms?
                    in
                    let freeThms? =
                        if makeFreeTheoremsString in? strs
                          then true
                        else if noMakeFreeTheoremsString in? strs
                          then false
                          else freeThms?
                    in
                    makeSubtypeConstrThms(r_elts, el :: new_elts, subtypeConstrThms?, freeThms?)
                  | None -> makeSubtypeConstrThms(r_elts, el :: new_elts, subtypeConstrThms?, freeThms?))
               | (el as Op(qid as (Qualified(q,id)), def?, a)) :: r_elts
                   | (subtypeConstrThms? || ~def?) && ~(stpFun? id) ->
                 (case AnnSpec.findTheOp(spc,qid) of
                   | None -> (writeLine("Missing op def: "^show qid^"\n"^anyToString el); [])
                   | Some info ->
                 let (tvs, ty, defn) = unpackFirstOpDef info in
                 % let _ = writeLine ("\nstc: "^id^": "^printType ty) in
                 % let _ = writeLine(printType(raiseSubtypeFn(ty, spc))^"\n") in
                 let subTypeFmla = opSubtypeTheorem(spc, qid, info.fixity, tvs, ty,
                                                    defn, ho_eqfns, coercions,
                                                    stp_tbl, freeThms?)
                 in
                 % let _ = writeLine ("\n"^printTerm subTypeFmla) in
                 % ?? let liftedFmlas = removePatternTop(spc, subTypeFmla) in
                 (case simplify spc subTypeFmla of
                  | Fun(Bool true,_,_) -> makeSubtypeConstrThms(r_elts, el :: new_elts, subtypeConstrThms?, freeThms?)
                  | s_fm ->
                    % let _ = writeLine (" --> "^printTerm s_fm) in
                    let fms = separateRhsConjuncts spc s_fm in
                    let thms = map (fn (i, fm) ->
                                    let fm = if removeExcessAssumptions? then removeExcessAssumptions fm else fm in
                                    Property(if def? then Theorem else Axiom, 
                                             mkQualifiedId
                                               (q, id^"_subtype_constr"
                                                  ^(if i = 0 then "" else show i)), 
                                             [], fm, a))
                                 (tabulate (length fms, fn i -> (i, fms@i)))
                    in
                    let thms = reverse thms in  % Will be reversed again at the end
                    case r_elts of
                      | (p as Pragma _) :: rr_elts ->
                        makeSubtypeConstrThms(rr_elts, thms ++ [p, el] ++ new_elts, subtypeConstrThms?, freeThms?)
                      | _ -> makeSubtypeConstrThms(r_elts, thms ++ (el :: new_elts), subtypeConstrThms?, freeThms?)))
                 | el :: r_elts -> makeSubtypeConstrThms(r_elts, el :: new_elts, subtypeConstrThms?, freeThms?)
    in
    let spc = spc << {elements = makeSubtypeConstrThms(spc.elements, [], false, false)} in
    %% Regularize functions that may be used in equality tests
    let spc = regularizeFunctions spc in
    %let _ = writeLine(anyToString tbl) in
    % let _ = writeLine(printSpec spc) in
    let spc = mapSpec (relativizeQuantifiersSimpOption simplify? spc, id, id) spc in
    %% Replace subtypes by supertypes
    let spc = mapSpec (id,fn s ->
                         case s of
                           | Subtype(supTy,_,_) -> supTy
                           | _ -> s,
                       id)
                spc
    in
    % let _ = writeLine(printSpec spc) in
    spc

  % Boolean flag simplify? determines if relativizeQuantifiers does
  % formula simplification.
  op removeSubtypesInTerm (simplify?:Bool) (spc: Spec) (t: MSTerm): MSTerm =
    let t = mapTerm(relativizeQuantifiersSimpOption simplify? spc, id, id) t in
    mapTerm (id,fn s -> case s of
		          | Subtype(supTy,_,_) -> supTy
                          | _ -> s,
             id)
      t

  % Look up the qid_P op for qid used to lift subtype predicates to qid
  op hoSubtypePredicateForType(qid as Qualified(q,id): QualifiedId, tys: MSTypes, param_ty: MSType, spc: Spec)
     : Option MSTerm =
    let pred_qid = Qualified(q,id^"_P") in
    case AnnSpec.findTheOp(spc, pred_qid) of
      | None -> None
      | Some info ->
        let pred_args = map (fn ty -> mkOptLambda(typePattern(ty, spc))) tys in
        Some(mkAppl(mkOp(pred_qid, mkArrow(mkProduct(map (fn ty -> mkArrow(ty, boolType)) tys),
                                           mkArrow(param_ty, boolType))),
                    pred_args))

  % Build a pattern for matching subterms of a datatype along with a
  % term expressing the lifting predicate for the type of the subterm
  op typePattern(ty: MSType, spc: Spec): MSPattern * MSTerm =
    % NOTE: i here is for making fresh variable names
    let def aux(ty, i: Nat) =
          case ty of
            | TyVar(tv,a) ->
              let nm = "x"^show i in
              (mkVarPat(nm, ty), mkApply(mkVar("P_"^tv, Arrow(TyVar(tv, a), boolType, a)),
                                         mkVar(nm, ty)))
            | Base(qid, a_tys, a) | a_tys ~= [] ->
              (case hoSubtypePredicateForType(qid, a_tys, ty, spc) of
                 | Some pred ->
                   let nm = "x"^show i in
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
              (RecordPat(reverse pats, a), foldl Utilities.mkAnd trueTerm preds)
            | Arrow(dom,rng,_) ->
              let f_nm = "f"^show i in
              let arg_var = ("arg"^show i, dom) in
              (mkVarPat(f_nm , ty),
               mkBind (Forall, [arg_var],
                       mkCaseExpr (mkApply (mkVar (f_nm, ty),mkVar arg_var),
                                   [aux (rng, i+1)])))
            | Subtype(base_ty, pred, _) ->
              % FIXME: this case seems to be eliminated before we ever
              % get here...
              let nm = "x"^show i in
              (mkVarPat(nm , ty),
               %mkImplies ()
               mkCaseExpr (mkVar (nm, ty), [aux (base_ty, i+1)]))
            | _ -> (mkWildPat(ty), trueTerm)
    in
    aux(ty, 0)

  %% Create predicate lifter for each named type T a: a HO predicate T_P that takes a predicate on "a"
  %% and produces a predicate on T a
  %% The predicate lifter has type (a -> Bool) -> T a -> Bool
  op addSubtypePredicateLifters(spc: Spec): Spec =
    let def addPredDecl((qid as Qualified(q,id),a), el, n_elts, spc) =
          case AnnSpec.findTheType(spc, qid) of
            | Some info % ? | definedTypeInfo? info
              ->
              let (tvs,ty_def) = unpackFirstTypeDef info in
              if tvs = [] || (case ty_def of
                                | Any _ -> false
                                | CoProduct _ -> false
                                | Product _ -> false
                                | Quotient _ -> true % ?
                                | _ -> true)
                then (el :: n_elts, spc)
              else
              let pred_name = id^"_P" in
              % let _ = writeLine("making "^pred_name) in
              let pred_qid = Qualified(q, pred_name) in
              (case AnnSpec.findTheOp(spc, pred_qid) of
                 | Some _ -> (Cons(el, n_elts), spc) % already exists. Should check type is correct!
                 | None ->
               let param_ty = Base(qid, map (fn tv -> TyVar(tv, a)) tvs, a) in
               let pred_ty = Arrow(mkProduct(map (fn tv -> Arrow(TyVar(tv, a), boolType, a)) tvs),
                                   Arrow(param_ty, boolType, a), a)
               in
               let x_dfn = Pi(tvs, TypedTerm(Any a, pred_ty, a), a) in
               let op_map = insertAQualifierMap(spc.ops, q, pred_name,
                                                {names = [pred_qid], dfn = x_dfn,
                                                 fixity = Nonfix, fullyQualified? = false})
               in
               ([Op(pred_qid, ~(embed? Any ty_def), a), el] ++ n_elts, spc << {ops = op_map}))
            | _ -> (el :: n_elts, spc)
        def addPredDeclss (elts, op_map) =
          foldl (fn ((n_elts, op_map),el) ->
                 case el of
                   | Type sd -> addPredDecl(sd, el, n_elts, op_map)
                   | TypeDef sd -> addPredDecl(sd, el, n_elts, op_map)
                   | Import(s_tm, i_sp, i_elts, a) ->
                     let (r_elts, op_map) = addPredDeclss(i_elts, op_map) in
                     (Cons(Import(s_tm, i_sp, reverse r_elts, a), n_elts), op_map)
                   |  _ -> (Cons(el, n_elts), op_map))
            ([], op_map) elts
        def addPredDef((ty_qid as Qualified(q,id), a), spc) =
          case AnnSpec.findTheType(spc, ty_qid) of
            | Some info | definedTypeInfo? info ->
              let (tvs, ty_def) = unpackFirstTypeDef info in
              (if tvs = [] || (case ty_def of
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
                 | Some info | anyTerm? info.dfn ->    % Construct definition if there isn't one
                   let (tvs, pred_ty, _) = unpackFirstOpDef info in
                   let param_ty = Base(ty_qid, map (fn tv -> TyVar(tv, a)) tvs, a) in
                   let dfn = case ty_def of
                               | CoProduct(constrs,_) ->
                                 mkLambda(mkTuplePat(map (fn tv ->
                                                            mkVarPat("P_"^tv,
                                                                     Arrow(TyVar(tv, a),
                                                                           boolType, a)))
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
                                 mkLambda(mkTuplePat(map (fn tv -> mkVarPat("P_"^tv, Arrow(TyVar(tv, a), boolType, a)))
                                                       tvs),
                                          mkLambda(p, p_t))
                               | _ -> Any a
                   in
                   let x_dfn = Pi(tvs, TypedTerm(dfn, pred_ty, a), a) in
                   let ops = insertAQualifierMap(spc.ops, q, pred_name, info << {dfn = x_dfn}) in
                   spc << {ops = ops}
                 | _ -> spc)
            | _ -> spc
    in
    let (new_elts, spc) = addPredDeclss (spc.elements, spc) in
    let spc = spc << {elements = reverse new_elts} in
    let spc = foldlSpecElements
                (fn (spc, el) ->
                 case el of
                   | TypeDef ty_qid -> addPredDef(ty_qid, spc)
                   | _ -> spc)
                spc spc.elements
    in
    spc

endspec
