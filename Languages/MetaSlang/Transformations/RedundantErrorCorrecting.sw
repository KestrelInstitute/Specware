(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Script qualifying
spec
import /Languages/SpecCalculus/Semantics/Monad
import Simplify  %/Languages/MetaSlang/Specs/Utilities
import /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities
import /Languages/SpecCalculus/AbstractSyntax/SCTerm                 % SCTerm

type QIdMap a = PolyMap.Map (QualifiedId, a)

op criticalQIdMap(qid_maps: List QualifiedIdMap): QIdMap(QualifiedIds) =
  let qid_map1 :: r_qid_maps = qid_maps in
   foldMap (fn result_map -> fn d -> fn c ->
            let r_c_s = mapPartial (fn qid_mapi ->
                                    case evalPartial qid_mapi d of
                                      | Some ci | ci ~= c ->
                                        Some ci 
                                      | _ -> None)
                          r_qid_maps
            in
            if r_c_s = [] then result_map
              else % let _ = writeLine(show c) in
                   update result_map d (c :: r_c_s))
     emptyMap qid_map1

op criticalOpMap (morphs: List Morphism) : QIdMap QualifiedIds =
  criticalQIdMap(map (project opMap) morphs)

op criticalTypeMap (morphs: List Morphism) : QIdMap QualifiedIds =
  criticalQIdMap(map (project typeMap) morphs)

op mkApplyI (hd: MSTerm, args: List MSTerms, i: Nat): MSTerm =
  case args of
    | [] -> hd
    | ai :: r_args ->
      mkApplyI(mkApply(hd, ai@(min(i, length ai - 1))), r_args, i)

op replaceType (ty: MSType, src_ty: MSType, trg_ty: MSType): MSType =
  mapType (id, fn sty -> if equalType?(sty, src_ty) then trg_ty else sty, id) ty

op replaceTypeInPat(pat: MSPattern, src_ty: MSType, trg_ty: MSType): MSPattern =
  mapPattern (id, fn sty -> if equalType?(sty, src_ty) then trg_ty else sty, id) pat

op mkListType(ty: MSType): MSType = mkBase(Qualified("List", "List"), [ty])

op mkListForm(tms: MSTerms, ty: MSType): MSTerm =
  case tms of
    | [] -> mkEmbed0(Qualified("List", "Nil"), mkListType ty)
    | tm1 :: r_tms ->
      mkApply(mkEmbed1(Qualified("List", "Cons"), mkArrow(mkProduct[ty, mkListType ty], mkListType ty)),
              mkTuple[tm1, mkListForm(r_tms, ty)])

op mkRedundantDef(dfn: MSTerm, src_ty: MSType, trg_ty: MSType, test_fix_fn: MSTerm, ty_targets: MSTypes,
                  op_target_qids: QualifiedIds, spc: Spec): MSTerm =
  let op_targets = map (fn op_qid ->
                          let Some info = findTheOp(spc, op_qid) in
                          mkInfixOp(op_qid, info.fixity, inferType(spc, info.dfn)))
                     op_target_qids
  in
  let def convertDef(tm) =
        case tm of
          | Pi(tvs, stm, a) -> Pi(tvs, convertDef(stm), a)
          | TypedTerm(stm, ty, a) -> TypedTerm(convertDefTyArgs(stm, ty, [], []), convertType ty, a)
          | _ -> convertDefTyArgs(tm, inferType(spc, tm), [], [])
      def convertDefTyArgs(tm: MSTerm, ty: MSType, args: List MSTerms, src_params: Ids): MSTerm =
        case tm of
          | Lambda([(pat, pred, bod)], a) ->
            let new_args = tabulate(length ty_targets, fn i -> convertPatToArg(pat, i)) in
            let new_src_params = foldSubPatterns (fn (p, src_params) ->
                                                  case p of
                                                    | VarPat((v,ty), _) | equalType?(ty, src_ty) -> v :: src_params
                                                    | _ -> src_params)
                                   [] pat
            in
            let Some rng = rangeOpt(spc, ty) in
            Lambda([(convertPat pat, pred, convertDefTyArgs(bod, rng, args ++ [new_args], src_params ++ new_src_params))], a)
          | _ ->
            let result_comps = tabulate(length op_targets,
                                        fn i -> mkApplyI(op_targets@i, args, i))
            in
            let main_bod =
                if equalType?(ty, src_ty)
                  then mkTuple(result_comps)
                else mkApply(mkOp(Qualified("SemanticError", "returnMostPopular"),
                                           mkArrow(mkListType ty, ty)),
                             mkListForm(result_comps, ty))
            in
            %% Add test_fix_fn lets
            foldl (fn (bod, v) ->
                     let pat = mkTuplePat(tabulate(length ty_targets,
                                               fn i -> mkVarPat(v^"__"^show i, ty_targets@i)))
                     in
                     mkLet([(pat, mkApply(test_fix_fn, patToTerm pat))], bod))
              main_bod src_params
      def convertType ty = replaceType(ty, src_ty, trg_ty)
      def convertPat(pat: MSPattern): MSPattern =
        mapPattern (id, id,
                    fn pat ->
                      case pat of
                        | VarPat((v,ty), _) | equalType?(ty, src_ty) ->
                          mkTuplePat(tabulate(length ty_targets,
                                              fn i -> mkVarPat(v^"__"^show i, ty_targets@i)))
                        | _ -> pat)
          pat
      def convertPatToArg(pat: MSPattern, i: Nat): MSTerm =
        let pati = mapPattern (id, id,
                               fn pat ->
                                 case pat of
                                   | VarPat((v,ty), _) | equalType?(ty, src_ty) ->
                                     mkVarPat(v^"__"^show i, ty_targets@i)
                                   | _ -> pat)
                     pat
        in
        patToTerm pati
      def patToTerm pati =
        case patternToTerm pati of
          | Some tm -> tm
          | None -> mkBool false   %% Should check to make sure this cannot happen!
  in
  convertDef dfn

op findUniversalIdentity(ty: MSType, term: MSTerm): Option (MSVar * MSTerm) =
  let def findId(t, universals: MSVars) =
        case t of
          | Apply(Fun(Equals,_,_), Record([(_,Var(v, _)), (_, rhs as Apply _)], _),_) ->
             %% let _ = writeLine("findUniversalIdentity:\n"^printTerm t) in
              %% Maybe should have a more stringent test on rhs
              if equalType?(v.2, ty) && inVars?(v, universals)
                  && (case freeVars rhs of
                        | [v2] -> equalVar?(v, v2)
                        | _ -> false)
              then Some(v, rhs) else None
          | Apply(Fun(And,_,_), Record([("1",p),("2",q)],_),_) ->
            (case findId(p, universals) of
              | None -> findId(q, universals)
              | result -> result)               
          | Bind(Forall, uvs, body, _) ->
            findId(body, universals ++ uvs)
          | _ -> None
  in
  findId(term, [])

op findIdentityExpr(ty: MSType, spc: Spec): Option (MSVar * MSTerm) =
  foldlSpecElements (fn (result, el) ->
                       if some? result then result
                       else case el of
                              | Property(_,_,_,term,_) ->
                                findUniversalIdentity(ty, term)
                              | _ -> None)
    None spc.elements

op prependIdInQId(Qualified(q, id): QualifiedId, prefix: String): QualifiedId =
  Qualified(q, prefix ^ id)

op makeCheckRandom?: Bool = true
op randomCheck?Appl: MSTerm = mkAppl(mkOp(Qualified("SemanticError", "randomCheck?"),
                                           mkArrow(mkProduct[], boolType)),
                                      [])

op mkWarningForm(warn_str: String): MSTerm =
  mkApply(mkOp(Qualified("System", "warn"), mkArrow(stringType, voidType)),
          mkString warn_str)

op mkFailForm(fail_str: String): MSTerm =
  mkApply(mkOp(Qualified("System", "fail"), mkArrow(stringType, voidType)),
          mkString fail_str)

op mkConverterFromIdFun(src_ty_ind     : Nat, 
                        trg_ty_ind     : Nat, 
                        src_var        : MSTerm, 
                        primary_ty_qid : QualifiedId, 
                        ident_param    : MSVar,
                        ident_exp      : MSTerm, 
                        primary_ty     : MSType, 
                        ty_targets     : MSTypes, 
                        ops_map        : QIdMap QualifiedIds, 
                        spc            : Spec)
   : MSTerm =
   mapTerm(fn t ->
             case t of
               | Var(v, _) | equalVar?(v, ident_param) -> src_var
               | Fun(Op(qid, fx), f_ty, a) ->
                 (case evalPartial ops_map qid of
                    | None -> t
                    | Some op_qids ->
                      case arrowOpt(spc, f_ty) of
                        | None ->
                          (if equalType?(f_ty, primary_ty)
                           then Fun(Op(op_qids@trg_ty_ind, fx), ty_targets@trg_ty_ind, a)
                           else t)
                        | Some(dom, rng) ->
                          case rng of
                            | Base(ty_qid, _, _) | ty_qid = primary_ty_qid ->
                              Fun(Op(op_qids@trg_ty_ind, fx), mkArrow(dom, ty_targets@trg_ty_ind), a)
                            | _ ->
                              if primary_ty_qid in? typesInType dom
                                then Fun(Op(op_qids@src_ty_ind, fx),
                                         mkArrow(replaceType(dom, primary_ty, ty_targets@src_ty_ind), rng), a)
                              else t)
               | _ -> t                ,
           id, id)
     ident_exp

op mkNumCondn(ps: MSTerms, i: Nat): MSTerm =
  case ps of
    | [] -> mkNat i
    | p :: r_ps -> MS.mkIfThenElse(p, mkNat i, mkNumCondn(r_ps, i+1))

op mkTestFixFunction(primary_ty_qid: QualifiedId, primary_ty: MSType, ty_targets: MSTypes, pos: Position,
                     opt_qual: Option Qualifier, ops_map: QIdMap(QualifiedIds), spc: Spec, new_spc: Spec)
  : Env(QualifiedId * MSTerm) =
  case findIdentityExpr(primary_ty, spc) of
    | None -> raise(TypeCheck (pos, "Can't find identity theorem for type: "
                           ^ printType primary_ty))
    | Some(ident_param, ident_exp) ->
  let test_fix_fn_qid = makeDerivedQId spc (prependIdInQId(primary_ty_qid, "TestFix__")) opt_qual in
  let arg_vars = tabulate(length ty_targets, fn i -> ("x_"^show i, ty_targets@i)) in
  let param = mkTuplePat(map mkVarPat arg_vars) in
  let arg = mkTuple(map mkVar arg_vars) in
  let subtype_pred_tms = map (fn (v,ty) -> simplifiedApply(subtypePredicate(ty, new_spc), mkVar(v,ty), spc)) arg_vars in
  let def mkTestFixBody(subtype_pred_tms) =
       let num_args = length arg_vars in
       let arg_var_tms = map mkVar arg_vars in
       if num_args = 2
        then
          MS.mkIfThenElse
            (subtype_pred_tms@0,
             MS.mkIfThenElse
               (subtype_pred_tms@1, mkTuple(arg_var_tms),
                mkSeq[mkWarningForm("Component 2 of "^show primary_ty_qid^" corrupted! Recomputing from component 1"),
                      mkTuple[mkVar(arg_vars@0),
                              mkConverterFromIdFun(0, 1, mkVar(arg_vars@0), primary_ty_qid, ident_param, ident_exp,
                                                   primary_ty, ty_targets, ops_map, spc)]]),
             MS.mkIfThenElse
               (subtype_pred_tms@1, 
                mkSeq[mkWarningForm("Component 1 of "^show primary_ty_qid^" corrupted! Recomputing from component 2"),
                      mkTuple[mkConverterFromIdFun(1, 0, mkVar(arg_vars@1), primary_ty_qid, ident_param, ident_exp,
                                                   primary_ty, ty_targets, ops_map, spc),
                              mkVar(arg_vars@1)]],
                mkSeq[mkWarningForm("All implementations of "^show primary_ty_qid^" corrupted!"),
                      mkTuple(arg_var_tms)]))
       else
         let result_tuple = mkTuple(arg_var_tms) in
         let flags = tabulate(num_args, fn i -> ("p"^show i, boolType)) in
         let flag_binds = tabulate(num_args, fn i -> (mkVarPat(flags@i), subtype_pred_tms@i)) in
         let flag_tms = map mkVar flags in
         let good_posn = ("good_posn", natType) in
         let result_cases =
             tabulate(num_args,
                      fn i ->
                        let i_cases =
                            tabulate(num_args,
                                     fn j -> (mkNatPat j,
                                              if i = j then arg_var_tms@i
                                                else let conv_tm = mkConverterFromIdFun(j, i, arg_var_tms@j, primary_ty_qid, ident_param,
                                                                                        ident_exp, primary_ty, ty_targets, ops_map, spc)
                                                     in
                                                     let warn_tm = mkWarningForm("Component "^show(i+1)^" of "^show primary_ty_qid
                                                                                   ^" corrupted! Recomputing from component "^show(j+1))
                                                     in
                                                     if j < i
                                                       then MS.mkIfThenElse
                                                              (flag_tms@i, arg_var_tms@i,
                                                               mkSeq[warn_tm, conv_tm])
                                                       else mkSeq[warn_tm, conv_tm]))
                        in
                        mkCaseExpr(mkVar good_posn, i_cases))
         in
         mkLet(flag_binds,
               MS.mkIfThenElse
                 (mkConj(flag_tms),
                  result_tuple,
                  mkLet([(mkVarPat good_posn, mkNumCondn(flag_tms, 0))],
                        MS.mkIfThenElse
                          (mkEquality(natType, mkVar good_posn, mkNat num_args),
                           mkSeq[mkWarningForm("All implementations of "^show primary_ty_qid^" corrupted!"),
                                 result_tuple],
                           mkTuple result_cases))))
  in
  let fix_body = simplify spc (mkTestFixBody(subtype_pred_tms)) in
  let check_fn = mkLambda(param, if makeCheckRandom?
                                  then MS.mkIfThenElse(randomCheck?Appl, fix_body, arg)
                                  else fix_body) in
  return(test_fix_fn_qid, check_fn)

%% Defined in /Languages/SpecCalculus/Semantics/Evaluate/Spec.sw
op SpecCalc.mergeImport: SCTerm -> Spec -> Spec -> Position -> Env Spec

op redundantErrorCorrectingProduct (spc: Spec) (morphs: List (SCTerm * Morphism)) (opt_qual: Option Qualifier)
                                   (tracing?: Bool): Env(Spec * Bool) =
%%  return(spc, tracing?) (*
  let ((_,pos), morph1) :: _ = morphs in
  {morphs2 <- return(map (fn (_,yy) -> yy) morphs);
   ops_map <- return(criticalOpMap morphs2);      % Maps source ops to list of ops (when mapped differently)
   types_map <- return(criticalTypeMap morphs2);  % Maps source types to list of types -- should only be one
   trg_spcs <- return(map (project cod) morphs2);
   types_map_l <- return(mapToList types_map);
   when (length types_map_l ~= 1)
      (raise(TypeCheck (pos, "Should be exactly 1 type mapped differently by morphisms:\n"
                           ^ foldr (fn ((qid,_), s) -> show qid^" "^s) "" (map head (mapToList types_map)))));
   (primary_ty_qid, ty_target_qids) :: _ <- return types_map_l;
   primary_ty <- return(mkBase(primary_ty_qid, []));
   ty_targets <- return(map (fn qid -> mkBase(qid, [])) ty_target_qids);
   new_primary_ty_qid <- return(makeDerivedQId spc primary_ty_qid opt_qual);
   new_primary_ty <- return(mkBase(new_primary_ty_qid, []));
   src_spc <- return morph1.dom;
   when (src_spc ~= spc)
     (raise(TypeCheck (pos, "Transformed spec should be target of morphisms.")));
   new_spc <- foldM (fn spc -> fn imp_spec ->
                       let Some imp_spc_uid = findRelativeUIDforValue(Spec imp_spec) in
                       mergeImport (UnitId imp_spc_uid, noPos) imp_spec spc pos)
                emptySpec
                trg_spcs;
   new_spc <- return(addTypeDef(new_spc, new_primary_ty_qid, mkProduct ty_targets));
   (test_fix_fn_qid, test_fix_fn_def) <- mkTestFixFunction(primary_ty_qid, primary_ty, ty_targets, pos,
                                                           opt_qual, ops_map, spc, new_spc);
   new_spc <- return(addOpDef(new_spc, test_fix_fn_qid, Nonfix, test_fix_fn_def));
   new_spc <- return(foldMap (fn new_spc -> fn qid -> fn op_target_qids ->
                                let Some opinfo = findTheOp(spc, qid) in
                                addOpDef(new_spc, makeDerivedQId spc qid opt_qual,
                                         opinfo.fixity,
                                         mkRedundantDef(opinfo.dfn, primary_ty, new_primary_ty,
                                                        mkOp(test_fix_fn_qid, mkArrow(new_primary_ty, new_primary_ty)),
                                                        ty_targets, op_target_qids, new_spc)))
                       new_spc ops_map);
   return(new_spc, tracing?)}      % *)

op mkCoProdOfTypes(ty_target_qids: QualifiedIds): MSType =
  let coprod_flds = map (fn qid as Qualified(q,id) -> (Qualified(q,q^"__"^id), Some(mkBase(qid, [])))) ty_target_qids in
  let errorFld = (mkUnQualifiedId "Data_Error", Some(natType)) in
  mkCanonCoProduct(errorFld :: coprod_flds)

op mkTestFunction(primary_ty_qid: QualifiedId, new_primary_ty: MSType, CoProduct(coprod_flds, _): MSType,
                  opt_qual: Option Qualifier, new_spc: Spec)
  : QualifiedId * MSTerm =
  let test_fn_qid = makeDerivedQId new_spc (prependIdInQId(primary_ty_qid, "Test__")) opt_qual in
  let param = ("x", new_primary_ty) in
  let cases = map (fn (id, Some ty) ->
                   let pv = ("y", ty) in
                   (mkEmbedPat(id, Some(mkVarPat pv), new_primary_ty), trueTerm,
                    if equalType?(ty, natType)
                      then falseTerm
                      else simplifiedApply(subtypePredicate(ty, new_spc), mkVar pv, new_spc)))
                coprod_flds
  in                     
  let test_fn_body = mkLambda(mkVarPat param, mkApply(Lambda(cases, noPos), mkVar param)) in
  (test_fn_qid, test_fn_body)

op restartCountTerm: MSTerm = mkOp(Qualified("SemanticError", "restartCount"), natType)
op mkThrowForm(fail_str: String): MSTerm =
  mkApply(mkOp(Qualified("SemanticError", "throwToRestart"), mkArrow(stringType, voidType)),
          mkString fail_str)


op mkChooseFunction(primary_ty_qid: QualifiedId, new_primary_ty: MSType, coProd_def as CoProduct(coprod_flds, _): MSType,
                    conversion_fn_defs: List(QualifiedId * MSTerm * MSTerm),
                    opt_qual: Option Qualifier, ty_targets: MSTypes, new_spc: Spec)
  : QualifiedId * MSTerm =
  let choose_fn_qid = makeDerivedQId new_spc (prependIdInQId(primary_ty_qid, "Choose__")) opt_qual in
  let param = ("x", new_primary_ty) in
  let cases = tabulate(length ty_targets,
                       fn i -> (mkNatPat i, trueTerm,
                                let tyi = ty_targets@i in
                                let constr_qid = constructorForQid(tyi, coProd_def) in
                                mkApply(mkEmbed1(constr_qid, mkArrow(tyi, new_primary_ty)),
                                        mkApply((conversion_fn_defs@i).3,
                                                mkVar param))))
  in                     
  let other_case = (mkWildPat natType, trueTerm, mkFailForm("All representations of "^show primary_ty_qid^" failed.")) in
  let choose_fn_body = mkLambda(mkVarPat param, mkApply(Lambda(cases ++ [other_case], noPos), restartCountTerm)) in
  (choose_fn_qid, choose_fn_body)


op mkConversionFunction (to_type_qid               : QualifiedId, 
                         primary_ty                : MSType, 
                         primary_ty_qid            : QualifiedId, 
                         new_primary_ty            : MSType, 
                         new_primary_ty_qid        : QualifiedId, 
                         CoProduct(coprod_flds, _) : MSType, 
                         ident_param               : MSVar, 
                         ident_exp                 : MSTerm,
                         opt_qual                  : Option Qualifier, 
                         ty_targets                : MSTypes, 
                         ops_map                   : QIdMap QualifiedIds,
                         new_spc                   : Spec)
   : QualifiedId * MSTerm * MSTerm =
  let to_type = mkBase(to_type_qid, []) in
  let conversion_fn_qid = makeDerivedQId new_spc (prependIdInQId(to_type_qid, "to_")) opt_qual in
  let param = ("x", new_primary_ty) in
  let cases = map (fn (id, Some ty) ->
                   let pv = ("y", ty) in
                   (mkEmbedPat(id, Some(mkVarPat pv), new_primary_ty), trueTerm,
                    if equalType?(ty, natType)
                      then mkFailForm("Error in "^show new_primary_ty_qid^" Data.")
                      else if equalType?(ty, to_type)
                      then mkVar pv
                      else mkConverterFromIdFun(positionOf(ty_targets, ty), positionOf(ty_targets, to_type), mkVar pv,
                                                primary_ty_qid, ident_param, ident_exp, primary_ty, ty_targets, ops_map, new_spc)))
                coprod_flds
  in                     
  let conversion_fn_body = mkLambda(mkVarPat param, mkApply(Lambda(cases, noPos), mkVar param)) in
  (conversion_fn_qid, conversion_fn_body, mkOp(conversion_fn_qid, mkArrow(new_primary_ty, to_type)))

op constructorForQid(ty: MSType, CoProduct(coprod_flds, _): MSType): QualifiedId =
  case findLeftmost (fn (qid, Some c_ty) -> equalType?(ty, c_ty)) coprod_flds of
    | Some(qid,_) -> qid

op mkCaseDef(dfn: MSTerm, primary_ty: MSType, new_primary_ty: MSType, coProd_def as CoProduct(coprod_flds, _): MSType,
             conversion_fn_defs: List(QualifiedId * MSTerm * MSTerm),
             test_fn: MSTerm, choose_fn: MSTerm,
             ty_targets: MSTypes, op_target_qids: QualifiedIds, spc: Spec): MSTerm =
  let op_targets = map (fn op_qid ->
                          let Some info = findTheOp(spc, op_qid) in
                          mkInfixOp(op_qid, info.fixity, inferType(spc, info.dfn)))
                     op_target_qids
  in
  let def convertDef(tm) =
        case tm of
          | Pi(tvs, stm, a) -> Pi(tvs, convertDef(stm), a)
          | TypedTerm(stm, ty, a) -> TypedTerm(convertDefTyArgs(stm, ty, [], []), convertType ty, a)
          | _ -> convertDefTyArgs(tm, inferType(spc, tm), [], [])
      def convertDefTyArgs(tm: MSTerm, ty: MSType, args: MSTerms, src_params: Ids): MSTerm =
        case tm of
          | Lambda([(pat, pred, bod)], a) ->
            let new_src_params = foldSubPatterns (fn (p, src_params) ->
                                                  case p of
                                                    | VarPat((v,ty), _) | equalType?(ty, primary_ty) -> v :: src_params
                                                    | _ -> src_params)
                                   [] pat
            in
            let Some rng = rangeOpt(spc, ty) in
            let pat = replaceTypeInPat(pat, primary_ty, new_primary_ty) in
            Lambda([(pat, pred, convertDefTyArgs(bod, rng, args ++ [patToTerm pat], src_params ++ reverse new_src_params))], a)
          | _ ->
            let main_bod =
                case src_params of
                  | [] ->   % No parameters of pertinent type
                    if equalType?(ty, primary_ty)
                      then let cases = tabulate(length ty_targets,
                                                fn i -> (mkNatPat i, trueTerm,
                                                         let tyi = ty_targets@i in
                                                         let constr_id = constructorForQid(tyi, coProd_def) in
                                                         let conv_bod = foldl (fn (hd, arg) -> mkApply(hd, arg)) (op_targets@i) args in
                                                         mkApply(mkEmbed1(constr_id, mkArrow(tyi, new_primary_ty)),
                                                                 conv_bod)))
                           in                     
                           let other_case = (mkWildPat natType, trueTerm, mkFailForm("All representations of "^printType primary_ty^" failed.")) in
                           mkApply(Lambda(cases ++ [other_case], noPos), restartCountTerm)
                      else mkFailForm "Type must appear as explicit parameter or return type"
                   | src_param0 :: r_src_params ->
                     let main_body =
                         if equalType?(ty, primary_ty)
                           then let cases = map (fn (constr_id, Some ty0) ->
                                                 let pv = (src_param0^"_0", ty0) in
                                                 (mkEmbedPat(constr_id, Some(mkVarPat pv), new_primary_ty),
                                                  trueTerm,
                                                  if constr_id = mkUnQualifiedId "Data_Error" then mkThrowForm("Error in "^printType primary_ty^" Data.")
                                                  else
                                                  let target_i = positionOf(ty_targets, ty0) in
                                                  let coercion_fn = (conversion_fn_defs@target_i).3 in
                                                  let sbst = ((src_param0, primary_ty), mkVar pv)
                                                            :: map (fn src_id -> ((src_id, primary_ty), mkVar(src_id^"_0", ty0)))
                                                                 r_src_params
                                                  in
                                                  let main_expr = mkCurriedApply(op_targets@target_i, args) in
                                                  mkLet(map (fn src_id ->
                                                             (mkVarPat(src_id^"_0", ty0), mkApply(coercion_fn, mkVar(src_id, ty0))))
                                                          r_src_params,
                                                        mkApply(mkEmbed1(constr_id, mkArrow(ty0, new_primary_ty)),
                                                                substitute(main_expr, sbst)))))
                                              coprod_flds
                                in
                                mkApply(Lambda(cases, noPos), mkApply(choose_fn, mkVar(src_param0, new_primary_ty)))
                         else let cases = map (fn (constr_id, Some ty0) ->
                                                 let pv = (src_param0^"_0", ty0) in
                                                 (mkEmbedPat(constr_id, Some(mkVarPat pv), new_primary_ty),
                                                  trueTerm,
                                                  if constr_id = mkUnQualifiedId "Data_Error" then mkThrowForm("Error in "^printType primary_ty^" Data.")
                                                  else
                                                  let sbst = ((src_param0, primary_ty), mkVar pv)
                                                            :: map (fn src_id -> ((src_id, primary_ty), mkVar(src_id^"_0", ty0)))
                                                                r_src_params
                                                  in
                                                  let target_i = positionOf(ty_targets, ty0) in
                                                  substitute(mkCurriedApply(op_targets@target_i, args), sbst)))
                                            coprod_flds
                                in
                                mkApply(Lambda(cases, noPos), mkApply(choose_fn, mkVar(src_param0, new_primary_ty)))
                     in
                     MS.mkIfThenElse(mkConj(map (fn param -> mkApply(test_fn, mkVar(param, new_primary_ty))) src_params),
                                     main_body,
                                     mkThrowForm("Error in "^printType primary_ty^" Data."))
            in
            simplify spc main_bod
      def convertType ty = replaceType(ty, primary_ty, new_primary_ty)
      def patToTerm pati =
        case patternToTerm pati of
          | Some tm -> tm
          | None -> mkBool false   %% Should check to make sure this cannot happen!
  in
  convertDef dfn

 op Specware.evaluateUnitId: String -> Option Value   % Defined in /Languages/SpecCalculus/Semantics/Bootstrap, which imports this spec
op runtimeSemanticErrorSpec: String = "/Languages/MetaSlang/Transformations/RuntimeSemanticError"

op redundantErrorCorrectingRestart (spc: Spec) (morphs: List (SCTerm * Morphism)) (opt_qual: Option Qualifier) (tracing?: Bool): Env(Spec * Bool) =
%%  return(spc, tracing?) (*
  let ((_,pos), morph1) :: _ = morphs in
  {morphs2 <- return(map (fn (_,yy) -> yy) morphs);
   ops_map <- return(criticalOpMap morphs2);      % Maps source ops to list of ops (when mapped differently)
   types_map <- return(criticalTypeMap morphs2);  % Maps source types to list of types -- should only be one
   trg_spcs <- return(map (project cod) morphs2);
   types_map_l <- return(mapToList types_map);
   when (length types_map_l ~= 1)
      (raise(TypeCheck (pos, "Should be exactly 1 type mapped differently by morphisms:\n"
                           ^ foldr (fn ((qid,_), s) -> show qid^" "^s) "" (map head (mapToList types_map)))));
   (primary_ty_qid, ty_target_qids) :: _ <- return types_map_l;
   primary_ty <- return(mkBase(primary_ty_qid, []));
   case findIdentityExpr(primary_ty, spc) of
    | None -> raise(TypeCheck (pos, "Can't find identity theorem for type: "
                           ^ printType primary_ty))
    | Some(ident_param, ident_exp) ->
   {ty_targets <- return(map (fn qid -> mkBase(qid, [])) ty_target_qids);
    new_primary_ty_qid <- return(makeDerivedQId spc primary_ty_qid opt_qual);
    new_primary_ty <- return(mkBase(new_primary_ty_qid, []));
    src_spc <- return morph1.dom;
    when (src_spc ~= spc)
      (raise(TypeCheck (pos, "Transformed spec should be target of morphisms.")));
    new_spc <- foldM (fn spc -> fn imp_spec ->
                        let Some imp_spc_uid = findRelativeUIDforValue(Spec imp_spec) in
                      mergeImport (UnitId imp_spc_uid, noPos) imp_spec spc pos)
      emptySpec
      trg_spcs;
    new_spc <- let Some(Spec rse_spc) = evaluateUnitId runtimeSemanticErrorSpec in
               let Some rse_spc_uid = findRelativeUIDforValue(Spec rse_spc) in
               mergeImport (UnitId rse_spc_uid, noPos) rse_spc new_spc pos;
    coProd_def <- return(mkCoProdOfTypes(ty_target_qids));
    new_spc <- return(addTypeDef(new_spc, new_primary_ty_qid, coProd_def));
    (test_fn_qid, test_fn_def) <- return(mkTestFunction(primary_ty_qid, new_primary_ty, coProd_def, opt_qual, new_spc));
    new_spc <- return(addOpDef(new_spc, test_fn_qid, Nonfix, test_fn_def));
    conversion_fn_defs <- return(map (fn ty_target_qid ->
                                        mkConversionFunction(ty_target_qid, primary_ty, primary_ty_qid, new_primary_ty, new_primary_ty_qid,
                                                             coProd_def, ident_param, ident_exp, opt_qual, ty_targets, ops_map, new_spc))
                                   ty_target_qids);
    new_spc <- return(foldl (fn (new_spc, (qid, defn, _)) -> addOpDef(new_spc, qid, Nonfix, defn)) new_spc conversion_fn_defs);
    (choose_fn_qid, choose_fn_def) <- return(mkChooseFunction(primary_ty_qid, new_primary_ty, coProd_def, conversion_fn_defs, opt_qual,
                                                              ty_targets, new_spc));
    new_spc <- return(addOpDef(new_spc, choose_fn_qid, Nonfix, choose_fn_def));
    new_spc <- return(foldMap (fn new_spc -> fn qid -> fn op_target_qids ->
                               let Some opinfo = findTheOp(spc, qid) in
                               % let _ = writeLine("Doing "^show qid) in 
                               addOpDef(new_spc, makeDerivedQId spc qid opt_qual,
                                        opinfo.fixity,
                                        mkCaseDef(opinfo.dfn, primary_ty, new_primary_ty, coProd_def, conversion_fn_defs,
                                                  mkOp(test_fn_qid, mkArrow(new_primary_ty, boolType)),
                                                  mkOp(choose_fn_qid, mkArrow(new_primary_ty, new_primary_ty)),
                                                  ty_targets, op_target_qids, new_spc)))
                        new_spc ops_map);
    return(new_spc, tracing?)}}      % *)

op redundantErrorCorrecting (spc: Spec) (morphs: List (SCTerm * Morphism)) (opt_qual: Option Qualifier)
                            (restart?: Bool)(tracing?: Bool): Env(Spec * Bool) =
  if restart?
    then redundantErrorCorrectingRestart spc morphs opt_qual tracing?
    else redundantErrorCorrectingProduct spc morphs opt_qual tracing?

end-spec

