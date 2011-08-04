Script qualifying
spec
import /Languages/SpecCalculus/Semantics/Monad
import Simplify  %/Languages/MetaSlang/Specs/Utilities
import /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities

type QIdMap a = PolyMap.Map (QualifiedId, a)

op criticalQIdMap(qid_maps: List QualifiedIdMap): QIdMap(List QualifiedId) =
  let qid_map1 :: r_qid_maps = qid_maps in
   foldMap (fn result_map -> fn d -> fn c ->
            let r_c_s = mapPartial (fn qid_mapi ->
                                    case evalPartial qid_mapi d of
                                      | Some ci | ci ~= c -> Some ci 
                                      | _ -> None)
                          r_qid_maps
            in
            if r_c_s = [] then result_map
              else % let _ = writeLine(show c) in
                   update result_map d (c :: r_c_s))
     emptyMap qid_map1

op criticalOpMap(morphs: List Morphism): QIdMap(List QualifiedId)  =
  criticalQIdMap(map (project opMap) morphs)

op criticalTypeMap(morphs: List Morphism): QIdMap(List QualifiedId) =
  criticalQIdMap(map (project sortMap) morphs)

op mkApplyI(hd: MS.Term, args: List Terms, i: Nat): MS.Term =
  case args of
    | [] -> hd
    | ai :: r_args ->
      mkApplyI(mkApply(hd, ai@(min(i, length ai - 1))), r_args, i)

op replaceType(ty: Sort, src_ty: Sort, trg_ty: Sort): Sort =
  mapSort (id, fn sty -> if equalType?(sty, src_ty) then trg_ty else sty, id) ty

op mkRedundantDef(dfn: MS.Term, src_ty: Sort, trg_ty: Sort, test_fix_fn: MS.Term, ty_targets: Sorts,
                  op_target_qids: QualifiedIds, spc: Spec): MS.Term =
  let op_targets = map (fn op_qid ->
                          let Some info = findTheOp(spc, op_qid) in
                          mkInfixOp(op_qid, info.fixity, inferType(spc, info.dfn)))
                     op_target_qids
  in
  let def convertDef(tm) =
        case tm of
          | Pi(tvs, stm, a) -> Pi(tvs, convertDef(stm), a)
          | SortedTerm(stm, ty, a) -> SortedTerm(convertDefTyArgs(stm, ty, [], []), convertType ty, a)
          | _ -> convertDefTyArgs(tm, inferType(spc, tm), [], [])
      def convertDefTyArgs(tm: MS.Term, ty: Sort, args: List Terms, src_params: Ids): MS.Term =
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
            let main_bod =
                if equalType?(ty, src_ty)
                  then mkTuple(tabulate(length op_targets,
                                        fn i -> mkApplyI(op_targets@i, args, i)))
                else mkApplyI(op_targets@0, args, 0)
            in
            %% Add test_fix_fn lets
            foldl (fn (bod, v) ->
                     let pat = mkTuplePat(tabulate(length ty_targets,
                                               fn i -> mkVarPat(v^"__"^show i, ty_targets@i)))
                     in
                     mkLet([(pat, mkApply(test_fix_fn, patToTerm pat))], bod))
              main_bod src_params
      def convertType ty = replaceType(ty, src_ty, trg_ty)
      def convertPat(pat: Pattern): Pattern =
        mapPattern (id, id,
                    fn pat ->
                      case pat of
                        | VarPat((v,ty), _) | equalType?(ty, src_ty) ->
                          mkTuplePat(tabulate(length ty_targets,
                                              fn i -> mkVarPat(v^"__"^show i, ty_targets@i)))
                        | _ -> pat)
          pat
      def convertPatToArg(pat: Pattern, i: Nat): MS.Term =
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

op findUniversalIdentity(ty: Sort, term: MS.Term): Option(Var * MS.Term) =
  let def findId(t, universals: Vars) =
        case t of
          | Apply(Fun(Equals,_,_), Record([(_,Var(v, _)), (_, rhs as Apply _)], _),_) ->
            % let _ = writeLine("findUniversalIdentity:\n"^printTerm t) in
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

op findIdentityExpr(ty: Sort, spc: Spec): Option(Var * MS.Term) =
  foldlSpecElements (fn (result, el) ->
                       if some? result then result
                       else case el of
                              | Property(_,_,_,term,_) ->
                                findUniversalIdentity(ty, term)
                              | _ -> None)
    None spc.elements

op prependIdInQId(Qualified(q, id): QualifiedId, prefix: String): QualifiedId =
  Qualified(q, prefix ^ id)

op randomCheck?Appl: MS.Term = mkAppl(mkOp(Qualified("SemanticError", "randomCheck?"),
                                           mkArrow(mkProduct[], boolSort)),
                                      [])

op mkWarningForm(warn_str: String): MS.Term =
  mkApply(mkOp(Qualified("System", "warn"), mkArrow(stringSort, voidType)),
          mkString warn_str)

op mkTestFixFunction(primary_ty_qid: QualifiedId, primary_ty: Sort, ty_targets: Sorts, pos: Position,
                     opt_qual: Option Qualifier, ops_map: QIdMap(List QualifiedId), spc: Spec, new_spc: Spec)
  : Env(QualifiedId * MS.Term) =
  case findIdentityExpr(primary_ty, spc) of
    | None -> raise(TypeCheck (pos, "Can't find identity theorem for type: "
                           ^ printSort primary_ty))
    | Some(ident_param, ident_exp) ->
  let test_fix_fn_qid = makeDerivedQId spc (prependIdInQId(primary_ty_qid, "TestFix__")) opt_qual in
  let arg_vars = tabulate(length ty_targets, fn i -> ("x_"^show i, ty_targets@i)) in
  let param = mkTuplePat(map mkVarPat arg_vars) in
  let arg = mkTuple(map mkVar arg_vars) in
  let subtype_pred_tms = map (fn (v,ty) -> simplifiedApply(subtypePredicate(ty, new_spc), mkVar(v,ty), spc)) arg_vars in
  let def mkTestFixBody(subtype_pred_tms) =
         if length arg_vars = 2
          then MS.mkIfThenElse(subtype_pred_tms@0,
                               MS.mkIfThenElse(subtype_pred_tms@1, mkTuple(map mkVar arg_vars),
                                               mkSeq[mkWarningForm("Component 2 of "^show primary_ty_qid^" corrupted! Recomputing from component 1"),
                                                     mkTuple[mkVar(arg_vars@0),
                                                             mkConverterFromIdFun(0, 1, mkVar(arg_vars@0))]]),
                               MS.mkIfThenElse(subtype_pred_tms@1, 
                                               mkSeq[mkWarningForm("Component 1 of "^show primary_ty_qid^" corrupted! Recomputing from component 2"),
                                                     mkTuple[mkConverterFromIdFun(1, 0, mkVar(arg_vars@1)),
                                                             mkVar(arg_vars@1)]],
                                               mkSeq[mkWarningForm("All implementations of "^show primary_ty_qid^" corrupted!"),
                                                     mkTuple(map mkVar arg_vars)]))
          else mkString "mkTestFixBody in RedundantErrorCorrecting only implemented for two"
      def mkConverterFromIdFun(src_ty_ind, trg_ty_ind, src_var) =
        mapTerm(fn t ->
                  case t of
                    | Var(v, _) | equalVar?(v, ident_param) -> src_var
                    | Fun(Op(qid, fx), f_ty, a) ->
                      (case evalPartial ops_map qid of
                         | None -> t
                         | Some op_qids ->
                       case arrowOpt(spc, f_ty) of
                         | None -> t
                         | Some(dom, rng) ->
                       case rng of
                         | Base(ty_qid, _, _) | ty_qid = primary_ty_qid ->
                           Fun(Op(op_qids@trg_ty_ind, fx), mkArrow(dom, ty_targets@trg_ty_ind), a)
                         | _ ->
                           if primary_ty_qid in? typesInType dom
                             then Fun(Op(op_qids@src_ty_ind, fx), mkArrow(replaceType(dom, primary_ty, ty_targets@src_ty_ind), rng), a)
                           else t)
                    | _ -> t                ,
                id, id)
          ident_exp
  in
  let fix_body = mkTestFixBody(subtype_pred_tms) in
  let check_fn = mkLambda(param, MS.mkIfThenElse(randomCheck?Appl, simplify spc fix_body, arg)) in
  return(test_fix_fn_qid, check_fn)

%% Defined in /Languages/SpecCalculus/Semantics/Evaluate/Spec.sw
op SpecCalc.mergeImport: SCTerm -> Spec -> Spec -> Position -> Env Spec

op redundantErrorCorrecting (spc: Spec) (morphs: List(SCTerm * Morphism)) (opt_qual: Option Qualifier) (tracing?: Bool): Env(Spec * Bool) =
%%  return(spc, tracing?) (*
  let {sorts = spc_types, ops = spc_ops, elements = _, qualifier = _} = spc in
  let ((_,pos), morph1) :: _ = morphs in
  {morphs2 <- return(map (fn (_,yy) -> yy) morphs);
   ops_map <- return(criticalOpMap morphs2);      % Maps source ops to list of ops (when mapped differently)
   types_map <- return(criticalTypeMap morphs2);  % Maps source types to list of types -- should only be one
   trg_spcs <- return(map (project cod) morphs2);
   types_map_l <- return(mapToList types_map);
   when (length types_map_l ~= 1)
      (raise(TypeCheck (pos, "Should be exactly 1 type mapped differently by morphisms:\n"
                           ^ foldr (fn ((qid,_), s) -> show qid^s) "" (map head (mapToList types_map)))));
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

end-spec
