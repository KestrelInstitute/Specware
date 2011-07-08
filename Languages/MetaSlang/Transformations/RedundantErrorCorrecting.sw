Script qualifying
spec
import /Languages/SpecCalculus/Semantics/Monad
import /Languages/MetaSlang/Specs/Utilities
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
              else update result_map d (c :: r_c_s))
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

op mkRedundantDef(dfn: MS.Term, src_ty: Sort, trg_ty: Sort, ty_targets: Sorts, op_target_qids: QualifiedIds, spc: Spec): MS.Term =
  let op_targets = map (fn op_qid ->
                          let Some info = findTheOp(spc, op_qid) in
                          mkInfixOp(op_qid, info.fixity, inferType(spc, info.dfn)))
                     op_target_qids
  in
  let def convertDef(tm) =
        case tm of
          | Pi(tvs, stm, a) -> Pi(tvs, convertDef(stm), a)
          | SortedTerm(stm, ty, a) -> SortedTerm(convertDefTyArgs(stm, ty, []), convertType ty, a)
          | _ -> convertDefTyArgs(tm, inferType(spc, tm), [])
      def convertDefTyArgs(tm, ty, args) =
        case tm of
          | Lambda([(pat, pred, bod)], a) ->
            let new_args = tabulate(length ty_targets, fn i -> convertPatToArg(pat, i)) in
            let Some rng = rangeOpt(spc, ty) in
            Lambda([(convertPat pat, pred, convertDefTyArgs(bod, rng, args ++ [new_args]))], a)
          | _ ->
            if equalType?(ty, src_ty)
              then mkTuple(tabulate(length op_targets,
                                    fn i -> mkApplyI(op_targets@i, args, i)))
              else mkApplyI(op_targets@0, args, 0)
      def convertType ty =
        mapSort (id, fn sty -> if equalType?(sty, src_ty) then trg_ty else sty, id) ty
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
        case patternToTerm pati of
          | Some tm -> tm
          | None -> mkNat i   %% Should check to make sure this cannot happen!
  in
  convertDef dfn

%% Defined in /Languages/SpecCalculus/Semantics/Evaluate/Spec.sw
op SpecCalc.mergeImport: SCTerm -> Spec -> Spec -> Position -> Env Spec

op redundantErrorCorrecting (spc: Spec) (morphs: List(SCTerm * Morphism)) (opt_qual: Option Qualifier) (tracing?: Bool): Env(Spec * Bool) =
%%  return(spc, tracing?) (*
  let {sorts = spc_types, ops = spc_ops, elements = _, qualifier = _} = spc in
  let ((_,pos), morph1) :: _ = morphs in
  {morphs2 <- return(map (fn (_,y) -> y) morphs);
   ops_map <- return(criticalOpMap morphs2);
   types_map <- return(criticalTypeMap morphs2);
   trg_spcs <- return(map (project cod) morphs2);
   types_map_l <- return(mapToList types_map);
   when (length types_map_l ~= 1)
      (raise(TypeCheck (pos, "Should be exactly 1 type mapped differently by morphisms:\n"
                           ^ foldr (fn ((qid,_), s) -> show qid^s) "" (map head (mapToList types_map)))));
   (ty_qid, ty_target_qids) :: _ <- return types_map_l;
   ty_targets <- return(map (fn qid -> mkBase(qid, [])) ty_target_qids);
   new_ty_qid <- return(makeDerivedQId spc ty_qid opt_qual);
   src_spc <- return morph1.dom;
   when (src_spc ~= spc)
     (raise(TypeCheck (pos, "Transformed spec should be target of morphisms.")));
   new_spc <- foldM (fn spc -> fn imp_spec ->
                       let Some imp_spc_uid = findRelativeUIDforValue(Spec imp_spec) in
                       mergeImport (UnitId imp_spc_uid, noPos) imp_spec spc pos)
                emptySpec
                trg_spcs;
   new_spc <- return(addTypeDef(new_spc, new_ty_qid, mkProduct ty_targets));
   new_spc <- return(foldMap (fn new_spc -> fn qid -> fn op_target_qids ->
                                let Some opinfo = findTheOp(spc, qid) in
                                addOpDef(new_spc, makeDerivedQId spc qid opt_qual,
                                         opinfo.fixity,
                                         mkRedundantDef(opinfo.dfn, mkBase(ty_qid, []), mkBase(new_ty_qid, []),
                                                        ty_targets, op_target_qids, new_spc)))
                       new_spc ops_map);
   return(new_spc, tracing?)}      % *)

end-spec
