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

op redundantErrorCorrecting (spc: Spec) (morphs: List(SCTerm * Morphism)) (opt_qual: Option Qualifier) (tracing?: Bool): SpecCalc.Env(Spec * Bool) =
  return(spc, tracing?)
(*
  {morphs2 <- return(map (fn (_,y) -> y) morphs);
   ((_,pos), morph1) :: _ <- return morphs;
   ops_map <- return(criticalOpMap morphs2);
   types_map <- return(criticalTypeMap morphs2);
   types_map_l <- return(mapToList types_map);
   when (length types_map_l ~= 1)
      (raise(TypeCheck (pos, "Should be exactly 1 type mapped differently by morphisms:\n"
                           ^ foldr (fn ((qid,_), s) -> show qid^s) "" (map head (mapToList types_map)))));
   (ty_qid, _) :: _ <- return types_map_l;
   new_ty_qid <- return(makeDerivedQId spc ty_qid opt_qual);
   src_spc <- return morph1.dom;
   when (src_spc ~= spc)
     (raise(TypeCheck (pos, "Transformed spec should be target of morphisms.")));
   Some src_spc_uid <- return(findRelativeUIDforValue(Spec src_spc));
   new_elts <- return(Import((UnitId src_spc_uid, noPos), spc, spc.elements, noPos)
                        :: SortDef(new_ty_qid, noPos)
                        :: foldMap (fn elts -> fn qid -> fn _ ->
                                      Op(makeDerivedQId spc qid opt_qual, true, noPos) :: elts)
                             [] ops_map);

   return(spc, tracing?)} *)

end-spec
