Script qualifying
spec
 import /Languages/SpecCalculus/Semantics/Monad

 op criticalQIdMap(qid_maps: List QualifiedIdMap): PolyMap.Map (QualifiedId, List QualifiedId) =
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

 op criticalOpMap(morphs: List Morphism): PolyMap.Map (QualifiedId, List QualifiedId)  =
   criticalQIdMap(map (project opMap) morphs)
                  
 op criticalTypeMap(morphs: List Morphism): PolyMap.Map (QualifiedId, List QualifiedId)  =
   criticalQIdMap(map (project sortMap) morphs)

   

 op redundantErrorCorrecting (spc: Spec) (morphs: List(SCTerm * Morphism)) (opt_qual: Option Qualifier) (tracing?: Bool): SpecCalc.Env(Spec * Bool) =
   {morphs2 <- return(map (fn (_,y) -> y) morphs);
    ((_,pos), _) :: _ <- return morphs;
    ops_map <- return(criticalOpMap morphs2);
    types_map <- return(criticalTypeMap morphs2);
    if length(mapToList types_map) ~= 1
      then raise(TypeCheck (pos, "More than 1 type mapped by morphisms:\n"^foldr (fn ((qid,_), s) -> show qid^s) "" (map head (mapToList types_map))))
    else
    
     return(spc, tracing?)}

end-spec
