\subsection{Evalution of Spec Morphisms}

\begin{spec}
SpecCalc qualifying spec {
  import Signature 
  import Spec/Utilities                               % for coerceToSpec
  import /Library/Legacy/DataStructures/ListUtilities % for listUnion
  import UnitId/Utilities                                % for uidToString, if used...
\end{spec}

For morphisms, evaluate the domain and codomain terms, and check
coherence conditions of the morphism elements. 

\begin{spec}
  def SpecCalc.evaluateSpecMorph (domTerm,codTerm,morphRules) = {
    unitId <- getCurrentUID;
    print (";;; Elaborating spec-morphism at " ^ (uidToString unitId) ^ "\n");
    (domValue,domTimeStamp,domDepUIDs) <- evaluateTermInfo domTerm;
    (codValue,codTimeStamp,codDepUIDs) <- evaluateTermInfo codTerm;
    coercedDomValue <- return (coerceToSpec domValue);
    coercedCodValue <- return (coerceToSpec codValue);
    case (coercedDomValue, coercedCodValue) of
      | (Spec spc1, Spec spc2) -> {
            morph <- makeSpecMorphism spc1 spc2 morphRules (positionOf domTerm);
            return (Morph morph,max(domTimeStamp,codTimeStamp),
                    listUnion (domDepUIDs,codDepUIDs))
          }
      | (Other _, _) ->
          evaluateOtherSpecMorph (coercedDomValue,domTimeStamp,domDepUIDs)
                             (coercedCodValue,codTimeStamp,codDepUIDs) morphRules (positionOf domTerm)
      | (_, Other _) -> 
          evaluateOtherSpecMorph (coercedDomValue,domTimeStamp,domDepUIDs)
                             (coercedCodValue,codTimeStamp,codDepUIDs) morphRules (positionOf codTerm)
      | (Spec _, _) -> raise
          (TypeCheck (positionOf domTerm,
                      "domain of spec morphism is not a spec"))
      | (_, Spec _) -> raise
          (TypeCheck (positionOf codTerm,
                      "codomain of spec morphism is not a spec"))

      | (_,_) -> raise
          (TypeCheck (positionOf domTerm,
                      "domain and codomain of spec morphism are not specs"))
    }

  op makeSpecMorphism : Spec -> Spec -> List (SpecMorphRule Position) -> Position -> Env Morphism
  def makeSpecMorphism domSpec codSpec rawMapping position = {
      morph <- makeResolvedMapping domSpec codSpec rawMapping;
      buildSpecMorphism domSpec codSpec morph position
    }

  op makeResolvedMapping :
        Spec
     -> Spec
     -> List (SpecMorphRule Position)
     -> Env ((AQualifierMap QualifiedId) * (AQualifierMap QualifiedId))

  def makeResolvedMapping dom_spec cod_spec sm_rules =
    let 
      def findCodOp position qid =
        case findAllOps (cod_spec, qid) of
          | ((found_qid as Qualified (found_qualifier,_))::_,_,_,_)::rs -> {
                when (~(rs = []) & ~(found_qualifier = UnQualified))
                  (raise (MorphError (position, "Ambiguous target op " ^ (printQualifiedId qid))));
                return found_qid
              }
          | _ -> raise (MorphError (position, "Unrecognized target op " ^ (printQualifiedId qid)))

      def findCodSort position qid =
        case findAllSorts (cod_spec, qid) of
          | ((found_qid as Qualified (found_qualifier,_))::_,_,_)::rs -> {
                when (~(rs = []) & ~(found_qualifier = UnQualified))
                  (raise (MorphError (position, "Ambiguous target sort " ^ (printQualifiedId qid))));
                return found_qid
              }
          | _ -> raise (MorphError (position, "Unrecognized target sort " ^ (printQualifiedId qid)))

      def insert (op_map,sort_map) ((sm_rule,position) : (SpecMorphRule Position)) =
        case sm_rule of
          | Sort (dom_qid, cod_qid) ->
            (case findAllSorts (dom_spec, dom_qid) of
               | ((Qualified (found_qualifier, found_id))::_,_,_)::rs  -> {
                     when (~(rs = []) & ~(found_qualifier = UnQualified))
                       (raise (MorphError (position, "Ambiguous source sort " ^ (printQualifiedId dom_qid))));
                     case findAQualifierMap (sort_map, found_qualifier, found_id) of
                       | None -> {
                             cod_sort <- findCodSort position cod_qid;
                             return (op_map, 
                                   insertAQualifierMap (sort_map, found_qualifier, found_id, cod_sort))
                           }
                       | _ -> raise (MorphError (position, "Multiple rules for source sort "
                                                           ^ (printQualifiedId dom_qid)))
                   }
               | _ -> raise (MorphError (position, "Unrecognized source sort " ^ (printQualifiedId dom_qid))))

          | Op ((dom_qid, opt_dom_sort), (cod_qid, opt_cod_sort)) ->
            %% TODO:  Currently ignores sort information.
            (case findAllOps (dom_spec, dom_qid) of
               | ((Qualified (found_qualifier, found_id))::_,_,_,_)::rs -> {
                     when (~(rs = []) & ~(found_qualifier = UnQualified))
                        (raise (MorphError (position, "Ambiguous source op " ^ (printQualifiedId dom_qid))));
                     case findAQualifierMap (op_map, found_qualifier, found_id) of
                       | None -> {
                             cod_op <- findCodOp position cod_qid;
                             return (insertAQualifierMap (op_map, found_qualifier, found_id, cod_op),
                                     sort_map)
                           }
                       | _ -> raise (MorphError (position, "Multiple rules for source op "
                                                          ^ (printQualifiedId dom_qid)))
                   }
               | _ -> raise (MorphError (position, "Unrecognized source op " ^ (printQualifiedId dom_qid))))

          | Ambiguous (dom_qid, cod_qid) ->
              let dom_sorts = findAllSorts (dom_spec, dom_qid) in
              let dom_ops   = findAllOps   (dom_spec, dom_qid) in
              case (dom_sorts, dom_ops) of
                | ([], []) ->
                    raise (MorphError (position, "Unrecognized source sort/op identifier "
                                                 ^ (printQualifiedId dom_qid)))
                | (((Qualified (found_qualifier, found_id))::_,_,_)::rs, [])  -> {
                       when (~(rs = []) & ~(found_qualifier = UnQualified))
                         (raise (MorphError (position, "Ambiguous source sort "
                                                       ^ (printQualifiedId dom_qid))));
                       case findAQualifierMap (sort_map, found_qualifier, found_id) of
                         | None -> {
                               cod_sort <- findCodSort position cod_qid;
                               return (op_map, 
                                       insertAQualifierMap (sort_map, found_qualifier, found_id, cod_sort))
                             }
                         | _ -> raise (MorphError (position, "Multiple rules for source sort "
                                                             ^ (printQualifiedId dom_qid)))
                    }
                | ([], ((Qualified (found_qualifier, found_id))::_,_,_,_)::rs) -> {
                      when (~(rs = []) & ~(found_qualifier = UnQualified))
                        (raise (MorphError (position, "Ambiguous source op "
                                                      ^ (printQualifiedId dom_qid))));
                      case findAQualifierMap (op_map, found_qualifier, found_id) of
                        | None -> {
                              cod_op <- findCodOp position cod_qid;
                              return (insertAQualifierMap (op_map, found_qualifier, found_id, cod_op),
                                      sort_map)
                            }
                        | _ -> raise (MorphError (position, "Multiple rules for source op "
                                                            ^ (printQualifiedId dom_qid)))
                    }
                | (_, _) ->
                    raise (MorphError (position, "Ambiguous source sort/op identifier "
                                                 ^ (printQualifiedId dom_qid)))
    in
       foldM insert (emptyAQualifierMap,emptyAQualifierMap) sm_rules

  op buildSpecMorphism :
         Spec 
      -> Spec 
      -> (AQualifierMap QualifiedId) * (AQualifierMap QualifiedId)
      -> Position
      -> Env Morphism
  def buildSpecMorphism domSpec codSpec (opMap,sortMap) position = {
      newOpMap <- completeMorphismMap opMap domSpec.ops codSpec.ops position;
      newSortMap <- completeMorphismMap sortMap domSpec.sorts codSpec.sorts position;
      return {
          dom     = domSpec,
          cod     = codSpec,
          opMap   = newOpMap,
          sortMap = newSortMap
        }
    }
\end{spec}

The first pass to creating a morphism doesn't mention the ops
and sorts that ops and sorts with the same name. The function
below completes the map.

A better strategy would be to use a different map theory that
allows us to omit the identity components.

If we explicitly indicate a mapping, use that
TODO: What if explicit map is to non-existant target?
Should we check to see if qid is in cod_map??  

\begin{spec}
  op completeMorphismMap:
    fa(a,b) AQualifierMap QualifiedId
         -> AQualifierMap a
         -> AQualifierMap b
         -> Position
         -> Env (PolyMap.Map (QualifiedId, QualifiedId))

  def completeMorphismMap trans_map dom_map cod_map position =
    let def compl (qualifier, id, _ (* val *), new_map) =
      case findAQualifierMap (trans_map, qualifier, id) of
        | Some qid -> return (update new_map (Qualified (qualifier,id)) qid) % explicit
        | _ ->
           %% Otherwise, if the identity map works, use that
           case findAQualifierMap (cod_map, qualifier, id) of
             | Some _ -> return (update new_map (Qualified (qualifier,id)) (Qualified (qualifier,id))) % identity
             | _ -> raise (MorphError (position, "No mapping for " ^ qualifier ^ "." ^ id)) %return new_map
    in
      foldOverQualifierMap compl emptyMap dom_map
}
\end{spec}
