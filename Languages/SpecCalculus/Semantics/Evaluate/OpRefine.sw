(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

SpecCalc qualifying spec 
  import Signature
  import Spec
  import UnitId/Utilities                             % for uidToString, if used...

  def SpecCalc.evaluateOpRefine (spec_tm, op_elts) pos =
    {
     unitId <- getCurrentUID;
     print (";;; Elaborating op-refinement at " ^ (uidToString unitId) ^ "\n");
     spec_value_info  as (spec_value,  spec_timestamp,  spec_dep_UIDs)  <- evaluateTermInfo spec_tm;
     coercedSpecValue <- return (coerceToSpec spec_value);
     case coercedSpecValue of
       | Spec spc ->
         {
	  pos_spec <- evaluateSpecEltElems spc op_elts;
	  elaborated_spec <- elaborateSpecM pos_spec;
	  compressed_spec <- complainIfAmbiguous elaborated_spec pos; % (compressDefs elaborated_spec) pos;
          ordered_spec <- return(adjustElementOrder compressed_spec);
	  return (Spec ordered_spec, spec_timestamp, spec_dep_UIDs)
	  }
       | _  -> raise (TypeCheck (positionOf spec_tm, "op refinement attempted on a non-spec"))
     }

  op  evaluateSpecEltElems : Spec -> SpecElemTerms -> SpecCalc.Env Spec
  def evaluateSpecEltElems src_spec elts = 
    {src_spec <- return(exposeOpsForRefine(src_spec, elts));
     (spc,opt_el,pragmas) <- foldrM evaluateSpecEltElem (src_spec, None, []) elts;
     let spc = if pragmas = [] then spc else addElementsBeforeOrAtEnd(spc, pragmas, opt_el) in
     return spc}

  op  evaluateSpecEltElem : (Spec * Option SpecElement * SpecElements) -> SpecElemTerm 
      -> SpecCalc.Env (Spec * Option SpecElement * SpecElements)
  def evaluateSpecEltElem (spc, opt_next_el, pragmas) (elem, pos) =
    %let _ = writeLine("opt_next_el: "^anyToString opt_next_el^"\n"^printSpec spc) in
    case elem of
      | Op(names, fxty, refine?, dfn) ->
        {(spc,next_el) <- addOrRefineOp names fxty refine? dfn spc pos opt_next_el false;
         let spc = addElementsAfterConjecture(spc, pragmas, next_el) in
         return (spc,Some next_el,[])}
      | Type(names, ty_defn) ->
        {(spc,next_el) <- addOrRefineType names ty_defn spc pos opt_next_el false false;
         let spc = addElementsAfterConjecture(spc, pragmas, next_el) in
         return (spc,Some next_el,[])}
      | Pragma(prefix, body, postfix) ->
        let prag = Pragma(prefix, body, postfix, pos) in
        return (spc, opt_next_el, prag::pragmas)
      | _ -> raise (SpecError(pos,"Given refinement element is not an op definition."))

  op exposeOpsForRefine(spc: Spec, refine_elts: SpecElemTerms): Spec =
    let ops = mapPartial (fn (elem,_) ->
                                 case elem of
                                   | Op(op_id::_, _, _, _) -> Some op_id
                                   | _ -> None)
                refine_elts
    in
    let tys = mapPartial (fn (elem,_) ->
                                 case elem of
                                   | Type(ty_id::_, _) -> Some ty_id
                                   | _ -> None)
                refine_elts
    in
    let def maybeUnfoldImports(elts) =
          foldl (fn (new_elts, el) ->
                   case el of
                     | Import(_, im_spc, im_elts, _)
                         | exists? (fn op_id -> some?(findTheOp  (im_spc, op_id))) ops
                          || exists? (fn ty_id -> some?(findTheType(im_spc, ty_id))) tys
                        ->
                        maybeUnfoldImports im_elts ++ new_elts
                     | _ -> el::new_elts)
            [] elts
    in
    let new_elts = reverse(maybeUnfoldImports spc.elements) in
    setElements(spc, new_elts)

endspec
