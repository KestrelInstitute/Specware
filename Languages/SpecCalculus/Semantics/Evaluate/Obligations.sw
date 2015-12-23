(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(*
The spec calculus Obligations construct takes a spec or a a morphism and 
returns a spec including the proof obligations as conjectures.
*)

SpecCalc qualifying spec 

  import /Languages/MetaSlang/Specs/TypeObligations
  import /Languages/MetaSlang/Specs/CompressSpec
  import /Languages/MetaSlang/Transformations/DefToAxiom

  import Signature                 % including SCTerm
  import UnitId/Utilities  
  import Spec/ComplainIfAmbiguous

  def SpecCalc.evaluateObligations term = {
     unitId <- getCurrentUID;
     print (";;; Elaborating obligator at " ^ (uidToString unitId) ^ "\n");
     (value, time_stamp, dep_UIDs) <- evaluateTermInfo term;
      case value of

	| Spec  spc -> {ob_spec <- return (specObligations (spc,term));
			compressed_spec <- complainIfAmbiguous (compressDefs ob_spec)
			                     (positionOf term);
			return (Spec compressed_spec, time_stamp, dep_UIDs)}

	| Morph sm  -> {globalContext <- getGlobalContext;
			ob_spec <- return (morphismObligations (sm,globalContext,positionOf term));
			compressed_spec <- complainIfAmbiguous (compressDefs ob_spec)
			                     (positionOf term);
			return (Spec compressed_spec, time_stamp, dep_UIDs)}

        | Other  other -> evaluateOtherObligations other (positionOf term)

	| _ -> raise (Unsupported (positionOf term,
				   "Can create obligations for Specs and Morphisms only"))
		      }
 
  op morphismObligations: Morphism * GlobalContext * Position -> Spec
  def morphismObligations ({dom, cod, typeMap, opMap, pragmas, sm_tm=_},globalContext,pos) =
    % let tcc = MetaSlangTypeCheck.checkSpec(domain2) in
    let opFixityMap = addOpFixity cod opMap in
    let translated_dom_axioms =
        foldrSpecElements (fn (el,newprops) ->
			   case el of
			     | Property(Axiom, name, tyvars, fm, _) ->
			       let new_fm = translateTerm (fm, typeMap, opFixityMap) in
			       if existsSpecElement?
				    (fn el ->
				     case el of
				       | Property(_,_,tvs,fm1,_) ->
				         tyvars = tvs && equivTerm? cod (new_fm,fm1)
				       | _ -> false)
				    cod.elements
			       then newprops
			       else Cons(mkConjecture(name, tyvars, new_fm),newprops)
			   | _ -> newprops) 
	  [] dom.elements
    in
    let dom_definitions_not_in_cod
       = foldriAQualifierMap
           (fn (q, id, dom_info, rdefs) ->
	    case opInfoDefs dom_info of
	      | [] -> rdefs
	      | dom_def1 :: _ ->
                let trans_def1 = translateTerm(dom_def1, typeMap, opFixityMap) in
                let n_qid as Qualified(n_q, n_id) = translateQId opMap (Qualified(q, id)) in
		case findAQualifierMap (cod.ops, n_q, n_id) of
		  | Some cod_info | termIn?(trans_def1, opInfoDefs cod_info) -> rdefs
                  | _ -> defToConjecture(dom, n_qid, q, id, trans_def1) ++ rdefs)
	   [] 
	   dom.ops
    in
    let obligation_props = translated_dom_axioms ++ dom_definitions_not_in_cod in
    let cod_tm = case findUnitIdForUnit(Spec cod,globalContext) of
		   | Some unitId -> (UnitId (SpecPath_Relative unitId),pos)
		   | _ -> 
                     %% TODO: determine real timestamp and dependencies
                     let cod_value_info = (Spec cod, oldestTimeStamp, []) in
		     (Quote cod_value_info,pos)
    in
    let ob_spc = cod << {elements =  [Import(cod_tm,cod,cod.elements,noPos)] ++ obligation_props
                                     ++ map (fn ((p1,p2,p3),pos) -> Pragma(p1,p2,p3,pos)) pragmas} in
    ob_spc

  op defToConjecture (spc: Spec, opName: QualifiedId, q: Qualifier, id: Id, term: MSTerm): SpecElements =
    let srt = inferType (spc, term) in
    let initialFmla = head (unLambdaDef(spc, srt, opName, term)) in
    let liftedFmlas = removePatternTop(spc, initialFmla) in
    %let simplifiedLiftedFmlas = map (fn (fmla) -> simplify(spc, fmla)) liftedFmlas in
    map (fn(fmla) -> mkConjecture(Qualified (q, id ^ "_def"), [], fmla)) liftedFmlas

  op translateQId(m: QualifiedIdMap) (qid: QualifiedId): QualifiedId =
    case evalPartial m qid of
      | Some nqid -> nqid
      | None -> qid

  op translateQIdFixity(m: MorphismOpFixityMap) (qid: QualifiedId) (old_fx: Fixity): QualifiedId * Fixity =
    case evalPartial m qid of
      | Some nqid_fx -> nqid_fx
      | None -> (qid, old_fx)

  op translateTerm: MSTerm * MorphismTypeMap * MorphismOpFixityMap -> MSTerm
  def translateTerm (tm, typeMap, opFixityMap) =
    let def translateType srt =
	  case srt of
	    | Base (QId, srts, a) -> 
	      let cod_srt =
	          (case translateQId typeMap QId of
		     | Qualified("Bool", "Bool") -> Boolean a
		     | cod_qid -> Base (cod_qid, srts, a))
	      in
		cod_srt
	    | _ -> srt
	def translateTerm trm =
	  case trm of
	    | Fun (Op (dom_qid, fixity), srt, a) -> 
	      let (cod_qid as Qualified (q, id), fixity) = translateQIdFixity opFixityMap dom_qid fixity in
	      let fun =
	          (case q of
		     | "Bool" ->
	               (case id of 
			  | "~"   -> Not
			  | "&&"  -> 
			    let _ = toScreen ("\n?? Translating " ^ (printQualifiedId dom_qid) ^  " to '&&' ??\n") in
			    And
			  | "||"  -> 
			    let _ = toScreen ("\n?? Translating " ^ (printQualifiedId dom_qid) ^  " to '||' ??\n") in
			    Or
			  | "=>"  -> 
			    let _ = toScreen ("\n?? Translating " ^ (printQualifiedId dom_qid) ^  " to '=>' ??\n") in
			    Implies
			  | "<=>" -> Iff
			  | "="   -> Equals
			  | "~="  -> NotEquals
			  | _ -> Op (cod_qid, fixity))
		     | _ -> Op (cod_qid, fixity))
	      in
		Fun (fun, srt, a)
	    | _ -> trm
    in 
    mapTerm (translateTerm, translateType, id) tm

op SM_PragmaToElement (pragma as ((s1, s2, s3), pos): SM_Pragma): SpecElement =
  Pragma(s1, s2, s3, pos)

op addMorphismTheorems (cod_spc: Spec) (sm: Morphism): Spec =
  let opFixityMap = addOpFixity cod_spc sm.opMap in
  let new_theorems =
        foldrSpecElements (fn (el, new_theorems) ->
			   case el of
			     | Property(_, name, tyvars, fm, _) ->
			       let new_fm = translateTerm (fm, sm.typeMap, opFixityMap) in
			       if existsSpecElement?
				    (fn el ->
				     case el of
				       | Property(_,_,tvs,fm1,_) ->
				         tyvars = tvs && equivTerm? cod_spc (new_fm,fm1)
				       | _ -> false)
				    cod_spc.elements
			       then new_theorems
			       else mkTheorem(name, tyvars, new_fm) :: new_theorems
                           | Pragma(s1, s2, s3, _) | ~(existsSpecElement? (fn eli -> equalSpecElement?(eli, el)) cod_spc.elements) ->
                             el :: new_theorems
			   | _ -> new_theorems)
          [] sm.dom.elements
  in
  let sm_pragma_elts = map SM_PragmaToElement sm.pragmas in
  let sm_cod_imports = filterSpecElements (fn el ->
                                             case el of
                                               | Import (_, i_sp, _, _) -> i_sp = sm.cod
                                               | _ -> false)
                         cod_spc.elements
  in
  let import_el = case findRightmost (fn el ->
                                        case el of
                                          | Import (_, i_sp, _, _) -> i_sp = sm.cod
                                          | _ -> false)
                         cod_spc.elements of
                    | Some el -> el
                    | None ->
                  case findRightmost (fn el ->
                                        case el of
                                          | Import _ -> true
                                          | _ -> false)
                         cod_spc.elements of
                    | Some el -> el
                    | None -> last  cod_spc.elements
  in
  addElementsAfter(cod_spc, new_theorems ++ sm_pragma_elts, import_el)

  op specObligations : Spec * SCTerm -> Spec % Result was Env Spec, but can there be errors, etc.?
  def specObligations (spc, spcTerm) = 
    %% So far only does type conditions (for subtypes
    %% TODO: Add obligations found by definitions, etc.
    %% Second argument should be specRef for spc (showTerm blows up)
    let pos = positionOf spcTerm in
    makeTypeCheckObligationSpec (spc, false, FALSE, positionSource pos)
endspec
