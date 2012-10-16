SpecCalc qualifying spec 
 import /Languages/SpecCalculus/Semantics/Environment
 import /Languages/SpecCalculus/AbstractSyntax/SCTerm  % SCTerm
 import AccessSpec
 import /Languages/MetaSlang/Specs/Environment
 import /Library/Legacy/DataStructures/TopSort

 op addType:  QualifiedIds -> MSType -> Spec -> Position -> SpecCalc.Env Spec
 op addOp  :  QualifiedIds -> Fixity -> Bool -> MSTerm -> Spec -> Position -> SpecCalc.Env Spec

  %% called by evaluateSpecElem 
 def addType new_names new_dfn old_spec pos =
   {(sp,_) <- addOrRefineType new_names new_dfn old_spec pos None true;
    return sp}

 op  addOrRefineType: QualifiedIds -> MSType -> Spec -> Position -> Option SpecElement -> Bool -> SpecCalc.Env (Spec * SpecElement)

 def addOrRefineType new_names new_dfn old_spec pos opt_next_el addOnly? =
  %%% some of the names may refer to previously declared types,
  %%% some of which may be identical
  %%% Collect the info's for such references
  let new_names = reverse (removeDuplicates new_names) in % don't let duplicate names get into a typeinfo!
  let new_names = map (addQualifier old_spec) new_names in
  let primaryName = head new_names in
  let new_info = {names = new_names, 
		  dfn   = new_dfn}
  in
  let old_infos = foldl (fn (old_infos,new_name) ->
                         case findTheType (old_spec, new_name) of
                           | Some info -> 
                             if exists? (fn old_info -> info = old_info) old_infos then
                               old_infos
                             else
                               Cons (info, old_infos)
                           | _ -> old_infos)
                        []
                        new_names
  in
  {
    mapM (fn name -> 
	  if false then    % basicQualifiedId? name then
	    raise (SpecError (pos, (printAliases new_names)^" is a basic type, hence cannot be redeclared."))
	  else
	    return ())
         new_names;
    new_types <-
     case old_infos of
       | [] ->
         %%  We're declaring a brand new type.
         return (foldl (fn (new_types, name as Qualified (q, id)) ->
                        insertAQualifierMap (new_types, q, id, new_info))
                       old_spec.types
                       new_names)
       | [old_info] ->
         %%  We're merging new information with a previously declared type.
         let combined_names = listUnion (old_info.names, new_names) in
	 let combined_names = removeDuplicates combined_names in % redundant?
	 let (old_tvs, old_srt) = unpackFirstTypeDef old_info in
	 let (new_tvs, new_srt) = unpackFirstTypeDef new_info in
         if equalTyVarSets?(new_tvs, old_tvs) then % TODO: for now at least, this is very literal -- should test for alpha-equivalence.
           (let old_dfn = old_info.dfn in
	    case (definedType? old_dfn, definedType? new_dfn) of
              | (false, false) ->
                %%  Old: Type S    [or S(A,B), etc.]
                %%  New: Type S    [or S(X,Y), etc.]
                raise (SpecError (pos, "Type "^(printAliases new_names)^" has been redeclared."))
              | (false,  true) ->
                %%  Old: Type S (A,B)
                %%  New: Type S (X,Y) = T(X,Y)
                % let _ = warn("Type "^(printAliases new_names)^" has been redeclared (Use spec substitution)") in
		let new_info = {names = combined_names, 
				dfn   = new_dfn}
		in
                return (foldl (fn (new_types, name as Qualified (q, id)) ->
                               insertAQualifierMap (new_types, q, id, new_info))
                              old_spec.types
                              combined_names)
%% Eventually disallow
%                raise (SpecError (pos, 
%                                  "Type "^(printAliases new_names)^" has been redeclared"
%                                  ^ "\n(Type refinement is no longer allowed -- use spec substitution)" ))
              | (true, false) ->
                %%  Old: Type S (X,Y) = T(X,Y)
                %%  New: Type S (A,B)
                raise (SpecError (pos, 
                                  "Type "^(printAliases new_names)^" has been redeclared"
                                  ^ "\n from "^ (printType old_dfn)))
	      | _ ->
                %%  Old: Type S (X,Y) = T(X,Y)
                %%  New: Type S (A,B) = W(A,B)
                raise (SpecError (pos, 
                                  "Type "^(printAliases new_names)^" has been redefined"
                                  ^ "\n from "^ (printType old_dfn)
                                  ^ "\n   to "^ (printType new_dfn))))
         else
           %%  Old: Type S (a)
           %%  New: Type S (x,y)
           raise (SpecError (pos, 
                           "Type "^(printAliases new_names)^" has been redeclared or redefined"
                           ^"\n with new type variables "^(printTyVars new_tvs)
                           ^"\n    differing from prior "^(printTyVars old_tvs)))
       | _ ->
         %%  We're trying to merge information with two or more previously declared types.
         raise (SpecError (pos, 
                         "Type "^(printAliases new_names)^" refers to multiple prior types"));
     sp <- return (setTypes (old_spec, new_types));
     let el = if definedType? new_dfn
                then TypeDef (primaryName, pos)
              else Type (primaryName, pos)
     in
     let sp = if exists? (fn eli -> equalSpecElement?(el, eli)) sp.elements then sp
              else if old_infos = [] || addOnly?
                     then addElementBeforeOrAtEnd(sp, el, opt_next_el)
              else let elts = foldr (fn (eli, elts) ->
                                       case eli of
                                         | TypeDef(qid,_) | qid = primaryName -> elts
                                         | Type(qid, _)   | qid = primaryName -> el::elts
                                         | _                                  -> eli::elts)
                                 [] sp.elements
                   in
                   if el in? elts
                     then setElements(sp, elts)
                   else addElementBeforeOrAtEnd(sp, el, opt_next_el)
     in
     return (sp, el)
    }

  %% called by evaluateSpecElem and LiftPattern
 def addOp new_names new_fixity refine? new_dfn old_spec pos =
   {(sp,_) <- addOrRefineOp new_names new_fixity refine? new_dfn old_spec pos None true;
    return sp}

 op  addOrRefineOp: QualifiedIds -> Fixity -> Bool -> MSTerm -> Spec -> Position -> Option SpecElement -> Bool
                  -> SpecCalc.Env(Spec * SpecElement)
 def addOrRefineOp new_names new_fixity refine? new_dfn old_spec pos opt_next_el addOnly? =
  %%% some of the names may refer to previously declared types,
  %%% some of which may be identical
  %%% Collect the info's for such references
  let new_names = reverse (removeDuplicates new_names) in % don't let duplicate names get into an opinfo!
  let new_names = map (addQualifier old_spec) new_names in
  let primaryName = head new_names in
  let new_info = {names  = new_names, 
		  fixity = new_fixity, 
		  dfn    = new_dfn,
		  fullyQualified? = false}
  in
  let old_infos = foldl (fn (old_infos, new_name) ->
                         case findTheOp (old_spec, new_name) of
                           | Some info -> 
                             if exists? (fn old_info -> info = old_info) old_infos then
                               old_infos
                             else
                               info :: old_infos
                           | _ -> old_infos)
                        []
                        new_names
  in
  let (old_infos, primaryName, new_info, new_names) =
      if old_infos = [] && refine? && unQualifiedId?(primaryName)
        then %% Implicit qualification
             (case findAllOps(old_spec, primaryName) of
                | [old_info] -> ([old_info], head(old_info.names),
                                 new_info << {names = old_info.names},
                                 old_info.names)
                | _ -> ([], primaryName, new_info, new_names))
      else (old_infos, primaryName, new_info, new_names)
  in {
    mapM (fn name -> 
	  if false then    %basicQualifiedId? name then
	    raise (SpecError (pos, (printAliases new_names)^" is a basic op, hence cannot be redeclared."))
	  else
	    return ())
         new_names;
   new_ops <-
   case old_infos of
     | [] ->
       %%  We're declaring a brand new op
       if refine?
         then raise (SpecError (pos, "Attempt to refine "^(printAliases new_names)^" which is not defined."))
       else
       return (foldl (fn (new_ops, name as Qualified (q, id)) ->
                      insertAQualifierMap (new_ops, q, id, new_info))
                     old_spec.ops
                     new_names)

     | [old_info] ->
       %%  We're merging new information with a previously declared op.
       (let old_dfn = old_info.dfn in
	let combined_names = listUnion (old_info.names, new_names) in
	let combined_names = removeDuplicates combined_names in % redundant?
	let (old_tvs, old_srt, old_tm) = unpackFirstOpDef old_info in
	let (new_tvs, new_srt, new_tm) = unpackFirstOpDef new_info in
        % let _ = if refine? then writeLine("Old: "^printAliases new_names^": "^printType old_srt^" =\n"^printTerm old_tm) else () in
        % let _ = if refine? then writeLine("New: "^printAliases new_names^": "^printType new_srt^" =\n"^printTerm new_tm) else () in
	let old_defined? = definedTerm? old_dfn in
	let new_defined? = definedTerm? new_dfn in
        case (old_defined?, new_defined?) of
          | (false, false) | refine? => equalType?(old_srt, new_srt) ->
            %%  Old: op foo : ...
            %%  New: op foo : ...
            raise (SpecError (pos, 
                              "Operator "^(printAliases new_names)^" has been redeclared"
                              ^ "\n from " ^ (printType (maybePiType (old_tvs, old_srt)))
                              ^ "\n   to " ^ (printType (maybePiType (new_tvs, new_srt)))))
          | (true, false) ->
	    %%  Old:  def foo ... = ...
	    %%  New:  op foo : ...
	    raise (SpecError (pos, 
			      "Operator "^(printAliases new_names)^" has been redeclared"
                              ^ "\n from " ^ (printTerm old_dfn)
                              ^ "\n   to " ^ (printTerm new_dfn)))
	  | _ ->
            %%  New: def foo 
	    (if ~addOnly?             %%  Old: op foo : ... or      (add definition)
	                              %%  Old: def foo : ... = ...  (replace definition)
               || refine?             %%  New: refine def foo : ... = ...  (add refined definition)
	       || ~old_defined? then  %%  Old: op foo : ...
	       let happy? = (case new_tvs of
			       | [] ->
			       %%  Old:  op foo : ...
			       %%  New:  def foo x = ...
			       true
			       | _ -> 
			       %%  Old:  op foo : ...
			       %%  New:  def [a,b,c] foo ... = ...
			       equalTyVarSets?(new_tvs, old_tvs))
	       in
	       (if happy? then
		  let combined_srt = (case (old_srt, new_srt) of
					 | (Any _,       _) -> new_srt
					 | (_,       Any _) -> old_srt
					 | (MetaTyVar _, _) -> new_srt
					 | (_, MetaTyVar _) -> old_srt
                                         % | _ | existsInType? (embed? MetaTyVar) new_srt -> old_srt
                                         | _ | refine? -> combineSubTypes(old_srt, new_srt, old_tm, new_tm)
					 | _ -> old_srt)   % TODO:  maybeAndType ([old_srt, new_srt], typeAnn new_srt)
		  in
                  let new_tm = if refine? && old_defined? then
                                 %% Reverse order so most refined term first
                                 And (new_tm :: opDefInnerTerms old_info, termAnn new_tm)
                               else 
                                 new_tm
                  in
                  % let _ = if refine? then writeLine("refine "^(printAliases new_names)^": "^printType combined_srt^" =\n"^printTerm new_tm) else () in
		  let combined_dfn = if false && refine? && ~old_defined? then
                                       let triples = unpackTypedTerms old_info.dfn in
                                       maybePiAndTypedTerm ((old_tvs, combined_srt, new_tm) :: triples)
                                     else 
                                       maybePiTerm (old_tvs, 
                                                    TypedTerm (new_tm, combined_srt, termAnn new_tm))
                  in
                  % let _ = writeLine("addOP "^id":\n"^printTerm combined_dfn) in
		  let combined_info = old_info << {names = combined_names, 
                                                   dfn   = combined_dfn,
                                                   fullyQualified? = false} 
		  in
		  return (foldl (fn (new_ops, name as Qualified (q, id)) ->
				 insertAQualifierMap (new_ops, q, id, combined_info))
			  old_spec.ops
			  combined_names)
		else
		  raise (SpecError (pos, 
				    "Operator "^(printAliases new_names)^" has been redefined"
				    ^"\n with new type variables "^(printTyVars new_tvs)
				    ^"\n    differing from prior "^(printTyVars old_tvs))))
	     else
	       %%  def foo ...
	       raise (SpecError (pos, 
				 "Operator "^(printAliases new_names)^" has been redefined"
				 ^ "\n from " ^ (printTerm old_dfn)
				 ^ "\n   to " ^ (printTerm new_dfn)))))
     | _ ->
       %%  We're trying to merge information with two or more previously declared types.
       raise (SpecError (pos, 
                         "Op "^(printAliases new_names)^" refers to multiple prior ops"));

    sp <- return (setOps (old_spec, new_ops));
    let el = case old_infos of
               | old_info::_ | refine? -> OpDef (primaryName, length(opDefInnerTerms old_info), [], pos)
               | _::_ | addOnly? -> OpDef (primaryName, 0, [], pos)
               | _ -> Op (primaryName, definedTerm? new_dfn, pos)
    in
    let sp = if exists? (fn eli -> equalSpecElement?(el, eli)) sp.elements then sp
              else if old_infos = [] || addOnly? || refine?
                     then addElementBeforeOrAtEnd(sp, el, opt_next_el)
              else let elts = foldr (fn (eli, elts) ->
                                       case eli of
                                         | OpDef(qid,_,_,_) | qid = primaryName -> elts
                                         | Op(qid, _, _)  | qid = primaryName -> el::elts
                                         | _                                  -> eli::elts)
                                 [] sp.elements
                   in
                   if el in? elts
                     then setElements(sp, elts)
                   else addElementBeforeOrAtEnd(sp, el, opt_next_el)
    in
    %% If replacing then add proof obligation that old defn is a theorem
    let sp = if old_infos = [] || addOnly? then sp
             else
             let dfn = (head old_infos).dfn in
             let (tvs, ty, term) = unpackFirstTerm dfn in
             if anyTerm? term
               then sp
             else
             let Qualified(q,nm) = primaryName in
             let initialFmla = defToTheorem(sp, ty, primaryName, term) in
             % let _ = writeLine("def_thm: "^printTerm initialFmla) in
             let liftedFmlas = [initialFmla] in % removePatternTop(sp, initialFmla) in
             let (_,thms) = foldl (fn((i,result), fmla) ->
                                     (i + 1,
                                      result ++ [mkConjecture(Qualified (q, nm^"__r_def"^(if i = 0 then ""
                                                                                            else show i)),
                                                              tvs, fmla)]))
                              (0,[]) liftedFmlas
             in
             addElementsAfter(sp, thms, el)
    in
    return (sp, el)
    }

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op addImport      : (SCTerm * Spec)                                  * Spec * Position -> Spec
 op addProperty    : Property                                         * Spec -> Spec
 op addAxiom       : (PropertyName * TyVars * MSTerm * Position)      * Spec -> Spec
 op addConjecture  : (PropertyName * TyVars * MSTerm * Position)      * Spec -> Spec
 op addTheorem     : (PropertyName * TyVars * MSTerm * Position)      * Spec -> Spec
 op addTheoremLast : (PropertyName * TyVars * MSTerm * Position)      * Spec -> Spec
 op addConjectures : List (PropertyName * TyVars * MSTerm * Position) * Spec -> Spec
 op addTheorems    : List (PropertyName * TyVars * MSTerm * Position) * Spec -> Spec
 op addComment     : String * Position                                * Spec -> Spec
 op addPragma      : (String * String * String * Position)            * Spec -> Spec

 %% called by evaluateSpecImport
 def addImport ((specCalcTerm, imported_spec), spc, pos) =
   appendElement (spc, Import (specCalcTerm, imported_spec, imported_spec.elements, pos))

 %% called by evaluateSpecElem 

 def addProperty (new_property, spc) =
   let spc = setElements (spc, spc.elements ++ [Property new_property]) in
   spc    % addLocalPropertyName(spc,propertyName new_property)

 def addAxiom       ((name, tvs, formula, a), spc) =
   addProperty ((Axiom      : PropertyType, name, tvs, formula, a), spc) 
 def addConjecture  ((name, tvs, formula, a), spc) =
   addProperty ((Conjecture : PropertyType, name, tvs, formula, a), spc) 
 def addTheorem     ((name, tvs, formula, a), spc) =
   addProperty ((Theorem    : PropertyType, name, tvs, formula, a), spc) 

 def addTheoremLast ((name, tvs, formula, a), spc) =  
   setElements (spc, spc.elements ++ [Property(Theorem, name, tvs, formula, a)])

 def addConjectures (conjectures, spc) = foldl (fn (spc,cnj) -> addConjecture(cnj,spc)) spc conjectures
 def addTheorems    (theorems,    spc) = foldl (fn (spc,thm) -> addTheorem   (thm,spc)) spc theorems

 def addComment     (str, a, spc) = 
   let spc = setElements (spc, spc.elements ++ [Comment (str,a)]) in
   spc    % addLocalPropertyName(spc,propertyName new_property)

 def addPragma      (pragma_content, spc) = 
   let spc = setElements (spc, spc.elements ++ [Pragma pragma_content]) in
   spc    % addLocalPropertyName(spc,propertyName new_property)

 def addElementsBeforeOrAtEnd(spc: Spec, new_elts: SpecElements, opt_old_elt: Option SpecElement): Spec =
   case opt_old_elt of
     | None -> setElements(spc, spc.elements ++ new_elts)
     | Some old_elt -> addElementsBefore(spc, new_elts, old_elt)

 def addElementBeforeOrAtEnd(spc: Spec, new_elt: SpecElement, opt_old_elt: Option SpecElement): Spec =
   case opt_old_elt of
     | None -> appendElement(spc, new_elt)
     | Some old_elt -> addElementBefore(spc, new_elt, old_elt)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% op addLocalTypeName     : Spec * QualifiedId -> Spec 
% op addLocalOpName       : Spec * QualifiedId -> Spec 
% op addLocalPropertyName : Spec * QualifiedId -> Spec 
 op addToNames           : QualifiedId * QualifiedIds -> QualifiedIds

% def addLocalTypeName (spc, new_local_type) =
%   let localTypes = spc.importInfo.localTypes in
%   if memberNames (new_local_type, localTypes) then
%     spc
%   else 
%     setLocalTypes (spc, addToNames (new_local_type, localTypes))

% def addLocalOpName (spc, new_local_op) =
%   let localOps = spc.importInfo.localOps in
%   if memberNames (new_local_op, localOps) then
%     spc
%   else 
%     setLocalOps (spc, addToNames (new_local_op, localOps))

(* Obsolete ?
 def addLocalPropertyName (spc, new_local_op) =
   let localProperties = spc.importInfo.localProperties in
   if memberNames (new_local_op, localProperties) then
     spc
   else 
     setLocalProperties (spc, addToNames (new_local_op, localProperties))
*)
 def addToNames (qid, qids) = qid::qids

 op lastOpInSpec(qids: QualifiedIds, spc: Spec | qids ~= []): QualifiedId =
   let _ = writeLine("lookingForOps: "^anyToString(qids)) in
   case qids of
     | [qid] -> qid
     | _ ->
       foldl (fn (last_qid, el) ->
                case el of
                  | Op(op_id, _, _) | op_id in? qids -> op_id
                  | _ -> last_qid)
         (head qids) spc.elements

 op topSortElements (spc: Spec, elements : SpecElements): SpecElements =
  let 
    def refsToElements(op_ids, ty_ids) =
      if op_ids = [] && ty_ids = [] then 
        []
      else
        %% Inefficient, but good enough?
        filter (fn | Op(op_id, _, _)   -> op_id in? op_ids
                   | Type(ty_id, _)    -> ty_id in? ty_ids
                   | TypeDef(ty_id, _) -> ty_id in? ty_ids
                   | _ -> false)
               spc.elements
    def body_refs op_id =
      case findTheOp(spc, op_id) of
        | Some info -> let refs = refsToElements(opsInTerm info.dfn, typesInTerm info.dfn) in
                       % let _ = writeLine("refs of "^show op_id^": "^anyToString refs) in
                       refs
        | None -> (writeLine("Warning! Missing op in adjustElementOrder: "
                               ^printQualifiedId op_id);
                   [])
    def element_refs el =
      case el of
        | Op(op_id, _, _)    -> body_refs op_id
        | OpDef(op_id, _, _, _) -> body_refs op_id
        | Property(_, p_nm, _, body, _) -> refsToElements(opsInTerm body, typesInTerm body)
        | TypeDef(ty_id, _) ->
          (case findTheType(spc, ty_id) of
             | Some info ->
               %% make sure types are early until have better circularity resolution mechanism
               refsToElements([],    % opsInType info.dfn, 
                              typesInType info.dfn)
             | _ -> (writeLine("Warning! Missing type in adjustElementOrder: "
                                 ^printQualifiedId ty_id);
                     []))
          
        | _ -> []
  in
  topSort (EQUAL, element_refs, elements) % robustTopSort

 (* Adjust order of top-level ops to avoid forward references except for mutual recursion *)
 op adjustElementOrder(spc: Spec): Spec =
  setElements(spc, topSortElements (spc, spc.elements))


% op adjustOpOrder(spc: Spec): Spec =
%   let def moveIfForwardRefs(ref_ops, el, seen_ops, spc) =
%         let forward_refs = filter (fn qid -> qid in? seen_ops) ref_ops in
%         if forward_refs = [] then (seen_ops, spc)
%         else                    
%         let last_needed_qid = lastOpInSpec(forward_refs, spc) in
%         let _ = writeLine("last op: "^printQualifiedId last_needed_qid) in
%         %let _ = writeLine(printSpec spc) in
%         let spc = deleteElement(spc, el) in
%         %let _ = writeLine(printSpec spc) in
%         let spc = addElementAfter(spc, el, Op(last_needed_qid, true, noPos)) in
%         %let _ = writeLine(printSpec spc) in
%         (seen_ops, spc)
%       def moveOpDef?(op_id, el, seen_ops, spc) =
%          case findTheOp(spc, op_id) of
%            | Some info ->
%              let _ = writeLine("Move op "^printQualifiedId op_id^" ? : "^anyToString(opsInTerm info.dfn)) in
%              let seen_ops = info.names ++ seen_ops in
%              moveIfForwardRefs(opsInTerm info.dfn, el, seen_ops, spc)
%            %| _ -> (seen_ops, spc)   % Shouldn't happen
%       def maybeMoveElt(el, result as (seen_ops, spc)) =
%         case el of
%           | Op(op_id, true, _) -> moveOpDef?(op_id, el, seen_ops, spc)
%           | OpDef(op_id, _,_) -> moveOpDef?(op_id, el, seen_ops, spc)
%           | Op(op_id, false, _) ->
%             (case findTheOp(spc, op_id) of
%                | Some info ->
%                  let op_ty = firstOpDefInnerType info in
%                  moveIfForwardRefs(opsInType op_ty, el, seen_ops, spc)
%                | _ -> result)
%           | TypeDef(ty_id, _) ->
%             (case findTheType(spc, ty_id) of
%                | Some info ->
%                  moveIfForwardRefs(opsInType info.dfn, el, seen_ops, spc)
%                | _ -> result)
%           | Property(_, p_nm, _, body, _) ->
%             let _ = writeLine("Move thm "^printQualifiedId p_nm^" ? : "^anyToString(opsInTerm body)) in
%             moveIfForwardRefs(opsInTerm body, el, seen_ops, spc)
%           | _ -> result
%   in
%   let (_, spc) = foldr maybeMoveElt ([],spc) spc.elements in
%   spc

endspec
