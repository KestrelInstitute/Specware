SpecCalc qualifying spec 

  import /Languages/MetaSlang/Specs/CompressSpec

  import Signature 
  import Spec/MergeSpecs
  import Spec/VarOpCapture
  import Spec/ComplainIfAmbiguous

  %% To qualify a spec means to change all unqualified names to qualified
  %% names. This can raise exceptions since qualifying a name may identify
  %% it with a name that already exists.
  %% 
  %% The current version need not visit the imported specs as the hierarchy
  %% is flattened,
  %% 
  %% Change UnQualified to new_qualifier in all qualified names

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  def SpecCalc.evaluateQualify sc_term new_q = 
   let pos = positionOf sc_term in
   {
    value_info as (value, ts, uids) <- SpecCalc.evaluateTermInfo sc_term;
    case coerceToSpec value of
      | Spec spc -> 
        {
	 qualified_spec <- qualifySpec spc new_q [] pos;
	 return (Spec qualified_spec, ts, uids)
	}
      | Other other -> 
	evaluateOtherQualify sc_term value_info new_q pos
      | _ -> raise (TypeCheck (pos, "qualifying a term that is not a specification"))
   }

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% qualifySpec is also called from Accord
  op  qualifySpec : Spec -> Qualifier -> Ids -> Position -> SpecCalc.Env Spec
  def qualifySpec spc new_q immune_ids pos =

    %% For core Specware per se, immune_ids will be [].
    %% But in some contexts (e.g. Accord) we might have "local" ops that 
    %% we would prefer not to qualify.  
    %% Moreover, by definition only unqualified names are candidates for 
    %% qualification, so we need only check the ids of the "local" ops
    %% (as opposed to checking against the full name).

    let

      def check_for_type_collisions () =
        foldOverQualifierMap (fn (q, id, old_info, _) -> 
                              if q = UnQualified then
                                case findAQualifierMap (spc.types, new_q, id) of
                                  | Some new_info ->
                                    if new_info = old_info then
                                      %% collapsing {id, new_q.id} into {new_q.id} is ok 
                                      return ()
                                    else
                                      %% collapsing one info named id with another named new_q.id is bad
                                      raise_later (QualifyError (pos, 
                                                                 new_q ^ " would collide type " ^ 
                                                                   printAliases old_info.names ^ " into " ^ 
                                                                   printAliases new_info.names))
                                  | _ -> return ()
                              else
                                return ())
                             ()
                             spc.types
        
      def check_for_op_collisions () =
        foldOverQualifierMap (fn (q, id, old_info, _) -> 
                              if q = UnQualified then
                                case findAQualifierMap (spc.ops, new_q, id) of
                                  | Some new_info ->
                                    if new_info = old_info then
                                      %% collapsing {id, new_q.id} into {new_q.id} is ok 
                                      return ()
                                    else
                                      %% collapsing one info named id with another named new_q.id is bad
                                      raise_later (QualifyError (pos, 
                                                                 new_q ^ " would collide op " ^ 
                                                                   printAliases old_info.names ^ " into " ^ 
                                                                   printAliases new_info.names))
                                  | _ -> return ()
                              else
                                return ())
                             ()
                             spc.ops
        
      def qualify_type type_term =
        case type_term of
         | Base (qid, srts, a) ->
           let new_qid = qualifyTypeId new_q qid in
           if new_qid = qid then type_term else Base (new_qid, srts, a)
         | _ -> type_term
  
      def qualify_term op_term =
        case op_term of
         | Fun (Op (qid, fixity), srt, a) ->
           let new_qid = qualifyOpId new_q immune_ids qid in
           if new_qid = qid then op_term else Fun (Op (new_qid, fixity), srt, a)
         | _ -> op_term
  
      def qualify_pattern pat = pat
  
      def qualify_types types =
        let 
          def qualify_typeinfo (q, _, info, types) =
	    let revised_q = if q = UnQualified then new_q else q in
	    %% Translation can cause names to become duplicated, so remove duplicates
	    let new_names = reverse (removeDuplicates (map (qualifyTypeId revised_q) info.names)) in % revised_q was new_q ??
	    let new_info  = info << {names = new_names} in
	    return (mergeTypeInfo spc types new_info)
	in
	  foldOverQualifierMap qualify_typeinfo emptyAQualifierMap types

      def qualify_ops ops =
        let 
          def qualify_opinfo (q, id, info, ops) =
	    let revised_q = if q = UnQualified && id nin? immune_ids then new_q else q in
	    %% Translation can cause names to become duplicated, so remove duplicates
	    let new_names = reverse (removeDuplicates (List.map (qualifyOpId revised_q immune_ids) info.names)) in % revised_q was new_q ??
	    let new_info  = info << {names = new_names} in
	    return (mergeOpInfo spc ops new_info)
	in
	  foldOverQualifierMap qualify_opinfo emptyAQualifierMap ops 
  
    in
      case spc.qualifier of
        | Some prior_q ->
          %% annoying that this is reached twice -- 
          %%  once while processing imports, then again for normal processing
          let _ = toScreen("\n;;; Warning: Attempt to qualify spec previously qualified by " ^ prior_q ^ " with " ^ new_q ^ 
                             " is ignored at " ^
                             (case pos of
                                | Internal msg -> msg
                                | String (string, left, right) ->
                                  let printPos = fn (line,column,byte) -> (Nat.show line)^"."^(Nat.show column) in
                                  printPos left ^ "-" ^ printPos right ^ " in \n;;;          [" ^ string ^ "]"
                                | File (filename, left, right) ->
                                  let printPos = fn (line,column,byte) -> (Nat.show line)^"."^(Nat.show column) in
                                  printPos left ^ "-" ^ printPos right ^ " in \n;;;          " ^ filename)
                             ^ "\n")
          in
            return spc
        | _ ->
          let {types, ops, elements, qualifier} = 
              mapSpecUnqualified (qualify_term, qualify_type, qualify_pattern) spc
          in 
            {
             check_for_type_collisions ();
             check_for_op_collisions   ();
             newTypes    <- qualify_types types;
             newOps      <- qualify_ops   ops;
             newElements <- return (qualifySpecElements new_q immune_ids elements);
             new_spec    <- return {types     = newTypes,
                                    ops       = newOps,
                                    elements  = newElements,
                                    qualifier = Some new_q};
            %% Qualification cannot introduce a var op capture!
            %% new_spec    <- return (removeVarOpCaptures new_spec);
             new_spec    <- return (compressDefs        new_spec);
             new_spec    <- complainIfAmbiguous new_spec pos;
             raise_any_pending_exceptions;
             return new_spec
             }
      
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% Accord prefers to have qualifySpecElements and qualifySpecElement
  %% as standalone functions (not local to qualifySpec) so it can call 
  %% them from other contexts, as when qualifying modules, classes, etc.

  op  qualifySpecElements : Qualifier -> Ids -> SpecElements -> SpecElements
  def qualifySpecElements new_q immune_ids elts =
    List.map (qualifySpecElement new_q immune_ids) elts

  op  qualifySpecElement : Qualifier -> Ids -> SpecElement -> SpecElement
  def qualifySpecElement new_q immune_ids el =
    case el of
      | Import (sp_tm, sp, els, a) ->
        if qualifiedSpec? sp then 
	  el
	else 
	  Import ((Qualify (sp_tm, new_q), noPos),
		  sp,
		  qualifySpecElements new_q immune_ids els, a)
      | Op      (qid,def?,a) -> Op      (qualifyOpId   new_q immune_ids qid, def?,a)
      | OpDef   (qid, refine?, hist, a) -> OpDef   (qualifyOpId   new_q immune_ids qid, refine?, hist, a)
      | Type    (qid,a)      -> Type    (qualifyTypeId new_q qid,a)
      | TypeDef (qid,a)      -> TypeDef (qualifyTypeId new_q qid,a)
      | Property (pt, qid, tvs, fmla, a) ->
	%% Translation can cause names to become duplicated, but won't remove duplicates
	let new_name = qualifyPropertyId new_q qid in
	let newProp = (pt, new_name, tvs, fmla, a) in
	Property newProp
      | _ -> el

  def qualifyOpId new_q immune_ids (qid as Qualified (q, id)) =
    if q = UnQualified && id nin? immune_ids then
      Qualified (new_q, id)
    else 
      qid

  def qualifyTypeId new_q (qid as Qualified (q, id)) =
    if q = UnQualified then
      Qualified (new_q, id)
    else 
      qid

  def qualifyPropertyId new_q (qid as Qualified (q, id)) =
    if q = UnQualified then
      Qualified (new_q, id)
    else 
      qid
  
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

endspec
