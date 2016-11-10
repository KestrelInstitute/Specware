(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

SpecCalc qualifying spec
 import /Languages/SpecCalculus/Semantics/Environment
 import /Languages/SpecCalculus/AbstractSyntax/SCTerm  % SCTerm
 import AccessSpec
 import /Languages/MetaSlang/Specs/Environment
 import /Library/Legacy/DataStructures/TopSort

 %% called by evaluateSpecElem
 op addType (new_names :QualifiedIds)
            (new_dfn   : MSType)
            (old_spec  : Spec)
            (pos       : Position)
            (qualifyConstructorsWithTypeName?: Bool)
  : SpecCalc.Env Spec =
  {(sp,_) <- addOrRefineType new_names new_dfn old_spec pos None true qualifyConstructorsWithTypeName?;
   return sp}

  op addQualifiersToCoProduct (o_qual: Option Id) (ty: MSType): MSType =
   case ty
     | CoProduct(fields, a) ->
       CoProduct(map (fn (qid, o_ty) -> (addQualifier o_qual qid, o_ty))fields, a)
     | _ -> ty

 op addOrRefineType (new_names    : QualifiedIds)
                    (new_dfn      : MSType)
                    (old_spec     : Spec)
                    (pos          : Position)
                    (opt_next_elt : Option SpecElement)
                    (addOnly?     : Bool)
                    (qualifyConstructorsWithTypeName?: Bool)
  : SpecCalc.Env (Spec * SpecElement) =
  % some of the names may refer to previously declared types,
  % some of which may be identical
  % Collect the info's for such references
  let new_names   = reverse (removeDuplicates new_names)  in % don't let duplicate names get into a typeinfo!
  let new_names   = map (addQualifier old_spec.qualifier) new_names in
  let primaryName = head new_names in
  let new_dfn     = case unpackType new_dfn
                      | (tvs, ty as CoProduct _) ->
                        maybePiType(tvs, addQualifiersToCoProduct(if qualifyConstructorsWithTypeName?
                                                                    then Some(mainId primaryName)
                                                                  else old_spec.qualifier)
                                           ty)
                      | _ -> new_dfn
  in
  let new_info    = {names = new_names, dfn = new_dfn} in
  let (new_tvs, _)   = unpackFirstTypeDef new_info in
  let old_infos = foldl (fn (old_infos,new_name) ->
                         case findTheType (old_spec, new_name)
                           | Some info ->
                             if exists? (fn old_info -> info = old_info) old_infos then
                               old_infos
                             else
                               info :: old_infos
                           | _ -> old_infos)
                        []
                        new_names
  in
  {
   % mapM (fn name ->
   %        if basicQualifiedId? name then
   %         raise (SpecError (pos, (printAliases new_names) ^ " is a basic type, hence cannot be redeclared."))
   %        else
   %         return ())
   %      new_names;
   new_types <-
     case old_infos
       | [] ->
         %  We're declaring a brand new type.
         return (foldl (fn (new_types, Qualified (q, id)) ->
                          insertAQualifierMap (new_types, q, id, new_info))
                       old_spec.types
                       new_names)
       | [old_info] ->
         %  We're merging new information with a previously declared type.
         let combined_names = listUnion (old_info.names, new_names) in
         let combined_names = removeDuplicates combined_names       in % redundant?
         let (old_tvs, _)   = unpackFirstTypeDef old_info           in
         % TODO: for now at least, this is very literal -- maybe should test for alpha-equivalence.
         if equalTyVarSets? (new_tvs, old_tvs) then
           let old_dfn = old_info.dfn in
           case (definedType? old_dfn, definedType? new_dfn)

             | (false, false) ->
               %  Old: Type S    [or S(A,B), etc.]
               %  New: Type S    [or S(X,Y), etc.]
               raise (SpecError (pos, "Type " ^ printAliases new_names ^ " has been redeclared."))

             | (false,  true) ->
               %  Old: Type S (A,B)
               %  New: Type S (X,Y) = T(X,Y)

               %% Eventually disallow
               % raise (SpecError (pos,
               %                   "Type " ^ printAliases new_names ^ " has been redeclared"
               %                   ^ "\n(Type refinement is no longer allowed -- use spec substitution)" ))
               let new_info = {names = combined_names,
                               dfn   = new_dfn}
               in
               return (foldl (fn (new_types, Qualified (q, id)) ->
                                insertAQualifierMap (new_types, q, id, new_info))
                             old_spec.types
                             combined_names)


             | (true, false) ->
               %  Old: Type S (X,Y) = T(X,Y)
               %  New: Type S (A,B)
               raise (SpecError (pos,
                                 "Previously defined type " ^ printAliases new_names ^ " has been redeclared"
                                   ^ "\n from " ^ printType old_dfn))
             | _ ->
               %  Old: Type S (X,Y) = T(X,Y)
               %  New: Type S (A,B) = W(A,B)
               raise (SpecError (pos,
                                 "Type " ^ printAliases new_names ^ " has been redefined"
                                   ^ "\n from "^ printType old_dfn
                                   ^ "\n   to "^ printType new_dfn))
         else
           %  Old: Type S (a)
           %  New: Type S (x,y)
           raise (SpecError (pos,
                             "Type " ^ printAliases new_names ^ " has been redeclared or redefined"
                               ^ "\n with new type variables " ^ printTyVars new_tvs
                               ^ "\n    differing from prior " ^ printTyVars old_tvs))
       | _ ->
         %  We're trying to merge information with two or more previously declared types.
         raise (SpecError (pos, "Type " ^ printAliases new_names ^ " refers to multiple prior types"));

   sp <- return (setTypes (old_spec, new_types));
   let new_elt = if definedType? new_dfn then
                   TypeDef (primaryName, pos)
                 else
                   Type    (primaryName, pos)
   in
   let sp = if exists? (fn old_elt -> equalSpecElement? (new_elt, old_elt)) sp.elements then
              sp
            else if old_infos = [] || addOnly? then
              addElementBeforeOrAtEnd (sp, new_elt, opt_next_elt)
            else
              let elts = foldr (fn (old_elt, elts) ->
                                  case old_elt
                                    | TypeDef (qid, _) | qid = primaryName -> elts
                                    | Type    (qid, _) | qid = primaryName -> new_elt :: elts
                                    | _                                    -> old_elt :: elts)
                               []
                               sp.elements
              in
              if new_elt in? elts then
                setElements (sp, elts)
              else
                addElementBeforeOrAtEnd (sp, new_elt, opt_next_elt)
   in
   {sp <- addOpsForCoProduct sp primaryName new_dfn new_tvs;
    return (sp, new_elt)}
   }

 op addOpsForCoProduct (spc: Spec) (ty_qid: QualifiedId) (ty_dfn: MSType) (tvs: TyVars): SpecCalc.Env Spec =
   case ty_dfn
     | CoProduct(fields, pos) ->
       let coprod_ty_tm = mkBase(ty_qid, map mkTyVar tvs) in
       foldM (fn spc -> fn (fld_qid, o_param_ty) ->
                let op_ty = case o_param_ty
                              | None -> coprod_ty_tm
                              | Some arg_ty -> Arrow(arg_ty, coprod_ty_tm, pos)
                in
                let constr_type = if some? o_param_ty then Constructor1 else Constructor0 in
                addOp [fld_qid] constr_type false (maybePiTypedTerm(tvs, Some op_ty, Any pos)) spc pos)
         spc fields
     | Pi(tvs, ty, _) -> addOpsForCoProduct spc ty_qid ty tvs
     | _ -> return spc

 %% called by evaluateSpecElem and LiftPattern
 op addOp (new_names : QualifiedIds)
          (fixity    : Fixity)
          (refine?   : Bool)
          (new_dfn   : MSTerm)
          (old_spec  : Spec)
          (pos       : Position)
  : SpecCalc.Env Spec =
  {(sp,_) <- addOrRefineOp new_names fixity refine? new_dfn old_spec pos None true;
   return sp}

 op addOrRefineOp (new_names    : QualifiedIds)
                  (new_fixity   : Fixity)
                  (refine?      : Bool)
                  (new_dfn      : MSTerm)
                  (old_spec     : Spec)
                  (pos          : Position)
                  (opt_next_elt : Option SpecElement)
                  (addOnly?     : Bool)
  : SpecCalc.Env (Spec * SpecElement) =
  % some of the names may refer to previously declared types,
  % some of which may be identical
  % Collect the info's for such references
  let new_names   = reverse (removeDuplicates new_names)  in % don't let duplicate names get into an opinfo!
  let new_names   = map (addQualifier old_spec.qualifier) new_names in
  let primaryName = head new_names in
  let new_info    = {names  = new_names,
                     fixity = new_fixity,
                     dfn    = new_dfn,
                     fullyQualified? = false}
  in
  let old_infos   = foldl (fn (old_infos, new_name) ->
                             case findTheOp (old_spec, new_name)
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
      if old_infos = [] && refine? && unQualifiedId? primaryName then
        % have implicit qualification:
        (case findAllOps(old_spec, primaryName)
           | [old_info] -> ([old_info],
                            head old_info.names,
                            new_info << {names = old_info.names},
                            old_info.names)
           | _ -> ([], primaryName, new_info, new_names))
      else
        (old_infos, primaryName, new_info, new_names)
  in
  {
   % mapM (fn name ->
   %         if basicQualifiedId? name then
   %           raise (SpecError (pos, printAliases new_names ^ " is a basic op, hence cannot be redeclared."))
   %         else
   %           return ())
   %      new_names;
   new_ops <-
     case old_infos

       | [] ->
         % Declaring brand new op:
         if refine? then
           raise (SpecError (pos, "Attempt to refine " ^ printAliases new_names ^ " which is not defined."))
         else
           return (foldl (fn (new_ops, Qualified (q, id)) ->
                            insertAQualifierMap
                              (new_ops, q, id,
                               new_info << {fixity = if new_info.fixity = Unspecified
                                                       then Nonfix
                                                     else new_info.fixity}))
                         old_spec.ops
                         new_names)

       | [old_info] ->
         % Merging new information with previously declared op:
         let old_dfn                    = old_info.dfn                          in
         let combined_names             = listUnion (old_info.names, new_names) in
         let combined_names             = removeDuplicates combined_names       in % redundant?
         let old_triples                = unpackTypedTerms(old_info.dfn)        in
         let (old_tvs, old_typ, old_tm) = head old_triples                      in
         let (new_tvs, new_typ, new_tm) = unpackFirstOpDef new_info             in
         let old_defined?               = definedTerm? old_dfn                  in
         let new_defined?               = definedTerm? new_dfn                  in
         (case (old_defined?, new_defined?)

            | (false, false) | (~ refine? || equalType? (old_typ, new_typ)) ->
              %  Old: op foo : T1
              %  New: op foo : T2
              raise (SpecError (pos,
                                "Operator "^(printAliases new_names)^" has been redeclared"
                                ^ "\n from " ^ (printType (maybePiType (old_tvs, old_typ)))
                                ^ "\n   to " ^ (printType (maybePiType (new_tvs, new_typ)))))

            | (true, false) ->
              %  Old:  op foo : T1 = ...
              %  New:  op foo : T2
              raise (SpecError (pos,
                                "Operator " ^ printAliases new_names ^ " has been redeclared"
                                  ^ "\n from " ^ printTerm old_dfn
                                  ^ "\n   to " ^ printTerm new_dfn))

            | _ ->
              %  Old might or might not be defined
              %  New is defined, and might be an explicit refinement
              if  ~old_defined?  %  No old definition:
                                 %   Old: op foo : T
                                 %   New: op foo : T = new_body
               || refine?        %  Refining op (via "refine def ..."):
                                 %   Old: op foo : T
                                 %   Old: op foo : T = old_body
                                 %   New: refine def foo : T = new_body
               || ~addOnly?      %  Refining spec (via "refine spc by ..."):
                                 %   Old: op foo : T
                                 %   Old: op foo : T = old_body
                                 %   New: def foo : T = new_body
                then
                  let consistent_tvs? = (case new_tvs
                                           | [] ->
                                             %  Old:  op foo : T
                                             %  New:  def foo x = ...
                                             true
                                           | _ ->
                                             %  Old:  op [a,b,c] foo : T
                                             %  New:  def [a,b,c] foo : T = body
                                             equalTyVarSets? (new_tvs, old_tvs))
                  in
                  let _ = writeLine("old_tm: "^printTerm old_tm^"\nnew_tm: "^printTerm new_tm) in
                  if consistent_tvs? then
                    let combined_typ  = case (old_typ, new_typ)
                                          | (Any _,       _)           -> new_typ
                                          | (_,           Any _)       -> old_typ
                                          | (MetaTyVar _, _)           -> new_typ
                                         | (_,           MetaTyVar _) -> old_typ
                                        %| _ | existsInType? (embed? MetaTyVar) new_typ -> old_typ
                                         | _ | refine? || embed? Lambda old_tm -> combineSubTypes(old_typ, new_typ, old_tm, new_tm)
                                         | _                          -> old_typ  % TODO:  maybeAndType ([old_typ, new_typ], typeAnn new_typ)
                    in
                    let new_tm        = if false && refine? && old_defined? then
                                          % Reverse order so most refined term first
                                          And (new_tm :: opDefInnerTerms old_info, termAnn new_tm)
                                        else
                                          new_tm
                    in
                    let combined_dfn  = if refine? then
                                          maybePiAndTypedTerm ((old_tvs, combined_typ, new_tm) :: old_triples)
                                        else
                                          maybePiTerm (old_tvs,
                                                       TypedTerm (new_tm, combined_typ, termAnn new_tm))
                    in
                     % let _ = if show primaryName = "f" then writeLine("addop: "^show primaryName^"\n"^printTerm old_info.dfn^"\n-->\n"
                     %                                                    ^printTerm combined_dfn) else () in
                    let combined_info = old_info << {names           = combined_names,
                                                     dfn             = combined_dfn,
                                                     fullyQualified? = false}
                    in
                    return (foldl (fn (new_ops, Qualified (q, id)) ->
                                     insertAQualifierMap (new_ops, q, id, combined_info))
                                  old_spec.ops
                                  combined_names)
                  else
                    % inconsistent type vars
                    raise (SpecError (pos,
                                      "Operator " ^ printAliases new_names ^ " has been redefined"
                                        ^ "\n with new type variables " ^ printTyVars new_tvs
                                        ^ "\n    differing from prior " ^ printTyVars old_tvs))
              else
                % old def exists, new def is not a refinement
                raise (SpecError (pos,
                                  "Operator " ^ printAliases new_names ^ " has been redefined"
                                    ^ "\n from " ^ printTerm old_dfn
                                    ^ "\n   to " ^ printTerm new_dfn)))
       | _ ->
         %  Merging information with two or more previously declared types.
         raise (SpecError (pos, "Op " ^ printAliases new_names ^ " refers to multiple prior ops"));

   sp <- return (setOps (old_spec, new_ops));
   let new_elt = case old_infos
                   | old_info::_ | refine? -> OpDef (primaryName, length (opDefInnerTerms old_info), None, pos)
                   | _::_ | addOnly?       -> OpDef (primaryName, 0,                                 None, pos)
                   | _                     -> Op    (primaryName, definedTerm? new_dfn, pos)
   in
   let sp = if exists? (fn old_elt -> equalSpecElement? (new_elt, old_elt)) sp.elements then
              sp
            else if old_infos = [] || addOnly? || refine? then
              addElementBeforeOrAtEnd (sp, new_elt, opt_next_elt)
            else
              let elts = foldr (fn (old_elt, elts) ->
                                  case old_elt
                                    | OpDef (qid,_,_,_) | qid = primaryName -> elts
                                    | Op    (qid, _, _) | qid = primaryName -> new_elt :: elts
                                    | _                                     -> old_elt :: elts)
                               []
                               sp.elements
              in
              if new_elt in? elts then
                setElements (sp, elts)
              else
                addElementBeforeOrAtEnd (sp, new_elt, opt_next_elt)
   in
   % If replacing then add proof obligation that old defn is a theorem
   let sp = if old_infos = [] || addOnly? then
              sp
            else
              let dfn             = (head old_infos).dfn in
              let (tvs, ty, term) = unpackFirstTerm dfn  in
              if anyTerm? term then
                sp
              else
                let Qualified (q, id) = primaryName                              in
                let initialFmla       = defToTheorem (sp, ty, primaryName, term) in
                let liftedFmlas       = [initialFmla]                            in % removePatternTop(sp, initialFmla) in
                let (_, thms) =
                    foldl (fn ((i, result), fmla) ->
                             let suffix  = if i = 0 then "" else show i      in
                             let new_id  = id ^ "__r_def" ^ suffix           in
                             let new_qid = Qualified (q, new_id)             in
                             let new_elt = mkConjecture (new_qid, tvs, fmla) in
                             (i + 1,
                              result ++ [new_elt]))
                          (0, [])
                          liftedFmlas
                in
                addElementsAfter (sp, thms, new_elt)
   in
   return (sp, new_elt)
   }

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% called by evaluateSpecImport
 op addImport ((specCalcTerm  : SCTerm,
                imported_spec : Spec),
               spc : Spec,
               pos : Position)
  : Spec =
  appendElement (spc, Import (specCalcTerm, imported_spec, imported_spec.elements, pos))

 %% called by evaluateSpecElem
 op addProperty (new_property : Property,
                 spc          : Spec)
  : Spec =
  appendElement (spc, Property new_property)

 op addAxiom ((name    : PropertyName,
               tvs     : TyVars,
               formula : MSTerm,
               pos     : Position),
              spc : Spec)
  : Spec =
  addProperty ((Axiom, name, tvs, formula, pos), spc)

 op addConjecture ((name    : PropertyName,
                    tvs     : TyVars,
                    formula : MSTerm,
                    pos     : Position),
                   spc : Spec)
  : Spec =
  addProperty ((Conjecture, name, tvs, formula, pos), spc)

 op addTheorem    ((name    : PropertyName,
                    tvs     : TyVars,
                    formula : MSTerm,
                    pos     : Position),
                   spc : Spec)
  : Spec =
  addProperty ((Theorem, name, tvs, formula, pos), spc)

 op addTheoremLast ((name    : PropertyName,
                     tvs     : TyVars,
                     formula : MSTerm,
                     pos     : Position),
                    spc : Spec)
  : Spec =
  appendElement (spc, Property (Theorem, name, tvs, formula, pos))

 op addConjectures (conjectures : List (PropertyName * TyVars * MSTerm * Position),
                    spc         : Spec)
  : Spec =
  foldl (fn (spc, cnj) -> addConjecture (cnj, spc))
        spc
        conjectures

 op addTheorems (theorems : List (PropertyName * TyVars * MSTerm * Position),
                 spc      : Spec)
  : Spec =
  foldl (fn (spc, thm) -> addTheorem (thm, spc))
        spc
        theorems

 op addComment (comment : String,
                pos     : Position,
                spc     : Spec)
  : Spec =
  appendElement (spc, Comment (comment, pos))

 op addPragma (pragma_content : String * String * String * Position,
               spc            : Spec)
  : Spec =
  appendElement (spc, Pragma pragma_content)

 op addElementsBeforeOrAtEnd (spc         : Spec,
                              new_elts    : SpecElements,
                              opt_old_elt : Option SpecElement)
  : Spec =
  case opt_old_elt
    | Some old_elt -> addElementsBefore (spc, new_elts, old_elt)
    | _            -> setElements       (spc, spc.elements ++ new_elts)

 op addElementBeforeOrAtEnd (spc         : Spec,
                             new_elt     : SpecElement,
                             opt_old_elt : Option SpecElement)
  : Spec =
  case opt_old_elt
    | Some old_elt -> addElementBefore (spc, new_elt, old_elt)
    | _            -> appendElement    (spc, new_elt)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op addToNames (qid : QualifiedId, qids : QualifiedIds) : QualifiedIds =
  qid :: qids

 op lastOpInSpec (qids: QualifiedIds, spc: Spec | qids ~= []) : QualifiedId =
   let _ = writeLine ("lookingForOps: " ^ anyToString qids) in
   case qids
     | [qid] -> qid
     | _ ->
       foldl (fn (last_qid, el) ->
                case el
                  | Op(op_id, _, _) | op_id in? qids -> op_id
                  | _ -> last_qid)
         (head qids) spc.elements

 op topSortElements (spc : Spec, elements : SpecElements) : SpecElements =
  let
    def refsToElements(op_ids, ty_ids) =
      if op_ids = [] && ty_ids = [] then
        []
      else
        % Inefficient, but good enough?
        filter (fn | Op(op_id, _, _)   -> op_id in? op_ids
                   | Type(ty_id, _)    -> ty_id in? ty_ids
                   | TypeDef(ty_id, _) -> ty_id in? ty_ids
                   | _ -> false)
               spc.elements
    def body_refs op_id =
      case findTheOp(spc, op_id)
        | Some info -> let refs = refsToElements (opsInTerm info.dfn, typesInTerm info.dfn) in
                       % let _ = writeLine ("refs of " ^ show op_id ^ ": "^ anyToString refs) in
                       refs
        | _ -> (writeLine ("Warning! Missing op in adjustElementOrder: "
                             ^ printQualifiedId op_id);
                [])
    def element_refs el =
      case el
        | Op       (op_id, _,         _) -> body_refs op_id
        | OpDef    (op_id, _, _,      _) -> body_refs op_id
        | Property (_, p_nm, _, body, _) -> refsToElements(opsInTerm body, typesInTerm body)
        | TypeDef  (ty_id,            _) ->
          (case findTheType (spc, ty_id)
             | Some info ->
               % make sure types are early until have better circularity resolution mechanism
               refsToElements ([],    % opsInType info.dfn,
                               typesInType info.dfn)
             | _ -> (writeLine ("Warning! Missing type in adjustElementOrder: "
                                  ^ printQualifiedId ty_id);
                     []))

        | _ -> []
  in
  topSort (EQUAL, element_refs, elements) % robustTopSort

 (* Adjust order of top-level ops to avoid forward references except for mutual recursion *)
 op SpecTransform.adjustElementOrder (spc: Spec): Spec =
  setElements (spc, topSortElements (spc, spc.elements))

endspec
