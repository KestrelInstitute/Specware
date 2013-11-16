Globalize qualifying spec
{
 import /Languages/MetaSlang/Transformations/Setf
 import /Languages/MetaSlang/Transformations/SliceSpec
 import /Languages/MetaSlang/Transformations/RecordMerge
 import /Languages/MetaSlang/Transformations/CommonSubExpressions
 import /Languages/MetaSlang/CodeGen/SubstBaseSpecs  
 import /Languages/MetaSlang/CodeGen/DebuggingSupport
 import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements  % for addOp of global var

 type OpTypes         = AQualifierMap MSType
 type MSVarName       = Id
 type MSVarNames      = List MSVarName
 type MSFieldName     = Id

 type RefMode         = | Access | Update
 type GlobalRef       = RefMode *  MSVarName * MSFieldName
 type GlobalRefs      = List GlobalRef
 type ConflictingRefs = List (MSVarName * MSFieldName) 

 %% GlobalRefs are used to create MSSubstitutions

 type MSSubstitution  = {global_var_id : MSVarName,
                         field_id      : MSFieldName,
                         temp_var      : MSVar}

 type MSSubstitutions = List MSSubstitution

 type LetBinding = MSPattern * MSTerm  % must match structure of Let in AnnTerm.sw

 type LetBindings = List LetBinding

 type Context = {spc              : Spec, 
                 root_ops         : OpNames,
                 global_var_name  : OpName,
                 global_type_name : TypeName,
                 global_type      : MSType,
                 global_var       : MSTerm,                 % if global type is not a product
                 global_var_map   : List (String * MSTerm), % if global type has product fields
                 global_init_name : QualifiedId,
                 setf_entries     : SetfEntries,
                 let_bindings     : LetBindings,
                 tracing?         : Bool}
                   
 type GlobalizedRule =    | Changed MSRule
                          | Unchanged

 type GlobalizedType =    | Changed MSType
                          | Unchanged

 type GlobalizedTerm =    | Changed MSTerm
                          | Unchanged
                          | GlobalVar    % for clarity (as opposed to Changed global_var)

 type GlobalizedPattern = | Changed MSPattern
                          | Unchanged
                          | GlobalVarPat % for clarity (as opposed to Changed global_var_pat)

 op global_q : Qualifier = "Global"
 op gPos     : Position = Internal "Globalize"

 %% ================================================================================

 op expandBindings (tm : MSTerm, bindings : LetBindings) : MSTerm =
  case bindings of
    | [] -> tm
    | _ ->
      let
        def expandTerm tm =
          case tm of
            | Var ((nm, _), _) -> 
              (case (findLeftmost (fn (pattern, value) ->
                                     case pattern of
                                       | VarPat ((vname, _), _) -> vname = nm
                                       | _ -> false)
                                  bindings)
                of
                 | Some (_, value) ->
                   %% Recur to expand outer let bindings in body of substituted term
                   expandBindings (value, tail bindings)
                 | _ -> tm)
            | _ -> tm
      in
      let ttp = (expandTerm, fn t -> t, fn p -> p) in
      mapTerm ttp tm

 %% ================================================================================

 op globalRefsInApply (context         : Context) 
                      (global_vars     : MSVarNames)
                      (Apply (x, y, _) : MSTerm) 
  : GlobalRefs =
  case (x, y) of

    | (Fun (Project field_id, _, _), 
       Var ((var_id, _), _))
      | var_id in? global_vars ->
        [(Access, var_id, field_id)]

    | (Fun (RecordMerge, _, _),
       Record ([(_, Var ((var_id, _), _)),
                (_, Record (fields, _))],
               _))
      | var_id in? global_vars ->
        foldl (fn (refs, (field_id, tm)) ->
                 refs ++
                 [(Update, var_id, field_id)] ++
                 globalRefsIn context global_vars tm)
              []
              fields

    | _ -> 
      (globalRefsIn context global_vars x) ++ 
      (globalRefsIn context global_vars y)

 op globalRefsInRecord (context            : Context) 
                       (global_vars        : MSVarNames)
                       (Record (fields, _) : MSTerm)
  : GlobalRefs =
  foldl (fn (refs, (_, tm)) -> 
           refs ++ globalRefsIn context global_vars tm) 
        [] 
        fields

 op globalRefsInLet (context                 : Context) 
                    (global_vars             : MSVarNames)
                    (Let (bindings, body, _) : MSTerm)
  : GlobalRefs =
  foldl (fn (refs, (_, tm)) -> 
           refs ++ globalRefsIn context global_vars tm)
        (globalRefsIn context global_vars body)
        bindings

 op globalRefsInLetRec (context                    : Context) 
                       (global_vars                : MSVarNames)
                       (LetRec (bindings, body, _) : MSTerm) 
  : GlobalRefs =
  foldl (fn (refs, (_, tm)) -> 
           refs ++ globalRefsIn context global_vars tm)
        (globalRefsIn context global_vars body)
        bindings

 op globalRefsInLambda (context           : Context) 
                       (global_vars       : MSVarNames)
                       (Lambda (match, _) : MSTerm) 
  : GlobalRefs =
  foldl (fn (refs, (_, _, body)) ->
           refs ++ globalRefsIn context global_vars body)
        []
        match

 op globalRefsIn (context     : Context) 
                 (global_vars : MSVarNames)
                 (term        : MSTerm) 
  : GlobalRefs =
  case term of
   | Apply  _ -> globalRefsInApply  context global_vars term
   | Record _ -> globalRefsInRecord context global_vars term
   | Let    _ -> globalRefsInLet    context global_vars term
   | LetRec _ -> globalRefsInLetRec context global_vars term
   | Lambda _ -> globalRefsInLambda context global_vars term
   | Bind   _ -> [] % exists, etc.

   | IfThenElse (x, y, z, _) -> (globalRefsIn context global_vars x) ++ 
                                (globalRefsIn context global_vars y) ++ 
                                (globalRefsIn context global_vars z)

   | Seq        (tms,     _) -> foldl (fn (refs, tm) -> 
                                         refs ++ globalRefsIn context global_vars tm) 
                                      [] 
                                      tms

   | The        (v, tm,   _) -> globalRefsIn context global_vars tm
   | TypedTerm  (tm, _,   _) -> globalRefsIn context global_vars tm
   | Pi         (_, tm,   _) -> globalRefsIn context global_vars tm
   | And        (tm::_,   _) -> globalRefsIn context global_vars tm

   | _ -> []
 
 %% ================================================================================

 op conflictingGlobalRefs (global_refs : List (Nat * GlobalRefs)) : ConflictingRefs =
  foldl (fn (result, (n1, grefs1)) ->
           foldl (fn (result, (mode1, var1, field1)) ->
                    % for a conflict, at least one ref must be an update
                    if mode1 = Update then 
                      foldl (fn (result, (n2, grefs2)) ->
                               if n1 = n2 then 
                                 % refs in the same context don't conflict
                                 result
                               else
                                 % refs in parallel contexts conflict,
                                 % whether access or update 
                                 foldl (fn (result, (_, var2, field2)) ->
                                          if var1 = var2 && field1 = field2 then 
                                            let conflicting_ref = (var1, field1) in
                                            % ignore duplicate conflicts
                                            if conflicting_ref in? result then
                                              result
                                            else
                                              result ++ [conflicting_ref]
                                          else
                                            result)
                                       result
                                       grefs2)
                            result
                            global_refs
                    else
                      result)
                 result
                 grefs1)
        []
        global_refs

 %% ================================================================================

 op conflictingGlobalRefsIn (context     : Context) 
                            (global_vars : MSVarNames)
                            (term        : MSTerm) 
  : ConflictingRefs =

  % The numbers used here indicate branching or parallel contexts.
  % Specware does not specify an evaluation order, so evaluation of anything in one 
  % context could preceed or follow evaluation of anything else in another context.
  % Thus to avoid indeterminate results, we must avoid an update to a global field 
  % in one context and a reference (either update or access) in some other context.

  % This code is invoked by globalizeTerm, which is invoked on every term, including
  % the subterms of this term.  Thus we only need to deconflict contexts created at 
  % the top level of this term, as each subterm will be separately deconflicted when
  % globalTerm is called on it.

  let (_, all_refs) =
      case term of
        | Apply (Fun (RecordMerge, _, _), 
                 Record ([(_, Var ((var_id, _), _)),
                          (_, Record (fields, _))],
                         _),
                 _)
          | var_id in? global_vars ->
            foldl (fn ((n, all_refs), (field_id, tm)) ->
                     let updates = [(Update, var_id, field_id)] 
                                   ++
                                   globalRefsIn context global_vars tm
                     in
                     (n + 1, all_refs ++ [(n, updates)]))
                  (0, [])
                  fields
          
        | Apply (x, y, _) -> 
          (2, [(0, globalRefsIn context global_vars x), 
               (1, globalRefsIn context global_vars y)])

        | Record (fields, _) -> 
          foldl (fn ((n, all_refs), (_, tm)) ->
                   (n + 1, 
                    all_refs ++ [(n, globalRefsIn context global_vars tm)]))
                (0, [])
                fields

        | Seq (tms, _) -> 
          foldl (fn ((n, all_refs), tm) -> 
                   (n + 1, 
                    all_refs ++ [(n, globalRefsIn context global_vars tm)]))
                (0, [])
                tms

        | _ -> 
          (0, [])
  in
  conflictingGlobalRefs all_refs 
      
 %% ================================================================================

 op nullTerm : MSTerm    = Record    ([], noPos)
 op nullType : MSType    = Product   ([], noPos)
 op nullPat  : MSPattern = RecordPat ([], noPos)
 op wildPat (typ : MSType) : MSPattern = WildPat (typ, noPos)

 op showTypeName (info : TypeInfo) : String = printQualifiedId (primaryTypeName info)
 op showOpName   (info : OpInfo)   : String = printQualifiedId (primaryOpName   info)

 op baseOp? (qid as Qualified(q, id) : QualifiedId) : Bool = 
  q in? ["Bool", "Char", "Compare", "Function", "Integer", "IntegerAux", "List", "List1", "Nat", "Option", "String"]

 op baseType? (qid as Qualified(q, id) : QualifiedId) : Bool = 
  q in? ["Bool", "Char", "Compare", "Function", "Integer", "IntegerAux", "List", "List1", "Nat", "Option", "String"]

 op myTrue : MSTerm = Fun (Bool true, Boolean noPos, noPos)

 %% ================================================================================
 %% Verify that the suggested global type actually exists
 %% ================================================================================

 op checkGlobalType (spc: Spec, gtype as Qualified(q,id) : TypeName) : SpecCalc.Env TypeName =
  case findTheType (spc, gtype) of
    | Some _ -> return gtype
    | _ ->
      if q = UnQualified then
        case wildFindUnQualified (spc.types, id) of
          | [_]   -> return gtype
          | []    -> raise (Fail ("Proposed type to globalize does not exist: " ^ show gtype))
          | first :: rest -> 
            let names = foldl (fn (names, info) -> names ^ ", " ^ showTypeName info) (showTypeName first) rest in
            raise (Fail ("Proposed type to globalize is ambiguous: " ^ names))
      else
        raise (Fail ("Proposed type to globalize does not exist: " ^ show gtype))
          
 %% ================================================================================
 %% Verify that the suggested global var is plausible
 %% ================================================================================

 op checkGlobalVar (spc: Spec, gvar as Qualified(q,id) : OpName, gtype : TypeName) : SpecCalc.Env OpName =
  let
    def verify opinfo =
      let typ = inferType (spc, opinfo.dfn) in
      case typ of
        | Base (qid, [], _) | gtype = qid -> return gvar
        | _ ->
          raise (Fail ("Global var " ^ show gvar ^ " with expected type " ^ show gtype ^ " is already defined with type " ^ printType typ))
  in
  case findTheOp (spc, gvar) of
    | Some opinfo -> verify opinfo
    | _ ->
      if q = UnQualified then
        case wildFindUnQualified (spc.ops, id) of
          | [opinfo] -> verify opinfo
          | []       -> return gvar    % Ok -- we will add the proposed var later.
          | first :: rest ->
            let names = foldl (fn (names, info) -> names ^ ", " ^ showOpName info) (showOpName first) rest in
            raise (Fail ("Proposed global var is already ambiguous among " ^ names))
      else
        % Ok -- we will add the proposed var later.
        return gvar 
          
%% ================================================================================
 %% Find a plausible init op that produces something of the appropriate type
 %% ================================================================================

 op valTypeMatches? (typ : MSType, name : TypeName) : Bool =
  case typ of
    | Base    (nm, [], _) -> nm = name 
    | Subtype (typ, _, _) -> valTypeMatches? (typ, name)
    | Product (pairs,  _) -> exists? (fn (_, typ) -> valTypeMatches? (typ, name)) pairs
    | Arrow   (_, rng, _) -> valTypeMatches? (rng, name)
    | _ -> false

 op findInitOp (spc : Spec, gtype: TypeName) : SpecCalc.Env QualifiedId =
  let candidates =
      foldriAQualifierMap (fn (q, id, info, candidates) ->
                             let optype = inferType (spc, info.dfn) in
                             if valTypeMatches? (optype, gtype) && ~ (valTypeMatches? (optype, gtype)) then
                               (mkQualifiedId (q, id)) :: candidates 
                             else
                               candidates)
                          []
                          spc.ops
  in
  case candidates of
    | []             -> raise (Fail ("Could not find an initializer for type " ^ show gtype))
    | [init_op_name] -> return init_op_name
    | first :: rest  -> let init_ops = foldl (fn (names, init_op_name) -> 
                                                names ^ ", " ^ show init_op_name) 
                                             (show first)
                                             rest
                        in
                        raise (Fail ("Found multiple initializers for type " ^ show gtype ^ " : " ^ init_ops))

 %% ================================================================================
 %% Verify that the suggested init op produces something of the appropriate type
 %% ================================================================================

 op checkGlobalInitOp (spc: Spec, ginit as Qualified(q,id) : OpName, gtype : TypeName) : SpecCalc.Env QualifiedId =
  let
    def removeSubtypes typ = % do not use stripSubtypes, which uses unfoldBase
      case typ of
        | Subtype (typ, _, _) -> removeSubtypes typ
        | _ -> typ
          
    def verify opinfo =
      let full_type = inferType (spc, opinfo.dfn) in
      case full_type of
        
        | Base (qid, [], _) | gtype = qid -> return ginit        % op foo : State
          
        | Subtype (typ, _, _) ->
          (let typ = removeSubtypes typ in
           case typ of
             
             | Base (qid, [], _) | gtype = qid -> return ginit   % op foo : (State | p?)
               
             | _ ->
               raise (Fail ("Op " ^ show ginit ^ " for producing initial global " ^ 
                              show gtype ^ " is defined with type " ^ printType full_type)))
          
        | Arrow (_, rng, _) ->
          (let rng = removeSubtypes rng in
           case rng of
             
             | Base (qid, [], _) | gtype = qid -> return ginit    % op foo : X -> State  %  op foo : X -> (State | p?)
               
             | _ ->
               raise (Fail ("Op " ^ show ginit ^ " for producing initial global " ^ 
                              show gtype ^ " is defined with type " ^ printType full_type)))
          
        | _ ->
          raise (Fail ("Op " ^ show ginit ^ " for producing initial global " ^ 
                         show gtype ^ " is defined with type " ^ printType full_type))
  in
  case findTheOp (spc, ginit) of
    | Some opinfo -> verify opinfo
    | _ ->
      if q = UnQualified then
        case wildFindUnQualified (spc.ops, id) of
          | [opinfo] -> verify opinfo
          | []       -> raise (Fail ("Op " ^ show ginit ^ " for producing initial global " ^ show gtype ^ " is undefined."))
          | first :: rest -> 
            let names = foldl (fn (names, qid) -> names ^ ", " ^ showOpName qid) (showOpName first) rest in
            raise (Fail ("Op " ^ show ginit ^ " for producing initial global " ^ show gtype ^ " is ambiguous among " ^ names))
      else
        raise (Fail ("Op " ^ show ginit ^ " for producing initial global " ^ show gtype ^ " is undefined."))
          

 op globalizeInitOp (spc              : Spec, 
                     global_type      : MSType,
                     global_var       : MSTerm,
                     global_var_map   : List (String * MSTerm),
                     global_init_name : OpName,
                     tracing?         : Bool)
  : Option OpInfo =
  %% modify init fn to set global variable rather than return value
  let Some info = findTheOp (spc, global_init_name) in
  let old_dfn   = info.dfn in
  let old_dfn   = case old_dfn of
                    | And (tm :: _, _) -> tm
                    | _ -> old_dfn
  in
  let 
    def aux tm =
      case tm of

        | Lambda (rules, _) ->
          let new_rules = 
              map (fn (fn_pat, cond, fn_body) -> 
                     let let_pat      = VarPat (("x", global_type), noPos) in
                     let let_var      = Var    (("x", global_type), noPos) in
                     let let_bindings = [(let_pat, fn_body)] in
                     let updates      = map (fn (field_id, field_var as Fun (_, field_type, _)) ->
                                               makeSetf (field_var,
                                                         Apply (Fun (Project field_id, 
                                                                     Arrow (global_type, field_type, noPos),
                                                                     noPos),
                                                                let_var,
                                                                noPos)))
                                            global_var_map
                     in
                     let new_let = Let (let_bindings, Seq(updates, noPos), noPos) in
                     % let setf_args = Record ([("1", global_var), ("2", body)], noPos) in
                     % let new_tm   = Apply  (setfRef, setf_args, noPos) in
                     (fn_pat, cond, new_let))
                  rules
          in
          let new_dfn = Lambda (new_rules, noPos) in
          let _ = if tracing? then
                    let _ = writeLine ""                          in
                    let _ = writeLine ("Globalize:  changing init fn " ^ show global_init_name) in
                    let _ = writeLine (printTerm old_dfn)         in
                    let _ = writeLine "  => "                     in
                    let _ = writeLine (printTerm new_dfn)         in
                    let _ = writeLine ""                          in
                    ()
                  else
                    ()
          in
          Some new_dfn

        | TypedTerm (tm, typ, _) -> 
          aux tm

        | Pi (_, tm, _) ->
          aux tm

        | _ ->
          let _ = writeLine("--------------------") in
          let _ = writeLine("??? Globalize: global init fn " ^ show global_init_name ^ " is not defined using lambda rules:") in
          let _ = writeLine("   ----   ") in
          let _ = writeLine(printTerm info.dfn) in
          let _ = writeLine("   ----   ") in
          let _ = writeLine(anyToString info.dfn) in
          let _ = writeLine("--------------------") in
          None
  in
  case aux old_dfn of
    | Some new_dfn -> Some (info << {dfn = new_dfn})
    | _ -> None

 %% ================================================================================
 %% Remove vars of given type from pattern
 %% ================================================================================

 op [a] renumber (fields : List (Id * a)) : List (Id * a) =
  %% [("1", a), ("2", b), ("4", c), ("5", d)]
  %%   =>
  %% [("1", a), ("2", b), ("3", c), ("4", d)]
  if forall? (fn (id, _) -> natConvertible id) fields then
    let (new_fields, _) =
        foldl (fn ((row, n), (_, tm)) ->
                 (row ++ [(show n, tm)], n+1))
              ([], 1)
              fields
    in
    new_fields
  else
    fields

 op globalizeAliasPat (context                       : Context)
                      (vars_to_remove                : MSVarNames) % vars of global type, remove on sight
                      (pat as AliasPat (p1, p2, pos) : MSPattern)
  : Ids * GlobalizedPattern = 
  let (ids1, opt_new_p1) = globalizePattern context vars_to_remove p1 in
  let (ids2, opt_new_p2) = globalizePattern context vars_to_remove p2 in
  (ids1 ++ ids2,
   case (opt_new_p1, opt_new_p2) of
     | (GlobalVarPat, _)                -> GlobalVarPat
     | (_, GlobalVarPat)                -> GlobalVarPat
     | (Changed new_p1, Changed new_p2) -> Changed (AliasPat (new_p1, new_p2, noPos))
     | (Changed new_p1, Unchanged)      -> Changed (AliasPat (new_p1, p2,     noPos))
     | (Unchanged,      Changed new_p2) -> Changed (AliasPat (p1,     new_p2, noPos))
     | (Unchanged,      Unchanged)      -> Unchanged)

 op globalizeEmbedPat (context                                 : Context)
                      (vars_to_remove                          : MSVarNames) % vars of global type, remove on sight
                      (pat as EmbedPat (id, opt_pat, typ, pos) : MSPattern)
  : Ids * GlobalizedPattern = 
  % let _ = writeLine("??? globalize ignoring EmbedPat: " ^ anyToString pat) in
  ([], Unchanged)

 op globalizeRecordPat (context                 : Context)
                       (vars_to_remove          : MSVarNames) % vars of global type, remove on sight
                       (RecordPat (fields, pos) : MSPattern)
  : Ids * GlobalizedPattern = 
  let
    def aux (vars_to_remove, new_fields, old_fields, changed?, shortened?) =
      case old_fields of
        | [] -> (vars_to_remove, new_fields, changed?, shortened?)
        | (id, pat) :: ptail ->
          let (ids, opt_pat) = globalizePattern context vars_to_remove pat in
          let new_vars_to_remove = vars_to_remove ++ ids in
          let (new_fields, changed?, shortened?) =
              case opt_pat of
                | Changed new_pat -> (new_fields ++ [(id, new_pat)], true, shortened?)
                | Unchanged       -> (new_fields ++ [(id, pat)], changed?, shortened?)
                | GlobalVarPat    -> (new_fields, true, true)
          in
          aux (new_vars_to_remove, new_fields, ptail, changed?, shortened?)
  in
  let (vars_to_remove, new_fields, changed?, shortened?) = aux ([], [], fields, false, false) in
  %% can't reduce to a single global var pat, as that would be removed by aux
  (vars_to_remove,
   if changed? then
     Changed (case new_fields of
                | [(id, pat)] | natConvertible id -> pat
                | _ -> 
                  if shortened? then
                    RecordPat (renumber new_fields, noPos)
                  else
                    RecordPat (new_fields, noPos))
   else
     Unchanged)

 op globalizeQuotientPat (context                                  : Context)
                         (vars_to_remove                           : MSVarNames) % vars of global type, remove on sight
                         (pat as (QuotientPat (p1, _, _, _)) : MSPattern)
  : Ids * GlobalizedPattern = 
  globalizePattern context vars_to_remove p1

 op globalizeRestrictedPat (context                              : Context)
                           (vars_to_remove                       : MSVarNames) % vars of global type, remove on sight
                           (pat as (RestrictedPat (p1, tm, pos)) : MSPattern)
  : Ids * GlobalizedPattern = 
  globalizePattern context vars_to_remove p1

 op globalType? (context : Context) (typ : MSType) : Bool =
  possiblySubtypeOf? (typ, context.global_type, context.spc)

 op globalizeVarPat (context                          : Context)
                    (vars_to_remove                   : MSVarNames) % vars of global type, remove on sight
                    (pat as (VarPat ((id, typ), pos)) : MSPattern)
  : Ids * GlobalizedPattern =
  if globalType? context typ then
    ([id], GlobalVarPat)
  else
    ([], Unchanged)

 op globalizeWildPat (context                     : Context)
                     (vars_to_remove              : MSVarNames) % vars of global type, remove on sight
                     (pat as (WildPat (typ, pos)) : MSPattern)
  : Ids * GlobalizedPattern =
  if globalType? context typ then
    ([], GlobalVarPat)
  else
    ([], Unchanged)

 op globalizeTypedPat (context                          : Context)
                      (vars_to_remove                   : MSVarNames) % vars of global type, remove on sight
                      (pat as (TypedPat (p1, typ, pos)) : MSPattern)
  : Ids * GlobalizedPattern =
  %% TODO: ??
  globalizePattern context vars_to_remove p1

 op globalizePattern (context        : Context)
                     (vars_to_remove : MSVarNames)  % vars of global type, remove on sight
                     (pat            : MSPattern) 
  : Ids * GlobalizedPattern = 
  case pat of
    | AliasPat      _ -> globalizeAliasPat      context vars_to_remove pat
    | VarPat        _ -> globalizeVarPat        context vars_to_remove pat
    | WildPat       _ -> globalizeWildPat       context vars_to_remove pat
    | EmbedPat      _ -> globalizeEmbedPat      context vars_to_remove pat
    | RecordPat     _ -> globalizeRecordPat     context vars_to_remove pat
    | QuotientPat   _ -> globalizeQuotientPat   context vars_to_remove pat
    | RestrictedPat _ -> globalizeRestrictedPat context vars_to_remove pat
    | TypedPat      _ -> globalizeTypedPat      context vars_to_remove pat
   % literals can never be the state
   %| BoolPat       
   %| NatPat        
   %| StringPat     
   %| CharPat       
    | _ -> ([], Unchanged)


 %% ================================================================================
 %% Given global type, find patterns and terms of that type and remove them
 %% ================================================================================

 op makeGlobalAccess (context    : Context)
                     (field_name : Id)
                     (field_type : MSType) 
  : MSTerm =
  case findLeftmost (fn (id, _) -> id = field_name) context.global_var_map of
    | Some (_, var) -> var

 op substVarBindings (set_indices_bindings : List (MSTerm * MSTerm), get_indices : MSTerms, access : MSTerm) : MSTerm =
  % let _ = app (fn (x,y) -> writeLine("substVarBindings: set_binding = " ^ printTerm x ^ " -- " ^ printTerm y)) set_indices_bindings in
  % let _ = app (fn (x) -> writeLine("substVarBindings: get_index = " ^ printTerm x)) get_indices in
  let
    def aux (tm, args) =
      case args of
        | [] -> tm
        | arg :: args -> 
          let new_tm = Apply (tm, arg, noPos) in
          % let _ = writeLine ("substVarBindings : tm     = " ^ printTerm tm) in
          % let _ = writeLine ("substVarBindings : arg    = " ^ printTerm arg) in
          % let _ = writeLine ("substVarBindings : new_tm = " ^ printTerm new_tm) in
          aux (new_tm, args)
  in
  aux (access, get_indices)

 op makeGlobalFieldUpdates (context           : Context)
                           (vars_to_remove    : MSVarNames)      % vars of global type, remove on sight
                           (substitutions     : MSSubstitutions) % tm -> var
                           (merger            : MSTerm)          % RecordMerge
                           (Record (fields,_) : MSTerm)          % record of fields to update
  : MSTerm =
  let assignments =
      map (fn (id, old_value) ->
              let Some (_, global_var_op) = findLeftmost (fn (x, _) -> x = id) context.global_var_map in
              let new_value = case globalizeTerm context vars_to_remove substitutions old_value false of
                                | Changed new_value -> new_value
                                | GlobalVar -> 
                                  let _ = writeLine("Warning: Updating a single global field with the entire master global value.") in
                                  context.global_var
                                | _ -> old_value
              in
              %% Do not call expandBindings here.
              %% That could reintroduce terms with side effects that we purposely let-bound to serialize them.
              makeUpdate context.spc context.setf_entries global_var_op new_value)
          fields
  in
  Seq (assignments, noPos)

 op applyHeadType (tm : MSTerm, context : Context) : MSType =
  case tm of
    | Apply (t1, t2, _) -> applyHeadType (t1, context)
    | Fun (Op (qid, _), typ, _) -> 
      (case findTheOp (context.spc, qid) of
         | Some opinfo -> firstOpDefInnerType opinfo
         | _ -> inferType (context.spc, tm))
    | _ -> 
      inferType (context.spc, tm)
      
 op globalizeApply (context                     : Context)
                   (vars_to_remove              : MSVarNames)      % vars of global type, remove on sight
                   (substitutions               : MSSubstitutions) % tm -> varname
                   (tm as (Apply (t1, t2, pos)) : MSTerm)
  : GlobalizedTerm = 
  let
    def dom_type typ =
      case typ of
        | Arrow   (t1, _, _) -> Some t1
        | Subtype (t1, _, _) -> dom_type t1
        | _ -> None

    def retype_fun (tm, typ) =
      case tm of
        | Fun (x, _, pos) -> Fun (x, typ, pos)
        | _ ->
          let _ = writeLine ("??? Globalize expected a primtive Fun term for retyping, but got : " ^ compressWhiteSpace(printTerm tm)) in
          TypedTerm (tm, typ, pos)

    def globalize_merge_arg arg source? =
      case globalizeTerm context vars_to_remove substitutions arg source? of
        | Changed new_arg -> (true, new_arg)
        | GlobalVar -> 
          let _ = writeLine(if source? then
                              "Warning: using the master global var for a record update source."
                            else
                              "Warning: using the master global var for a record update target.")
          in
          (true, context.global_var)
        | Unchanged -> (false, arg)
  in
  case (t1, t2) of
    | (Fun (RecordMerge, _, _),  Record ([(_, Var ((id, _), _)), (_, t4)], _)) | id in? vars_to_remove 
      ->
      %%  special case for global update:  
      %%     local_var_to_be_globalized << {...}
      %%       =>
      %%     global_update (global_var, {...})
      let (_, new_t4) = globalize_merge_arg t4 true in
      %% new_t4 is now a record whose fields are a subset of those in the global type
      let new_tm = makeGlobalFieldUpdates context vars_to_remove substitutions t1 new_t4 in
      Changed new_tm
   | _ ->
     let opt_new_t1 = globalizeTerm context vars_to_remove substitutions t1 false in
     let opt_new_t2 = case (t1, t2) of
                        | (Fun (RecordMerge, _, _),  Record ([("1", t3), ("2", t4)], _)) ->
                          let (changed_t3?, new_t3) = globalize_merge_arg t3 false in
                          let (changed_t4?, new_t4) = globalize_merge_arg t4 true  in
                          if changed_t3? || changed_t4? then
                            Changed (Record ([("1", new_t3), ("2", new_t4)], noPos))
                          else
                            Unchanged
                        | _ -> 
                          globalizeTerm context vars_to_remove substitutions t2 false 
     in
     %% Vars to be removed will have been removed from inside t1 and t2, but if t1 or t2 itself 
     %% is global it will have been replaced with context.global_var

     let new_t1 = case opt_new_t1 of
                    | Changed new_t1 -> new_t1
                    | GlobalVar -> 
                      let _ = writeLine("Warning: Applying the master global var.") in
                      context.global_var
                    | Unchanged -> t1
     in
     case opt_new_t2 of

       | GlobalVar ->
         %% TODO: Changed new_t1
         %% was (f x ...)  where x had global type
         let head_type = applyHeadType (t1, context) in
         let head_type = unfoldToArrow (context.spc, head_type) in
        %let head_type = nullify_global (context, vars_to_remove, substitutions, head_type) in
         Changed (case dom_type head_type of
                    | Some dtype | globalType? context dtype ->
                      (case t1 of
                         | Fun (Project field_name, _, _) ->
                           %%  special case for global access:  
                           %%    (local_var_to_be_globalized.xxx)
                           %%      =>
                           %%    (global_var.xxx)
                           makeGlobalAccess context field_name (inferType (context.spc, tm))
                         | _ ->
                           case head_type of
                             | Arrow (_, Arrow _, _) ->
                               %% (f x y ...)  where x has global type, and domain of f is global type
                               %%   =>
                               %% (f y ...)
                               let range_type = inferType (context.spc, tm) in
                               retype_fun (t1, range_type)
                             | _ ->
                               %% (f x) where x has global type, and domain of f is global type
                               %%   =>
                               %% (f ())
                               Apply (new_t1, nullTerm, pos))
                    | _ ->
                      %% (f x y ...)  where x has global type, but domain of f is NOT global type (presumably is polymorphic)
                      %%   =>
                      %% (f gvar y ...)
                      Apply (new_t1, context.global_var, pos))

       | Changed new_t2 ->
         Changed (Apply (new_t1, new_t2, pos))
                    
       | _ ->
         case opt_new_t1 of
           | Changed new_t1 ->
             Changed (Apply (new_t1, t2, pos))

           | _ ->
             Unchanged

 %% ================================================================================

 op globalizeRecord (context              : Context)
                    (vars_to_remove       : MSVarNames)      % vars of global type, remove on sight
                    (substitutions        : MSSubstitutions) % tm -> varname
                    (Record (fields, pos) : MSTerm)
                    (under_merge?         : Bool)
  : GlobalizedTerm = 
  let (changed?, shortened?, new_fields, opt_prefix) = 
      foldl (fn ((changed?, shortened?, new_fields, opt_prefix), (id, old_tm)) -> 
               let (changed?, new_tm) = 
                   case globalizeTerm context vars_to_remove substitutions old_tm false of
                     | Changed new_tm -> (true, new_tm)
                     | Unchanged -> (changed?, old_tm)
                     | GlobalVar -> (true, old_tm) 
               in
               let tt = inferType (context.spc, old_tm) in
               if globalType? context tt then
                 % evaluate term of global type before evaluating tuple, and don't include that result in tuple
                 (true, 
                  true,
                  new_fields,
                  % but no need to evaluate term of global type if it is just a variable
                  case new_tm of
                    | Var _ -> opt_prefix      
                    | _     -> Changed new_tm)
               else
                 (changed?, 
                  shortened?,
                  new_fields ++ [(id, new_tm)], 
                  opt_prefix))
            (false, false, [], Unchanged)
            fields 
  in
  if changed? then
    let new_result =
        case new_fields of
          | [(lbl, tm)] | (~ under_merge?) && natConvertible lbl -> 
            % If a var x is removed from 2-element record '(x, y)' 
            %  simplify resulting singleton record '(y)' down to 'y'.
            % But don't simplify a 1-element record with an explicitly named 
            %  field such as {a = x}
            % And don't simply records that appear as second arg to RecordMerge
            tm  
          | _ -> 
            Record (if shortened? then renumber new_fields else new_fields,
                    pos)
    in
    Changed (case opt_prefix of
               | Changed prefix -> Seq ([prefix, new_result], noPos)
               | _ -> new_result)
  else 
    Unchanged

 %% ================================================================================
 %% Given global type, find argument variables of that type and remove them
 %% ================================================================================

 op globalizeLet (context                   : Context)
                 (outer_vars_to_remove      : MSVarNames)      % vars of global type, remove on sight
                 (substitutions             : MSSubstitutions) % tm -> varname
                 (tm as Let (bindings, body, pos) : MSTerm)
  : GlobalizedTerm = 
  let (new_bindings, all_vars_to_remove, local_vars_to_remove, changed_bindings?) = 
      %% since Let's in practice are always 1 element lists, this is a bit of overkill:
      foldl (fn ((bindings, all_vars_to_remove, local_vars_to_remove, changed_binding?), (pat, tm)) -> 
               let (changed_tm?, new_tm) =
                   case globalizeTerm context outer_vars_to_remove substitutions tm false of
                     | Changed new_tm -> (true, new_tm)
                     | GlobalVar -> 
                       let _ = writeLine("Warning: Binding a let var to the master global var.") in
                       (true, context.global_var)
                     | _ -> (false, tm)
               in
               let (new_vars_to_remove, opt_new_pat) = globalizePattern context outer_vars_to_remove pat in
               let new_pat =
                   case opt_new_pat of
                     | Unchanged       -> pat
                     | Changed new_pat -> new_pat
                     | GlobalVarPat    -> 
                       %% this should be nullType, but inferType should have worked and not entered the debugger
                       wildPat nullType % (inferType (context.spc, new_tm))
               in
               let new_bindings = bindings ++ [(new_pat, new_tm)] in
               case new_vars_to_remove of
                 | [] -> (new_bindings, 
                          all_vars_to_remove, 
                          local_vars_to_remove, 
                          changed_tm?)
                 | _ -> (new_bindings, 
                         all_vars_to_remove ++ new_vars_to_remove,
                         local_vars_to_remove ++ new_vars_to_remove,
                         true))
            ([], outer_vars_to_remove, [], false)
            bindings 
  in
  let substitutions = [] in

  let tame_bindings =
      foldl (fn (tame_bindings, new_binding) ->
               case new_binding of
                 | (WildPat _, _) -> tame_bindings
                 | (pat, tm) -> 
                   % let _ = writeLine ("tame binding: " ^ printPattern pat ^ " = " ^ printTerm tm ^ "\n") in
                   tame_bindings ++ [(pat, tm)])
            []
            new_bindings
  in
  let context = context << {let_bindings = tame_bindings ++ context.let_bindings} in
  
  let opt_new_body  = globalizeTerm context all_vars_to_remove substitutions body false in
  let (changed_body?, new_body) = 
      case opt_new_body of
        | Changed new_body -> 
          (true,  new_body)

        | GlobalVar ->
          (true, nullTerm)

        | Unchanged -> 
          (false, body)
  in
  if changed_bindings? || changed_body? then
    Changed (Let (new_bindings, new_body, pos))
  else
    Unchanged

 %% ================================================================================

 op globalizeLetRec (context                      : Context)
                    (vars_to_remove               : MSVarNames)  % vars of global type, remove on sight
                    (substitutions                : MSSubstitutions) % tm -> varname
                    (LetRec (bindings, body, pos) : MSTerm)
  : GlobalizedTerm = 
  %% (old_bindings   : List (MSVar * MSTerm))  (old_body       : MSTerm) 
  Unchanged

 op globalizeLambda (context             : Context)
                    (vars_to_remove      : MSVarNames)      % vars of global type, remove on sight
                    (substitutions       : MSSubstitutions) % tm -> varname
                    (tm as Lambda (rules, pos) : MSTerm)
  : GlobalizedTerm = 
  let 
    def globalizeRule (rule as (pat, cond, body)) =
      let (new_vars_to_remove, opt_new_pat) = globalizePattern context vars_to_remove pat in
      let vars_to_remove = vars_to_remove ++ new_vars_to_remove in
      let substitutions = [] in
      let opt_new_body = globalizeTerm context vars_to_remove substitutions body false in
      let new_body = case opt_new_body of
                       | Changed new_body -> new_body
                       | GlobalVar -> nullTerm
                       | Unchanged -> body
      in
      case opt_new_pat of
        | Unchanged ->
          (case opt_new_body of
             | Changed new_body -> Changed (pat, myTrue, new_body)
             | GlobalVar        -> Changed (pat, myTrue, new_body)
             | Unchanged        -> Unchanged)

        | Changed new_pat ->
          Changed (new_pat, myTrue, new_body)

        | GlobalVarPat ->
          (case new_body of
             | Lambda ([(inner_pat, new_cond, inner_body)], _) ->
               %% fn (x:Global) -> fn (new_pat) -> inner_body
               %%  =>
               %%                  fn (new_pat) -> inner_body
               Changed (inner_pat, myTrue, inner_body)
             | _ ->
               %% fn (x:Global) -> body
               %%  =>
               %% fn () -> new_body
               Changed (nullPat, myTrue, new_body))

  in
  let opt_new_rules = map globalizeRule rules in
  if exists? (fn opt_rule -> case opt_rule of | Changed _ -> true | _ -> false) opt_new_rules then
    let new_rules = map2 (fn (rule, opt_new_rule) -> 
                            case opt_new_rule of
                              | Changed new_rule -> new_rule
                              | _ -> rule)
                         (rules, opt_new_rules)
    in
    Changed (Lambda (new_rules, pos))
  else
    Unchanged

 %% ================================================================================

 op globalizeIfThenElse (context                      : Context)
                        (vars_to_remove               : MSVarNames)  % vars of global type, remove on sight
                        (substitutions                : MSSubstitutions) % tm -> varname
                        (IfThenElse (t1, t2, t3, pos) : MSTerm)
  : GlobalizedTerm = 
  let opt_new_t1 = globalizeTerm context vars_to_remove substitutions t1 false in
  let opt_new_t2 = globalizeTerm context vars_to_remove substitutions t2 false in
  let opt_new_t3 = globalizeTerm context vars_to_remove substitutions t3 false in
  case (opt_new_t1, opt_new_t2, opt_new_t3) of
    | (Unchanged, Unchanged, Unchanged) -> 
      Unchanged 
    | _ -> 
      let new_t1 = case opt_new_t1 of
                     | Changed new_t1 -> new_t1
                     | GlobalVar -> 
                       let _ = writeLine ("Warning:  Using the master global var as the predicate in an IfThenElse.") in
                       context.global_var
                     | Unchanged -> t1
      in
      let new_t2 = case opt_new_t2 of
                     | Changed new_t2 -> new_t2
                     | GlobalVar -> nullTerm
                     | Unchanged -> t2
      in
      let new_t3 = case opt_new_t3 of
                     | Changed new_t3 -> new_t3
                     | GlobalVar -> nullTerm
                     | _ -> t3
      in
      Changed (IfThenElse (new_t1, new_t2, new_t3, pos))


 %% ================================================================================

 op globalizeSeq (context        : Context)
                 (vars_to_remove : MSVarNames)      % vars of global type, remove on sight
                 (substitutions  : MSSubstitutions) % tm -> varname
                 (Seq (tms, pos) : MSTerm) 
  : GlobalizedTerm = 
  let opt_new_tms = map (fn tm -> globalizeTerm context vars_to_remove substitutions tm false) tms in
  if exists? (fn opt_tm -> case opt_tm of | Changed _ -> true | GlobalVar -> true | _ -> false) opt_new_tms then  
    let pairs = zip (tms, opt_new_tms) in
    let new_tms = foldl (fn (new_tms, (tm, opt_new_tm)) ->
                           case opt_new_tm of 
                             | Unchanged      -> new_tms ++ [tm]
                             | Changed new_tm -> new_tms ++ [new_tm]
                             | GlobalVar      -> new_tms)
                        []
                        pairs
    in
    Changed (case new_tms of
               | [tm] -> tm
               | _ -> Seq (new_tms, pos))
  else
    Unchanged

 %% ================================================================================

 op nullify_global (context        : Context,
                    vars_to_remove : MSVarNames,      % vars of global type, remove on sight
                    substitutions  : MSSubstitutions, % tm -> varname
                    xtyp           : MSType)
  : MSType =
  let
    def aux typ =
      if globalType? context typ then
        nullType
      else
        case typ of

          | Arrow (dom, rng, pos) -> 
            let rng = aux rng in
            if globalType? context dom then
              case rng of
                | Arrow _ -> rng
                | _ -> Arrow (aux dom, rng, noPos)
            else
              Arrow (aux dom, rng, noPos)

          | Product (fields, pos) ->
            (let new_fields = foldl (fn (fields, (id, typ)) ->
                                       if globalType? context typ then
                                         fields
                                       else
                                         fields ++ [(id, aux typ)])
                                    []
                                    fields
             in
             case new_fields of
               | [(id, typ)] | natConvertible id -> typ
               | _ -> Product (renumber new_fields, noPos))
          | CoProduct (fields, pos) -> 
            let new_fields = foldl (fn (fields, field as (id, opt_typ)) ->
                                      case opt_typ of
                                        | Some typ ->
                                          fields ++ [(id, Some (aux typ))]
                                        | _ ->
                                          fields ++ [field])
                                   []
                                   fields
            in
            CoProduct (new_fields, noPos)

          | Quotient (typ, tm, pos) -> 
            let new_typ = aux typ in
            let new_tm = 
                case globalizeTerm context vars_to_remove substitutions tm false of
                  | Changed new_tm -> new_tm
                  | GlobalVar -> 
                    let _ = writeLine("Warning: Using the master global var as a quotient relation.") in
                    context.global_var
                  | Unchanged -> tm
            in
            Quotient (new_typ, new_tm, pos)

          | Subtype (typ, tm, pos) -> 
            let new_typ = aux typ in
            let new_tm = 
                case globalizeTerm context vars_to_remove substitutions tm false of
                  | Changed new_tm -> new_tm
                  | GlobalVar -> 
                    let _ = writeLine("Warning: Using the master global var as a subtype predicate.") in
                    context.global_var
                  | Unchanged -> tm
            in
            Subtype (new_typ, new_tm, pos)

          | Pi (tvs, typ, pos) -> Pi (tvs, aux typ, pos)
            
          | And (tm :: _, _) -> aux tm
            
          | _ -> typ
  in
  aux xtyp

 op globalizeTypedTerm (context                  : Context)
                       (vars_to_remove           : MSVarNames)      % vars of global type, remove on sight
                       (substitutions            : MSSubstitutions) % tm -> varname
                       (TypedTerm (tm, typ, pos) : MSTerm)
  : GlobalizedTerm = 
  case globalizeTerm context vars_to_remove substitutions tm false of
    | Changed new_tm ->
      let new_typ = nullify_global (context, vars_to_remove, substitutions, typ) in 
      Changed (TypedTerm (new_tm, new_typ, pos))

    | GlobalVar -> GlobalVar

    | Unchanged ->
        case tm of
          | Any  _ -> let new_typ = nullify_global (context, vars_to_remove, substitutions, typ) in
                          if equalType?(new_typ, typ)
                            then Unchanged
                            else Changed (TypedTerm (tm, new_typ, pos))
                       
          | _ -> Unchanged

 op globalizeFun (context        : Context)
                 (vars_to_remove : MSVarNames)      % vars of global type, remove on sight
                 (substitutions  : MSSubstitutions) % tm -> varname
                 (term           : MSTerm) 
  : GlobalizedTerm =
  case term of

    | Fun (old_ref, old_type, _) -> 
      let new_type = nullify_global (context, vars_to_remove, substitutions, old_type) in 
      if equalType? (new_type, old_type) then
        Unchanged
      else
        let new_ref = old_ref in
        % TODO:
        % let new_ref = case old_ref of 
        %                | Op (Qualified (_,        id), _) -> 
        %                  Op (Qualified (global_q, id), Nonfix) 
        %                | _ -> 
        %                  old_ref
        % in
        Changed (Fun (new_ref, new_type, gPos))

    | _ -> 
      Unchanged

 %% ================================================================================

 op globalizePi (context              : Context)
                (vars_to_remove       : MSVarNames)      % vars of global type, remove on sight
                (substitutions        : MSSubstitutions) % tm -> varname
                (Pi (tyvars, tm, pos) : MSTerm)
  : GlobalizedTerm = 
  case globalizeTerm context vars_to_remove substitutions tm false of
    | Changed new_tm ->
      Changed (Pi (tyvars, new_tm, pos)) % TODO: remove unused tyvars

    | GlobalVar ->
      GlobalVar

    | _ ->
      Unchanged

 %% ================================================================================

 op globalizeAnd (context        : Context)
                 (vars_to_remove : MSVarNames)      % vars of global type, remove on sight
                 (substitutions  : MSSubstitutions) % tm -> varname
                 (And (tms, pos) : MSTerm)
  : GlobalizedTerm = 
  case tms of
    | tm :: _ -> globalizeTerm context vars_to_remove substitutions tm false
    | [] -> Unchanged

 %% ================================================================================

 op reviseGlobalRefs (substitutions : MSSubstitutions) (tm : MSTerm) : MSTerm =
  let 
    def revise_global_ref (subtm : MSTerm) =
      case subtm of
        | Apply (Fun (Project f1, _, _),
                 Var ((v1, _), _),
                 _) 
          ->
          (case findLeftmost (fn {global_var_id = v2, field_id = f2, temp_var = _} -> 
                                v2 = v1 && f2 = f1)
                             substitutions 
             of
             | Some subst -> Var (subst.temp_var, noPos)
             | _ -> subtm)
        | _ ->
          subtm
  in
  mapSubTerms revise_global_ref tm 

 op globalFieldType (context : Context) (f1 : MSFieldName) : MSType =
  let Some (_, Fun (_, field_type, _)) =  % the type of the field (not the arrow type)
      findLeftmost (fn (f2, _) -> f2 = f1) 
                   context.global_var_map 
  in
  field_type

 op deconflict (context     : Context, 
                global_vars : MSVarNames, 
                conflicts   : ConflictingRefs, 
                term        : MSTerm) 
  : MSTerm =
  let
    def aux (n, tm) =
      let grefs = globalRefsIn context global_vars tm in
      if (exists? (fn (var, field) -> 
                     exists? (fn (mode, v, f) -> 
                                mode = Access && v = var && f = field) 
                             grefs)
                  conflicts)
         &&
         ~ (exists? (fn (var, field) -> 
                       exists? (fn (mode, v, f) -> 
                                  mode = Update && v = var && f = field) 
                               grefs)
                    conflicts)
        then
          let new_vname = "deconflict_" ^ show n in
          let new_vtype = inferType (context.spc, tm) in
          let new_var   = (new_vname, new_vtype) in
          Some (VarPat (new_var, noPos),
                Var    (new_var, noPos))
      else
        None
  in
  case term of
    | Apply (Fun (RecordMerge, _, _), _, _) ->
      term

    | Apply (x, y, _) -> 
      let (xbindings, x) = case aux (0, x) of
                             | Some (pat, var) -> ([(pat, x)], var)
                             | _ ->               ([],         x)
      in
      let (ybindings, y) = case aux (1, y) of
                             | Some (pat, var) -> ([(pat, y)], var)
                             | _ ->               ([],         y)
      in
      let bindings = xbindings ++ ybindings in
      (case bindings of
         | [] -> term
         | _ ->
           Let (bindings, Apply (x, y, noPos), noPos))

    | Record (fields, _) -> 
      let (n, bindings, fields) = 
          foldl (fn ((n, bindings, fields), field as (id, tm)) ->
                   case aux (n, tm) of
                     | Some (pat, var) ->
                       (n+1,
                        bindings ++ [(pat, tm)],
                        fields   ++ [(id, var)])
                     | _ ->
                       (n, bindings, fields  ++ [field]))
                (0, [], [])
                fields
      in
      (case bindings of
         | [] -> term
         | _ ->
           Let (bindings, Record (fields, noPos), noPos))

    | Seq (tms, _) -> 
      % let _ = writeLine("Seq Term = " ^ printTerm term) in
      let (_, bindings, tms) =
          foldl (fn ((n, bindings, tms), tm) -> 
                   case aux (n, tm) of
                     | Some (pat, var) ->
                       (n + 1,
                        bindings ++ [(pat, tm)],
                        tms      ++ [var])
                     | _ ->
                       (n, bindings, tms ++ [tm]))
                (0, [], [])
                tms
      in
      (case bindings of
         | [] -> term
         | _ ->
           Let (bindings, Seq (tms, noPos), noPos))
      
     | _ -> 
       term

 op globalizeTerm (context        : Context)
                  (vars_to_remove : MSVarNames)  % vars of global type, remove on sight
                  (substitutions  : MSSubstitutions) % tm -> varname
                  (term           : MSTerm) 
                  (under_merge?   : Bool) 
  : GlobalizedTerm = 
  let
    def add_bindings substs body =
      case substs of
        | {global_var_id, field_id, temp_var} :: substs ->
          let pat             = VarPat (temp_var, noPos) in
          let field_type      = globalFieldType context field_id in
          let projection_type = Arrow (context.global_type, field_type, noPos) in
          let tm              = Apply (Fun (Project field_id, projection_type, noPos),
                                       Var ((global_var_id, context.global_type), noPos),
                                       noPos)
          in
          let new_term        = 
          Let ([(pat, tm)], body, noPos) in
          add_bindings substs new_term
        | _ ->
          body
  in
  let conflicts = conflictingGlobalRefsIn context vars_to_remove term in
  let (term, conflicts) = case conflicts of
                            | [] -> (term, [])
                            | _ ->
                              %% introduce lets to linearize accesses before updates in parallel terms
                              let term      = deconflict (context, vars_to_remove, conflicts, term) in
                              % let _ = writeLine("Before: " ^ printTerm term) in
                              % let _ = writeLine("        " ^ anyToString conflicts) in
                              let term      = abstractCommonSubExpressions (term, context.spc)      in
                              let conflicts = conflictingGlobalRefsIn context vars_to_remove term   in
                              % let _ = writeLine("After: " ^ printTerm term) in
                              % let _ = writeLine("       " ^ anyToString conflicts) in
                              (term, conflicts)
  in
  let substitutions = map (fn (var_id, field_id) ->
                             let temp_id   = "temp_" ^ var_id ^ "_" ^ field_id in
                             let temp_type = globalFieldType context field_id in
                             let temp_var  = (temp_id, temp_type) in
                             {global_var_id = var_id, 
                              field_id      = field_id, 
                              temp_var      = temp_var})
                          conflicts
  in
  let term         = reviseGlobalRefs substitutions term in
  let term         = add_bindings substitutions term     in
  let opt_term =
      case term of
        | Apply      _ -> globalizeApply      context vars_to_remove substitutions term
        | Record     _ -> globalizeRecord     context vars_to_remove substitutions term under_merge?
        | Let        _ -> globalizeLet        context vars_to_remove substitutions term
        | LetRec     _ -> globalizeLetRec     context vars_to_remove substitutions term
        | Lambda     _ -> globalizeLambda     context vars_to_remove substitutions term
        | IfThenElse _ -> globalizeIfThenElse context vars_to_remove substitutions term
        | Seq        _ -> globalizeSeq        context vars_to_remove substitutions term
        | TypedTerm  _ -> globalizeTypedTerm  context vars_to_remove substitutions term
        | Pi         _ -> globalizePi         context vars_to_remove substitutions term
        | And        _ -> globalizeAnd        context vars_to_remove substitutions term
          
        | Fun        _ -> globalizeFun        context vars_to_remove substitutions term

       %| ApplyN     _ -> Unchanged % not present after elaborateSpec is called
       %| Bind       _ -> Unchanged % should not be globalizing inside quantified terms
       %| The        _ -> Unchanged % should not be globalizing inside 'the' term
       %| Transform  _ -> Unchanged % doesn't make sense to globalize this
       %| Any        _ -> Unchanged % can appear within typed term, for example
          
        | Var ((id,typ), _) -> 
          if id in? vars_to_remove then
            GlobalVar
          else if equivType? context.spc (typ, context.global_type) then
            GlobalVar
          else
            Unchanged

        | _ -> 
          Unchanged
  in
  case (opt_term, conflicts) of
    | (Unchanged, []) -> 
      Unchanged     
    | (Unchanged, _)  -> 
      Changed term  % consider changed if there are conflicts
    | _ ->
      opt_term      % changed or global
      
 %% ================================================================================

 op globalizeOpInfo (context    : Context,
                     old_info   : OpInfo)
  : OpInfo =
  let old_name as Qualified(q, id) = primaryOpName old_info in
  if baseOp? old_name then
    old_info
  else
    let old_dfn = case old_info.dfn of 
                    | And (tm :: _, _) -> tm 
                    | tm -> tm 
    in
    case globalizeTerm context [] [] old_dfn false of
      | Changed new_dfn -> 
        let new_name = old_name in % TODO: Qualified (global_q, id) in
        let new_info = old_info << {names = [new_name], dfn = new_dfn} in
        let _ = if context.tracing? then
                  let _ = writeLine ""                                                              in
                  let _ = writeLine ("Globalize: changing " ^ show old_name)                        in
                 %let _ = writeLine ("Globalize: adding " ^ show old_name ^ " => " ^ show new_name) in % TODO
                  let _ = writeLine (printTerm old_dfn)                                             in
                  let _ = writeLine "  => "                                                         in
                  let _ = writeLine (printTerm new_dfn)                                             in
                  let _ = writeLine ""                                                              in
                  ()
                else
                  ()
        in
        new_info

      | GlobalVar -> 
        let _ = writeLine ("Warning: value of op is master global var") in
        let new_dfn  = context.global_var in
        let new_info = old_info << {dfn = new_dfn} in
        let _ = if context.tracing? then
                  let _ = writeLine ""                                       in
                  let _ = writeLine ("Globalize: changing " ^ show old_name) in
                  let _ = writeLine (printTerm old_dfn)                      in
                  let _ = writeLine "  => "                                  in
                  let _ = writeLine (printTerm new_dfn)                      in
                  let _ = writeLine ""                                       in
                  ()
                else
                  ()
        in
        new_info

      | Unchanged -> 
        let _ = if context.tracing? then
                  let _ = writeLine("Globalize: no change to " ^ show old_name) in
                  let _ = writeLine (printTerm old_dfn)                         in
                  let _ = writeLine ""                                          in
                  ()
                else
                  ()
        in
        old_info

 op genericSlice (ms_spec    : Spec,
                  root_ops   : QualifiedIds,
                  root_types : QualifiedIds)
  : Slice =
  let
    def ignore_language_morphisms spc = []

    def vacuous_oracle (ref, slice) = None

  in
  executionSlice (ms_spec, ignore_language_morphisms, vacuous_oracle, root_ops, root_types)

 op replaceLocalsWithGlobalRefs (context : Context) : SpecCalc.Env (Spec * Bool) =
  (*
   * At this point, we know:
   *  gtype names a unique existing base type in spc,
   *  gvar  names a unique existing op in spc, of type 'gtype'
   *
   * For every op f in spc, remove local vars of type gtype, and replace with references to gvar.
   * If the final returned value is constructed "on-the-fly", add an assignment of that value to gvar.
   *)
  let spc = context.spc in
  let (root_ops, root_types) = 
      case context.root_ops of
        | [] -> topLevelOpsAndTypesExcludingBaseSubsts spc 
        | root_ops -> (root_ops, [])
  in

  % first slice gets ops to be globalized
  let first_slice        = genericSlice (spc, root_ops, root_types) in
  let ops_in_first_slice = opsInSlice   first_slice                 in

  % globalizing those ops may introduce new references to global vars
  % (and might remove some references to other ops in the process)
  let globalized_spec_ops =
      foldl (fn (new_ops, name  as Qualified(q,id)) ->
               case findTheOp (spc, name) of
                 | Some info -> 
                   let new_info = 
                       if context.global_init_name = name then % don't revise init op
                         info
                       else
                         globalizeOpInfo (context, info) 
                   in
                   insertAQualifierMap (new_ops, q, id, new_info) % TODO: global_q
                 | _ -> 
                   let _ = writeLine("??? Globalize could not find op " ^ show name) in
                   new_ops)
            spc.ops
            ops_in_first_slice
  in
  let spec_with_globalized_ops_added = spc << {ops = globalized_spec_ops} in

  % redo slice, this time chasing through any new references introduced just above
  % (also ignoring any old references removed just above)
 %let root_ops = map (fn Qualified(q, id) -> Qualified(global_q, id)) root_ops in % TODO
  let second_slice = genericSlice (spec_with_globalized_ops_added, root_ops, root_types) in
  let new_ops =
      let base_ops = mapiPartialAQualifierMap (fn (q, id, info) ->
                                                 if baseOp? (Qualified(q, id)) then
                                                   Some info
                                                 else
                                                   None)
                                              spec_with_globalized_ops_added.ops
      in
      let ops_in_second_slice = opsInSlice second_slice in

      % new ops are the base ops plus ops reached in second slice
      foldl (fn (new_ops, name as Qualified (q, id)) ->
               case findTheOp (spec_with_globalized_ops_added, name) of
                 | Some info -> 
                   let new_info =
                       if context.global_init_name = name then % don't revise init op
                         info
                       else
                         globalizeOpInfo (context, info) 
                   in
                   insertAQualifierMap (new_ops, q, id, new_info)
                 | _ -> 
                   let _ = writeLine("Internal confusion: Globalize could not find op " ^ show name) in
                   new_ops)
            base_ops
            ops_in_second_slice
  in
  let new_types =
      let base_types = mapiPartialAQualifierMap (fn (q, id, info) ->
                                                   if baseType? (Qualified(q, id)) then
                                                     Some info
                                                   else
                                                     None)
                                                spec_with_globalized_ops_added.types
      in
      let types_in_second_slice = typesInSlice second_slice in

      % new types are the base types plus types reached in second slice
      foldl (fn (new_types, name as Qualified (q, id)) ->
               case findTheType (spec_with_globalized_ops_added, Qualified (q, id)) of
                 | Some info -> 
                   insertAQualifierMap (new_types, q, id, info)
                 | _ -> 
                   let _ = writeLine("Internal confusion: Globalize could not find type " ^ show name) in
                   new_types)
            base_types
            types_in_second_slice
  in
  let 
    def globalize_elements elements =
      % uses new_ops and new_types defined above...
      foldl (fn (new_elts, elt) ->
               case elt of
                 | Import (sc_term, imported_spec, imported_elts, pos) ->
                   new_elts ++ [Import (sc_term, 
                                        imported_spec, 
                                        globalize_elements imported_elts, 
                                        pos)]
                 | Type (Qualified(q,id), _) ->
                   (case findAQualifierMap (new_types, q, id) of
                      | Some _ -> new_elts ++ [elt]
                      | _ -> new_elts)
                 | TypeDef (Qualified(q,id), _) ->
                   (case findAQualifierMap (new_types, q, id) of
                      | Some _ -> new_elts ++ [elt]
                      | _ -> new_elts)
                 | Op (Qualified(q,id), _, _) ->
                   (case findAQualifierMap (new_ops, q, id) of
                      | Some _ -> new_elts ++ [elt]
                      | _ -> new_elts)
                 | OpDef (Qualified(q,id), _, _, _) ->
                   (case findAQualifierMap (new_ops, q, id) of
                      | Some _ -> new_elts ++ [elt]
                      | _ -> new_elts)
                 | Pragma   _ -> new_elts ++ [elt]  % used by later code generators
                 | Property _ -> new_elts ++ [elt]  % used by later code generators
                 | _ -> new_elts)
             []
             elements
  in
  let new_elements = globalize_elements spec_with_globalized_ops_added.elements in
  let new_spec = spc << {ops      = new_ops, 
                         types    = new_types,
                         elements = new_elements} 
  in
  return (new_spec, context.tracing?)

 op printTerms (tms : MSTerms) : String =
  foldl (fn (s, tm) -> s ^ " " ^ printTerm tm) "" tms

 op accessms (tm : MSTerm) : MSTerms =
  case tm of
    | Record (fields, _) -> map (fn (_, tm) -> tm) fields
    | _ -> [tm]

 op showIntermediateSpec (msg : String, spc : Spec) : SpecCalc.Env () =
  {
   print ("\n===" ^ msg ^ " ===\n");
   print (printSpecFlat spc);
   print ("\n=======\n")
  }

 op globalizeSingleThreadedType (spc              : Spec, 
                                 root_ops         : OpNames,
                                 global_type_name : TypeName, 
                                 global_var_id    : String,
                                 opt_ginit        : Option OpName,
                                 tracing?         : Bool)
  : SpecCalc.Env (Spec * Bool) =
  let global_var_name = Qualified (global_q, global_var_id) in

  %% access_update pairs are used to create dsstructive updates into complex left-hand-sides
  let setf_entries = findSetfEntries spc in
  let _ = 
      if tracing? then
        let _ = writeLine("===================") in
        let _ = writeLine("Accesss -- Updates") in
        let _ = map (fn setf_entry -> writeLine (printQualifiedId setf_entry.accesser_name ^ " -- " ^ printQualifiedId setf_entry.updater_name)) 
                    setf_entries
        in
        let _ = writeLine("===================") in
        ()
      else
        ()
  in

  {
   global_type_name <- checkGlobalType (spc, global_type_name);
   global_var_name  <- checkGlobalVar  (spc, global_var_name, global_type_name);
   global_type      <- return (Base (global_type_name, [], noPos));
   global_var       <- return (Fun (Op (global_var_name, Nonfix), global_type, noPos));
   global_init_name <- (case opt_ginit of
                          | Some ginit -> 
                            (case ginit of
                               | Qualified(_, "None") -> return ginit
                               | _ -> checkGlobalInitOp (spc, ginit, global_type_name))
                          | _ -> findInitOp (spc, global_type_name));

  %root_ops         <- return (root_ops ++ [global_init_name]);
   global_var_map   <- return (case findTheType (spc, global_type_name) of
                                 | Some info -> 
                                   (case info.dfn of
                                      | Product (pairs, _) ->
                                        map (fn (field_id, field_type) ->
                                               let Qualified (_, global_id) = global_type_name in
                                               let global_var_id = Qualified (global_q, field_id) in
                                               let global_var = Fun (Op (global_var_id, Nonfix), field_type, noPos) in
                                               (field_id, global_var))
                                            pairs
                                      | _ -> empty)
                                 | _ -> []);

   % This shouldn't be necessary, but is for now to avoid complaints from replaceLocalsWithGlobalRefs.
   spec_with_gset   <- addOp [setfQid] Nonfix false setfDef spc noPos;

   % print ("\nglobal_var_map: " ^ anyToString global_var_map ^ "\n");
   % showIntermediateSpec ("with gset", spec_with_gset);

   % Add global vars for the fields before running replaceLocalsWithGlobalRefs,
   % to avoid complaints about unknown ops.

   spec_with_gvars  <- foldM (fn spc -> fn (_, global_field_var) ->
                                let Fun (Op (global_field_var_name, _), gtype, _) = global_field_var in
                                let refine? = false                                 in
                                let dfn     = TypedTerm (Any noPos, gtype, noPos)   in
                                addOp [global_field_var_name] Nonfix refine? dfn spc noPos)
                             spec_with_gset
                             global_var_map;
                             
   % return (let slice = genericSlice (spec_with_gvars, root_ops, []) in describeSlice ("Added GVars", slice));
   % showIntermediateSpec ("with gvars", spec_with_gvars);

   spec_with_ginit  <- return (case (global_init_name : QualifiedId) of
                                 | Qualified (_, "None") -> 
                                   %% Use "None" as hack to say there is no initializer, so don't look for one.
                                   spec_with_gvars 
                                 | _ -> 
                                   case findTheOp (spec_with_gvars, global_init_name) of
                                     | Some info ->
                                       (case globalizeInitOp (spec_with_gvars,
                                                              global_type, 
                                                              global_var, 
                                                              global_var_map,
                                                              global_init_name,
                                                              tracing?)
                                          of
                                          | Some new_info ->
                                            let Qualified (q,id) = global_init_name in
                                            let new_ops  = insertAQualifierMap (spec_with_gvars.ops, q, id, new_info) in
                                            spec_with_gvars << {ops = new_ops}
                                          | _ ->
                                            let _ = writeLine ("??? Globalize could not revise init op " ^ show global_init_name) in
                                            spec_with_gvars)
                                     | _ -> 
                                       let _ = writeLine ("??? Op " ^ show global_init_name ^ " for producing initial global " ^ show global_type_name ^ " is undefined.") in
                                       spec_with_gvars);


   % return (let slice = genericSlice (spec_with_ginit, root_ops, []) in describeSlice ("Added ginit", slice));
   % showIntermediateSpec ("with ginit", spec_with_ginit);

   % hack to fix problem where 'global_var << {..}' was becoming just '{...}'
   spec_with_restored_record_merges <- return (SpecTransform.introduceRecordMerges spec_with_ginit);

   (globalized_spec, tracing?) <- let context = {spc              = spec_with_restored_record_merges,
                                                 root_ops         = root_ops,
                                                 global_var_name  = global_var_name,
                                                 global_type_name = global_type_name,
                                                 global_type      = global_type,
                                                 global_var       = global_var,     % if global type does not have fields
                                                 global_init_name = global_init_name,
                                                 global_var_map   = global_var_map, % if global type has fields
                                                 setf_entries     = setf_entries,
                                                 let_bindings     = [],
                                                 tracing?         = tracing?}
                                  in
                                  replaceLocalsWithGlobalRefs context;

   % Add the main global var after calling replaceLocalsWithGlobalRefs, 
   % since that would prune it away before any references were introduced.
   spec_with_gvar <- (case findTheOp (globalized_spec, global_var_name) of
                        | Some _ -> 
                          return globalized_spec
                        | _ -> 
                          let refine? = false                               in
                          let gtype   = Base (global_type_name, [],  noPos) in
                          let dfn     = TypedTerm (Any noPos, gtype, noPos) in
                          addOp [global_var_name] Nonfix refine? dfn globalized_spec noPos);

   % return (let slice = genericSlice (spec_with_gvar, root_ops ++ [global_var_name], []) in describeSlice ("Globalized spec with gvar", slice));
   % showIntermediateSpec ("with gvar", spec_with_gvar);

   return (spec_with_gvar, tracing?)
   }

 op SpecTransform.globalize (spc              : Spec)
                            (root_ops         : OpNames,
                             global_type_name : TypeName,
                             global_var_id    : String,
                             opt_ginit        : Option OpName,
                             % for now, tracing? has no default value,
                             % nor does "trace on/off" affect it
                             tracing?         : Bool) 
  : Spec =
  % let _ = writeLine ("root_ops         = " ^ anyToString root_ops         ) in
  % let _ = writeLine ("global_type_name = " ^ anyToString global_type_name ) in
  % let _ = writeLine ("global_var_id    = " ^ anyToString global_var_id    ) in
  % let _ = writeLine ("opt_ginit        = " ^ anyToString opt_ginit        ) in
  % let _ = writeLine ("tracing?         = " ^ anyToString tracing?         ) in
  let (spc, tracing?) =
      run (globalizeSingleThreadedType (spc,
                                        root_ops,
                                        global_type_name,
                                        global_var_id,
                                        opt_ginit,
                                        tracing?))
  in
  % for now, there is no way to pass tracing? along
  spc

 %% ================================================================================

}

