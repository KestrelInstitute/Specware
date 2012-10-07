Globalize qualifying spec
{
 import /Languages/MetaSlang/Specs/Environment
 import /Languages/MetaSlang/Transformations/SliceSpec
 import /Languages/MetaSlang/CodeGen/SubstBaseSpecs  
 import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements  % for addOp of global var

 %% TODO: need to emit (defsetf MAPSASVECTORS::TMAPPLY-2 MapsAsVectors::update-1-1-1)

 op compressWhiteSpace (s : String) : String =
  let 
    def whitespace? char = 
      char = #\s || char = #\n || char = #\t

    def compress (chars, have_whitespace?) =
      %% avoid deep recursions...
      let (chars, _) = 
          foldl (fn ((chars, have_whitespace?), char) ->
                   if whitespace? char then
                     if have_whitespace? then
                       (chars, have_whitespace?)
                     else
                       ([#\s] ++ chars, true)
                   else
                     ([char] ++ chars, false))
                ([], true)
                chars
      in
      reverse chars
  in
  implode (compress (explode s, true))

 type OpTypes         = AQualifierMap MSType
 type MSRule          = MSPattern * MSTerm * MSTerm
 type MSVar           = AVar Position
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

 type SetfEntry = {accesser_name   : OpName, 
                   updater_name    : OpName, 
                   accesser        : MSTerm, 
                   updater         : MSTerm, 
                   update_template : MSTerm,
                   setf_template   : MSTerm}

 type SetfEntries = List SetfEntry

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

   | The        (v, tm,   _) -> globalRefsIn context global_vars term
   | TypedTerm  (tm, _,   _) -> globalRefsIn context global_vars term
   | Pi         (_, tm,   _) -> globalRefsIn context global_vars term
   | And        (tm::_,   _) -> globalRefsIn context global_vars term

   | _ -> []
 
 %% ================================================================================

 op conflictingGlobalRefs (all_refs : List (Nat * GlobalRefs)) 
  : ConflictingRefs =
  foldl (fn (pairs, (i, xrefs)) ->
           foldl (fn (pairs, (r1, v1, f1)) ->
                    % for a conflict, at least one ref must be an update
                    if r1 = Update then 
                      foldl (fn (pairs, (j, yrefs)) ->
                               if i = j then
                                 pairs
                               else
                                 foldl (fn (pairs, (_, v2, f2)) ->
                                          % the matching ref can be access or update
                                          if v2 = v1 && f2 = f1 then 
                                            let new_pair = (v1, f1) in
                                            if new_pair in? pairs then
                                              pairs
                                            else
                                              pairs ++ [new_pair]
                                          else
                                            pairs)
                                       pairs
                                       yrefs)
                            pairs
                            all_refs
                    else
                      pairs)
                 pairs
                 xrefs)
        []
        all_refs

 %% ================================================================================

 op conflictingGlobalRefsIn (context     : Context) 
                            (global_vars : MSVarNames)
                            (term        : MSTerm) 
  : ConflictingRefs =
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

 op nullTerm : MSTerm    = Record  ([], noPos)
 op nullType : MSType    = Product ([], noPos)
 op nullPat  : MSPattern = WildPat (nullType, noPos)

 op showTypeName (info : TypeInfo) : String = printQualifiedId (primaryTypeName info)
 op showOpName   (info : OpInfo)   : String = printQualifiedId (primaryOpName   info)

 op baseOp? (qid as Qualified(q, id) : QualifiedId) : Bool = 
  q in? ["Bool", "Char", "Compare", "Function", "Integer", "IntegerAux", "List", "List1", "Nat", "Option", "String"]

 op baseType? (qid as Qualified(q, id) : QualifiedId) : Bool = 
  q in? ["Bool", "Char", "Compare", "Function", "Integer", "IntegerAux", "List", "List1", "Nat", "Option", "String"]

 op myTrue : MSTerm = Fun (Bool true, Boolean noPos, noPos)

 %% Setf

 op setfQid  : QualifiedId = Qualified ("System", "setf")
 op setfType : MSType      = Arrow (Product ([("1", TyVar ("A", noPos)), 
                                              ("2", TyVar ("A", noPos))], 
                                             noPos), 
                                    Product ([], noPos),
                                    noPos)

 op setfDef : MSTerm       = TypedTerm (Any noPos, setfType, noPos) 
 op setfRef : MSTerm       = Fun (Op (setfQid, Nonfix), setfType, noPos)

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
      let typ = termTypeEnv (spc, opinfo.dfn) in
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
                             let optype = termTypeEnv (spc, info.dfn) in
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
      let full_type = termTypeEnv (spc, opinfo.dfn) in
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
                                               Apply (setfRef, 
                                                      Record ([("1", field_var), 
                                                               ("2", Apply (Fun (Project field_id, 
                                                                                 Arrow (global_type, field_type, noPos),
                                                                                 noPos),
                                                                            let_var,
                                                                            noPos))],
                                                              noPos), 
                                                      noPos))
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
                    let _ = writeLine ("Globalizing init fn " ^ show global_init_name) in
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
                         (pat as (QuotientPat (p1, typename, pos)) : MSPattern)
  : Ids * GlobalizedPattern = 
  globalizePattern context vars_to_remove p1

 op globalizeRestrictedPat (context                              : Context)
                           (vars_to_remove                       : MSVarNames) % vars of global type, remove on sight
                           (pat as (RestrictedPat (p1, tm, pos)) : MSPattern)
  : Ids * GlobalizedPattern = 
  globalizePattern context vars_to_remove p1

 op globalType? (context : Context) (typ : MSType) : Bool =
  case typ of
    | Base     (nm, [], _) -> nm = context.global_type_name
    | Subtype  (typ, _, _) -> globalType? context typ
    | Quotient (typ, _, _) -> globalType? context typ  %% TODO??
    | _ -> false

 op globalizeVarPat (context                          : Context)
                    (vars_to_remove                   : MSVarNames) % vars of global type, remove on sight
                    (pat as (VarPat ((id, typ), pos)) : MSPattern)
  : Ids * GlobalizedPattern =
  if globalType? context typ then
    ([id], GlobalVarPat)
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
    | EmbedPat      _ -> globalizeEmbedPat      context vars_to_remove pat
    | RecordPat     _ -> globalizeRecordPat     context vars_to_remove pat
    | QuotientPat   _ -> globalizeQuotientPat   context vars_to_remove pat
    | RestrictedPat _ -> globalizeRestrictedPat context vars_to_remove pat
    | VarPat        _ -> globalizeVarPat        context vars_to_remove pat
    | TypedPat      _ -> globalizeTypedPat      context vars_to_remove pat
   %| WildPat       
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

 op makeSetf (lhs : MSTerm, rhs : MSTerm) : MSTerm =
  Apply (setfRef, Record ([("1", lhs), ("2", rhs)], noPos), noPos)


 op opAndArgs (tm : MSTerm) : Option (OpName * MSTerm * MSTerms) =
  case tm of
    |  Fun (Op (opname, _), _, _) -> Some (opname, tm, [])
       
    |  Apply (f, arg, _) ->
       (case opAndArgs f of
          | Some (opname, f, f_args) ->  
            Some (opname, f, f_args ++ [arg])
          | _ -> None)
       
    | _ -> None
      
 op updateAndArgs (tm : MSTerm) : Option (OpName * MSTerm * MSTerm * MSTerms * MSTerm) = 
   case opAndArgs tm of
     | Some (opname, update, args) ->
       (case flattenArgs args of
          | container :: indices_and_value ->
            (case reverse indices_and_value of
               | [_] -> None
               | new_value :: rev_indices -> Some (opname, update, container, reverse rev_indices, new_value)
               | _ -> None)
          | _ -> None)
     | _ -> None

 op accessAndArgs (tm : MSTerm) : Option (OpName * MSTerm * MSTerm * MSTerms) = 
   case opAndArgs tm of
     | Some (opname, access, args) ->
       (case flattenArgs args of
          | container :: indices ->
            Some (opname, access, container, indices)
          | _ -> None)
     | _ -> None


 op reviseTemplate (template : MSTerm, bindings : List (MSTerm * MSTerm)) : MSTerm =
  let 
    def subst tm =
      case findLeftmost (fn (x, y) -> equalTerm? (x, tm)) bindings of
        | Some (_, y) -> y
        | _ ->
          case tm of
            | Apply (x, y, _) -> Apply (subst x, subst y, noPos)
            | Record (fields, _) -> Record (map (fn (x, y) -> (x, subst y)) fields, noPos)
            | _ -> tm
  in
  subst template

 op reviseUpdate (context : Context, lhs : MSTerm, rhs : MSTerm) : MSTerm =
  case updateAndArgs rhs of
    | Some (update_op_name, update, set_container, set_indices, new_value) ->
      (case new_value of
         | Apply (Fun (RecordMerge, _, _), 
                  Record ([("1", access_tm),
                           ("2", value as Record (new_value_pairs, _))],
                          _),
                  _)
           ->
           (case accessAndArgs access_tm of
              | Some (access_op_name, access, get_container, get_indices) ->
                % let _ = writeLine ("update        = " ^ anyToString update) in
                % let _ = writeLine ("access        = " ^ anyToString access) in
                % let _ = writeLine ("lhs           = " ^ printTerm lhs)           in
                % let _ = writeLine ("get_container = " ^ printTerm get_container) in
                % let _ = writeLine ("set_container = " ^ printTerm set_container) in
                % let _ = writeLine ("set_indices   ="  ^ printTerms set_indices)   in
                % let _ = writeLine ("get_indices   ="  ^ printTerms get_indices)   in
                if equalTerm?  (lhs,           set_container) && 
                   equalTerm?  (set_container, get_container) && 
                   equalTerms? (set_indices,   get_indices)   && 
                   forall? (fn (index,_) -> natConvertible index) new_value_pairs 
                   % && update_op = Qualified ("MapsAsVectors", "update")
                   % && access_op = Qualified ("MapsAsVectors", "TMApply")
                  then
                    % let _ = writeLine ("MATCH!") in
                    let dom_type = termType access_tm in
                    let updates = 
                        map (fn (index, value) ->
                               let new_type = Arrow (dom_type, termType value, noPos) in
                               let field = Apply (Fun (Project index, new_type, noPos), access_tm, noPos) in
                               makeUpdate context field value)
                             new_value_pairs
                    in
                    % let _ = writeLine ("updates = " ^ printTerms updates) in
                    (case updates of
                       | [update] -> update
                       | _ -> Seq (updates, noPos))
                else
                  makeSetf (lhs, rhs)
              | _ -> 
                makeSetf (lhs, rhs))
         | _ -> 
           case findLeftmost (fn (entry : SetfEntry) -> update_op_name = entry.updater_name) context.setf_entries of
             | Some setf_pair ->
               % let _ = writeLine ("reviseUpdate: not a merge") in
               % let _ = writeLine ("reviseUpdate: lhs = " ^ printTerm lhs) in
               % let _ = writeLine ("reviseUpdate: rhs = " ^ printTerm rhs) in
               % let _ = writeLine ("reviseUpdate: update template = " ^ printTerm setf_pair.update_template) in
               (case makeVarBindings (setf_pair.update_template, rhs) of
                  | Some bindings ->
                    % let _ = app (fn (x, y)->  writeLine ("reviseUpdate: pair = " ^ printTerm x ^ " -- " ^ printTerm y)) bindings in
                    % let _ = writeLine ("reviseUpdate: setf template = " ^ printTerm setf_pair.setf_template) in
                    let setf_term = reviseTemplate (setf_pair.setf_template, bindings) in
                    % let _ = writeLine ("reviseUpdate: setf term     = " ^ printTerm setf_term) in
                    setf_term
                  | _ ->
                    % let _ = writeLine ("reviseUpdate: no match") in
                    makeSetf (lhs, rhs))
             | _ ->
               makeSetf (lhs, rhs))
    | _ -> 
     makeSetf (lhs, rhs)

 op makeVarBindings (template : MSTerm, tm : MSTerm) : Option (List (MSTerm * MSTerm)) =
  % let _ = writeLine("makeVarBindings: template = " ^ printTerm template) in
  % let _ = writeLine("makeVarBindings: term     = " ^ printTerm tm) in
  let
    def match (xfields, yfields) =
      case (xfields, yfields) of
        | ([], []) -> Some []
        | ((_, x) :: xfields, (_, y) :: yfields) ->
          (case match (xfields, yfields) of
             | Some pairs -> Some ((x, y) :: pairs)
             | _  -> None)
        | _ -> None
  in
  case template of
    | Var _ -> Some [(template, tm)]
    | Apply (f, x, _) ->
      (case tm of
         | Apply (g, y, _) ->
           (case (makeVarBindings (f, g), makeVarBindings (x, y)) of
              | (Some aa, Some bb) -> Some (aa ++ bb)
              | _ -> None)
         | _ ->
           None)
    | Record (xfields, _) ->
      (case tm of
         | Record (yfields, _) ->
           match (xfields, yfields)
         | _ ->
           None)
    | _ ->
      if equalTerm? (template, tm) then
        Some []
      else
        None


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

 op makeUpdate (context : Context)
               (lhs     : MSTerm)
               (rhs     : MSTerm)
   : MSTerm =
   % let _ = writeLine (" lhs: " ^ printTerm lhs) in
   % let _ = writeLine (" rhs: " ^ printTerm rhs) in
   % let _ = writeLine ("let bindings:\n") in
   % let _ = map (fn (pattern, value) -> writeLine (printPattern pattern ^ " = " ^ printTerm value)) context.let_bindings in
   case rhs of
     | Record (pairs, _) | forall? (fn (index,_) -> natConvertible index) pairs ->
       (let dom_type = termType lhs in
        let updates = 
            map (fn (index, value) ->
                   let new_type = Arrow (dom_type, termType value, noPos) in
                   let new_lhs = Apply (Fun (Project index, new_type, noPos), lhs, noPos) in
                   makeSetf (new_lhs, value))
                pairs
        in
        case updates of
          | [update] -> update
          | _ -> Seq (updates, noPos))

     | _ ->
       reviseUpdate (context, lhs, rhs)

 op makeGlobalFieldUpdates (context           : Context)
                           (vars_to_remove    : MSVarNames)      % vars of global type, remove on sight
                           (substitutions     : MSSubstitutions) % tm -> var
                           (merger            : MSTerm)          % RecordMerge
                           (Record (fields,_) : MSTerm)          % record of fields to update
  : MSTerm =
  let assignments =
      map (fn (id, old_value) ->
              let Some (_, global_var_op) = findLeftmost (fn (x, _) -> x = id) context.global_var_map in
              let new_value = case globalizeTerm context vars_to_remove substitutions old_value of
                                | Changed new_value -> new_value
                                | GlobalVar -> 
                                  let _ = writeLine("Warning: Updating a single global field with the entire master global value.") in
                                  context.global_var
                                | _ -> old_value
              in
              let expanded_value = expandBindings (new_value, context.let_bindings) in
              makeUpdate context global_var_op expanded_value)
          fields
  in
  Seq (assignments, noPos)

 op applyHeadType (tm : MSTerm, context : Context) : MSType =
  case tm of
    | Apply (t1, t2, _) -> applyHeadType (t1, context)
    | Fun (Op (qid, _), typ, _) -> 
      (case findTheOp (context.spc, qid) of
         | Some opinfo -> firstOpDefInnerType opinfo
         | _ -> termTypeEnv (context.spc, tm))
    | _ -> 
      termTypeEnv (context.spc, tm)
      
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
  in
  case (t1, t2) of
    | (Fun (RecordMerge, _, _),  Record ([(_, Var ((id, _), _)), (_, t3)], _)) | id in? vars_to_remove 
      ->
      %%  special case for global update:  
      %%     local_var_to_be_globalized << {...}
      %%       =>
      %%     global_update (global_var, {...})
      let new_t3 = case globalizeTerm context vars_to_remove substitutions t3 of
                     | Changed new_t3 -> new_t3
                     | GlobalVar -> 
                       let _ = writeLine("Warning: using the master global var for a record update source.") in
                       context.global_var
                     | _ -> t3
      in
      %% new_t3 is now a record whose fields are a subset of those in the global type
      let new_tm = makeGlobalFieldUpdates context vars_to_remove substitutions t1 new_t3 in
      Changed new_tm
   | _ ->
     let opt_new_t1 = globalizeTerm context vars_to_remove substitutions t1 in
     let opt_new_t2 = globalizeTerm context vars_to_remove substitutions t2 in
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
         %% was (f x ...)  where x had global type
         let head_type = applyHeadType (t1, context) in
         let head_type = unfoldToArrow (context.spc, head_type) in
         Changed (case dom_type head_type of
                    | Some dtype | globalType? context dtype ->
                      (case t1 of
                         | Fun (Project field_name, _, _) ->
                           %%  special case for global access:  
                           %%    (local_var_to_be_globalized.xxx)
                           %%      =>
                           %%    (global_var.xxx)
                           makeGlobalAccess context field_name (termTypeEnv (context.spc, tm))
                         | _ ->
                           case head_type of
                             | Arrow (_, Arrow _, _) ->
                               %% (f x y ...)  where x has global type, and domain of f is global type
                               %%   =>
                               %% (f y ...)
                               let range_type = termTypeEnv (context.spc, tm) in
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
  : GlobalizedTerm = 
  let (changed?, shortened?, new_fields, opt_prefix) = 
      foldl (fn ((changed?, shortened?, new_fields, opt_prefix), (id, old_tm)) -> 
               let (changed?, new_tm) = 
                   case globalizeTerm context vars_to_remove substitutions old_tm of
                     | Changed new_tm -> (true, new_tm)
                     | Unchanged -> (changed?, old_tm)
                     | GlobalVar -> (true, old_tm) 
               in
               let tt = termTypeEnv (context.spc, old_tm) in
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
          | [(lbl, tm)] | natConvertible lbl -> 
            % If a var x is removed from 2-element record '(x, y)' 
            %  simplify resulting singleton record '(y)' down to 'y'.
            % But don't simplify a 1-element record with an explicitly named 
            %  field such as {a = x}
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
                   case globalizeTerm context outer_vars_to_remove substitutions tm of
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
                     | GlobalVarPat    -> nullPat
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
  
  let opt_new_body  = globalizeTerm context all_vars_to_remove substitutions body in
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
      let opt_new_body = globalizeTerm context vars_to_remove substitutions body in
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
               let null_pat = WildPat (TyVar ("wild", noPos),noPos) in
               Changed (null_pat, myTrue, new_body))

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
  let opt_new_t1 = globalizeTerm context vars_to_remove substitutions t1 in
  let opt_new_t2 = globalizeTerm context vars_to_remove substitutions t2 in
  let opt_new_t3 = globalizeTerm context vars_to_remove substitutions t3 in
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
  let opt_new_tms = map (fn tm -> globalizeTerm context vars_to_remove substitutions tm) tms in
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

 op globalizeTypedTerm (context                  : Context)
                       (vars_to_remove           : MSVarNames)      % vars of global type, remove on sight
                       (substitutions            : MSSubstitutions) % tm -> varname
                       (TypedTerm (tm, typ, pos) : MSTerm)
  : GlobalizedTerm = 
  let
   def nullify_global typ =
     if globalType? context typ then
       nullType
     else
       case typ of

         | Arrow (dom, rng, pos) -> 
           let rng = nullify_global rng in
           if globalType? context dom then
             case rng of
               | Arrow _ -> rng
               | _ -> Arrow (nullify_global dom, rng, noPos)
           else
             Arrow (nullify_global dom, rng, noPos)

         | Product (fields, pos) ->
           (let new_fields = foldl (fn (fields, (id, typ)) ->
                                      if globalType? context typ then
                                        fields
                                      else
                                        fields ++ [(id, nullify_global typ)])
                                   []
                                   fields
            in
            case new_fields of
              | [(id, typ)] | natConvertible id -> typ
              | _ -> Product (renumber new_fields, noPos))
         | CoProduct (fields, pos) -> 
           %% TODO: revise CoProduct ??
           let new_fields = foldl (fn (fields, field as (id, opt_typ)) ->
                                     case opt_typ of
                                       | Some typ ->
                                         if globalType? context typ then
                                           fields
                                         else
                                           fields ++ [(id, Some (nullify_global typ))]
                                       | _ ->
                                         fields ++ [field])
                                  []
                                  fields
           in
           CoProduct (new_fields, noPos)

         | Quotient (typ, tm, pos) -> 
           let new_typ = nullify_global typ in
           let new_tm = 
               case globalizeTerm context vars_to_remove substitutions tm of
                 | Changed new_tm -> new_tm
                 | GlobalVar -> 
                   let _ = writeLine("Warning: Using the master global var as a quotient predicate.") in
                   context.global_var
                 | Unchanged -> tm
           in
           Quotient (new_typ, new_tm, pos)

         | Subtype (typ, _, _) -> nullify_global typ

         | Pi (tvs, typ, pos) -> Pi (tvs, nullify_global typ, pos)

         | And (tm :: _, _) -> nullify_global tm

         | _ -> typ

  in
  case globalizeTerm context vars_to_remove substitutions tm of
    | Changed new_tm ->
      let new_typ = nullify_global typ in 
      Changed (TypedTerm (new_tm, new_typ, pos))

    | GlobalVar ->
      GlobalVar

    | _ ->
      Unchanged

 %% ================================================================================

 op globalizePi (context              : Context)
                (vars_to_remove       : MSVarNames)      % vars of global type, remove on sight
                (substitutions        : MSSubstitutions) % tm -> varname
                (Pi (tyvars, tm, pos) : MSTerm)
  : GlobalizedTerm = 
  case globalizeTerm context vars_to_remove substitutions tm of
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
    | tm :: _ -> globalizeTerm context vars_to_remove substitutions tm 
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

 op globalizeTerm (context        : Context)
                  (vars_to_remove : MSVarNames)  % vars of global type, remove on sight
                  (substitutions  : MSSubstitutions) % tm -> varname
                  (term           : MSTerm) 
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
          let new_term        = Let ([(pat, tm)], body, noPos) in
          add_bindings substs new_term
        | _ ->
          body
  in
  let conflicts = conflictingGlobalRefsIn context vars_to_remove term in
  let substitutions = map (fn (var_id, field_id) ->
                             let temp_id   = "temp_" ^ var_id ^ "_" ^ field_id in
                             let temp_type = globalFieldType context field_id in
                             let temp_var  = (temp_id, temp_type) in
                             {global_var_id = var_id, 
                              field_id      = field_id, 
                              temp_var      = temp_var})
                          conflicts
  in
  let term = reviseGlobalRefs substitutions term in
  let term = add_bindings substitutions term in
  let opt_term =
      case term of
        | Apply      _ -> globalizeApply      context vars_to_remove substitutions term
        | Record     _ -> globalizeRecord     context vars_to_remove substitutions term
        | Let        _ -> globalizeLet        context vars_to_remove substitutions term
        | LetRec     _ -> globalizeLetRec     context vars_to_remove substitutions term
        | Lambda     _ -> globalizeLambda     context vars_to_remove substitutions term
        | IfThenElse _ -> globalizeIfThenElse context vars_to_remove substitutions term
        | Seq        _ -> globalizeSeq        context vars_to_remove substitutions term
        | TypedTerm  _ -> globalizeTypedTerm  context vars_to_remove substitutions term
        | Pi         _ -> globalizePi         context vars_to_remove substitutions term
        | And        _ -> globalizeAnd        context vars_to_remove substitutions term
          
       %| ApplyN     _ -> Unchanged % not present after elaborateSpec is called
       %| Bind       _ -> Unchanged % should not be globalizing inside quantified terms
       %| The        _ -> Unchanged % should not be globalizing inside 'the' term
       %| Fun        _ -> Unchanged % primitive terms are never global
       %| Transform  _ -> Unchanged % doesn't make sense to globalize this
       %| Any        _ -> Unchanged % can appear within typed term, for example
          
        | Var ((id,_), _) -> if id in? vars_to_remove then
                               GlobalVar
                             else
                               Unchanged
        | _ -> Unchanged
  in
  case (opt_term, conflicts) of
    | (Unchanged, []) -> Unchanged     
    | (Unchanged, _)  -> Changed term  % consider changed if there are conflicts
    | _               -> opt_term      % changed or global
      
 %% ================================================================================

 op globalizeOpInfo (context    : Context,
                     old_info   : OpInfo)
  : OpInfo =
  let qid as Qualified(q, id) = primaryOpName old_info in
  if baseOp? qid then
    old_info
  else
    let old_dfn = case old_info.dfn of 
                    | And (tm :: _, _) -> tm 
                    | tm -> tm 
    in
    case globalizeTerm context [] [] old_dfn of
      | Changed new_dfn -> 
        let new_info = old_info << {dfn = new_dfn} in
        let _ = if context.tracing? then
                  let _ = writeLine ""                          in
                  let _ = writeLine ("Globalizing " ^ show qid) in
                  let _ = writeLine (printTerm old_dfn)         in
                  let _ = writeLine "  => "                     in
                  let _ = writeLine (printTerm new_dfn)         in
                  let _ = writeLine ""                          in
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
                  let _ = writeLine ""                          in
                  let _ = writeLine ("Globalizing " ^ show qid) in
                  let _ = writeLine (printTerm old_dfn)         in
                  let _ = writeLine "  => "                     in
                  let _ = writeLine (printTerm new_dfn)         in
                  let _ = writeLine ""                          in
                  ()
                else
                  ()
        in
        new_info

      | Unchanged -> 
        old_info

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
  let base_ops = mapiPartialAQualifierMap (fn (q, id, info) ->
                                             if baseOp? (Qualified(q, id)) then
                                               Some info
                                             else
                                               None)
                                          spc.ops
  in
  let base_types = mapiPartialAQualifierMap (fn (q, id, info) ->
                                               if baseType? (Qualified(q, id)) then
                                                 Some info
                                               else
                                                 None)
                                            spc.types
  in
  let (ops_to_revise, types_to_keep) =
      let chase_terms_in_types? = false in
      let chase_theorems?       = false in
      sliceSpecInfo (spc, 
                     root_ops, root_types,  % start searching from these, and include them
                     baseOp?, baseType?,    % stop searching at these, and do not include them
                     chase_terms_in_types?, 
                     chase_theorems?,
                     false)
  in
  let new_ops =
      foldriAQualifierMap (fn (q, id, x, pending_ops) ->
                             let qid = Qualified (q, id) in
                               case findTheOp (spc, qid) of
                                 | Some info -> 
                                   let new_info = 
                                       if context.global_init_name = qid then
                                         % let _ = writeLine("Not revising init op " ^ q ^ "." ^ id) in
                                         info
                                       else
                                         globalizeOpInfo (context, info) 
                                   in
                                   insertAQualifierMap (pending_ops, q, id, new_info)
                                 | _ -> 
                                   let _ = writeLine("??? Globalize could not find op " ^ q ^ "." ^ id) in
                                   pending_ops)
                          base_ops
                          ops_to_revise
  in
  let new_types =
      foldriAQualifierMap (fn (q, id, x, pending_types) ->
                             case findTheType (spc, Qualified (q, id)) of
                               | Some info -> 
                                 insertAQualifierMap (pending_types, q, id, info)
                               | _ -> 
                                 let _ = writeLine("??? Globalize could not find type " ^ q ^ "." ^ id) in
                                 pending_types)
                          base_types
                          types_to_keep
  in
  let new_spec = spc << {ops = new_ops, types = new_types} in
  let 
    def globalize_elements elements =
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
                 | _ -> new_elts)
             []
             elements
  in
  let new_elements = globalize_elements spc.elements in
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

 op equalTerms? (tms1 : MSTerms, tms2 : MSTerms) : Bool =
  case (tms1, tms2) of
    | ([], []) -> true
    | (tm1 :: tms1, tm2 :: tms2) -> 
      equalTerm? (tm1,tm2) && equalTerms? (tms1, tms2)
    | _ ->
      false

 op semanticsOfGetSet? (get_args  : MSTerms,
                        set_args  : MSTerms,
                        var_pairs : List (MSTerm * MSTerm),
                        then_tm   : MSTerm,
                        else_tm   : MSTerm)
  : Bool =

  let 
    def similar? (set_indices, get_indices) =
      case (set_indices, get_indices) of
        | ([], []) -> true
        | (x :: set_indices, y :: get_indices) ->
          (exists? (fn (a, b) -> 
                      (equalTerm? (x, a) && equalTerm? (y, b)) || 
                      (equalTerm? (x, b) && equalTerm? (y, a)))
                   var_pairs)
          &&
          similar? (set_indices, get_indices)
        | _ -> false
  in
  let flattened_get_args = flattenArgs get_args in
  let flattened_set_args = flattenArgs set_args in
  let updated_container  = head flattened_set_args in
  let get_indices        = tail flattened_get_args in
  let set_indices        = reverse (tail (reverse (tail flattened_set_args))) in
  %% corresponding get and set indices should be equal
  similar? (get_indices, set_indices) 
  &&
  %% the get in lhs should use same indices as the get in the else term
  (case opAndArgs else_tm of
     | Some (_, _, get2_args) ->
       let get2_args = flattenArgs get2_args in
       (case get2_args of
          | accessed_container :: get2_indices ->
            equalTerm? (updated_container, accessed_container) && equalTerms? (get_indices, get2_indices)
          | _ -> 
            false)
     | _ -> 
       false)

 op varsCompared (tm : MSTerm) : Option (List (MSTerm * MSTerm)) =
  let
    def pair_up_vars_in_fields (lfields, rfields) =
      case (lfields, rfields) of
        | ([],[]) -> Some []
        | ((_, lhs) :: lfields, (_, rhs) :: rfields) ->
          (case pair_up_vars_in_terms (lhs, rhs) of 
             | Some pairs ->
               (case pair_up_vars_in_fields (lfields, rfields) of
                  | Some more_pairs -> Some (pairs ++ more_pairs)
                  | _ -> None)
             | _ -> None)
        | _ -> None
           
    def pair_up_vars_in_terms (lhs, rhs) =
      case (lhs, rhs) of
        | (Var  _, Var _) ->
          Some [(lhs, rhs)]
        | (Record (lpairs, _), Record (rpairs, _)) -> 
          pair_up_vars_in_fields (lpairs, rpairs)
        | _ ->
          None
  in
  case tm of
    | Apply (Fun (Equals, _, _), Record ([(_, lhs), (_, rhs)], _), _) ->
      pair_up_vars_in_terms (lhs, rhs)
    | Apply (Fun (And, _, _), Record ([(_, t1), (_, t2)], _), _) ->
      (case (varsCompared t1, varsCompared t2) of
         | (Some x, Some y) -> Some (x ++ y)
         | _ -> None)
    | _ ->
      None

 %%%   get (set (m, i, x), j) = if i = j then x else get (m, j)
 %%%   get (set m i x, j)      = if i = j then x else get (m, j)
 %%%   get (set (m, i, x))  j = if i = j then x else get (m, j)
 %%%   get (set m i x) j      = if i = j then x else get (m, j)

 op flattenArgs (args : MSTerms) : MSTerms =
  foldl (fn (args, arg) ->
           args ++
           (case arg of
              | Record (pairs, _) -> map (fn (_, arg) -> arg)  pairs
              | _  ->  [arg]))
        []
        args
                               
 op makeSetfTemplate (tm : MSTerm, vpairs : List (MSTerm * MSTerm), value : MSTerm) : Option MSTerm =
   % let _ = List.app (fn (x,y) -> writeLine ("makeSetfTemplate: subst_pair: " ^ printTerm x ^ " -- " ^ printTerm y)) vpairs in
   let
     def first_arg_of tm = 
       case tm of
         | Apply (f, arg, _) ->
           (case f of
              | Apply _ ->
                first_arg_of f
              | _ ->
                case arg of
                  | Var _ -> Some arg
                  | Record ((_, arg) :: _, _) -> Some arg
                  | _ -> None)
         | _ -> None

     def subst_vars arg =
       let new_arg =
       case arg of
         | Var _ -> 
           (case findLeftmost (fn (x, y) -> equalTerm? (x, arg)) vpairs of
              | Some (_, y) -> y
              | _ ->
                case findLeftmost (fn (x, y) -> equalTerm? (y, arg)) vpairs of
                  | Some (x, _) -> x
                  | _ ->
                    arg)
         | Record (fields, _) ->
           Record (map (fn (index, arg) -> (index, subst_vars arg)) fields, noPos)
         | _ ->
           arg
       in
       % let _ = writeLine ("makeSetfTemplate: old arg = " ^ anyToString arg) in
       % let _ = writeLine ("makeSetfTemplate: new arg = " ^ anyToString new_arg) in
       new_arg

     def revise tm =
       case tm of 
         | Apply (f, arg, _) ->
           (case f of
              | Apply _ ->
                (case revise f of
                   | Some new_f ->
                     Some (Apply (new_f, subst_vars arg, noPos))
                   | _ ->
                     None)
              | _ ->
                case (arg : MSTerm) of
                  | Record ((x, update) :: fields, _) ->
                    (case first_arg_of update of
                       | Some container ->
                         let new_fields = map (fn (x, arg) -> (x, subst_vars arg)) fields in
                         Some (Apply (f, Record ((x, container) :: new_fields, noPos), noPos))
                       | _ ->
                         None)
                  | _ ->
                    case first_arg_of arg of
                      | Some container ->
                        Some (Apply (f, container, noPos))
                      | _ ->
                        None)
         | _ ->
           None
   in
   case revise tm of
     | Some tm ->
       Some (Apply (setfRef, Record ([("1", tm), ("2", value)], noPos), noPos))
     | _ ->
       % let _ = writeLine ("makeSetfTemplate: Failure") in
       None

 op extractSetfEntry (fm : MSTerm) : Option SetfEntry =
  case fm of
    | Pi   (_, fm,    _) -> extractSetfEntry fm
    | And  (fm :: _,  _) -> extractSetfEntry fm
    | Bind (_, _, fm, _) -> extractSetfEntry fm

    | Apply (Fun (Equals, _, _), Record ([(_, lhs), (_, IfThenElse (pred, then_tm, else_tm, _))], _), _) ->
      % let _ = writeLine ("--------------------") in
      % let _ = writeLine ("extractSetfEntry: have Apply") in
      (case varsCompared pred of
         | Some vpairs ->
           % let _ = writeLine ("extractSetfEntry: have Compared") in
           (case opAndArgs lhs of
              | Some (accesser_name, accesser, get_args) -> 
                % let _ = writeLine ("extractSetfEntry: have opAndArgs for lhs") in
                (case flattenArgs get_args of
                   | update_template :: _ :: _ ->
                     % let _ = writeLine ("extractSetfEntry: have flattened") in
                     (case opAndArgs update_template of
                        | Some (updater_name, updater, set_args) ->
                          % let _ = writeLine ("extractSetfEntry: have opAndArgs for update") in
                          if semanticsOfGetSet? (get_args, set_args, vpairs, then_tm, else_tm) then
                            % let _ = writeLine ("extractSetfEntry: have semantics") in
                            case makeSetfTemplate (lhs, vpairs, then_tm) of % then_tm is same as value assigned in updater
                              | Some setf_template ->
                                % let _ = writeLine ("extractSetfEntry: accesser_name   = " ^ anyToString accesser_name   ) in
                                % let _ = writeLine ("extractSetfEntry: updater_name    = " ^ anyToString updater_name    ) in
                                % let _ = writeLine ("extractSetfEntry: accesser        = " ^ printTerm accesser        ) in
                                % let _ = writeLine ("extractSetfEntry: updater         = " ^ printTerm updater         ) in
                                % let _ = writeLine ("extractSetfEntry: update_template = " ^ printTerm update_template ) in
                                % let _ = writeLine ("extractSetfEntry: setf_template   = " ^ printTerm setf_template   ) in
                                % let _ = writeLine ("--------------------") in
                                Some {accesser_name   = accesser_name, 
                                      updater_name    = updater_name, 
                                      accesser        = accesser,
                                      updater         = updater,
                                      update_template = update_template,
                                      setf_template   = setf_template}
                              | _ -> 
                                None
                          else
                            None
                        | _ -> None)
                   | _ -> None)
              | _ -> None)
         | _ -> None)
    | _ -> None

 op findSetfEntries (spc  : Spec) : SetfEntries =
  foldrSpecElements (fn (elt, access_updates) ->
                       case elt of
                         |  Property (typ, name, _, fm, _) | typ = Axiom || typ = Theorem -> 
                            % let _ = writeLine ("find gs: " ^ anyToString typ ^ " -- " ^ anyToString name) in
                            (case extractSetfEntry fm of
                               | Some access_update -> access_update :: access_updates
                               | _ -> access_updates)
                         | _ ->
                           access_updates)
                    []
                    spc.elements

 op convertUpdateToAccess (update : MSTerm) : MSTerm

 op globalizeSingleThreadedType (spc              : Spec, 
                                 root_ops         : OpNames,
                                 global_type_name : TypeName, 
                                 global_var_id    : String,
                                 opt_ginit        : Option OpName,
                                 tracing?         : Bool)
  : SpecCalc.Env (Spec * Bool) =
  let global_var_name = Qualified ("Global", global_var_id) in

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
                          | Some ginit -> checkGlobalInitOp (spc, ginit, global_type_name)
                          | _ -> findInitOp (spc, global_type_name));

   global_var_map   <- return (case findTheType (spc, global_type_name) of
                                 | Some info -> 
                                   (case info.dfn of
                                      | Product (pairs, _) ->
                                        map (fn (field_id, field_type) ->
                                               let Qualified (_, global_id) = global_type_name in
                                               let global_var_id = Qualified ("Global", field_id) in
                                               let global_var = Fun (Op (global_var_id, Nonfix), field_type, noPos) in
                                               (field_id, global_var))
                                            pairs
                                      | _ -> empty)
                                 | _ -> []);

   %% This shouldn't be necessary, but is for now to avoid complaints from replaceLocalsWithGlobalRefs.
   spec_with_gset   <- addOp [setfQid] Nonfix false setfDef spc noPos;

   %% Add global vars for the fields before running replaceLocalsWithGlobalRefs,
   %% to avoid complaints about unknown ops.
   spec_with_gvars  <- foldM (fn spc -> fn (_, global_field_var) ->
                                let Fun (Op (global_field_var_name, _), gtype, _) = global_field_var in
                                let refine? = false                                 in
                                let dfn     = TypedTerm (Any noPos, gtype, noPos)   in
                                addOp [global_field_var_name] Nonfix refine? dfn spc noPos)
                             spec_with_gset
                             global_var_map;
                             
   spec_with_ginit  <- return (case findTheOp (spec_with_gvars, global_init_name) of
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

   %% hack to fix problem where 'global_var << {..}' was becoming just '{...}'
   spec_with_restored_record_merges <- return (SpecTransform.introduceRecordMerges (spec_with_ginit, []));

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

   %% Add the main global var after calling replaceLocalsWithGlobalRefs, 
   %% since that would prune it away before any references were introduced.
   spec_with_gvar   <- (case findTheOp (globalized_spec, global_var_name) of
                          | Some _ -> return globalized_spec
                          | _ -> 
                            let refine? = false                               in
                            let gtype   = Base (global_type_name, [],  noPos) in
                            let dfn     = TypedTerm (Any noPos, gtype, noPos) in
                            addOp [global_var_name] Nonfix refine? dfn globalized_spec noPos);

   return (spec_with_gvar, tracing?)
   }

 %% ================================================================================

}

