Globalize qualifying spec
{
 import /Languages/MetaSlang/Specs/Environment
 import /Languages/MetaSlang/Transformations/SliceSpec
 import /Languages/MetaSlang/CodeGen/SubstBaseSpecs  

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

 type OpTypes = AQualifierMap MSType
 type MSRule  = MSPattern * MSTerm * MSTerm
 type MSVar   = AVar Position
 type VarNames = List Id

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
      let typ = termType opinfo.dfn in
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
                             let optype = termType info.dfn in
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
      let full_type = termType opinfo.dfn in
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

 op globalizeAliasPat (tname                         : TypeName)
                      (gvar                          : OpName)
                      (vars_to_remove                : VarNames) % vars of global type, remove on sight
                      (pat as AliasPat (p1, p2, pos) : MSPattern)
  : Ids * Option MSPattern = 
  let (ids1, opt_new_p1) = globalizePattern tname gvar vars_to_remove p1 in
  let (ids2, opt_new_p2) = globalizePattern tname gvar vars_to_remove p2 in
  (ids1 ++ ids2,
   case (opt_new_p1, opt_new_p2) of
     | (Some new_p1, Some new_p2) -> Some (AliasPat (new_p1, new_p2, noPos))
     | (None, None)               -> None
     | _ -> fail ("inconsistent globalization of alias patterns"))

 op globalizeEmbedPat (tname                                   : TypeName)
                      (gvar                                    : OpName)
                      (vars_to_remove                          : VarNames) % vars of global type, remove on sight
                      (pat as EmbedPat (id, opt_pat, typ, pos) : MSPattern)
  : Ids * Option MSPattern = 
  % let _ = writeLine("??? globalize ignoring EmbedPat: " ^ anyToString pat) in
  ([], Some pat)

 op globalizeRecordPat (tname                   : TypeName)
                       (gvar                    : OpName)
                       (vars_to_remove          : VarNames) % vars of global type, remove on sight
                       (RecordPat (fields, pos) : MSPattern)
  : Ids * Option MSPattern = 
  let
    def aux (vars_to_remove, new_fields, old_fields) =
      case old_fields of
        | [] -> (vars_to_remove, new_fields)
        | (id, pat) :: ptail ->
          let (ids, opt_pat) = globalizePattern tname gvar vars_to_remove pat in
          let new_vars_to_remove = vars_to_remove ++ ids in
          let new_fields =
              case opt_pat of
                | Some new_pat -> new_fields ++ [(id, new_pat)]
                | _ -> new_fields
          in
          aux (new_vars_to_remove, new_fields, ptail)
  in
  let (vars_to_remove, new_fields) = aux ([], [], fields) in
  (vars_to_remove,
   Some (case new_fields of
           | [(id, pat)] -> pat
           | _ -> RecordPat (renumber new_fields, noPos)))

 op globalizeQuotientPat (tname                                    : TypeName)
                         (gvar                                     : OpName)
                         (vars_to_remove                           : VarNames) % vars of global type, remove on sight
                         (pat as (QuotientPat (p1, typename, pos)) : MSPattern)
  : Ids * Option MSPattern = 
  globalizePattern tname gvar vars_to_remove p1

 op globalizeRestrictedPat (tname                                : TypeName)
                           (gvar                                 : OpName)
                           (vars_to_remove                       : VarNames) % vars of global type, remove on sight
                           (pat as (RestrictedPat (p1, tm, pos)) : MSPattern)
  : Ids * Option MSPattern = 
  globalizePattern tname gvar vars_to_remove p1

 op globalType? (tname : TypeName) (typ : MSType) : Bool =
  case typ of
    | Base     (nm, [], _) -> nm = tname 
    | Subtype  (typ, _, _) -> globalType? tname typ
    | Quotient (typ, _, _) -> globalType? tname typ  %% TODO??
    | _ -> false

 op globalizeVarPat (tname                            : TypeName)
                    (gvar                             : OpName)
                    (vars_to_remove                   : VarNames) % vars of global type, remove on sight
                    (pat as (VarPat ((id, typ), pos)) : MSPattern)
  : Ids * Option MSPattern = 
  if globalType? tname typ then
    ([id], None)
  else
    ([], Some pat)

 op globalizePattern (tname          : TypeName)
                     (gvar           : OpName)
                     (vars_to_remove : VarNames)  % vars of global type, remove on sight
                     (pat            : MSPattern) 
  : Ids * Option MSPattern = 
  case pat of
    | AliasPat      _  -> globalizeAliasPat      tname gvar vars_to_remove pat
    | EmbedPat      _  -> globalizeEmbedPat      tname gvar vars_to_remove pat
    | RecordPat     _  -> globalizeRecordPat     tname gvar vars_to_remove pat
    | QuotientPat   _  -> globalizeQuotientPat   tname gvar vars_to_remove pat
    | RestrictedPat _  -> globalizeRestrictedPat tname gvar vars_to_remove pat
    | VarPat        _  -> globalizeVarPat        tname gvar vars_to_remove pat
   %| WildPat       
   %| BoolPat       
   %| NatPat        
   %| StringPat     
   %| CharPat       
   %| TypedPat      
    | _ -> ([], None)


 %% ================================================================================
 %% Given global type, find patterns and terms of that type and remove them
 %% ================================================================================

 op makeGlobalAccess (tname      : TypeName)
                     (gvar       : OpName)
                     (field_name : Id)
                     (field_type : MSType) 
  : MSTerm =
  let global_type  = Base (tname, [], noPos)                       in
  let global_var   = Fun (Op (gvar, Nonfix), global_type, noPos)   in
  let project_type = Arrow (global_type, field_type, noPos)        in
  let projection   = Fun (Project field_name, project_type, noPos) in
  Apply (projection, global_var, noPos)

 op makeGlobalUpdate (tname      : TypeName)
                     (gvar       : OpName)
                     (merger     : MSTerm)  % RecordMerge
                     (new_fields : MSTerm)  % record of fields to update
  : MSTerm =
  let global_type = Base (tname, [], noPos)                                in
  let global_var  = Fun (Op (gvar, Nonfix), global_type, noPos)            in
  let merge_args  = Record ([("1", global_var), ("2", new_fields)], noPos) in
  let merge       = Apply (merger, merge_args, noPos)                      in
  let setter      = Fun (Op (Qualified ("Global", "set"), Nonfix), 
                         Product ([("1", global_type), ("2", global_type)], noPos),
                         noPos)
  in
  let set_args    = Record ([("1", global_var), ("2", merge)], noPos)      in
  Apply (setter, set_args, noPos)
  
 op globalizeApply (tname                       : TypeName)
                   (gvar                        : OpName)
                   (vars_to_remove              : VarNames) % vars of global type, remove on sight
                   (tm as (Apply (t1, t2, pos)) : MSTerm)
  : Option MSTerm = 
  let

    def arrow_type? typ =
      case typ of
        | Arrow   _  -> true
        | Subtype (typ, _, _) -> arrow_type? typ
        | _ -> false

    def retype_fun (tm, typ) =
      case tm of
        | Fun (x, _, pos) -> Fun (x, typ, pos)
        | _ ->
          let _ = writeLine ("??? Don't know how to retype : " ^ compressWhiteSpace(printTerm tm)) in
          tm
  in
  case (t1, t2) of
    | (Fun (RecordMerge, _, _),  Record ([(_, Var ((id, _), _)), (_, t3)], _)) | id in? vars_to_remove 
      ->
      %%  special case for global update:  
      %%     local_var_to_be_globalized << {...}
      %%       =>
      %%     global_update (global_var, {...})
      let new_t3 = case globalizeTerm tname gvar vars_to_remove t3 of
                     | Some new_t3 -> new_t3
                     | _ -> t3
      in
      Some (makeGlobalUpdate tname gvar t1 new_t3)
   | _ ->
     let opt_new_t1 = globalizeTerm tname gvar vars_to_remove t1 in
     let opt_new_t2 = globalizeTerm tname gvar vars_to_remove t2 in
     %% Vars to be removed will have been removed from inside t1 and t2, but not if t1 or t2 itself is global.
     let (changed1?, new_t1) =
         case opt_new_t1 of
           | Some new_t1 -> (true,  new_t1)
           | _           -> (false, t1)
     in
     let (changed2?, new_t2) =
         case opt_new_t2 of
           | Some new_t2 -> (true,  new_t2)
           | _           -> (false, t2)
     in
     case new_t2 of
       | Var ((id, _), _) | id in? vars_to_remove ->
         %%  special case for global access:  
         %%    local_var_to_be_globalized.xxx
         %%      =>
         %%    global_var.xxx
         (let ttype = termType tm in
          if arrow_type? ttype then
            Some (retype_fun (t1, ttype))
          else
            case t1 of
              | Fun (Project field_name, _, _) ->
                Some (makeGlobalAccess tname gvar field_name (termType tm))
              | _ ->
                Some (Apply (new_t1, nullTerm, pos)))
       | _ ->
         if changed1? || changed2? then
           Some (Apply (new_t1, new_t2, pos))
         else
           None
      
 %% ================================================================================

 op globalizeRecord (tname                : TypeName)
                    (gvar                 : OpName)
                    (vars_to_remove       : VarNames)  % vars of global type, remove on sight
                    (Record (fields, pos) : MSTerm)
  : Option MSTerm = 
  let (revised?, new_fields) = 
      foldl (fn ((revised?, new_fields), (id, old_tm)) -> 
               case old_tm of
                 | Var ((id, _), _) | id in? vars_to_remove -> 
                   (true, new_fields)
                 | _ -> 
                   case globalizeTerm tname gvar vars_to_remove old_tm of
                     | Some new_tm -> (true,     new_fields ++ [(id, new_tm)])
                     | _           -> (revised?, new_fields ++ [(id, old_tm)]))
            (false, [])
            fields 
  in
  if revised? then
    Some (case new_fields of
            | [(_, tm)] -> tm  % var was removed from 2-element record
            | _ -> Record (renumber new_fields, pos))
  else 
    % term is unchanged
    None

 %% ================================================================================
 %% Given global type, find argument variables of that type and remove them
 %% ================================================================================

 op globalizeLet (tname                     : TypeName)
                 (gvar                      : OpName)
                 (vars_to_remove            : VarNames)  % vars of global type, remove on sight
                 (Let (bindings, body, pos) : MSTerm)
  : Option MSTerm = 
  let (new_bindings, vars_to_remove, changed_bindings?) = 
      foldl (fn ((bindings, vars_to_remove, changed_binding?), (pat, tm)) -> 
               let (changed_tm?, new_tm) =
                   case globalizeTerm tname gvar vars_to_remove tm of
                     | Some new_tm -> (true, new_tm)
                     | _ -> (false, tm)
               in
               let (new_vars_to_remove, opt_new_pat) = globalizePattern tname gvar vars_to_remove pat in
               let new_pat =
                   case opt_new_pat of
                     | Some new_pat -> new_pat
                     | _ -> nullPat
               in
               let new_bindings = bindings ++ [(new_pat, new_tm)] in
               case new_vars_to_remove of
                 | [] -> (new_bindings, 
                          vars_to_remove, 
                          changed_tm?)
                 | _ -> (new_bindings, 
                         vars_to_remove ++ new_vars_to_remove,
                         true))
            ([],vars_to_remove, false)
            bindings 
  in
  let opt_new_body = globalizeTerm tname gvar vars_to_remove body in
  let (changed_body?, new_body) = 
      case opt_new_body of
        | Some new_body -> (true,  new_body)
        | _ ->             
          case body of
            | Var ((id, _), _) | id in? vars_to_remove -> (true, nullTerm)
            | _ -> (false, body)
  in
  if changed_bindings? || changed_body? then
    Some (Let (new_bindings, new_body, pos))
  else
    None

 %% ================================================================================

 op globalizeLetRec (tname                        : TypeName)
                    (gvar                         : OpName)
                    (vars_to_remove               : VarNames)  % vars of global type, remove on sight
                    (LetRec (bindings, body, pos) : MSTerm)
  : Option MSTerm = 
  %% (old_bindings   : List (MSVar * MSTerm))  (old_body       : MSTerm) 
  None

 %% ================================================================================
 %% Given global type, find argument variables of that type and remove them
 %% ================================================================================

 op globalizeLambda (tname               : TypeName) 
                    (gvar                : OpName)
                    (vars_to_remove      : VarNames)  % vars of global type, remove on sight
                    (Lambda (rules, pos) : MSTerm)
  : Option MSTerm = 
  let 
    def globalizeRule (rule as (pat, cond, body)) =
      case globalizePattern tname gvar vars_to_remove pat of
        | ([], _) -> 
          (case globalizeTerm tname gvar vars_to_remove body of
             | Some new_body ->
               Some (pat, cond, new_body)
             | _ ->
               None)
        | (new_vars_to_remove, Some new_pat) ->
          Some (new_pat, 
                myTrue, 
                case globalizeTerm tname gvar (vars_to_remove ++ new_vars_to_remove) body of
                  | Some new_body -> new_body
                  | _ -> body)
        | (new_vars_to_remove, None) ->
          %% fn (x:Global) -> 
          let new_body =
              case globalizeTerm tname gvar (vars_to_remove ++ new_vars_to_remove) body of
                | Some new_body -> new_body
                | _ -> body
          in
          case new_body of
            | Lambda ([(new_pat, new_cond, new_body)], _) ->
              %% fn (x:Global) -> fn (new_pat) -> new_body
              %%  =>
              %%                  fn (new_pat) -> new_body
              Some (new_pat, new_cond, new_body)
            | _ ->
              %% fn (x:Global) -> new_body
              %%  =>
              %% fn _ -> new_body
              Some (nullPat, myTrue, new_body)
          
  in
  let opt_new_rules = map globalizeRule rules in
  if exists? (fn opt_rule -> case opt_rule of | Some _ -> true | _ -> false) opt_new_rules then
    let new_rules = map2 (fn (rule, opt_new_rule) -> 
                            case opt_new_rule of
                              | Some new_rule -> new_rule
                              | _ -> rule)
                         (rules, opt_new_rules)
    in
    Some (Lambda (new_rules, pos))
  else
    % None indicates no change
    None

 %% ================================================================================

 op globalizeIfThenElse (tname                        : TypeName)
                        (gvar                         : OpName)
                        (vars_to_remove               : VarNames)  % vars of global type, remove on sight
                        (IfThenElse (t1, t2, t3, pos) : MSTerm)
  : Option MSTerm = 
  let opt_new_t1 = globalizeTerm tname gvar vars_to_remove t1 in
  let opt_new_t2 = globalizeTerm tname gvar vars_to_remove t2 in
  let opt_new_t3 = globalizeTerm tname gvar vars_to_remove t3 in
  case (opt_new_t1, opt_new_t2, opt_new_t3) of
    | (None, None, None) -> 
      % Term is unchanged
      None 
    | _ -> 
      let new_t1 = case opt_new_t1 of
                     | Some new_t1 -> new_t1
                     | _ -> t1
      in
      let new_t2 = case opt_new_t2 of
                     | Some new_t2 -> new_t2
                     | _ -> t2
      in
      let new_t2 = case new_t2 of
                     | Var ((id, _), _) | id in? vars_to_remove -> nullTerm
                     | _ -> new_t2
      in
      let new_t3 = case opt_new_t3 of
                     | Some new_t3 -> new_t3
                     | _ -> t3
      in
      let new_t3 = case new_t3 of
                     | Var ((id, _), _) | id in? vars_to_remove -> nullTerm
                     | _ -> new_t3
      in
      Some (IfThenElse (new_t1, new_t2, new_t3, pos))


 %% ================================================================================

 op globalizeSeq (tname          : TypeName)
                 (gvar           : OpName)
                 (vars_to_remove : VarNames)  % vars of global type, remove on sight
                 (Seq (tms, pos) : MSTerm) 
  : Option MSTerm = 
  let opt_new_tms = map (fn tm -> globalizeTerm tname gvar vars_to_remove tm) tms in
  if exists? (fn opt_tm -> case opt_tm of | Some _ -> true | _ -> false) opt_new_tms then  
    let new_tms = map2 (fn (tm, opt_new_tm) ->
                         case opt_new_tm of 
                           | Some new_tm -> new_tm
                           | _ -> tm)
                       (tms, opt_new_tms)
    in
    Some (Seq (new_tms, pos))
  else
    None

 %% ================================================================================

 op globalizeTypedTerm (tname                    : TypeName)
                       (gvar                     : OpName)
                       (vars_to_remove           : VarNames)  % vars of global type, remove on sight
                       (TypedTerm (tm, typ, pos) : MSTerm)
  : Option MSTerm = 
  let
   def nullify_global typ =
     if globalType? tname typ then
       nullType
     else
       case typ of

         | Arrow (dom, rng, pos) -> 
           let rng = nullify_global rng in
           if globalType? tname dom then
             case rng of
               | Arrow _ -> rng
               | _ -> Arrow (nullify_global dom, rng, noPos)
           else
             Arrow (nullify_global dom, rng, noPos)

         | Product (fields, pos) ->
           (let new_fields = foldl (fn (fields, (id, typ)) ->
                                      if globalType? tname typ then
                                        fields
                                      else
                                        fields ++ [(id, nullify_global typ)])
                                   []
                                   fields
            in
            case new_fields of
              | [(_, typ)] -> typ
              | _ -> Product (renumber new_fields, noPos))
         | CoProduct (fields, pos) -> 
           %% TODO: revise CoProduct ??
           let new_fields = foldl (fn (fields, field as (id, opt_typ)) ->
                                     case opt_typ of
                                       | Some typ ->
                                         if globalType? tname typ then
                                           fields
                                         else
                                           fields ++ [(id, Some (nullify_global typ))]
                                       | _ ->
                                         fields ++ [field])
                                  []
                                  fields
           in
           CoProduct (new_fields, noPos)
         | _ -> typ

  in
  case globalizeTerm tname gvar vars_to_remove tm of
    | Some new_tm ->
      let new_typ = nullify_global typ in 
      Some (TypedTerm (new_tm, new_typ, pos))
    | _ ->
      None

 %% ================================================================================

 op globalizePi (tname                : TypeName)
                (gvar                 : OpName)
                (vars_to_remove       : VarNames)  % vars of global type, remove on sight
                (Pi (tyvars, tm, pos) : MSTerm)
  : Option MSTerm = 
  case globalizeTerm tname gvar vars_to_remove tm of
    | Some new_tm ->
      Some (Pi (tyvars, new_tm, pos)) % TODO: remove unused tyvars
    | _ ->
      None

 %% ================================================================================

 op globalizeAnd (tname          : TypeName)
                 (gvar           : OpName)
                 (vars_to_remove : VarNames)  % vars of global type, remove on sight
                 (And (tms, pos) : MSTerm)
  : Option MSTerm = 
  case tms of
    | tm :: _ -> globalizeTerm tname gvar vars_to_remove tm
    | [] -> None

 %% ================================================================================

 op globalizeTerm (tname          : TypeName)
                  (gvar           : OpName)
                  (vars_to_remove : VarNames)  % vars of global type, remove on sight
                  (term           : MSTerm) 
  : Option MSTerm = 
  case term of
    | Apply      _ -> globalizeApply      tname gvar vars_to_remove term
    | Record     _ -> globalizeRecord     tname gvar vars_to_remove term
    | Let        _ -> globalizeLet        tname gvar vars_to_remove term
    | LetRec     _ -> globalizeLetRec     tname gvar vars_to_remove term
    | Lambda     _ -> globalizeLambda     tname gvar vars_to_remove term
    | IfThenElse _ -> globalizeIfThenElse tname gvar vars_to_remove term
    | Seq        _ -> globalizeSeq        tname gvar vars_to_remove term
    | TypedTerm  _ -> globalizeTypedTerm  tname gvar vars_to_remove term
    | Pi         _ -> globalizePi         tname gvar vars_to_remove term
    | And        _ -> globalizeAnd        tname gvar vars_to_remove term

   %| ApplyN     _ -> None % not present after elaborateSpec is called
   %| Bind       _ -> None % should not be globalizing inside quantified terms
   %| The        _ -> None % should not be globalizing inside 'the' term
   %| Var        _ -> None % vars to be globalized should be removed from parent before we get to this level
   %| Fun        _ -> None % primitive terms are never global
   %| Transform  _ -> None % doesn't make sense to globalize this
   %| Any        _ -> None % can appear within typed term, for example

    | _ -> None

 %% ================================================================================

 op globalizeOpInfo (spc        : Spec, 
                     old_info   : OpInfo, 
                     gtype_name : TypeName,
                     gvar       : OpName, 
                     ginit      : OpName,
                     tracing?   : Bool)
  : OpInfo =
  let qid as Qualified(q, id) = primaryOpName old_info in
  if baseOp? qid then
    old_info
  else
    let old_dfn = case old_info.dfn of 
                    | And (tm :: _, _) -> tm 
                    | tm -> tm 
    in
    case globalizeTerm gtype_name gvar [] old_dfn of
      | Some new_dfn -> 
        let new_info = old_info << {dfn = new_dfn} in
        let _ = if tracing? then
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
      | _ -> 
        old_info

 op replaceLocalsWithGlobalRefs (spc      : Spec, 
                                 gtype    : TypeName, 
                                 gvar     : OpName, 
                                 ginit    : OpName,
                                 tracing? : Boolean) 
  : SpecCalc.Env (Spec * Bool) =
  (*
   * At this point, we know:
   *  gtype names a unique existing base type in spc,
   *  gvar  names a unique existing op in spc, of type 'gtype'
   *  ginit names a unique existing op in spc, of type 'gtype' or 'X -> gtype'
   *
   * For every op f in spc, remove local vars of type gtype, and replace with references to gvar.
   * If the final returned value is constructed "on-the-fly", add an assignment of that value to gvar.
   *)
  let (root_ops, root_types) = topLevelOpsAndTypesExcludingBaseSubsts spc in
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
                     chase_theorems?)
  in
  % let _ = appiAQualifierMap (fn (q, id, _) -> writeLine("Old op       : " ^ q ^ "." ^ id)) spc.ops in
  % let _ = appiAQualifierMap (fn (q, id, _) -> writeLine("Op to revise : " ^ q ^ "." ^ id)) ops_to_revise in
  let new_ops =
      foldriAQualifierMap (fn (q, id, x, pending_ops) ->
                             case findTheOp (spc, Qualified (q, id)) of
                               | Some info -> 
                                 let new_info = globalizeOpInfo (spc, info, gtype, gvar, ginit, tracing?) in
                                 % let _ = writeLine("Found          " ^ q ^ "." ^ id) in
                                 insertAQualifierMap (pending_ops, q, id, new_info)
                               | _ -> 
                                 let _ = writeLine("??? Could not find op " ^ q ^ "." ^ id) in
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
                                 let _ = writeLine("??? Could not find type " ^ q ^ "." ^ id) in
                                 pending_types)
                          base_types
                          types_to_keep
  in
  let new_spec = spc << {ops = new_ops, types = new_types} in
  let 
    def aux elements =
      foldl (fn (new_elts, elt) ->
               case elt of
                 | Import (sc_term, imported_spec, imported_elts, pos) ->
                   new_elts ++ [Import (sc_term, imported_spec, aux imported_elts, pos)]
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
                 | OpDef (Qualified(q,id), _, _) ->
                   (case findAQualifierMap (new_ops, q, id) of
                      | Some _ -> new_elts ++ [elt]
                      | _ -> new_elts)
                 | _ -> new_elts)
             []
             elements
  in
  let new_elements = aux spc.elements in
  % let _ = appiAQualifierMap (fn (q, id, _) -> writeLine("New type     : " ^ q ^ "." ^ id)) new_types in
  % let _ = appiAQualifierMap (fn (q, id, _) -> writeLine("New op       : " ^ q ^ "." ^ id)) new_ops   in
  return (spc << {ops = new_ops, types = new_types, elements = new_elements}, tracing?)

 op globalizeSingleThreadedType (spc       : Spec, 
                                 gtype     : TypeName, 
                                 gvar      : OpName, 
                                 opt_ginit : Option OpName,
                                 tracing?  : Boolean)
  : SpecCalc.Env (Spec * Bool) =
  let _ = writeLine("tracing? = " ^ show tracing?) in
  let tracing? = true in
  let _ = writeLine("force tracing? = " ^ show tracing?) in
  {
   gtype <- checkGlobalType (spc, gtype);
   gvar  <- checkGlobalVar  (spc, gvar, gtype);
   ginit <- (case opt_ginit of
               | Some ginit -> checkGlobalInitOp (spc, ginit, gtype)
               | _ -> findInitOp (spc, gtype));
   spec_with_gvar <- return (case findTheOp (spc, gvar) of
                               | Some _ -> spc
                               | _ -> spc);  % addOp (spc, gvar, type)
   replaceLocalsWithGlobalRefs (spc, gtype, gvar, ginit, tracing?)
   }

 %% ================================================================================

}

