SliceSpec qualifying spec 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Old stuff that is deprecated
%%% See below for new stuff
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

import ../Specs/AnalyzeRecursion

type QualifierSet = AQualifierMap Bool

op emptySet: QualifierSet = emptyAQualifierMap

op in? (Qualified(q,id): QualifiedId, s: QualifierSet) infixl 20 : Bool =
 some?(findAQualifierMap(s, q, id) )

op nin?  (Qualified(q,id): QualifiedId, s: QualifierSet) infixl 20 : Bool =
 none?(findAQualifierMap(s, q, id) )

op <| (s: QualifierSet, Qualified(x, y): QualifiedId) infixl 25 : QualifierSet =
 insertAQualifierMap(s, x, y, true)

op addList(s: QualifierSet, l: QualifiedIds): QualifierSet =
 foldl (<|) s l

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op codeGenElement?(el: SpecElement): Bool =
 case el of
   | Pragma("#translate", _, "#end", _) -> true
   | Pragma _ -> false
   | _ -> true

op scrubSpec (spc : Spec, op_set : QualifierSet, type_set : QualifierSet) : Spec =
 let new_types =
     mapiPartialAQualifierMap (fn (q, id, v) ->
                                  if Qualified (q, id) in? type_set then
                                    Some v
                                  else 
                                    None)
                               spc.types
 in
 let new_ops =
     mapiPartialAQualifierMap (fn (q, id, v) ->
                                 if Qualified (q, id) in? op_set then
                                   Some v
                                 else 
                                   None)
                              spc.ops
 in
 let
   def filterElements (elements : SpecElements) : SpecElements =
     let
       def keep? el =
         case el of
           | Type     (qid,              _) -> qid in? type_set
           | TypeDef  (qid,              _) -> qid in? type_set
           | Op       (qid, _,           _) -> qid in? op_set && numRefinedDefs spc qid = 1
           | OpDef    (qid, refine_num,_,_) -> qid in? op_set && numRefinedDefs spc qid = refine_num + 1
           | Property (_, _, _, formula, _) ->
             forall? (fn qid -> qid in? op_set) (opsInTerm formula)
             && 
             forall? (fn qid -> qid in? type_set) (typesInTerm formula)
             % | Import   (_, _, elts,       _) -> exists? (fn el -> element_filter el) elts
           | Import _ -> true
           | _ -> codeGenElement? el
     in
     mapPartial (fn elt ->
                   if keep? elt then
                     Some (case elt of
                             | Import (s_tm, i_sp, elts,                a) ->
                               Import (s_tm, i_sp, filterElements elts, a)
                             | _ ->  elt)
                   else
                     None)
                elements
 in
 let new_elements = filterElements spc.elements in
 spc << {
         types    = new_types,
         ops      = new_ops, 
         elements = new_elements
         }

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Haskell generation calls this directly...
op sliceSpecInfoForCode (spc        : Spec,
                         root_ops   : QualifiedIds, 
                         root_types : QualifiedIds) 
 : QualifierSet * QualifierSet =
 let chase_terms_in_types? = false in
 let chase_theorems?       = false in
 let 
   def cut_op?   (qid : QualifiedId) : Bool = false
   def cut_type? (qid : QualifiedId) : Bool = false
 in
 sliceSpecInfo (spc, root_ops, root_types, cut_op?, cut_type?, chase_terms_in_types?, chase_theorems?, false)

op [a] foldJustTerms (f : a -> MSTerm -> a) (acc: a) (term : MSTerm) (firstDefsOnly? : Bool) : a =
 %% foldTerm recurs into term within types and patterns: subtypes, quotients, etc.
 let foldOfChildren = 
      case term of
        | Let        (decls, bdy, _) -> foldJustTerms f (foldl (fn (acc, (_,tm)) -> foldJustTerms f acc tm firstDefsOnly?) acc decls) bdy firstDefsOnly?
        | LetRec     (decls, bdy, _) -> foldJustTerms f (foldl (fn (acc, (_,tm)) -> foldJustTerms f acc tm firstDefsOnly?) acc decls) bdy firstDefsOnly?
        | Record     (row,        _) -> foldl (fn (acc, (id,tm)) -> foldJustTerms f acc tm firstDefsOnly?) acc row
        | IfThenElse (t1, t2, t3, _) -> foldJustTerms f (foldJustTerms f (foldJustTerms f acc t1 firstDefsOnly?) t2 firstDefsOnly?) t3 firstDefsOnly?
        | Lambda     (match,      _) -> foldl (fn (acc,(_,cond,tm)) -> foldJustTerms f (foldJustTerms f acc cond firstDefsOnly?) tm firstDefsOnly?) acc match
        | Bind       (_, _, tm,   _) -> foldJustTerms f acc tm firstDefsOnly?
        | The        (_, tm,      _) -> foldJustTerms f acc tm firstDefsOnly?
        | Apply      (t1, t2,     _) -> foldJustTerms f (foldJustTerms f acc t1 firstDefsOnly?) t2 firstDefsOnly?
        | Seq        (tms,        _) -> foldl (fn (acc, tm) -> foldJustTerms f acc tm firstDefsOnly?) acc tms
        | ApplyN     (tms,        _) -> foldl (fn (acc, tm) -> foldJustTerms f acc tm firstDefsOnly?) acc tms
        | TypedTerm  (tm, _,      _) -> foldJustTerms f acc tm firstDefsOnly?
        | Pi         (_, tm,      _) -> foldJustTerms f acc tm firstDefsOnly?
        | And        (tms,        _) -> (if firstDefsOnly? then
                                           foldJustTerms f acc (head tms) firstDefsOnly?
                                         else
                                           foldl (fn (acc, tm) -> foldJustTerms f acc tm firstDefsOnly?) acc tms
                                           )
        | _ -> acc
 in
 f foldOfChildren term
 
op sliceSpecInfo (spc                   : Spec, 
                  root_ops              : QualifiedIds, 
                  root_types            : QualifiedIds, 
                  cut_op?               : QualifiedId -> Bool, % stop recursion at these, and do not include them
                  cut_type?             : QualifiedId -> Bool, % stop recursion at these, and do not include them
                  chase_terms_in_types? : Bool, 
                  chase_theorems?       : Bool,
                  firstDefsOnly?        : Bool  %%governs handling of And terms
                  )
 : QualifierSet * QualifierSet =
 let 
   def eq_op_qid (Qualified (q, id)) = Qualified (q, "eq_" ^ id)
      
   def findQuotientOpsIn typ =
     foldType (fn result -> fn _ -> result,
               fn result -> fn typ -> 
                 case typ of
                   | Quotient (_, Fun (Op (qid, _), _, _), _) -> result ++ [qid]
                   | _ -> result,
               fn result -> fn _ -> result)
              []
              typ

   def newOpsInTerm (tm, newopids, op_set, firstDefsOnly?) =
     if chase_terms_in_types? then
       %% FIXME pass firstDefsOnly? to foldTerm?
       foldTerm (fn opids -> fn tm ->
                   case tm of
                     | Fun (Op (qid,_), funtype, _) ->
                       % let _ = writeLine("new_ops_in_term: " ^ show qid ^ " : " ^ show (cut_op? qid)) in
                       if cut_op? qid then
                         opids
                       else if qid nin? opids  && qid nin? op_set then
                         qid :: opids
                            else
                              opids
                     | Fun (Equals, Arrow (Product ([("1", Base (type_qid, _, _)), _], _), _, _), _) ->
                       let eq_qid = eq_op_qid type_qid in
                       % let _ = writeLine("new_ops_in_term: " ^ show eq_qid ^ " : " ^ show (cut_op? eq_qid)) in
                       if cut_op? eq_qid then
                         opids
                       else if eq_qid nin? opids  && eq_qid nin? op_set then % avoid millions of duplicate entries
                         eq_qid :: opids
                       else
                         opids
                     | _ -> opids,
                 fn result -> fn _ -> result,
                 fn result -> fn _ -> result)
                newopids 
                tm
     else
       foldJustTerms (fn opids -> fn tm ->
                        case tm of
                          | Fun (Op (qid,_), funtype, _) ->
                            % let _ = writeLine("new_ops_in_term: " ^ show qid ^ " : " ^ show (cut_op? qid)) in
                            if cut_op? qid then
                              opids
                            else if qid nin? opids  && qid nin? op_set then
                              qid :: opids
                            else
                              opids
                          | Fun  (Quotient typename, typ, _) -> 
                            (case findTheType (spc, typename) of
                               | Some typeinfo -> 
                                 %% quotient functions may be needed at runtime...
                                 let quotients = findQuotientOpsIn typeinfo.dfn in
                                 % let _ = writeLine("For type " ^ show typename ^ " : " ^ anyToString typeinfo) in
                                 % let _ = writeLine("Quotients = " ^ anyToString quotients) in
                                 quotients ++ opids
                               | _ ->
                                 % let _ = writeLine("For type " ^ show typename ^ " : no typeinfo") in
                                 opids)
                          | Fun (Equals, Arrow (Product ([("1", Base (type_qid, _, _)), _], _), _, _), _) ->
                            let eq_qid = eq_op_qid type_qid in
                            % let _ = writeLine("new_ops_in_term: " ^ show eq_qid ^ " : " ^ show (cut_op? eq_qid)) in
                            if cut_op? eq_qid then
                              opids
                            else if eq_qid nin? opids  && eq_qid nin? op_set then % avoid millions of duplicate entries
                              eq_qid :: opids
                            else
                              opids
                          | _ -> opids)
                     newopids 
                     tm
                     firstDefsOnly?

   def newOpsInType (ty : MSType, newopids : QualifiedIds, op_set : QualifierSet) : QualifiedIds =
     if chase_terms_in_types? then
       foldType (fn opids -> fn tm ->
                   case tm of
                     | Fun (Op (qid,_), funtype, _) ->
                       % let _ = writeLine("new_ops_in_type: " ^ show qid ^ " : " ^ show (cut_op? qid)) in
                       if cut_op? qid then
                         opids
                       else if qid nin? opids && qid nin? op_set then
                         qid :: opids
                       else
                         opids
                     | Fun (Equals, Arrow (Product ([("1", Base (type_qid, _, _)), _], _), _, _), _) ->
                       let eq_qid = eq_op_qid type_qid in
                       % let _ = writeLine("new_ops_in_type: " ^ show eq_qid ^ " : " ^ show (cut_op? eq_qid)) in
                       if cut_op? eq_qid then
                         opids
                       else if eq_qid nin? opids  && eq_qid nin? op_set then % avoid millions of duplicate entries
                         eq_qid :: opids
                            else
                              opids
                     | _ -> opids,
                 fn result -> fn _ -> result,
                 fn result -> fn _ -> result)
                newopids 
                ty
     else
       newopids

   def newTypesInTerm (tm : MSTerm, newtypeids : QualifiedIds, type_set : QualifierSet) : QualifiedIds =
     foldTerm (fn result -> fn _ -> result,
               fn result -> fn t ->
                 case t of
                   | Base (qid,_,_) ->
                     % let _ = writeLine("new_types_in_term: " ^ show qid ^ " : " ^ show (cut_type? qid)) in
                     if cut_type? qid then
                       result
                     else if qid nin? result && qid nin? type_set then
                       qid :: result
                     else
                       result
                   | _ -> result,
               fn result -> fn _ -> result)
              newtypeids 
              tm
      
   def newTypesInType (ty : MSType, newtypeids : QualifiedIds, type_set : QualifierSet) : QualifiedIds =
     foldType (fn result -> fn _ -> result,
               fn result -> fn t ->
                 case t of
                   | Base (qid,_,_) ->
                     % let _ = writeLine("new_types_in_type: " ^ show qid ^ " : " ^ show (cut_type? qid)) in
                     if cut_type? qid then
                       result
                     else if qid nin? result && qid nin? type_set then
                       qid :: result
                     else
                       result
                   | _ -> result,
               fn result -> fn _ -> result)
              newtypeids 
              ty
      
   def iterateDeps (new_ops, new_types, op_set, type_set, n, firstDefsOnly?) =
     % let _ = writeLine ("================================================================================") in
     % let _ = writeLine ("Round " ^ show n) in
     if new_ops = [] && new_types = [] then 
       % let _ = writeLine ("Done") in
       % let _ = writeLine ("================================================================================") in
       (op_set, type_set)
     else
       % let _ = writeLine ("New ops:  " ^ anyToString new_ops) in
       % let _ = writeLine ("New type: " ^ anyToString new_types) in
       let op_set   = addList (op_set,   new_ops)   in
       let type_set = addList (type_set, new_types) in
       let new_ops_in_ops = 
           foldl (fn (newopids, qid) ->
                    % let _ = writeLine("new_ops_in_ops: " ^ show qid ^ " : " ^ show (cut_op? qid)) in
                    if cut_op? qid then
                      newopids
                    else
                      case findTheOp (spc, qid) of
                        | Some opinfo -> 
                          % let _ = writeLine("Scanning ops in op: " ^ show (primaryOpName opinfo)) in
                          % let _ = writeLine("               dfn: " ^ printTerm opinfo.dfn) in
                          newOpsInTerm (opinfo.dfn, newopids, op_set, firstDefsOnly?)
                        | None -> newopids)
                 [] 
                 new_ops
       in
       let new_ops_in_ops_or_types = 
           if chase_terms_in_types? then 
             foldl (fn (newopids, qid) ->
                      % let _ = writeLine("new_ops_in_types: " ^ show qid ^ " : " ^ show (cut_type? qid)) in
                      if cut_type? qid then
                        newopids
                      else
                        case findTheType (spc, qid) of
                          | Some typeinfo -> 
                            % let _ = writeLine("Scanning ops in type: " ^ show (primaryTypeName typeinfo)) in
                            newOpsInType(typeinfo.dfn, newopids, op_set)
                          | None -> newopids)
                   new_ops_in_ops
                   new_types
           else
             new_ops_in_ops
       in
       let new_types_in_ops = 
           foldl (fn (newtypeids, qid) ->
                    % let _ = writeLine("new_types_in_ops: " ^ show qid ^ " : " ^ show (cut_op? qid)) in
                    if cut_op? qid then
                      newtypeids
                    else
                      case findTheOp (spc, qid) of
                        | Some opinfo -> 
                          % let _ = writeLine("Scanning types in op: " ^ show (primaryOpName opinfo)) in
                          newTypesInTerm (opinfo.dfn, newtypeids, type_set)
                        | None -> newtypeids)
                 [] 
                 new_ops
       in
       let new_types_in_ops_or_types = 
           foldl (fn (newtypeids, qid) ->
                    % let _ = writeLine("new_types_in_types: " ^ show qid ^ " : " ^ show (cut_type? qid)) in
                    if cut_type? qid then
                      newtypeids
                    else
                      case findTheType (spc, qid) of
                        | Some typeinfo -> 
                          % let _ = writeLine("Scanning types in type: " ^ show (primaryTypeName typeinfo)) in
                          newTypesInType (typeinfo.dfn, newtypeids, type_set)
                        | None -> newtypeids)
                 new_types_in_ops
                 new_types
       in
       iterateDeps (new_ops_in_ops_or_types, new_types_in_ops_or_types, op_set, type_set, n + 1, firstDefsOnly?)
 in
 let (op_set, type_set) = iterateDeps (root_ops, root_types, emptySet, emptySet, 0, firstDefsOnly?) in
 (op_set, type_set)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op sliceSpec (spc                   : Spec, 
              root_ops              : QualifiedIds,        % include these and things they recursively mention
              root_types            : QualifiedIds,        % include these and things they recursively mention
              cut_op?               : QualifiedId -> Bool, % stop recursion at these, and do not include them
              cut_type?             : QualifiedId -> Bool, % stop recursion at these, and do not include them
              chase_terms_in_types? : Bool,                % recur through subtype predicates and quotient relations
              chase_theorems?       : Bool)                % recur through axioms and theorems that mention included types and ops
 : Spec =
 let (op_set, type_set) = sliceSpecInfo (spc, root_ops, root_types, cut_op?, cut_type?, chase_terms_in_types?, chase_theorems?, false) in
 let sliced_spc         = scrubSpec     (spc, op_set,   type_set)                                                                      in
 sliced_spc
 
op sliceSpecForCode (spc        : Spec, 
                     root_ops   : QualifiedIds,        % include these and things they recursively mention
                     root_types : QualifiedIds,        % include these and things they recursively mention
                     cut_op?    : QualifiedId -> Bool, % stop recursion at these, and do not include them
                     cut_type?  : QualifiedId -> Bool) % stop recursion at these, and do not include them
 : Spec =
 let chase_terms_in_types? = false in  % do not recur through subtype predicates and quotient relations
 let chase_theorems?       = false in  % do not recur through axioms and theorems that mention included types and ops
 sliceSpec (spc, root_ops, root_types, cut_op?, cut_type?, chase_terms_in_types?, chase_theorems?)
 
op sliceSpecForCodeM (spc        : Spec, 
                      root_ops   : QualifiedIds,        % include these and things they recursively mention
                      root_types : QualifiedIds,        % include these and things they recursively mention
                      cut_op?    : QualifiedId -> Bool, % stop recursion at these, and do not include them
                      cut_type?  : QualifiedId -> Bool, % stop recursion at these, and do not include them
                      tracing?   : Bool)
 : Env (Spec * Bool) =
 return (sliceSpecForCode (spc, root_ops, root_types, cut_op?, cut_type?), tracing?)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% New Slicing Code -- Intended to replace much of the above
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

import /Languages/MetaSlang/Specs/Environment
import /Languages/MetaSlang/CodeGen/LanguageMorphism

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%W
%%%  Misc support
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%W

op [a] union (xs : List a, ys : List a) : List a =
 foldl (fn (new, x) -> 
          if x in? ys then
            new
          else
            x |> new)
       ys
       xs

op executable? (info : OpInfo) : Bool =
 let (decls, defs)  = opInfoDeclsAndDefs info in
 case defs of
   | dfn :: _ -> ~ (nonExecutableTerm1? dfn)
   | _ -> false

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%W
%%%  ADT for op/type reachability
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%W

type TranslationStatus = | Primitive | API | Handwritten | Macro

type DefStatus         = | Defined | Undefined | Missing

type Status            = | Translated TranslationStatus 
                         | Used       DefStatus 
                         | Logical    DefStatus 
                         | Contextual DefStatus 
                         | Misc       String

type TheoremName = PropertyName

type Locations     = List Location
type Location      = | ExecutionRoot
                     | TypingRoot
                     | LogicalRoot
                     | ContextRoot
                     | Op      {name : OpName,      pos: Position}
                     | Type    {name : TypeName,    pos: Position}
                     | Theorem {name : TheoremName, pos: Position}
                     | Unknown

type ResolvedOpRefs   = List ResolvedOpRef
type ResolvedOpRef    = {name            : OpName,   
                         contextual_type : MSType, % how it is used (as opposed to how it is defined)
                         locations       : Locations,
                         status          : Status}

type ResolvedTypeRefs = List ResolvedTypeRef
type ResolvedTypeRef  = {name      : TypeName, 
                         locations : Locations,
                         status    : Status}

type PendingOpRefs    = List PendingOpRef
type PendingOpRef     = {name            : OpName,   
                         contextual_type : MSType, % how it is used (as opposed to how it is defined)
                         location        : Location}

type PendingTypeRefs  = List PendingTypeRef
type PendingTypeRef   = {name     : TypeName, 
                         location : Location}

op empty_resolved_op_refs   : ResolvedOpRefs   = []
op empty_resolved_type_refs : ResolvedTypeRefs = []

type Slice = {ms_spec                  : Spec, 
              lm_data                  : LMData,
              % code is simpler if resolved and pending are tracked separately
              % (as opposed to having a Pending status)
              resolved_op_refs         : ResolvedOpRefs, 
              resolved_type_refs       : ResolvedTypeRefs,
              pending_op_refs          : PendingOpRefs,
              pending_type_refs        : PendingTypeRefs,
              oracular_op_ref_status   : PendingOpRef   -> Option Status,
              oracular_type_ref_status : PendingTypeRef -> Option Status}

type Groups = List Group
type Group  = {status     : Status, 
               type_names : Ref TypeNames,
               op_names   : Ref OpNames}

op describeGroup (group : Group) : () =
 case (! group.type_names, ! group.op_names) of
   | ([], []) -> ()
   | (type_names, op_names) ->
     let line  = case group.status of
                   | Translated Primitive   -> "These translate to primitive syntax : "
                   | Translated API         -> "These translate to an api interface : "
                   | Translated Handwritten -> "These translate to handwritten code : "
                   | Translated Macro       -> "These translate to macros : "

                   | Used       Defined     -> "These can be generated : "
                   | Used       Undefined   -> "WARNING: These are referenced, but undefined : "
                   | Used       Missing     -> "WARNING: These are referenced, but missing : "

                   | Logical    Defined     -> "These are provide explicit logical constraints, but won't be generated : "
                   | Logical    Undefined   -> "These are provide explicit logical constraints, and can't be generated : "
                   | Logical    Missing     -> "WARNING: These provide explicit logical constraints, but are missing : "

                   | Contextual Defined     -> "These provide implicit logical context, but won't be generated : "
                   | Contextual Undefined   -> "These provide implicit logical context, but can't be generated : "
                   | Contextual Missing     -> "WARNING: These provide implicit logical context, but are missing : "

                   | Misc       str         -> "NOTE: These have some miscellaneous property: " ^ str ^ " : "
     in
     let _ = writeLine line                                                              in
     let _ = writeLine ""                                                                in
     let _ = app (fn name -> writeLine ("  type " ^ show name)) type_names               in
     let _ = case (type_names, op_names) of | (_ :: _, _ :: _) -> writeLine "" | _ -> () in
     let _ = app (fn name -> writeLine ("  op "   ^ show name)) op_names                 in
     let _ = writeLine ""                                                                in
     ()

op describeSlice (msg : String, slice : Slice) : () =
 let
   def pad (str, n) =
     let m = length str in
     if m < n then
       str ^ implode (repeat #\s (n - m))
     else
       str

   def partition_type_refs (groups, type_ref) =
     case findLeftmost (fn group -> group.status = type_ref.status) groups of
       | Some group -> 
         let _ = (group.type_names := (! group.type_names) ++ [type_ref.name]) in
         groups
         
       | _ -> 
         %% Misc options will be added to end
         let group = {status     = type_ref.status, 
                      type_names = Ref [type_ref.name], 
                      op_names   = Ref []} in
         groups ++ [group]

   def partition_op_refs (groups, op_ref) =
     case findLeftmost (fn group -> group.status = op_ref.status) groups of
       | Some group -> 
         let _ = (group.op_names := (! group.op_names) ++ [op_ref.name]) in
         groups
         
       | _ -> 
         %% Misc options will be added to end
         let group = {status     = op_ref.status, 
                      type_names = Ref [], 
                      op_names   = Ref [op_ref.name]} in
         groups ++ [group]

 in
 let status_options = [Translated Primitive,
                       Translated API,
                       Translated Handwritten,
                       Translated Macro, 
                       Used       Defined,
                       Used       Undefined,
                       Used       Missing,
                       Logical    Defined,
                       Logical    Undefined,
                       Logical    Missing,
                       Contextual Defined,
                       Contextual Undefined,
                       Contextual Missing]
 in
 let groups = map (fn status -> 
                     {status     = status, 
                      type_names = Ref [], 
                      op_names   = Ref []})
                  status_options
 in
 let groups = foldl partition_op_refs   groups slice.resolved_op_refs   in
 let groups = foldl partition_type_refs groups slice.resolved_type_refs in

 let _ = writeLine ("") in
 let _ = writeLine ("Slice: " ^ msg) in
 let _ = writeLine ("") in

 let _ = if (length slice.pending_type_refs) + (length slice.pending_op_refs) > 0 then 
           let _ = writeLine "--------------------" in
           let _ = app (fn pending -> writeLine ("pending type: " ^ show pending.name)) slice.pending_type_refs in
           let _ = app (fn pending -> writeLine ("pending op:   " ^ show pending.name)) slice.pending_op_refs   in
           let _ = writeLine "--------------------" in
           ()
         else
           () 
 in

 let _ = app describeGroup groups in
 ()
 
op resolve_op_ref (slice   : Slice, 
                   pending : PendingOpRef,
                   status  : Status)
 : ResolvedOpRefs =
 let resolved_op_refs = slice.resolved_op_refs in
 case findLeftmost (fn resolved -> resolved.name = pending.name) resolved_op_refs of
   | Some _ -> 
     %% don't update if name already has a value
     resolved_op_refs
   | _ -> 
     let resolved_op_ref = {name            = pending.name, 
                            contextual_type = pending.contextual_type, 
                            locations       = [pending.location],
                            status          = status} 
     in
     resolved_op_ref |> resolved_op_refs

op resolve_type_ref (slice    : Slice, 
                     pending  : PendingTypeRef,
                     status   : Status)
 : ResolvedTypeRefs =
 let resolved_type_refs = slice.resolved_type_refs in
 case findLeftmost (fn resolved -> resolved.name = pending.name) resolved_type_refs of
   | Some _ -> 
     %% don't update if name already has a value
     resolved_type_refs
   | _ -> 
     let resolved_type_ref = {name      = pending.name, 
                              locations = [pending.location],
                              status    = status} 
     in
     resolved_type_ref |> resolved_type_refs

op ops_in_slice (slice : Slice) : OpNames =
 map (fn resolved -> resolved.name) slice.resolved_op_refs

op types_in_slice (slice : Slice) : TypeNames =
 map (fn resolved -> resolved.name) slice.resolved_type_refs

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%W
%%%  Chase invoked ops to fixpoint
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%W


op extend_execution_slice_for_pending_op_ref (pending_op_refs : PendingOpRefs)
                                             (slice           : Slice, 
                                              pending_op_ref  : PendingOpRef)
  : Slice =
 let 
   def status info = if executable? info then Defined else Undefined
 in
 case slice.oracular_op_ref_status pending_op_ref of
   | Some status ->
     let new_resolved_op_refs = resolve_op_ref (slice, pending_op_ref, status) in
     slice << {resolved_op_refs = new_resolved_op_refs}
   | _ ->
     case findTheOp (slice.ms_spec, pending_op_ref.name) of
       | Some info  ->
         let status               = Used (status info) in
         let new_resolved_op_refs = resolve_op_ref (slice, pending_op_ref, status) in
         let new_pending_op_refs  = foldl (fn (pendings, pending) ->
                                             case findLeftmost (fn resolved -> 
                                                                  resolved.name = pending.name)
                                                               new_resolved_op_refs 
                                               of
                                               | Some _ -> 
                                                 pendings
                                               | _ -> 
                                                 if pending in? pendings then
                                                   % it's already in the queue to be processed
                                                   pendings
                                                 else
                                                   pending |> pendings)
                                          []
                                          (pendingOpRefsInTerm info.dfn)
        in
        let new_pending_op_refs   = union (new_pending_op_refs, slice.pending_op_refs) in
        slice << {resolved_op_refs = new_resolved_op_refs,
                  pending_op_refs  = new_pending_op_refs}
       | _ ->
         let new_resolved_op_refs = resolve_op_ref (slice, pending_op_ref, Used Missing) in
         slice << {resolved_op_refs = new_resolved_op_refs}

op extend_execution_slice (s0 : Slice) : Slice =
 let pending_op_refs = s0.pending_op_refs           in
 let s1          = s0 << {pending_op_refs = []} in
 foldl (extend_execution_slice_for_pending_op_ref pending_op_refs)
       s1
       pending_op_refs

op execution_closure (slice : Slice) : Slice =
 case slice.pending_op_refs of
   | [] ->  slice
   | _ ->
     execution_closure (extend_execution_slice slice)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%W
%%%  Chase referenced types to fixpoint
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%W

op extend_typing_slice_for_pending_type_ref (pending : PendingTypeRefs)
                                            (slice            : Slice, 
                                             pending_type_ref : PendingTypeRef)
 : Slice =
 let 
   def status info = if anyType? info.dfn then Undefined else Defined
 in
 case slice.oracular_type_ref_status pending_type_ref of
   | Some status ->
     let new_resolved_type_refs = resolve_type_ref (slice, pending_type_ref, status) in
     slice << {resolved_type_refs = new_resolved_type_refs}
   | _ ->
     case findTheType (slice.ms_spec, pending_type_ref.name) of
       | Some info -> 
         let status                 = Used (status info) in
         let new_resolved_type_refs = resolve_type_ref (slice, pending_type_ref, status) in
         let new_pending_type_refs  = foldl (fn (pending_type_refs, pending) ->
                                               case findLeftmost (fn resolved -> 
                                                                    resolved.name = pending.name)
                                                                 new_resolved_type_refs 
                                                 of
                                                 | Some _ -> 
                                                   pending_type_refs
                                                 | _ -> 
                                                   if pending in? pending_type_refs then
                                                     % it's already in the queue to be processed
                                                     pending_type_refs
                                                   else
                                                     pending |> pending_type_refs)
                                            []
                                            (pendingTypeRefsInType info.dfn)
         in
         let new_pending_type_refs  = union (new_pending_type_refs, slice.pending_type_refs) in
         slice << {resolved_type_refs = new_resolved_type_refs,
                   pending_type_refs  = new_pending_type_refs}
       | _ ->
         let new_resolved_type_refs = resolve_type_ref (slice, pending_type_ref, Used Missing) in
         slice << {resolved_type_refs = new_resolved_type_refs}

op extend_typing_slice (s0 : Slice) : Slice =
 let pending = s0.pending_type_refs           in
 let s1      = s0 << {pending_type_refs = []} in
 foldl (extend_typing_slice_for_pending_type_ref pending)
       s1
       pending

op pendingOpRefsInTerm (term : MSTerm) : PendingOpRefs =
 %% TODO: get real locations
 map (fn name -> 
        {name            = name, 
         contextual_type = Any noPos, 
         location        = Unknown})
     (opsInTerm term)

op pendingOpRefsInType (typ : MSType) : PendingOpRefs =
 %% TODO: get real locations
 map (fn name -> 
        {name            = name, 
         contextual_type = Any noPos, 
         location        = Unknown})
     (opsInType typ)

op pendingTypeRefsInTerm (term : MSTerm) : PendingTypeRefs =
 %% TODO: get real locations
 map (fn name -> 
        {name     = name, 
         location = Unknown})
     (typesInTerm term)

op pendingTypeRefsInType (typ : MSType) : PendingTypeRefs =
 %% TODO: get real locations
 map (fn name -> 
        {name     = name, 
         location = Unknown})
     (typesInType typ)

op typing_closure (s0 : Slice) : Slice =
 let root_ops      = ops_in_slice   s0 in
 let root_types    = types_in_slice s0 in
 let pending_type_refs = map (fn name -> {name = name, location = TypingRoot}) root_types in
 let pending_type_refs = 
     foldl (fn (pending_type_refs, op_name) ->
              case findTheOp (s0.ms_spec, op_name) of
                | Some info ->
                  union (pendingTypeRefsInTerm info.dfn, pending_type_refs)
                | _ ->
                  pending_type_refs)
           pending_type_refs
           root_ops
 in
 let s1 = s0 << {pending_type_refs = pending_type_refs} in
 let
   def aux s2 =
     case s2.pending_type_refs of
       | [] ->  s2
       | _ ->
         aux (extend_typing_slice s2)
 in
 aux s1

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%W
%%%  Chase all referenced types and ops to fixpoint
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%W

op extend_logical_slice_for_pending_type_ref (pending_op_refs   : PendingOpRefs)
                                             (pending_type_refs : PendingTypeRefs)
                                             (slice            : Slice, 
                                              pending_type_ref : PendingTypeRef)
 : Slice =
 let 
   def status info = if anyType? info.dfn then Undefined else Defined
 in
 case slice.oracular_type_ref_status pending_type_ref of
   | Some status ->
     let new_resolved_type_refs = resolve_type_ref (slice, pending_type_ref, status) in
     slice << {resolved_type_refs = new_resolved_type_refs}
   | _ ->
     case findTheType (slice.ms_spec, pending_type_ref.name) of
       | Some info ->
         let status                 = Logical (status info) in
         let new_resolved_type_refs = resolve_type_ref (slice, pending_type_ref, status) in
         let new_pending_op_refs    = foldl (fn (pendings, pending) ->
                                           case findLeftmost (fn resolved -> 
                                                                resolved.name = pending.name) 
                                                             slice.resolved_op_refs 
                                             of
                                             | Some _ -> 
                                               pendings
                                             | _ -> 
                                               if pending in? pendings then
                                                 % it's already in the queue to be processed
                                                 pendings
                                               else
                                                pending |> pendings)
                                        []
                                        (pendingOpRefsInType info.dfn)
         in
         let new_pending_type_refs  = foldl (fn (pendings, pending) ->
                                           case findLeftmost (fn resolved -> 
                                                                resolved.name = pending.name)
                                                             new_resolved_type_refs 
                                             of
                                             | Some _ -> 
                                               pendings
                                             | _ -> 
                                               if pending in? pending_type_refs then
                                                 % it's already in the queue to be processed
                                                 pendings
                                               else
                                                 pending |> pendings)
                                        []
                                        (pendingTypeRefsInType info.dfn)
         in
         let new_pending_op_refs    = union (new_pending_op_refs,   slice.pending_op_refs)   in
         let new_pending_type_refs  = union (new_pending_type_refs, slice.pending_type_refs) in
         slice << {resolved_type_refs = new_resolved_type_refs,
                   pending_op_refs    = new_pending_op_refs,
                   pending_type_refs  = new_pending_type_refs}
       | _ ->
         let new_resolved_type_refs = resolve_type_ref (slice, pending_type_ref, Logical Missing) in
         slice << {resolved_type_refs = new_resolved_type_refs}

op extend_logical_slice_for_pending_op_ref (pending_op_refs   : PendingOpRefs)
                                           (pending_type_refs : PendingTypeRefs)
                                           (slice          : Slice, 
                                            pending_op_ref : PendingOpRef)
 : Slice =
 let 
   def status info = if executable? info then Defined else Undefined
 in
 case slice.oracular_op_ref_status pending_op_ref of
   | Some status ->
     let new_resolved_op_refs = resolve_op_ref (slice, pending_op_ref, status) in
     slice << {resolved_op_refs = new_resolved_op_refs}
   | _ ->
     case findTheOp (slice.ms_spec, pending_op_ref.name) of
       | Some info ->
         let status                = Logical (status info) in
         let new_resolved_op_refs  = resolve_op_ref (slice, pending_op_ref, status) in
         let new_pending_op_refs   = foldl (fn (pendings, pending) ->
                                              case findLeftmost (fn resolved -> 
                                                                   resolved.name = pending.name)
                                                                new_resolved_op_refs 
                                                of
                                                | Some _ -> 
                                                  pendings
                                                | _ -> 
                                                  if pending in? pendings then
                                                    % it's already in the queue to be processed
                                                    pendings
                                                  else
                                                    pending |> pendings)
                                           []
                                           (pendingOpRefsInTerm info.dfn)
         in
         let new_pending_type_refs = foldl (fn (pendings, pending) ->
                                              case findLeftmost (fn resolved -> 
                                                                   resolved.name = pending.name)
                                                                slice.resolved_type_refs 
                                                of
                                                | Some _ -> 
                                                  pendings
                                                | _ -> 
                                                  if pending in? pendings then
                                                    % it's already in the queue to be processed
                                                    pending_type_refs
                                                  else
                                                    pending |> pendings)
                                           []
                                           (pendingTypeRefsInTerm info.dfn)
         in
         let new_pending_op_refs   = union (new_pending_op_refs,   slice.pending_op_refs)   in
         let new_pending_type_refs = union (new_pending_type_refs, slice.pending_type_refs) in
         slice << {resolved_op_refs  = new_resolved_op_refs,
                   pending_op_refs   = new_pending_op_refs,
                   pending_type_refs = new_pending_type_refs}
       | _ ->
         let new_resolved_op_refs = resolve_op_ref (slice, pending_op_ref, Logical Missing) in
         slice << {resolved_op_refs = new_resolved_op_refs}

op extend_logical_slice (s0 : Slice) : Slice =
 let pending_type_refs = s0.pending_type_refs   in
 let pending_op_refs   = s0.pending_op_refs     in
 let s1 = s0 << {pending_op_refs   = [],
                 pending_type_refs = []}
 in
 let s2 = foldl (extend_logical_slice_for_pending_type_ref pending_op_refs pending_type_refs)
                s1
                pending_type_refs
 in
 let s3 = foldl (extend_logical_slice_for_pending_op_ref   pending_op_refs pending_type_refs)
                s2
                pending_op_refs
 in
 s3

op logical_closure (s0 : Slice) : Slice =
 let root_ops      = ops_in_slice   s0 in
 let root_types    = types_in_slice s0 in
 let pending_op_refs   = map (fn name ->
                                {name            = name, 
                                 contextual_type = Any noPos, 
                                 location        = LogicalRoot})  
                             root_ops
 in
 let pending_type_refs = map (fn name -> 
                                {name     = name, 
                                 location = LogicalRoot}) 
                             root_types
 in
 let s1 = s0 << {pending_op_refs   = pending_op_refs, 
                 pending_type_refs = pending_type_refs}
 in
 let
   def aux s2 =
     case (s2.pending_type_refs, s2.pending_op_refs) of
       | ([], []) ->  s2
       | _ ->
         aux (extend_logical_slice s2)
 in
 aux s1

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%W

op completeSlice (s0 : Slice) : Slice =
 %% s0 begins with pending ops and types
 let s1 = execution_closure s0 in
 let s2 = typing_closure    s1 in
 let s3 = logical_closure   s2 in
 s3

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%W

end-spec
