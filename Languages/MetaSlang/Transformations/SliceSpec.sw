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

   def newOpsInTerm (tm : MSTerm, newopids : QualifiedIds, op_set : QualifierSet, firstDefsOnly? : Bool) : QualifiedIds =
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
import /Library/Structures/Data/Maps/SimpleAsSTHarray
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

type TranslationStatus = | Primitive | API | Macro
type DefStatus = | Defined | Undefined | Missing
type Status   = | Translated TranslationStatus 
                | Used       DefStatus 
                | Logical    DefStatus 
                | Contextual DefStatus 
                | Misc       String

type OpMap   = STHMap.Map (OpName,   Status)
type TypeMap = STHMap.Map (TypeName, Status)

op empty_op_map   : OpMap   = STH_empty_map
op empty_type_map : TypeMap = STH_empty_map

type Slice = {ms_spec              : Spec, 
              lm_data              : LMData,
              op_map               : OpMap, 
              type_map             : TypeMap,
              pending_ops          : OpNames,
              pending_types        : TypeNames,
              oracular_type_status : TypeName -> Option Status,
              oracular_op_status   : OpName   -> Option Status}

type Groups = List Group
type Group  = {status     : Status, 
               type_names : Ref TypeNames,
               op_names   : Ref OpNames}

op describeGroup (group : Group) : () =
 case (! group.type_names, ! group.op_names) of
   | ([], []) -> ()
   | (type_names, op_names) ->
     let line  = case group.status of
                   | Translated Primitive -> "These translate to primitive syntax : "
                   | Translated API       -> "These translate to an api interface : "
                   | Translated Macro     -> "These translate to macros : "

                   | Used       Defined   -> "These can be generated : "
                   | Used       Undefined -> "WARNING: These are referenced, but undefined : "
                   | Used       Missing   -> "WARNING: These are referenced, but missing : "

                   | Logical    Defined   -> "These are provide explicit logical constraints, but won't be generated : "
                   | Logical    Undefined -> "These are provide explicit logical constraints, and can't be generated : "
                   | Logical    Missing   -> "WARNING: These provide explicit logical constraints, but are missing : "

                   | Contextual Defined   -> "These provide implicit logical context, but won't be generated : "
                   | Contextual Undefined -> "These provide implicit logical context, but can't be generated : "
                   | Contextual Missing   -> "WARNING: These provide implicit logical context, but are missing : "

                   | Misc       str       -> "NOTE: These have some miscellaneous property: " ^ str ^ " : "
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

   def partition_types (qid, status, groups) : Groups =
     case findLeftmost (fn group -> group.status = status) groups of
       | Some group -> 
         let _ = (group.type_names := (! group.type_names) ++ [qid]) in
         groups
         
       | _ -> 
         %% Misc options will be added to end
         let group = {status = status, type_names = Ref [qid], op_names = Ref []} in
         groups ++ [group]

   def partition_ops (qid, status, groups) : Groups =
     case findLeftmost (fn group -> group.status = status) groups of
       | Some group -> 
         let _ = (group.op_names := (! group.op_names) ++ [qid]) in
         groups
         
       | _ -> 
         %% Misc options will be added to end
         let group = {status = status, type_names = Ref [], op_names = Ref [qid]} in
         groups ++ [group]

 in
 let status_options = [Translated Primitive,
                       Translated API,
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
 let groups = foldi partition_ops   groups slice.op_map   in
 let groups = foldi partition_types groups slice.type_map in

 let _ = writeLine ("") in
 let _ = writeLine ("Slice: " ^ msg) in
 let _ = writeLine ("") in

 let _ = if length (slice.pending_types ++ slice.pending_ops) > 0 then 
           let _ = writeLine "--------------------" in
           let _ = app (fn name -> writeLine ("pending type: " ^ show name)) slice.pending_types in
           let _ = app (fn name -> writeLine ("pending op:   " ^ show name)) slice.pending_ops   in
           let _ = writeLine "--------------------" in
           ()
         else
           () 
 in

 let _ = app describeGroup groups in
 ()
 
op ops_update (ops : OpMap, name : OpName, status : Status) : OpMap =
 %% don't update if name already has a value
 case apply (ops, name) of
   | Some _ -> ops
   | _ -> update (ops, name, status)

op types_update (types: TypeMap, name : TypeName, status : Status) : TypeMap =
 %% don't update if name already has a value
 case apply (types, name) of
   | Some _ -> types
   | _ -> update (types, name, status)
 
op ops_in_slice (slice : Slice) : OpNames =
 domainToList slice.op_map

op types_in_slice (slice : Slice) : TypeNames =
 domainToList slice.type_map

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%W
%%%  Chase invoked ops to fixpoint
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%W


op extend_execution_slice_for_op (pending : OpNames) (slice : Slice, name : OpName) : Slice =
 % let _ = writeLine("") in
 % let _ = writeLine("Extending execution for op " ^ show name) in
 let 
   def status info = if executable? info then Defined else Undefined
 in
 case slice.oracular_op_status name of
   | Some status ->
     let new_op_map = ops_update (slice.op_map, name, status) in
     slice << {op_map = new_op_map}
   | _ ->
     case findTheOp (slice.ms_spec, name) of
       | Some info  ->
         let status       = Used (status info) in
         let new_op_map   = ops_update (slice.op_map, name, status) in
         let new_op_names = foldl (fn (names, name) ->
                                     case apply (new_op_map, name) of
                                       | Some _ -> names
                                       | _ -> 
                                         if name in? pending then
                                           % it's already in the queue to be processed
                                           names
                                         else
                                           name |> names)
                                  []
                                  (opsInTerm info.dfn)
        in
        % let _ = app (fn name -> writeLine("Newly pending op " ^ show name)) new_op_names in
        let new_pending_ops = union (new_op_names, slice.pending_ops)    in
        slice << {op_map      = new_op_map,
                  pending_ops = new_pending_ops}
       | _ ->
         let new_op_map = ops_update (slice.op_map, name, Used Missing) in
         slice << {op_map = new_op_map}

op extend_execution_slice (s0 : Slice) : Slice =
 % let _ = writeLine("-----------------------------") in
 % let _ = writeLine("new round for execution slice") in
 let pending = s0.pending_ops           in
 let s1      = s0 << {pending_ops = []} in
 foldl (extend_execution_slice_for_op pending)
       s1
       pending

op execution_closure (slice : Slice) : Slice =
 case slice.pending_ops of
   | [] ->  slice
   | _ ->
     execution_closure (extend_execution_slice slice)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%W
%%%  Chase referenced types to fixpoint
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%W

op extend_typing_slice_for_type (pending : TypeNames) (slice : Slice, name : TypeName) : Slice =
 % let _ = writeLine("") in
 % let _ = writeLine("Extending typing for type " ^ show name) in
 let 
   def status info = if anyType? info.dfn then Undefined else Defined
 in
 case slice.oracular_type_status name of
   | Some status ->
     let new_type_map = types_update (slice.type_map, name, status) in
     slice << {type_map = new_type_map}
   | _ ->
     case findTheType (slice.ms_spec, name) of
       | Some info -> 
         % let _ = writeLine("Found type " ^ show name) in
         % let _ = writeLine(anyToString info) in
         let status = Used (status info) in
         let new_type_map      = types_update (slice.type_map, name, status) in
         let new_type_names    = foldl (fn (names, name) ->
                                          case apply (new_type_map, name) of
                                            | Some _ -> names
                                            | _ -> 
                                              if name in? pending then
                                                % it's already in the queue to be processed
                                                names
                                              else
                                                name |> names)
                                       []
                                       (typesInType info.dfn)
         in
         % let _ = app (fn name -> writeLine("Newly pending type " ^ show name)) new_type_names in
         let new_pending_types = union (new_type_names, slice.pending_types) in
         slice << {type_map      = new_type_map,
                   pending_types = new_pending_types}
       | _ ->
         let new_type_map = types_update (slice.type_map, name, Used Missing) in
         slice << {type_map = new_type_map}

op extend_typing_slice (s0 : Slice) : Slice =
 % let _ = writeLine("--------------------------") in
 % let _ = writeLine("new round for typing slice") in
 % let _ = app (fn name -> writeLine("Pending type " ^ show name)) s0.pending_types in
 let pending = s0.pending_types           in
 let s1      = s0 << {pending_types = []} in
 foldl (extend_typing_slice_for_type pending)
       s1
       pending

op typing_closure (s0 : Slice) : Slice =
 let root_types = types_in_slice s0 in
 let root_ops   = ops_in_slice   s0 in
 % let _ = app (fn name -> writeLine("root type: " ^ show name)) root_types in
 % let _ = app (fn name -> writeLine("root op: " ^ show name)) root_ops   in
 let directly_referenced_types = 
     foldl (fn (type_names, op_name) ->
              case findTheOp (s0.ms_spec, op_name) of
                | Some info ->
                  union (typesInTerm info.dfn, type_names)
                | _ ->
                  type_names)
           root_types
           root_ops
 in
 let s1 = s0 << {pending_types = directly_referenced_types} in
 let
   def aux s2 =
     case s2.pending_types of
       | [] ->  s2
       | _ ->
         aux (extend_typing_slice s2)
 in
 aux s1

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%W
%%%  Chase all referenced types and ops to fixpoint
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%W

op extend_logical_slice_for_type (pending_ops   : OpNames) 
                                 (pending_types : TypeNames)
                                 (slice : Slice, 
                                  name  : TypeName) 
 : Slice =
 % let _ = writeLine("") in
 % let _ = writeLine("Extending logical slice for type " ^ show name) in
 let 
   def status info = if anyType? info.dfn then Undefined else Defined
 in
 case slice.oracular_type_status name of
   | Some status ->
     let new_type_map = types_update (slice.type_map, name, status) in
     slice << {type_map = new_type_map}
   | _ ->
     case findTheType (slice.ms_spec, name) of
       | Some info ->
         let status       = Logical (status info) in
         let new_type_map = types_update (slice.type_map, name, status) in
         let new_op_names = foldl (fn (names, name) ->
                                     case apply (slice.op_map, name) of
                                       | Some _ -> names
                                       | _ -> 
                                         if name in? pending_ops then
                                           % it's already in the queue to be processed
                                           names
                                         else
                                           name |> names)
                                  []
                                  (opsInType info.dfn)
         in
         % let _ = app (fn name -> writeLine("Newly pending op " ^ show name)) new_op_names in
         let new_type_names    = foldl (fn (names, name) ->
                                          case apply (new_type_map, name) of
                                            | Some _ -> names
                                            | _ -> 
                                              if name in? pending_types then
                                                % it's already in the queue to be processed
                                                names
                                              else
                                                name |> names)
                                       []
                                       (typesInType info.dfn)
         in
         % let _ = app (fn name -> writeLine("Newly pending type " ^ show name)) new_type_names in
         let new_pending_ops   = union (new_op_names,   slice.pending_ops)         in
         let new_pending_types = union (new_type_names, slice.pending_types)       in
         slice << {type_map      = new_type_map,
                   pending_ops   = new_pending_ops,
                   pending_types = new_pending_types}
       | _ ->
         let new_type_map = types_update (slice.type_map, name, Logical Missing) in
         slice << {type_map = new_type_map}

op extend_logical_slice_for_op (pending_ops   : OpNames)
                               (pending_types : TypeNames)
                               (slice : Slice, 
                                name  : OpName) 
 : Slice =
 % let _ = writeLine("") in
 % let _ = writeLine("Extending logical slice for op " ^ show name) in
 let 
   def status info = if executable? info then Defined else Undefined
 in
 case slice.oracular_op_status name of
   | Some status ->
     let new_op_map = ops_update (slice.op_map, name, status) in
     slice << {op_map = new_op_map}
   | _ ->
     case findTheOp (slice.ms_spec, name) of
       | Some info ->
         let status       = Logical (status info) in
         let new_op_map   = ops_update (slice.op_map, name, status) in
         let new_op_names = foldl (fn (names, name) ->
                                     case apply (new_op_map, name) of
                                       | Some _ -> names
                                       | _ -> 
                                         if name in? pending_ops then
                                           % it's already in the queue to be processed
                                           names
                                         else
                                           name |> names)
                                  []
                                  (opsInTerm info.dfn)
           in
           % let _ = app (fn name -> writeLine("Newly pending op " ^ show name)) new_op_names in
           let new_type_names    = foldl (fn (names, name) ->
                                            case apply (slice.type_map, name) of
                                              | Some _ -> names
                                              | _ -> 
                                                if name in? pending_types then
                                                  % it's already in the queue to be processed
                                                  names
                                                else
                                                  name |> names)
                                         []
                                         (typesInTerm info.dfn)
           in
           % let _ = app (fn name -> writeLine("Newly pending type " ^ show name)) new_type_names in
           let new_pending_ops   = union (new_op_names,   slice.pending_ops)   in
           let new_pending_types = union (new_type_names, slice.pending_types) in
           slice << {op_map        = new_op_map,
                     pending_ops   = new_pending_ops,
                     pending_types = new_pending_types}
       | _ ->
         let new_op_map = ops_update (slice.op_map, name, Logical Missing) in
         slice << {op_map = new_op_map}

op extend_logical_slice (s0 : Slice) : Slice =
 % let _ = writeLine("---------------------------") in
 % let _ = writeLine("new round for logical slice") in
 let pending_types = s0.pending_types   in
 let pending_ops   = s0.pending_ops     in
 let s1 = s0 << {pending_ops = [],
                 pending_types = []}
 in
 let s2 = foldl (extend_logical_slice_for_type pending_ops pending_types)
                s1
                pending_types
 in
 let s3 = foldl (extend_logical_slice_for_op pending_ops pending_types)
                s2
                pending_ops
 in
 s3

op logical_closure (s0 : Slice) : Slice =
 let root_ops   = ops_in_slice   s0 in
 let root_types = types_in_slice s0 in
 let s1 = s0 << {pending_ops   = root_ops, 
                 pending_types = root_types}
 in
 let
   def aux s2 =
     case (s2.pending_types, s2.pending_ops) of
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
