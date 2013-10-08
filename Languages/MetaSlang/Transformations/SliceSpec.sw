SliceSpec qualifying spec 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Old version that is deprecated
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

import OldSlice  % Deprecated

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% New Slicing Code
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

type Cohort           = | Interface      % the desired interface or API
                        | Implementation % used to implement the interface
                        | Assertion      % used in assertions, could define runtime asserts
                        | Context        % used in relevant context, could define monitors
                        | Ignored        

type Status           = | Primitive 
                        | API 
                        | Handwritten 
                        | Macro 
                        | Defined 
                        | Undefined 
                        | Missing 
                        | Misc String

type TheoremName      = PropertyName

type Locations        = List Location
type Location         = | Root 
                        | Op      {name : OpName,      pos: Position}
                        | Type    {name : TypeName,    pos: Position}
                        | Theorem {name : TheoremName, pos: Position}
                        | Unknown

type ResolvedOpRefs   = List ResolvedOpRef
type ResolvedOpRef    = {name            : OpName,   
                         cohort          : Cohort,
                         contextual_type : MSType, % how it is used (as opposed to how it is defined)
                         locations       : Locations,
                         status          : Status}

type ResolvedTypeRefs = List ResolvedTypeRef
type ResolvedTypeRef  = {name       : TypeName, 
                         cohort     : Cohort,
                         locations  : Locations,
                         status     : Status}

type PendingOpRefs    = List PendingOpRef
type PendingOpRef     = {name            : OpName,   
                         cohort          : Cohort,
                         contextual_type : MSType, % how it is used (as opposed to how it is defined)
                         location        : Location}

type PendingTypeRefs  = List PendingTypeRef
type PendingTypeRef   = {name     : TypeName, 
                         cohort   : Cohort,
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
type Group  = {cohort     : Cohort,
               status     : Status, 
               type_names : Ref TypeNames,
               op_names   : Ref OpNames}

op describeGroup (group : Group) : () =
 case (! group.type_names, ! group.op_names) of
   | ([], []) -> ()
   | (type_names, op_names) ->
     let (needed?, cohort) = case group.cohort of
                               | Interface      -> (true,  "These interface types and ops ")
                               | Implementation -> (true,  "These implementing types and ops ")
                               | Assertion      -> (false, "These types and ops in assertions ")
                               | Context        -> (false, "These types and ops in the relevant context ")
                               | Ignored        -> (false, "These ignored types and ops ")
     in
     let (warning, status) = case group.status of
                               | Primitive   -> ("", "translate to primitive syntax: ")
                               | API         -> ("", "translate to an API: ")
                               | Handwritten -> ("", "translate to handwritten code: ")
                               | Macro       -> ("", "translate to macros: ")
                               | Defined     -> ("", "are defined: ")
                               | Undefined   -> (if needed? then "WARNING: " else "", "are undefined: ")
                               | Missing     -> (if needed? then "WARNING: " else "", "are missing: ")
                               | Misc msg    -> ("", msg)
     in
     let heading = warning ^ cohort ^ status in

     let _ = writeLine heading                                                           in
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
     case findLeftmost (fn group ->
                          group.cohort = type_ref.cohort && 
                          group.status = type_ref.status) 
                       groups 
       of
       | Some group -> 
         let _ = (group.type_names := (! group.type_names) ++ [type_ref.name]) in
         groups
         
       | _ -> 
         %% Misc options will be added to end
         let group = {cohort     = type_ref.cohort,
                      status     = type_ref.status, 
                      type_names = Ref [type_ref.name], 
                      op_names   = Ref []} in
         groups ++ [group]

   def partition_op_refs (groups, op_ref) =
     case findLeftmost (fn group ->
                          group.cohort = op_ref.cohort && 
                          group.status = op_ref.status) 
                       groups 
       of
       | Some group -> 
         let _ = (group.op_names := (! group.op_names) ++ [op_ref.name]) in
         groups
         
       | _ -> 
         %% Misc options will be added to end
         let group = {cohort     = op_ref.cohort,
                      status     = op_ref.status, 
                      type_names = Ref [], 
                      op_names   = Ref [op_ref.name]} in
         groups ++ [group]

 in
 let cohorts     = [Interface, Implementation, Assertion, Context, Ignored]          in
 let status_list = [Primitive, API, Handwritten, Macro, Defined, Undefined, Missing] in
 let groups      = foldl (fn (groups, cohort) -> 
                            foldl (fn (groups, status) ->
                                     groups <| {cohort     = cohort,
                                                status     = status, 
                                                type_names = Ref [], 
                                                op_names   = Ref []})
                                  groups
                                  status_list)
                         []
                         cohorts
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
                            cohort          = pending.cohort,
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
                              cohort    = pending.cohort,
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
       | Some info ->
         let cohort               = Implementation in
         let status               = status info    in
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
                                          (pendingOpRefsInTerm (info.dfn, cohort))
        in
        let new_pending_op_refs   = union (new_pending_op_refs, slice.pending_op_refs) in
        slice << {resolved_op_refs = new_resolved_op_refs,
                  pending_op_refs  = new_pending_op_refs}
       | _ ->
         let new_resolved_op_refs = resolve_op_ref (slice, pending_op_ref, Missing) in
         slice << {resolved_op_refs = new_resolved_op_refs}

op extend_execution_slice (s0 : Slice) : Slice =
 let pending_op_refs = s0.pending_op_refs           in
 let s1          = s0 << {pending_op_refs = []} in
 foldl (extend_execution_slice_for_pending_op_ref pending_op_refs)
       s1
       pending_op_refs

op implementation_closure (slice : Slice) : Slice =
 case slice.pending_op_refs of
   | [] ->  
     typing_closure slice
   | _ ->
     implementation_closure (extend_execution_slice slice)

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
         let cohort                 = Implementation in
         let status                 = status info    in
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
                                            (pendingTypeRefsInType (info.dfn, cohort))
         in
         let new_pending_type_refs  = union (new_pending_type_refs, slice.pending_type_refs) in
         slice << {resolved_type_refs = new_resolved_type_refs,
                   pending_type_refs  = new_pending_type_refs}
       | _ ->
         let new_resolved_type_refs = resolve_type_ref (slice, pending_type_ref, Missing) in
         slice << {resolved_type_refs = new_resolved_type_refs}

op extend_typing_slice (s0 : Slice) : Slice =
 let pending = s0.pending_type_refs           in
 let s1      = s0 << {pending_type_refs = []} in
 foldl (extend_typing_slice_for_pending_type_ref pending)
       s1
       pending

op pendingOpRefsInTerm (term : MSTerm, cohort : Cohort) : PendingOpRefs =
 %% TODO: get real locations
 map (fn name -> 
        {name            = name, 
         cohort          = cohort,
         contextual_type = Any noPos, 
         location        = Unknown})
     (opsInTerm term)

op pendingOpRefsInType (typ : MSType, cohort : Cohort) : PendingOpRefs =
 %% TODO: get real locations
 map (fn name -> 
        {name            = name, 
         cohort          = cohort,
         contextual_type = Any noPos, 
         location        = Unknown})
     (opsInType typ)

op pendingTypeRefsInTerm (term : MSTerm, cohort : Cohort) : PendingTypeRefs =
 %% TODO: get real locations
 map (fn name -> 
        {name     = name, 
         cohort          = cohort,
         location = Unknown})
     (typesInTerm term)

op pendingTypeRefsInType (typ : MSType, cohort : Cohort) : PendingTypeRefs =
 %% TODO: get real locations
 map (fn name -> 
        {name     = name, 
         cohort          = cohort,
         location = Unknown})
     (typesInType typ)

op typing_closure (s0 : Slice) : Slice =
 let root_ops          = ops_in_slice   s0 in
 let root_types        = types_in_slice s0 in
 let pending_type_refs = map (fn name -> {name = name, cohort = Implementation, location = Root}) root_types in
 let pending_type_refs = 
     foldl (fn (pending_type_refs, op_name) ->
              case findTheOp (s0.ms_spec, op_name) of
                | Some info ->
                  union (pendingTypeRefsInTerm (info.dfn, Implementation), 
                         pending_type_refs)
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
         let cohort                 = Assertion   in
         let status                 = status info in
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
                                        (pendingOpRefsInType (info.dfn, cohort))
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
                                        (pendingTypeRefsInType (info.dfn, cohort))
         in
         let new_pending_op_refs    = union (new_pending_op_refs,   slice.pending_op_refs)   in
         let new_pending_type_refs  = union (new_pending_type_refs, slice.pending_type_refs) in
         slice << {resolved_type_refs = new_resolved_type_refs,
                   pending_op_refs    = new_pending_op_refs,
                   pending_type_refs  = new_pending_type_refs}
       | _ ->
         let new_resolved_type_refs = resolve_type_ref (slice, pending_type_ref, Missing) in
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
         let cohort                = Assertion   in
         let status                = status info in
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
                                          (pendingOpRefsInTerm (info.dfn, cohort))
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
                                           (pendingTypeRefsInTerm (info.dfn, cohort))
         in
         let new_pending_op_refs   = union (new_pending_op_refs,   slice.pending_op_refs)   in
         let new_pending_type_refs = union (new_pending_type_refs, slice.pending_type_refs) in
         slice << {resolved_op_refs  = new_resolved_op_refs,
                   pending_op_refs   = new_pending_op_refs,
                   pending_type_refs = new_pending_type_refs}
       | _ ->
         let new_resolved_op_refs = resolve_op_ref (slice, pending_op_ref, Missing) in
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

op assertion_closure (s0 : Slice) : Slice =
 let cohort        = Assertion         in
 let root_ops      = ops_in_slice   s0 in
 let root_types    = types_in_slice s0 in
 let pending_op_refs   = map (fn name ->
                                {name            = name, 
                                 cohort          = cohort,
                                 contextual_type = Any noPos, 
                                 location        = Root})  
                             root_ops
 in
 let pending_type_refs = map (fn name -> 
                                {name     = name, 
                                 cohort   = cohort,
                                 location = Root}) 
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

op context_closure (slice : Slice) : Slice =
 slice

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%W

op completeSlice (s0 : Slice) : Slice =
 %% s0 begins with pending ops and types
 let s1 = implementation_closure s0 in
 let s2 = assertion_closure      s1 in
 let s3 = context_closure        s2 in
 s3

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%W

end-spec
