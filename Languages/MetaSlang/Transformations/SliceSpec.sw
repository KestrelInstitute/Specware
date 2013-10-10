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
import /Library/Legacy/DataStructures/MergeSort   % to sort names when printing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%  Misc support
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%  ADT for op/type reachability
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type Cohorts          = List Cohort
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

type ResolvedRefs     = List ResolvedRef
type ResolvedRef      = | Op   ResolvedOpRef
                        | Type ResolvedTypeRef

type ResolvedOpRef    = {name            : OpName,   
                         cohort          : Cohort,
                         contextual_type : MSType, % how it is used (as opposed to how it is defined)
                         locations       : Locations,
                         status          : Status}

type ResolvedTypeRef  = {name       : TypeName, 
                         cohort     : Cohort,
                         locations  : Locations,
                         status     : Status}

op empty_resolved_refs   : ResolvedRefs   = []

type PendingRefs      = List PendingRef
type PendingRef       = | Op   PendingOpRef
                        | Type PendingTypeRef

type PendingOpRef     = {name            : OpName,   
                         cohort          : Cohort,
                         contextual_type : MSType, % how it is used (as opposed to how it is defined)
                         location        : Location}

type PendingTypeRef   = {name     : TypeName, 
                         cohort   : Cohort,
                         location : Location}


op pending.showName (pending : PendingRef) : String =
 case pending of
   | Op   oref -> show oref.name
   | Type tref -> show tref.name

type Slice = {ms_spec             : Spec, 
              lm_data             : LMData,
              oracular_ref_status : PendingRef * Slice -> Option Status,
              % code is simpler if pending and resolved refs are tracked separately
              % (as opposed to having a Pending/Resolved status)
              pending_refs        : PendingRefs,
              resolved_refs       : ResolvedRefs}

type RefNames = List RefName
type RefName  = | Op   OpName
                | Type TypeName

type Groups = List Group
type Group  = {cohort : Cohort,
               status : Status, 
               names  : Ref RefNames}

op describeGroup (group : Group) : () =
 case (! group.names) of
   | [] -> ()
   | names ->
     let (needed?, cohort) = case group.cohort of
                               | Interface      -> (true,  "These interface types and/or ops ")
                               | Implementation -> (true,  "These implementing types and/or ops ")
                               | Assertion      -> (false, "These types and/or ops in assertions ")
                               | Context        -> (false, "These types and/or ops in the relevant context ")
                               | Ignored        -> (false, "These ignored types and/or ops ")
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
     let type_names = foldl (fn (tnames, name) ->
                               case name of
                                 | Type tname -> (show tname) |> tnames
                                 | _ -> tnames)
                            []
                            names             
     in
     let op_names   = foldl (fn (onames, name) ->
                               case name of
                                 | Op oname -> (show oname) |> onames
                                 | _ -> onames)
                            []
                            names             
     in
     let type_names = sortGT (String.>) type_names in
     let op_names   = sortGT (String.>) op_names   in
     let _ = writeLine (warning ^ cohort ^ status) in
     let _ = case type_names of 
               | [] -> ()
               | _ ->
                 let _ = writeLine "" in
                 app (fn tname -> writeLine ("  type " ^ tname)) type_names 
     in
     let _ = case op_names of 
               | [] -> ()
               | _ ->
                 let _ = writeLine "" in
                 app (fn oname -> writeLine ("  op " ^ oname)) op_names 
     in
     let _ = writeLine "" in

     ()

op describeSlice (msg : String, slice : Slice) : () =
 let
   def pad (str, n) =
     let m = length str in
     if m < n then
       str ^ implode (repeat #\s (n - m))
     else
       str

   def partition_refs (groups : Groups, ref  : ResolvedRef) =
     case findLeftmost (fn (group : Group) ->
                          case ref of
                            | Op (oref : ResolvedOpRef) ->
                              group.cohort = oref.cohort && 
                              group.status = oref.status

                            | Type tref ->
                              group.cohort = tref.cohort && 
                              group.status = tref.status)

                       groups 
       of
       | Some group -> 
         let _  = (group.names := 
                     (! group.names) ++ 
                     [case ref of 
                        | Op   oref -> Op   oref.name
                        | Type tref -> Type tref.name])
         in
         groups
         
       | _ -> 
         %% Misc options will be added to end
         let (cohort, status, name) =
             case ref of 
               | Op   oref -> (oref.cohort, oref.status, Op   oref.name)
               | Type tref -> (tref.cohort, tref.status, Type tref.name)
         in
         let group : Group = {cohort = cohort,
                      status = status,
                      names  = Ref [name]}
         in
         groups ++ [group]

 in
 let cohorts     = [Interface, Implementation, Assertion, Context, Ignored]          in
 let status_list = [Primitive, API, Handwritten, Macro, Defined, Undefined, Missing] in
 let groups      = foldl (fn (groups, cohort) -> 
                            foldl (fn (groups, status) ->
                                     let group = {cohort     = cohort,
                                                  status     = status, 
                                                  names = Ref []}
                                     in
                                     groups <| group)
                                  groups
                                  status_list)
                         []
                         cohorts
 in
 let groups = foldl partition_refs groups slice.resolved_refs in

 let _ = writeLine ("") in
 let _ = writeLine ("Slice: " ^ msg) in
 let _ = writeLine ("") in

 let _ = case slice.pending_refs of
           | [] -> ()
           | pendings ->
             let _ = writeLine "--------------------" in
             let _ = app (fn pending -> writeLine ("pending type: " ^ showName pending)) pendings in
             let _ = writeLine "--------------------" in
             ()
 in

 let _ = app describeGroup groups in
 ()
 
op resolve_ref (slice   : Slice, 
                pending : PendingRef,
                status  : Status)
 : ResolvedRefs =
 let resolved_refs = slice.resolved_refs in
 case pending of
   | Op oref ->
     (case findLeftmost (fn resolved -> 
                           case resolved of 
                             | Op resolved -> resolved.name = oref.name
                             | _ -> false)
                        resolved_refs 
       of
        | Some _ -> resolved_refs  % don't update if name already has a value
        | _ -> 
          let resolved_ref =
              Op {name            = oref.name, 
                  cohort          = oref.cohort,
                  contextual_type = oref.contextual_type, 
                  locations       = [oref.location],
                  status          = status} 
          in
          resolved_ref |> resolved_refs)

   | Type tref ->
     case findLeftmost (fn resolved -> 
                          case resolved of 
                            | Type resolved -> resolved.name = tref.name
                            | _ -> false)
                       resolved_refs 
      of
       | Some _ -> resolved_refs  % don't update if name already has a value
       | _ -> 
         let resolved_ref =
             Type {name      = tref.name, 
                   cohort    = tref.cohort,
                   locations = [tref.location],
                   status    = status} 
         in
         resolved_ref |> resolved_refs

(*
op ops_in_slice (slice : Slice) : OpNames =
 map (fn resolved -> resolved.name) slice.resolved_op_refs

op types_in_slice (slice : Slice) : TypeNames =
 map (fn resolved -> resolved.name) slice.resolved_type_refs
*)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%  Chase referenced types and ops to fixpoint
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op extend_cohort_for_ref (cohort       : Cohort)
                         (pending_refs : PendingRefs)
                         (op_status    : OpInfo   -> Status)
                         (type_status  : TypeInfo -> Status)
                         (slice        : Slice, 
                          pending_ref  : PendingRef)
 : Slice =
 let
   def matches_op_ref pending_op_ref (resolved_ref : ResolvedRef) =
     case resolved_ref of
       | Op resolved_op_ref ->
         resolved_op_ref.cohort = pending_op_ref.cohort &&
         resolved_op_ref.name   = pending_op_ref.name
       | _ -> false

   def matches_type_ref (pending_type_ref : PendingTypeRef) (resolved : ResolvedRef) =
     case resolved of
       | Type resolved_type_ref ->
         resolved_type_ref.cohort = pending_type_ref.cohort &&
         resolved_type_ref.name   = pending_type_ref.name
       | _ -> false


   def add_pending_ref resolved_refs (pendings, pending) =
     case pending of
       | Op (pending_op_ref : PendingOpRef) ->
         (case findLeftmost (matches_op_ref pending_op_ref) resolved_refs of
            | Some _ -> pendings
            | _ -> 
              if pending in? pendings then
                % it's already in the queue to be processed
                pendings
              else
                pending |> pendings)
       | Type (pending_type_ref : PendingTypeRef) ->
         (case findLeftmost (matches_type_ref pending_type_ref) resolved_refs of
            | Some _ -> pendings
            | _ -> 
              if pending in? pendings then
                % it's already in the queue to be processed
                pendings
              else
                pending |> pendings)
 in
 case slice.oracular_ref_status (pending_ref, slice) of
   | Some status ->
     let new_resolved_refs = resolve_ref (slice, pending_ref, status) in
     slice << {resolved_refs = new_resolved_refs}
   | _ ->
     case pending_ref of
       | Op oref ->
         (case findTheOp (slice.ms_spec, oref.name) of
            | Some info ->
              let status            = op_status info                               in
              let new_resolved_refs = resolve_ref (slice, pending_ref, status)     in
              let new_pending_refs  = foldl (add_pending_ref new_resolved_refs)
                                            [] 
                                            (pendingRefsInTerm (info.dfn, cohort)) 
              in
              let new_pending_refs  = union (new_pending_refs, slice.pending_refs) in
              slice << {resolved_refs = new_resolved_refs,
                        pending_refs  = new_pending_refs}
            | _ ->
              let new_resolved_refs = resolve_ref (slice, pending_ref, Missing) in
              slice << {resolved_refs = new_resolved_refs})

       | Type tref ->
         (case findTheType (slice.ms_spec, tref.name) of
            | Some info ->
              let status            = type_status info                              in
              let new_resolved_refs = resolve_ref (slice, pending_ref, status)      in
              let new_pending_refs  = foldl (add_pending_ref new_resolved_refs)
                                            [] 
                                            (pendingRefsInType (info.dfn, cohort)) 
              in
              let new_pending_refs   = union (new_pending_refs, slice.pending_refs) in
              slice << {resolved_refs = new_resolved_refs,
                        pending_refs  = new_pending_refs}
            | _ ->
              let new_resolved_refs = resolve_ref (slice, pending_ref, Missing) in
              slice << {resolved_refs = new_resolved_refs})

op pendingRefsInTerm (term : MSTerm, cohort : Cohort) : PendingRefs =
 %% TODO: get real locations
 (map (fn name -> 
         Op {name            = name, 
             cohort          = cohort,
             contextual_type = Any noPos, 
             location        = Unknown})
      (opsInTerm term))
 ++
 (map (fn name -> 
         Type {name     = name, 
               cohort   = cohort,
               location = Unknown})
      (typesInTerm term))

op pendingRefsInType (typ : MSType, cohort : Cohort) : PendingRefs =
 %% TODO: get real locations
 let op_refs =
     case cohort of
       | Implementation -> []
       | _ ->
         map (fn name -> 
                Op {name            = name, 
                    cohort          = cohort,
                    contextual_type = Any noPos, 
                    location        = Unknown})
             (opsInType typ)
 in
 let type_refs = 
     map (fn name -> 
            Type {name     = name, 
                  cohort          = cohort,
                  location = Unknown})
         (typesInType typ)
 in
 op_refs ++ type_refs

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op extend_cohort (cohort : Cohort) (s0 : Slice) : Slice =
 let pending_refs = s0.pending_refs           in
 let s1           = s0 << {pending_refs = []} in
 let 
   def op_status   info = if executable? info     then Defined   else Undefined
   def type_status info = if anyType?    info.dfn then Undefined else Defined
 in
 foldl (extend_cohort_for_ref cohort pending_refs op_status type_status)
       s1
       pending_refs

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op cohort_closure (cohort : Cohort) (slice : Slice) : Slice =
 let
   def aux slice =
     case slice.pending_refs of
       | [] ->  
         slice
       | _ ->
         aux (extend_cohort cohort slice)
 in
 aux slice

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op implementation_closure (slice : Slice) : Slice = cohort_closure Implementation slice
op assertion_closure      (slice : Slice) : Slice = cohort_closure Assertion      slice
op context_closure        (slice : Slice) : Slice = slice

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op executionSlice (ms_spec    : Spec,
                   get_lms    : Spec -> LanguageMorphisms,
                   oracle     : PendingRef * Slice -> Option Status,
                   root_ops   : OpNames, 
                   root_types : TypeNames) 
 : Slice =
 let lms          = get_lms     ms_spec in
 let lm_data      = make_LMData lms     in
 let pending_refs = (map (fn name ->
                            Op {name            = name, 
                                cohort          = Interface,
                                contextual_type = Any noPos, 
                                location        = Root})
                         root_ops)
                    ++
                    (map (fn name -> 
                            Type {name     = name, 
                                  cohort   = Interface,
                                  location = Root})
                         root_types)
 in
 let s0 = {ms_spec             = ms_spec,
           lm_data             = lm_data,
           oracular_ref_status = oracle,
           pending_refs        = pending_refs,
           resolved_refs       = empty_resolved_refs}
 in
 let s1 = implementation_closure s0 in
 let s2 = assertion_closure      s1 in
 let s3 = context_closure        s2 in
 s3

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

end-spec
