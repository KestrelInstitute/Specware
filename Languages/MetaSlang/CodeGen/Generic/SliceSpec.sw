(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

SliceSpec qualifying spec 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% New Slicing Code
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

import /Languages/MetaSlang/Specs/Environment

import /Languages/MetaSlang/CodeGen/Generic/LanguageMorphism

import /Languages/MetaSlang/CodeGen/Stateful/Setf

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

op showCohort (cohort : Cohort) : String =
 case cohort of
   | Interface      -> "Interface"
   | Implementation -> "Implementation"
   | Assertion      -> "Assertion"
   | Context        -> "Context"
   | Ignored        -> "Ignored"

type Status           = | Primitive 
                        | API 
                        | Handwritten 
                        | Macro 
                        | Defined 
                        | Undefined 
                        | Missing 
                        | Misc String

op showStatus (status : Status) : String =
 case status of
   | Primitive   -> "primitive"
   | API         -> "API"
   | Handwritten -> "handwritten"
   | Macro       -> "macro"
   | Defined     -> "defined"
   | Undefined   -> "undefined"
   | Missing     -> "missing"
   | Misc msg    -> msg

type TheoremNames     = List TheoremName
type TheoremName      = PropertyName

type Locations        = List Location
type Location         = | Root 
                        | Op      {name : OpName,      pos: Position}
                        | Type    {name : TypeName,    pos: Position}
                        | Theorem {name : TheoremName, pos: Position}
                        | Unknown

op showPos (pos : Position) : String = 
 let
   def printLCB (line,column,byte) = show line ^ "." ^ show column 
 in
 case pos of 
   | Internal "no position"       -> " at unknown location"
   | Internal x                   -> " " ^ x
   | String   (s,    left, right) -> " in some string : " ^ (printLCB left) ^ "-" ^ (printLCB right)
   | File     (file, left, right) -> " from " ^ file ^ " at " ^ (printLCB left) ^ "-" ^ (printLCB right)
   | _ -> " at " ^ print pos

op showLocation (location : Location, pad_length : Nat) : String = 
 case location of
   | Root      -> "in  some root"
   | Op      x -> "in  op "      ^ pad (show x.name, pad_length) ^ showPos x.pos 
   | Type    x -> "in  type "    ^ pad (show x.name, pad_length) ^ showPos x.pos 
   | Theorem x -> "in  theorem " ^ show x.name ^ showPos x.pos 
   | Unknown   -> "at  unknown location"

op terseShowLocation (location : Location) : String = 
 case location of
   | Root      -> "a root"
   | Op      x -> show x.name
   | Type    x -> show x.name
   | Theorem x -> show x.name
   | Unknown   -> "unknown"

type ResolvedRefs     = List ResolvedRef
type ResolvedRef      = | Op      ResolvedOpRef
                        | Type    ResolvedTypeRef
                        | Theorem ResolvedTheorem % e.g. setf axioms

type ResolvedOpRef    = {name            : OpName,   
                         cohort          : Cohort,
                         contextual_type : MSType, % how it is used (as opposed to how it is defined)
                         locations       : Locations,
                         status          : Status}

type ResolvedTypeRef  = {name       : TypeName, 
                         cohort     : Cohort,
                         locations  : Locations,
                         status     : Status}

type ResolvedTheorem  = {name       : TheoremName, 
                         cohort     : Cohort,
                         element    : SpecElement,
                         status     : Status}

op empty_resolved_refs   : ResolvedRefs   = []

type PendingRefs      = List PendingRef
type PendingRef       = | Op      PendingOpRef
                        | Type    PendingTypeRef
                        | Theorem PendingTheoremRef

type PendingOpRef     = {name            : OpName,   
                         cohort          : Cohort,
                         contextual_type : MSType, % how it is used (as opposed to how it is defined)
                         location        : Location}

type PendingTypeRef   = {name     : TypeName, 
                         cohort   : Cohort,
                         location : Location}

type PendingTheoremRef = {name    : TheoremName, 
                          cohort  : Cohort,
                          element : SpecElement,
                          status  : Status}

type ParentName       = | Op      String
                        | Type    String
                        | Theorem String

op pending.showName (pending : PendingRef) : String =
 case pending of
   | Op      oref -> show oref.name
   | Type    tref -> show tref.name
   | Theorem tref -> show tref.name

type Slice = {ms_spec             : Spec, 
              lm_data             : LMData,
              oracular_ref_status : PendingRef * Slice -> Option Status,
              % code is simpler if pending and resolved refs are tracked separately
              % (as opposed to having a Pending/Resolved status)
              pending_refs        : PendingRefs,
              resolved_refs       : ResolvedRefs}

type Groups = List Group
type Group  = {cohort : Cohort,
               status : Status, 
               refs   : Ref ResolvedRefs}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op opsInSlice (slice : Slice) : OpNames =
 foldl (fn (names, ref) ->
          case ref of
            | Op oref -> oref.name |> names
            | _ -> names)
       []
       slice.resolved_refs

op opsInImplementation (slice : Slice) : OpNames =
 foldl (fn (names, ref) ->
          case ref of
            | Op oref -> 
              (case oref.cohort of
                 | Interface      -> oref.name |> names
                 | Implementation -> oref.name |> names
                   % Assertion, Context,Ignored        
                 | _ -> names)
            | _ -> names)
       []
       slice.resolved_refs

op opsInAssertions (slice : Slice) : OpNames =
 foldl (fn (names, ref) ->
          case ref of
            | Op oref -> 
              (case oref.cohort of
                 | Assertion      -> oref.name |> names
                   % Interface, Implementation, Context,Ignored        
                 | _ -> names)
            | _ -> names)
       []
       slice.resolved_refs

op opsInGroup (group : Group) : OpNames =
 foldl (fn (names, ref) ->
          case ref of
            | Op oref -> oref.name |> names
            | _ -> names)
       []
       (! group.refs)


op typesInSlice (slice : Slice) : TypeNames =
 foldl (fn (names, ref) ->
          case ref of
            | Type tref -> tref.name |> names
            | _ -> names)
       []
       slice.resolved_refs

op typesInImplementation (slice : Slice) : TypeNames =
 foldl (fn (names, ref) ->
          case ref of
            | Type tref -> 
              (case tref.cohort of
                 | Interface      -> tref.name |> names
                 | Implementation -> tref.name |> names
                   % Assertion, Context,Ignored        
                 | _ -> names)
            | _ -> names)
       []
       slice.resolved_refs

op typesInAssertions (slice : Slice) : TypeNames =
 foldl (fn (names, ref) ->
          case ref of
            | Type tref -> 
              (case tref.cohort of
                 | Assertion      -> tref.name |> names
                   % Interface, Implementation, Context,Ignored        
                 | _ -> names)
            | _ -> names)
       []
       slice.resolved_refs

op theoremInSlice (slice : Slice) : TheoremNames =
 foldl (fn (names, ref) ->
          case ref of
            | Theorem tref -> tref.name |> names
            | _ -> names)
       []
       slice.resolved_refs

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op pad (s : String, n : Nat)  : String =
  let len = length s in
  if len < n then
    let spaces = implode (repeat #\s n) in
    s ^ subFromTo (spaces, 0, n - len)
  else
    s

op showPendingRef (ref : PendingRef) (warning? : Bool) : String =
 let
   def show_theorem_name tref =
     let Property (kind, name, _, _, _) = tref.element in
     let kind_str =
         case kind of
           | Axiom      -> "axiom "
           | Theorem    -> "theorem "
           | Conjecture -> "conjecture "
           | _          -> "unrecognized "
         in
         kind_str ^ show tref.name
 in
 case ref of
   | Op      oref -> " op "   ^ show oref.name
   | Type    tref -> " type " ^ show tref.name
   | Theorem tref -> show_theorem_name tref

op showUsesOfType (tref : ResolvedTypeRef, slice : Slice, group : Group) : String =
 let
   def mentions? (typ, type_name) =
     foldTypesInType (fn (yes?, t1) -> 
                        yes? ||
                        (case t1 of
                           | Base (name, _, _) -> name = type_name
                           | _ -> false))
                     false
                     typ
 in
 "\n" ^
 foldl (fn (s, loc) ->
          s ^ 
          (case loc of
             | Op x -> 
               (case findTheOp (slice.ms_spec, x.name) of
                  | Some info ->
                    let (s1, _) =
                        foldSubTerms (fn (tm, (s, positions_seen)) ->
                                        case tm of
                                          | Fun (Nat n, typ, pos) ->
                                            if mentions? (typ, tref.name) && pos nin? positions_seen then
                                              let new = "\n " ^ pad (show n, 16) ^ " : " ^ printType typ ^ showPos pos ^ 
                                                        "\n     in " ^ terseShowLocation loc ^
                                                        "\n" 
                                              in
                                              (s ^ new, pos |> positions_seen)
                                            else
                                              (s, positions_seen)
                                      | Apply (t1 as Fun (x, typ, pos), _, _) ->
                                        if mentions? (typ, tref.name) && pos nin? positions_seen then
                                          let new = "\n   " ^ printTerm t1 ^ " : " ^ printType typ ^ 
                                                    "\n     in  " ^ printTerm tm ^
                                                    "\n     in " ^ terseShowLocation loc ^
                                                    "\n    " ^ showPos pos ^ 
                                                    "\n" 
                                          in
                                          (s ^ new, pos |> positions_seen)
                                        else
                                          (s, positions_seen)
                                      | _ -> 
                                        (s, positions_seen))
                                 ("", [])
                                 info.dfn
                    in
                    s1
                  | _ -> "\nERROR: Internal confusion: type mentioned by missing op: " ^ show x.name ^ "\n")
             | _ ->
               "\n     " ^ showLocation (loc, 20)))
       ""
       tref.locations

op showResolvedRef (ref        : ResolvedRef,
                    warning?   : Bool,
                    slice      : Slice,
                    group      : Group,
                    pad_length : Nat)
 : String =
 let
   def show_theorem_name tref =
     let Property (kind, name, _, _, _) = tref.element in
     let kind_str =
         case kind of
           | Axiom      -> " axiom "
           | Theorem    -> " theorem "
           | Conjecture -> " conjecture "
           | _          -> " unrecognized "
         in
         kind_str ^ show tref.name
 in
 if warning? then
   case ref of
     | Op   oref -> 
       " op "   ^   pad (show oref.name, pad_length) ^ " " ^ (showLocation (head oref.locations, pad_length)) ^
       (foldl (fn (s, loc) -> 
                 s ^ "\n    " ^ pad ("", pad_length) ^ " " ^ showLocation (loc, pad_length))
              "" 
              (tail oref.locations))

     | Type tref -> " type " ^ pad (show tref.name, pad_length) ^ "\t" ^ 
                     showUsesOfType (tref, slice, group)

     | Theorem tref -> show_theorem_name tref
 else
   case ref of
     | Op      oref -> " op "   ^ show oref.name
     | Type    tref -> " type " ^ show tref.name
     | Theorem tref -> show_theorem_name tref

op describeGroup (slice : Slice) (group : Group) : () =
 case (! group.refs) of
   | [] -> ()
   | refs ->
     let (needed?, cohort_msg)  = 
         case group.cohort of
           | Interface      -> (true,  "These interface types and/or ops ")
           | Implementation -> (true,  "These implementing types and/or ops ")
           | Assertion      -> (false, "These types and/or ops in assertions ")
           | Context        -> (false, "These types and/or ops in the relevant context ")
           | Ignored        -> (false, "These ignored types and/or ops ")
     in
     let (warning?, status_msg, pad_length) = 
         case group.status of
           | Primitive   -> (false, "translate to primitive syntax: ", 16)
           | API         -> (false, "translate to an API: ",           16)
           | Handwritten -> (false, "translate to handwritten code: ", 16)
           | Macro       -> (false, "translate to macros: ",           16)
           | Defined     -> (false, "are defined: ",                   16)
           | Undefined   -> (true,  "are undefined: ",                 32) % tend to be longer names
           | Missing     -> (true,  "are missing: ",                   32) % tend to be longer names
           | Misc msg    -> (false, msg,                               32)
     in
     let tref_lines = foldl (fn (lines, ref) ->
                               case ref of
                                 | Type tref -> 
                                   showResolvedRef (ref, warning?, slice, group, pad_length) |> lines
                                 | _ -> 
                                   lines)
                            []
                            refs
     in
     let oref_lines = foldl (fn (lines, ref) ->
                               case ref of
                                 | Op oref -> 
                                   showResolvedRef (ref, warning?, slice, group, pad_length) |> lines
                                 | _ -> 
                                   lines)
                            []
                            refs
     in
     let thref_lines = foldl (fn (lines, ref) ->
                                case ref of
                                  | Theorem tref -> 
                                    showResolvedRef (ref, warning?, slice, group, pad_length) |> lines
                                  | _ -> 
                                    lines)
                             []
                             refs
     in
     let tref_lines  = sortGT (String.>) tref_lines in
     let oref_lines  = sortGT (String.>) oref_lines in
     let thref_lines = sortGT (String.>) thref_lines in
     let _ = writeLine ((if warning? then "WARNING: " else "") ^ cohort_msg ^ status_msg ^ "\n") in
     let _ = case tref_lines of 
               | [] -> ()
               | _ ->
                 app writeLine tref_lines
     in
     let _ = case oref_lines of 
               | [] -> ()
               | _ ->
                 let _ = writeLine "" in
                 app writeLine oref_lines
     in
     let _ = case thref_lines of 
               | [] -> ()
               | _ ->
                 let _ = writeLine "" in
                 app writeLine thref_lines
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

   def partition_refs (groups : Groups, ref : ResolvedRef) : Groups =
     case findLeftmost (fn (group : Group) ->
                          case ref of
                            | Op (oref : ResolvedOpRef) ->
                              group.cohort = oref.cohort && 
                              group.status = oref.status

                            | Type tref ->
                              group.cohort = tref.cohort && 
                              group.status = tref.status

                            | Theorem tref ->
                              group.cohort = tref.cohort && 
                              group.status = tref.status

                            | _ ->
                              false)
                       groups 
       of
       | Some group -> 
         let _  = (group.refs := (! group.refs) ++ [ref]) in
         groups
         
       | _ -> 
         %% Misc options will be added to end
         let (cohort, status) =
             case ref of 
               | Op      oref -> (oref.cohort, oref.status)
               | Type    tref -> (tref.cohort, tref.status)
               | Theorem aref -> (aref.cohort, aref.status)
         in
         let group : Group = {cohort = cohort,
                              status = status,
                              refs   = Ref [ref]}
         in
         groups ++ [group]

 in
 let cohorts     = [Interface, Implementation, Assertion, Context, Ignored]          in
 let status_list = [Defined, Handwritten, API, Macro, Primitive, Undefined, Missing] in
 let groups      = foldl (fn (groups, cohort) -> 
                            foldl (fn (groups, status) ->
                                     let group = {cohort = cohort,
                                                  status = status, 
                                                  refs   = Ref []}
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

 let _ = case slice.resolved_refs of
           | [] -> writeLine("No types or ops in slice.")
           | _ -> app (describeGroup slice) groups 
 in
 ()

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op resolve_ref (slice   : Slice, 
                pending : PendingRef,
                status  : Status)
 : ResolvedRefs =
 let
   def names_match? (Qualified (xq, xid), Qualified (yq, yid)) =
     %% could have Nat32 and Nat.Nat32 -- sigh
     xid = yid &&
     (xq = yq || xq = UnQualified || yq = UnQualified)

   def cohort_number cohort =
     case cohort of
       | Interface      -> 1
       | Implementation -> 2
       | Assertion      -> 3
       | Context        -> 4

   def earlier_cohort? (c1, c2) =
     (cohort_number c1) < (cohort_number c2)
 in
 let resolved_refs = slice.resolved_refs in
(*
 let s = foldl (fn (s, ref) -> s ^ " " ^ 
                  (show (length (case ref of
                                   | Op      oref -> oref.locations
                                   | Type    tref -> tref.locations
                                   | Theorem tref -> tref.locations
                                   | _ -> []))))
               ""
               resolved_refs
 in
*)
 case pending of
   | Op oref ->
     (case splitAtLeftmost (fn resolved -> 
                              case resolved of 
                                | Op resolved -> 
                                  resolved.name = oref.name && 
                                  equalType? (resolved.contextual_type, oref.contextual_type) &&
                                  resolved.status = status
                                | _ -> false)
                           resolved_refs 
       of
        | Some (x, Op old, y) -> 
          if oref.location in? old.locations then
            resolved_refs
          else
            let cohort = 
                if earlier_cohort? (oref.cohort, old.cohort) then
                  oref.cohort
                else
                  old.cohort
            in
            let resolved_ref =
                Op {name            = oref.name, 
                    cohort          = cohort,
                    contextual_type = oref.contextual_type,
                    locations       = old.locations <| oref.location,
                    status          = status} 
            in
            x ++ [resolved_ref] ++ y

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
     (case splitAtLeftmost (fn resolved -> 
                              case resolved of 
                                | Type resolved -> 
                                  resolved.name = tref.name &&
                                  resolved.status = status
                                | _ -> false)
                           resolved_refs 
       of
        | Some (x, Type old, y) ->
          if tref.location in? old.locations then
            resolved_refs
          else
            let cohort = 
                if earlier_cohort? (tref.cohort, old.cohort) then
                  tref.cohort
                else
                  old.cohort
            in
            let resolved_ref =
                Type {name      = tref.name, 
                      cohort    = cohort,
                      locations = old.locations <| tref.location,
                      status    = status} 
            in
            x ++ [resolved_ref] ++ y
        | _ -> 
          let resolved_ref =
              Type {name      = tref.name, 
                    cohort    = tref.cohort,
                    locations = [tref.location],
                    status    = status} 
          in
          resolved_ref |> resolved_refs)

   | Theorem (tref : PendingTheoremRef) ->
     let resolved_ref = Theorem {name    = tref.name,
                                 cohort  = tref.cohort,
                                 element = tref.element,
                                 status  = status} 
     in
     resolved_ref |> resolved_refs

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
 %% let _ = writeLine(anyToString cohort ^ " Extending for ref: " ^ showPendingRef pending_ref false) in
 let
   def matches_resolved_op_ref? pending_op_ref resolved_ref =
     case resolved_ref of
       | Op resolved_op_ref -> 
         resolved_op_ref.name = pending_op_ref.name
       | _ -> 
         false

   def matches_resolved_type_ref? pending_type_ref resolved_ref =
     case resolved_ref of
       | Type resolved_type_ref ->
         let match? = (resolved_type_ref.name = pending_type_ref.name) in
         % let _ = writeLine("matching: " ^ anyToString pending_type_ref.name ^ " = " ^ anyToString resolved_type_ref.name ^ " => " ^ show match?) in
         match?
       | _ -> 
         false

   def matches_resolved_theorem_ref? pending_theorem_ref resolved_ref =
     case resolved_ref of
       | Theorem resolved_theorem_ref ->
         let match? = (resolved_theorem_ref.name = pending_theorem_ref.name) in
         % let _ = writeLine("matching: " ^ anyToString pending_type_ref.name ^ " = " ^ anyToString resolved_type_ref.name ^ " => " ^ show match?) in
         match?
       | _ -> 
         false

   def matches_pending_op_ref? (pending_op_ref : PendingOpRef) (pending_ref : PendingRef) =
     case pending_ref of
       | Op (old_pending_op_ref : PendingOpRef) -> 
         old_pending_op_ref.name = pending_op_ref.name
       | _ -> 
         false

   def matches_pending_type_ref? (pending_type_ref : PendingTypeRef) (pending_ref : PendingRef) =
     case pending_ref of
       | Type (old_pending_type_ref : PendingTypeRef) ->
         old_pending_type_ref.name = pending_type_ref.name
       | _ -> 
         false

   def matches_pending_theorem_ref? (pending_theorem_ref : PendingTheoremRef) (pending_ref : PendingRef) =
     case pending_ref of
       | Theorem (old_pending_theorem_ref : PendingTheoremRef) ->
         old_pending_theorem_ref.name = pending_theorem_ref.name
       | _ -> 
         false

   def add_pending_ref resolved_refs (pending_refs, pending_ref) =
     case pending_ref of
       | Op (pending_op_ref : PendingOpRef) ->
         (case findLeftmost (matches_resolved_op_ref? pending_op_ref) resolved_refs of
            | Some _ -> 
              pending_refs
            | _ -> 
              if exists? (fn pending_ref -> 
                            matches_pending_op_ref? pending_op_ref pending_ref) 
                         pending_refs 
                then
                  % it's already in the queue to be processed
                  pending_refs
              else
                pending_ref |> pending_refs)
       | Type (pending_type_ref : PendingTypeRef) ->
         (case findLeftmost (matches_resolved_type_ref? pending_type_ref) resolved_refs of
            | Some _ -> 
              pending_refs
            | _ -> 
              if exists? (fn pending_ref -> 
                            matches_pending_type_ref? pending_type_ref pending_ref) 
                         pending_refs 
                then
                  pending_refs
              else
                pending_ref |> pending_refs)
       | Theorem (pending_theorem_ref : PendingTheoremRef) ->
         (case findLeftmost (matches_resolved_theorem_ref? pending_theorem_ref) resolved_refs of
            | Some _ -> 
              pending_refs
            | _ -> 
              if exists? (fn pending_ref -> 
                            matches_pending_theorem_ref? pending_theorem_ref pending_ref) 
                         pending_refs 
                then
                  pending_refs
              else
                pending_ref |> pending_refs)

    %% 
    def subtype_cohort cohort =
      case cohort of
        | Context -> Context
        | _ -> Assertion

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
              let location          = Op {name = primaryOpName info, pos = noPos}  in
              let new_pending_refs  = foldl (add_pending_ref new_resolved_refs)
                                            [] 
                                            (pendingRefsInTerm (info.dfn, cohort, location))
              in
              let new_pending_refs  = union (new_pending_refs, slice.pending_refs) in

              % let _ = writeLine(" ") in
              % let _ = writeLine("extending for " ^ show op_name ^ " in " ^ anyToString cohort) in
              % let _ = writeLine ("dfn: " ^ printTerm info.dfn) in
              % let _ = writeLine ("dfn: " ^ anyToString info.dfn) in
              % let _ = app (fn pref ->
              %                  case pref of
              %                    | Op ref -> writeLine("adding op " ^ show ref.name)
              %                    | Type ref -> writeLine("adding op " ^ show ref.name)
              %                    | Theorem ref -> writeLine("adding op " ^ show ref.name))
              %             new_pending_refs
              % in
              % let _ = writeLine(" ") in

              slice << {resolved_refs = new_resolved_refs,
                        pending_refs  = new_pending_refs}
            | _ ->
              let new_resolved_refs = resolve_ref (slice, pending_ref, Missing) in
              slice << {resolved_refs = new_resolved_refs})

       | Type tref ->
         (case findTheType (slice.ms_spec, tref.name) of
            | Some info ->
              let (pending_ref, status) =
                  case info.dfn of
                    | Subtype (t1, pred, _) ->
                      let cohort      = subtype_cohort tref.cohort       in
                      let pending_ref = Type (tref << {cohort = cohort}) in
                      (pending_ref, Defined)
                    | _ ->
                      (pending_ref, type_status info)
              in
              let new_resolved_refs = resolve_ref (slice, pending_ref, status)        in
              let location          = Type {name = primaryTypeName info, pos = noPos} in
              let new_pending_refs  = foldl (add_pending_ref new_resolved_refs)
                                            [] 
                                            (pendingRefsInType (info.dfn, cohort, location))
              in
              let new_pending_refs   = union (new_pending_refs, slice.pending_refs) in
              slice << {resolved_refs = new_resolved_refs,
                        pending_refs  = new_pending_refs}
            | _ ->
              let new_resolved_refs = resolve_ref (slice, pending_ref, Missing) in
              slice << {resolved_refs = new_resolved_refs})
       | Theorem tref ->
         let (Property (_, theorem_name, _, formula, _)) = tref.element in
         let new_resolved_refs = resolve_ref (slice, pending_ref, Defined)  in
         let location          = Theorem {name = theorem_name, pos = noPos} in
         let new_pending_refs  = foldl (add_pending_ref new_resolved_refs)
                                       [] 
                                       (pendingRefsInTerm (formula, cohort, location))
         in
         let new_pending_refs  = union (new_pending_refs, slice.pending_refs) in
         slice << {resolved_refs = new_resolved_refs,
                   pending_refs  = new_pending_refs}

op change_pos (location : Location) (pos : Position) : Location =
 case location of
   | Op      x -> Op      (x << {pos = pos})
   | Type    x -> Type    (x << {pos = pos})
   | Theorem x -> Theorem (x << {pos = pos})

op refs_in_type (typ : MSType, cohort : Cohort, location : Location) : PendingRefs =
 let 
   def aux typ =
     case typ of

       | Base (qid, args, pos) ->
         let ref =
             Type {name     = qid,
                   cohort   = cohort,
                   location = change_pos location pos}
         in
         foldl (fn (refs, arg) -> refs ++ aux arg) [ref] args

       | Arrow     (t1, t2, _) -> aux t1 ++ aux t2

       | Product   (fields, _) -> foldl (fn (refs, (_, typ)) -> refs ++ aux typ) [] fields

       | CoProduct (fields, _) -> foldl (fn (refs, (_, opt_type)) -> 
                                           case opt_type of
                                             | Some typ -> refs ++ aux typ
                                             | _ -> refs)
                                        [] 
                                        fields

       | Subtype   (t1, _,    _) -> aux t1
       | Quotient  (t1, rel,  _) -> aux t1 ++ refs_in_term (rel, cohort, location)
       | Pi        (_, t1,    _) -> aux t1
       | And       (t1::_,    _) -> aux t1
       | _ -> []
 in
 aux typ

op refs_in_term (term : MSTerm, cohort : Cohort, location : Location) : PendingRefs =
 foldSubTerms (fn (tm, refs) -> 
                 case tm of
                   | Fun (Op (qid,_),typ,pos) ->
                     let ref = 
                         Op {name            = qid,
                             cohort          = cohort,
                             contextual_type = Any noPos, 
                             location        = change_pos location pos}
                     in
                     [ref] ++ (refs_in_type (typ, cohort, location)) ++ refs

                   | _ -> 
                     %% tm could bind variables (e.g., lambda, let, etc.),
                     %% in which case we need to include the types of those variables
                     let types_for_pattern_vars =
                         case tm of
                           | Lambda (rules,       _) -> map (fn (pat, _,   _) -> patternType pat) rules
                           | Let    (bindings, _, _) -> map (fn (pat,      _) -> patternType pat) bindings
                           | LetRec (bindings, _, _) -> map (fn ((_, typ), _) -> typ)             bindings
                           | _ -> []
                     in
                     foldl (fn (refs, typ) ->
                              refs ++ (refs_in_type (typ, cohort, location)))
                           refs
                           types_for_pattern_vars)
             []
             term

op pendingRefsInTerm (term : MSTerm, cohort : Cohort, location : Location) : PendingRefs =
 if cohort = Implementation then
   refs_in_term (term, cohort, location)
 else
   foldTerm (fn refs -> fn tm ->
               case tm of
                 | Fun (Op (qid,_),_,pos) ->
                   let ref = 
                       Op {name            = qid,
                           cohort          = cohort,
                           contextual_type = Any noPos, 
                           location        = change_pos location pos}
                   in
                   ref |> refs
                 | _ -> refs,
             fn refs -> fn typ ->
               case typ of
                 | Base (qid, _, pos) ->
                   let ref = 
                       Type {name     = qid,
                             cohort   = cohort,
                             location = change_pos location pos}
                   in
                   ref |> refs
                 | _ -> refs,
             fn refs -> fn _ -> refs)
            [] 
            term

op pendingRefsInType (typ : MSType, cohort : Cohort, location : Location) : PendingRefs =
 if cohort = Implementation then
   refs_in_type (typ, cohort, location) 
 else
   foldType (fn refs -> fn tm ->
               case tm of
                 | Fun (Op (qid,_),_,pos) ->
                   let ref = 
                       Op {name            = qid,
                           cohort          = cohort,
                           contextual_type = Any noPos, 
                           location        = location}
                       in
                       ref |> refs
                 | _ -> refs,

             fn refs -> fn typ ->
               case typ of
                 | Base (qid, _, pos) ->
                   let ref = 
                       Type {name      = qid,
                             cohort    = cohort,
                             location  = location}
                   in
                   ref |> refs
                 | _ -> refs,

             fn refs -> fn _ -> 
               refs)

            [] 
            typ
       
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
 let slice = aux slice                           in
 let slice = add_linking_theorems   cohort slice in
 let slice = add_quotient_relations cohort slice in
 case slice.pending_refs of
   | [] -> slice
   | _ -> cohort_closure cohort slice

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op term_mentions? (term : MSTerm) (names : OpNames) : Bool =
 foldTerm (fn mentions?-> fn tm ->
             case tm of
               | Fun (Op (name,_),_,pos) | name in? names -> true
               | _ -> mentions?,
           fn mentions? -> fn _ -> mentions?,
           fn mentions? -> fn _ -> mentions?)
         false
         term

op getLinkingTheorems (spc : Spec) : SpecElements =
 %% could be others, e.g. axioms for property maintenance
 let entries = findSetfEntries spc in
 map (fn entry -> entry.element) entries

op add_linking_theorems (cohort : Cohort) (slice : Slice) : Slice =
 let resolved_elements = foldl (fn (elements, resolved_ref) ->
                                  case resolved_ref of
                                    | Theorem tref -> elements <| tref.element
                                    | _ -> elements)
                               []
                               slice.resolved_refs
 in
 let ops_in_slice      = opsInSlice         slice         in
 let linking_theorems  = getLinkingTheorems slice.ms_spec in
 let pending_theorem_refs =
     foldl (fn (pending_refs, element) ->
              case element of
                | Property (_, name, _, formula, _) ->
                  if term_mentions? formula ops_in_slice then
                    if element in? resolved_elements then
                      pending_refs
                    else
                      let pending_ref = Theorem {name    = name,
                                                 cohort  = cohort,
                                                 element = element,
                                                 status  = Defined}
                      in
                      pending_refs <| pending_ref
                  else
                    pending_refs
                | _ ->
                    pending_refs)
            []
            linking_theorems
 in
 slice << {pending_refs = slice.pending_refs ++ pending_theorem_refs}

op add_quotient_relations (cohort : Cohort) (slice : Slice) : Slice =
 let
   def get_q_fns typ =
     foldTypesInType (fn (refs, typ) -> 
                        case typ of
                          | Quotient (_, rel, _) ->
                            (case rel of
                               | Fun (Op (name, _), typ, _) ->
                                 if exists? (fn ref -> 
                                               case ref of
                                                 | Op ref -> ref.name = name
                                                 | _ -> false)
                                            slice.resolved_refs
                                   then
                                     refs
                                 else
                                   let ref =
                                       Op {name            = name,
                                           cohort          = cohort,
                                           contextual_type = typ,
                                           location        = Unknown}
                                   in
                                   ref |> refs
                               | _ -> refs)
                          | _ -> refs)
                     []
                     typ 
 in
 let pending_q_refs = 
     foldl (fn (names, resolved_ref) ->
                      case resolved_ref of
                        | Type tref -> 
                          (case findTheType (slice.ms_spec, tref.name) of
                             | Some info ->
                               (get_q_fns info.dfn) ++ names
                             | _ ->
                               names)
                        | _ ->
                          names)
                   []
                   slice.resolved_refs
 in
 slice << {pending_refs = slice.pending_refs ++ pending_q_refs}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op implementation_closure (slice : Slice) : Slice = 
 cohort_closure Implementation slice

op assertion_closure      (slice : Slice) : Slice = 
 let pending_refs = map (fn resolved_ref ->
                           case resolved_ref of
                             | Op oref -> 
                               Op {name            = oref.name, 
                                   cohort          = Assertion,
                                   contextual_type = oref.contextual_type,
                                   location        = head oref.locations}

                             | Type tref ->
                               Type {name     = tref.name,
                                     cohort   = Assertion,
                                     location = head tref.locations}

                             | Theorem tref -> 
                               Theorem {name    = tref.name,
                                        cohort  = Assertion,
                                        element = tref.element,
                                        status  = tref.status})
                        slice.resolved_refs
 in
 let slice = slice << {pending_refs = pending_refs} in
 cohort_closure Assertion      slice

op context_closure        (slice : Slice) : Slice = 
 slice

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

op genericExecutionSlice (ms_spec    : Spec,
                          root_ops   : QualifiedIds,
                          root_types : QualifiedIds)
 : Slice =
 let
   def ignore_language_morphisms spc = []
   def vacuous_oracle (ref, slice) = None
 in
 executionSlice (ms_spec, 
                 ignore_language_morphisms, 
                 vacuous_oracle, 
                 root_ops, 
                 root_types)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

end-spec
