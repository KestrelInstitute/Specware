(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

removeGeneratedSuffixes qualifying spec

import /Languages/SpecCalculus/Semantics/Evaluate/Translate  % translateSpec
import /Languages/MetaSlang/Specs/Environment

(*
 * SpecTransform.removeGeneratedSuffixes is a transform that removes suffixes
 * added by removeCurrying, to the extent that this doesn't cause two distinct
 * ops to acquire the same name.
 * 
 * Ops such as foo.bar-3-1-2 are renamed to foo.bar unless some other op 
 * name foo.bar already exists or we would also be renaming some other op
 * such as foo.bar-7-2 to the same name.
 *
 * In the latter case, all the names that would have collided under 
 * simplification are preserved with no change -- none of them are renamed.
 *)

op SpecTransform.removeGeneratedSuffixes (ms_spec : Spec) : Spec =
 let
   def aux chars =
     case splitAtRightmost (fn char -> char = #-) chars of
       | Some (prefix, _, suffix) | natConvertible (implode suffix) ->
         Some (case aux prefix of
                 | Some shorter_prefix -> shorter_prefix
                 | _ -> prefix)
       | _ ->
         None

   def simplified id =
     case aux (explode id) of
       | Some prefix -> Some (implode prefix)
       | _ -> None

 in

 %% first collect the renamings we would like to do
 let desired_renamings =
     foldOpInfos (fn (op_info, renamings) ->
                    foldl (fn (renamings, old as Qualified (q, id)) ->
                             case simplified id of
                               | Some shorter_id ->
                                 let new = Qualified(q, shorter_id) in
                                 (old, new) :: renamings
                               | _ ->
                                 renamings)
                          renamings
                          op_info.names)
                 []
                 ms_spec.ops
 in

 %% then remove those that would rename an op into another pre-existing op
 let possible_renamings =
     filter (fn (old, new) -> 
               case findTheOp (ms_spec, new) of
                 | Some _ -> 
                   let _ = writeLine("removeGeneratedSuffixes can't rename " ^ show old ^ " to pre-existing " ^ show new) in
                   false
                 | _ -> 
                   true)
            desired_renamings
 in

 %% then remove any otherwise possible renamings that would rename into the same new name as another renaming
 %% (x => z and y => z)

 let candidate_new_names = map (fn (_, new) -> new) possible_renamings in

 let clashing_new_names = 
     filter (fn name ->
               let renamings_to_same_target = 
                    filter (fn (old, new) -> new = name) possible_renamings
               in
               let n = length renamings_to_same_target in
               if (n > 1) then
                 let _ = writeLine ("removeGeneratedSuffixes can't do the following renamings simultaneously: ") in
                 let _ = map (fn (old, new) -> 
                                writeLine(show old ^ " => " ^ show new)) 
                             renamings_to_same_target
                 in
                 true
               else
                 false)
            candidate_new_names
 in
 let viable_renamings = filter (fn (_, new) -> 
                                 ~ (new in? clashing_new_names))
                               possible_renamings 
 in

 %% Translate the spec using all the non-clashing renamings.

 let renaming_rules = map (fn (old, new) ->
                             (Op ((old, None), (new, None), [new]), noPos))
                          viable_renamings
 in
 let renaming = (renaming_rules, noPos) in

 let revised_spec = run (translateSpec false         % allow_exceptions? 
                                       ms_spec
                                       renaming 
                                       []            % immune_op_names 
                                       false         % allow_extra_rules? 
                                       None)         % currentUID?
 in
 revised_spec

end-spec
