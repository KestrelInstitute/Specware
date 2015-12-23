(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

liftSequences qualifying spec 
{

import /Languages/MetaSlang/CodeGen/DebuggingSupport

op lsPos : Position = Internal "liftSequences"

op lift_seq (tm : MSTerm) : MSTerm =
 case tm of
   | Apply (Seq (tms, _), t2, _) ->
     %% tms have been processsed, but could be seq's
     let final_tm :: rev_seq_prefix = reverse tms in
     let new_apply = Apply (final_tm, t2, lsPos)  in
     Seq (reverse (new_apply |> rev_seq_prefix), lsPos)

   | Apply (t1, t2 as Seq (tms, _), _) ->
     %% tms have been processsed, but could be seq's
     let final_tm :: rev_seq_prefix = reverse tms in
     let new_apply = Apply (t1, final_tm, lsPos)  in
     Seq (reverse (new_apply |> rev_seq_prefix), lsPos) 

   | Record (fields, _) ->
     let (ok?, opt_outer_seq, new_fields) =
     foldl (fn ((ok?, opt_outer_seq, new_fields), (id, tm)) ->
              case tm of
                | Seq (tms, _) ->
                  (case opt_outer_seq of
                     | Some _ ->
                       % Second (or later) sequence within one record...
                       (false, None, [])
                     | _ ->
                       let final_tm :: rev_seq_prefix = reverse tms                  in
                       let new_fields                 = new_fields <| (id, final_tm) in
                       let seq_prefix                 = reverse rev_seq_prefix       in
                       (ok?, Some seq_prefix, new_fields))
                | _ ->
                  let new_fields = new_fields <| (id, tm) in
                  (ok?, opt_outer_seq, new_fields))
           (true, None, [])
           fields
     in
     if ok? then
       case opt_outer_seq of
         | Some seq ->
           let new_record = Record (new_fields,        lsPos) in
           let new_seq    = Seq    (seq <| new_record, lsPos) in
           new_seq
         | _ -> tm
     else
       let _ = writeLine ("Can't lift two competing sequences in record fields.") in
       let _ = writeLine (printTerm tm) in
       tm
       
   | Seq (tms, _) ->
     let new_tms =
         foldl (fn (tms, tm) ->
                  %% We should only need one level of recursive flattening here
                  %% because tm will already have been processed by lift_seq.
                  case tm of
                    | Seq (sub_tms, _) -> tms ++ sub_tms
                    | _ -> tms <| tm)
               []
               tms
     in
     Seq (new_tms, lsPos)

   | _ ->
     tm

op SpecTransform.liftSequences (spc : Spec) : Spec =
 mapSpec (lift_seq, fn typ -> typ, fn pat -> pat) spc
}

