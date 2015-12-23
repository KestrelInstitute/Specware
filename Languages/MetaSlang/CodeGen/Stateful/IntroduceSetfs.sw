(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

IntroduceSetfs qualifying spec
{

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% These routines are used in the production of stateful code.
%%
%% They produce stateful quasi-specs, hence this file belongs in the CodeGen 
%% directory, not the Transformations directory.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

import /Languages/MetaSlang/CodeGen/Stateful/Setf

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% If the right hand side of a setf term matches a known updater, use that 
%% match to generate the corresponding accesser for the left hand side of 
%% a new setf term:
%%
%%   setf (container, update (container, i_1, i_2, ..., i_n, v))
%%      =>
%%   setf (access (container, i_1, i_2, ..., i_n), v)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op isPos : Position = Internal "IntroduceSetfs"

type Binding  = MSTerm * MSTerm
type Bindings = List Binding

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op makeSetfUpdate (ms_spec      : Spec)
                  (setf_entries : SetfEntries)
                  (lhs          : MSTerm)
                  (rhs          : MSTerm)
 : MSTerm =
 case rhs of
   | IfThenElse (p, tm1, tm2, _) ->
     IfThenElse (p, 
                 makeSetfUpdate ms_spec setf_entries lhs tm1, 
                 makeSetfUpdate ms_spec setf_entries lhs tm2, 
                 isPos)
     
   | Record (pairs, _) | forall? (fn (index,_) -> natConvertible index) pairs ->
     (let dom_type = inferType (ms_spec, lhs) in
      let updates = 
          map (fn (index, value) ->
                 let rng_type = inferType (ms_spec, value)               in
                 let new_type = Arrow (dom_type, rng_type,      isPos) in
                 let new_proj = Fun   (Project index, new_type, isPos) in
                 let new_lhs  = Apply (new_proj, lhs,           isPos) in
                 makeSetfUpdate ms_spec setf_entries new_lhs value)
              pairs
      in
      case updates of
        | [update] -> update
        | _ -> Seq (updates, isPos))
     
   | _ ->
     reviseUpdate (ms_spec, setf_entries, lhs, rhs)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op reviseUpdate (ms_spec      : Spec, 
                 setf_entries : SetfEntries, 
                 lhs          : MSTerm, 
                 rhs          : MSTerm)
  : MSTerm =
 % first check to see if this update matches some setter/getter pair
 let
   def extract_updater_and_args tm =
     %% deconstruct a possible update term in the rhs to extract the pieces
     %% corresponding to 'update (container, i_1, i_2, ..., i_n, v))'
     case opAndArgs tm of                                 % uncurry and split apart
       | Some (name_of_updater, updater, args) ->
         (case flattenArgs args of                        % flatten args
            | container :: indices_and_value ->
              (case reverse indices_and_value of
                 | [_] -> None
                 | new_value :: rev_indices -> 
                   let indices = reverse rev_indices in
                   %% returning the name of the updater lets us look it up in a table
                   Some (name_of_updater, updater, container, indices, new_value)
                 | _ -> None)
            | _ -> None)
       | _ -> None
         
   def extract_accesser_args tm =
     %% deconstruct a possible access term in the lhs to extract the pieces
     %% corrsesponding to 'access (container, i_1, i_2, ..., i_n)'
     case opAndArgs tm of                                 % uncurry and split apart
       | Some (_, _, args) ->                             % ignore accesser
         (case flattenArgs args of                        % flatten args
            | container :: indices ->
              Some (container, indices)
            | _ -> None)
       | _ -> None
 in
 case extract_updater_and_args rhs of
   | Some (name_of_updater, updater, updated_container, update_indices, new_value) ->
     (case new_value of
        | Apply (Fun (RecordMerge, _, _), 
                 Record ([("1", access_tm),
                          ("2", value as Record (new_value_pairs, _))],
                         _),
                 _)
          ->
          (case extract_accesser_args access_tm of
             | Some (accessed_container, access_indices) ->
               % let _ = writeLine ("update        = " ^ anyToString update) in
               % let _ = writeLine ("access        = " ^ anyToString access) in
               % let _ = writeLine ("lhs           = " ^ printTerm lhs)           in
               % let _ = writeLine ("get_container = " ^ printTerm get_container) in
               % let _ = writeLine ("set_container = " ^ printTerm set_container) in
               % let _ = writeLine ("set_indices   ="  ^ printTerms set_indices)  in
               % let _ = writeLine ("get_indices   ="  ^ printTerms get_indices)  in
               if equalTerm?  (lhs,               updated_container)  && 
                  equalTerm?  (updated_container, accessed_container) && 
                  equalTerms? (update_indices,    access_indices)   
                 then
                   let dom_type = inferType (ms_spec, access_tm) in
                   let updates = 
                       map (fn (index, value) ->
                              let new_type = Arrow (dom_type, inferType (ms_spec, value), isPos) in
                              let field = Apply (Fun (Project index, new_type, isPos), access_tm, isPos) in
                              makeSetfUpdate ms_spec setf_entries field value)
                           new_value_pairs
                   in
                   % let _ = writeLine ("updates = " ^ printTerms updates) in
                   (case updates of
                      | [update] -> update
                      | _ -> Seq (updates, isPos))
               else
                 makeSetf (lhs, rhs)
             | _ -> 
               makeSetf (lhs, rhs))
        | _ -> 
          case findLeftmost (fn setf_entry -> name_of_updater = setf_entry.updater_name) setf_entries  of
            | Some setf_pair ->
              %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
              %%  setf (foo, update (foo, indices, value))
              %%  =>
              %%  update (foo.indices,value)
              %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
              remove_setf_of_lhs_to_setf_pair_update_of_lhs (ms_spec, setf_entries, lhs, rhs, setf_pair) 
            | _ ->
              makeSetf (lhs, rhs))
   | _ -> 
     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
     %% setf (foo, foo << {foo.x = v})
     %%  =>
     %% setf (foo.x, v)
     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
     remove_setf_of_lhs_to_projection_update_of_lhs (lhs, rhs)
     
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op remove_setf_of_lhs_to_setf_pair_update_of_lhs (ms_spec      : Spec, 
                                                  setf_entries : SetfEntries, 
                                                  lhs          : MSTerm, 
                                                  rhs          : MSTerm,
                                                  setf_entry   : SetfEntry)
 : MSTerm =
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%  setf (foo, update (foo, indices, value))
 %%  =>
 %%  update (foo.indices,value)
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 case match_setf_entry (setf_entry.update_template, rhs) of

   | Some bindings ->
     let new_lhs   = revise_template (setf_entry.setf_lhs_template, bindings) in
     let new_rhs   = revise_template (setf_entry.setf_rhs_template, bindings) in
     let typed_lhs = TypedTerm (new_lhs, termType new_rhs, noPos) in
    %makeSetf (typed_lhs, new_rhs)                          %% older -- causes memory leak: setf (x, (a, b, c))
     makeSetfUpdate ms_spec setf_entries typed_lhs new_rhs  %% newer -- avoids memory leak: setf (x.1, a); setf (x.2, b); setf (x.3, c)

   | _ ->
     makeSetf (lhs, rhs)

op match_setf_entry (template : MSTerm, tm : MSTerm) : Option Bindings =
 let
   def match (template_fields, term_fields) =
     case (template_fields, term_fields) of

       | ([], []) -> Some []

       | ((_, template_field_tm) :: template_fields, 
          (_, term_field_tm)     :: term_fields) 
         ->
         (case match (template_fields, term_fields) of
            | Some bindings -> 
              let binding = (template_field_tm, term_field_tm) in
              Some (binding |> bindings)
            | _  -> None)

       | _ -> None
 in
 case template of
   | Var _ -> Some [(template, tm)]

   | Apply (template_f, template_arg, _) ->
     (case tm of

        | Apply (term_f, term_arg, _) ->
          (case (match_setf_entry (template_f,   term_f), 
                 match_setf_entry (template_arg, term_arg)) 
             of
             | (Some f_bindings, Some arg_bindings) -> 
               Some (f_bindings ++ arg_bindings)

             | _ -> None)

        | _ ->
          None)

   | Record (template_fields, _) ->
     (case tm of
        | Record (term_fields, _) ->
          match (template_fields, term_fields)
        | _ ->
          None)

   | _ ->
     if equalTerm? (template, tm) then
       Some []
     else
       None
       
op revise_template (template : MSTerm, bindings : Bindings) : MSTerm =
 let 
   def subst tm =
     case findLeftmost (fn (x, y) -> equalTerm? (x, tm)) bindings of
       | Some (_, y) -> y
       | _ ->
         case tm of
           | Apply  (x, y,   _) -> Apply  (subst x, subst y, isPos)
           | Record (fields, _) -> Record (map (fn (x, y) -> (x, subst y)) fields, isPos)
           | _ -> tm
 in
 subst template

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op remove_setf_of_lhs_to_projection_update_of_lhs (lhs : MSTerm, 
                                                   rhs : MSTerm) 
 : MSTerm =
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% setf (foo, foo << {x = v})
 %%  =>
 %% setf (foo.x, v)
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 let 
   def makeProjectionUpdate (x, field_id, v) =
     let proj_type = Arrow (termType x, termType v, isPos) in
     let new_lhs   = Apply (Fun (Project field_id, proj_type, isPos), 
                            lhs, 
                            isPos)
     in
     makeSetf (new_lhs, v)
 in
 case rhs of
   | Apply (Fun (RecordMerge, _, _), 
            Record ([("1", access_tm),
                     ("2", value as Record (new_value_pairs, _))],
                    _),
            _)
     | equalTerm? (lhs, access_tm)
     ->
     (case new_value_pairs of
        | [(x, v)] -> 
          %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
          %% setf (foo, foo << {x = v})
          %%  =>
          %% setf (foo.x, v)
          %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
          makeProjectionUpdate (access_tm, x, v)
        | _ -> 
          %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
          %% setf (foo, foo << {x = v, y = w})
          %%  =>
          %% seq (setf (foo.x, v), setf(foo.y, w))
          %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
          Seq (map (fn (x, v) -> 
                      makeProjectionUpdate (access_tm, x, v)) 
                 new_value_pairs, 
               isPos))
   | _ ->
     makeSetf (lhs, rhs)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

}
