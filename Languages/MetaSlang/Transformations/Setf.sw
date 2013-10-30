Setf qualifying spec

import /Languages/MetaSlang/Specs/MSTerm
import /Languages/MetaSlang/Specs/Utilities

op equalTerms? (tms1 : MSTerms, tms2 : MSTerms) : Bool =
 case (tms1, tms2) of
   | ([], []) -> true
   | (tm1 :: tms1, tm2 :: tms2) -> 
     equalTerm? (tm1,tm2) && equalTerms? (tms1, tms2)
   | _ ->
     false

op setfQid  : QualifiedId = Qualified ("System", "setf")
op setfType : MSType      = Arrow (Product ([("1", TyVar ("A", noPos)), 
                                             ("2", TyVar ("A", noPos))], 
                                            noPos), 
                                   Product ([], noPos),
                                   noPos)

op setfDef : MSTerm       = TypedTerm (Any noPos, setfType, noPos) 
op setfRef : MSTerm       = Fun (Op (setfQid, Nonfix), setfType, noPos)

type SetfEntry = {accesser_name       : OpName, 
                  updater_name        : OpName, 
                  accesser_arg_counts : List Nat,  % used to create names such as foo-1-1 in code generation
                  updater_arg_counts  : List Nat,
                  accesser            : MSTerm, 
                  updater             : MSTerm, 
                  update_template     : MSTerm,
                  setf_template       : MSTerm,
                  element             : SpecElement}

type SetfEntries = List SetfEntry

op makeSetf (lhs : MSTerm, rhs : MSTerm) : MSTerm =
 if equalTerm? (lhs, rhs) then
   Record ([], noPos) % no-op
 else
   Apply (setfRef, Record ([("1", lhs), ("2", rhs)], noPos), noPos)


op makeSetfTemplate (tm : MSTerm, vpairs : List (MSTerm * MSTerm), value : MSTerm) : Option MSTerm =
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
     case arg of
       | Var _ -> 
         (case findLeftmost (fn (x, y) -> equalTerm? (x, arg)) vpairs of
            | Some (_, y) -> y
            | _ ->
              case findLeftmost (fn (x, y) -> equalTerm? (y, arg)) vpairs of
                | Some (x, _) -> x
                | _ -> arg)
       | Record (fields, _) ->
         Record (map (fn (index, arg) -> 
                        (index, subst_vars arg)) 
                     fields, 
                 noPos)
       | _ ->
         arg

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
     None

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
     
op opAndArgs (tm : MSTerm) : Option (OpName * MSTerm * MSTerms) =
 case tm of
   |  Fun (Op (opname, _), _, _) -> Some (opname, tm, [])
      
   |  Apply (f, arg, _) ->
      (case opAndArgs f of
         | Some (opname, f, f_args) ->  
           Some (opname, f, f_args ++ [arg])
         | _ -> None)
      
   | _ -> None
      
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
                               
op extractSetfEntry (element : SpecElement) : Option SetfEntry =
 let 
   def aux fm =
     case fm of
       | Pi   (_, fm,    _) -> aux fm
       | And  (fm :: _,  _) -> aux fm
       | Bind (_, _, fm, _) -> aux fm

       | Apply (Fun (Equals, _, _), 
                Record ([(_, lhs), 
                         (_, IfThenElse (pred, then_tm, else_tm, _))], 
                        _), 
                _) 
         ->
         (case varsCompared pred of
            | Some vpairs ->
              (case opAndArgs lhs of
                 | Some (accesser_name, accesser, get_args) -> 
                   (case flattenArgs get_args of
                      | update_template :: _ :: _ ->
                        (case opAndArgs update_template of
                           | Some (updater_name, updater, set_args) ->
                             if semanticsOfGetSet? (get_args, set_args, vpairs, then_tm, else_tm) then
                               case makeSetfTemplate (lhs, vpairs, then_tm) of % then_tm is same as value assigned in updater
                                 | Some setf_template ->
                                   % let _ = writeLine ("extractSetfEntry: accesser_name   = " ^ anyToString accesser_name ) in
                                   % let _ = writeLine ("extractSetfEntry: updater_name    = " ^ anyToString updater_name  ) in
                                   % let _ = writeLine ("extractSetfEntry: accesser        = " ^ printTerm accesser        ) in
                                   % let _ = writeLine ("extractSetfEntry: updater         = " ^ printTerm updater         ) in
                                   % let _ = writeLine ("extractSetfEntry: update_template = " ^ printTerm update_template ) in
                                   % let _ = writeLine ("extractSetfEntry: setf_template   = " ^ printTerm setf_template   ) in
                                   % let _ = writeLine ("--------------------")                                              in
                                   let 
                                     def arg_counts args =
                                       map (fn arg ->
                                              case arg of
                                                | Record (fields, _) -> length fields
                                                | _ -> 1)
                                           args
                                   in
                                   Some {accesser_name       = accesser_name, 
                                         updater_name        = updater_name, 
                                         accesser_arg_counts = arg_counts get_args,
                                         updater_arg_counts  = arg_counts set_args,
                                         accesser            = accesser,
                                         updater             = updater,
                                         update_template     = update_template,
                                         setf_template       = setf_template,
                                         element             = element}
                                 | _ -> 
                                   None
                             else
                               None
                           | _ -> None)
                      | _ -> None)
                 | _ -> None)
            | _ -> None)
       | _ -> None
 in
 case element of
   | Property (_, _, _, fm, _) -> aux fm
   | _ -> None

op findSetfEntries (spc  : Spec) : SetfEntries =
 foldrSpecElements (fn (elt, entries) ->
                      case elt of
                        |  Property (typ, name, _, fm, _) | typ in? [Axiom, Theorem, Conjecture] ->
                           (case extractSetfEntry elt of
                              | Some entry -> entries <| entry
                              | _ -> entries)
                        | _ ->
                          entries)
                   []
                   spc.elements

op convertUpdateToAccess (update : MSTerm) : MSTerm

op reviseProjectionUpdates (lhs : MSTerm, rhs : MSTerm) : MSTerm =
 let 
   def makeProjectionUpdate (x, field_id, v) =
     let proj_type = Arrow (termType x, termType v, noPos) in
     let new_lhs   = Apply (Fun (Project field_id, proj_type, noPos), lhs, noPos) in
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
               noPos))
   | _ ->
     makeSetf (lhs, rhs)

op reviseUpdate (ms_spec : Spec, setf_entries : SetfEntries, lhs : MSTerm, rhs : MSTerm) : MSTerm =
 % first check to see if this update matches some setter/getter pair
 let
   def updateAndArgs tm =
     case opAndArgs tm of
       | Some (opname, update, args) ->
         (case flattenArgs args of
            | container :: indices_and_value ->
              (case reverse indices_and_value of
                 | [_] -> None
                 | new_value :: rev_indices -> 
                   Some (opname, update, container, reverse rev_indices, new_value)
                 | _ -> None)
            | _ -> None)
       | _ -> None
         
   def accessAndArgs tm =
     case opAndArgs tm of
       | Some (opname, access, args) ->
         (case flattenArgs args of
            | container :: indices ->
              Some (opname, access, container, indices)
            | _ -> None)
       | _ -> None
 in
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
               % let _ = writeLine ("set_indices   ="  ^ printTerms set_indices)  in
               % let _ = writeLine ("get_indices   ="  ^ printTerms get_indices)  in
               if equalTerm?  (lhs,           set_container) && 
                  equalTerm?  (set_container, get_container) && 
                  equalTerms? (set_indices,   get_indices)   
                 then
                   let dom_type = inferType (ms_spec, access_tm) in
                   let updates = 
                       map (fn (index, value) ->
                              let new_type = Arrow (dom_type, inferType (ms_spec, value), noPos) in
                              let field = Apply (Fun (Project index, new_type, noPos), access_tm, noPos) in
                              makeUpdate ms_spec setf_entries field value)
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
          case findLeftmost (fn (entry : SetfEntry) -> update_op_name = entry.updater_name) setf_entries of
            | Some setf_pair ->
              (case makeVarBindings (setf_pair.update_template, rhs) of
                 | Some bindings ->
                   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                   %% setf (container, update(container,index,v))
                   %%  =>
                   %% setf (access(container, index), v)
                   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                   reviseTemplate (setf_pair.setf_template, bindings)
                 | _ ->
                   % let _ = writeLine ("reviseUpdate: no match") in
                   makeSetf (lhs, rhs))
            | _ ->
              makeSetf (lhs, rhs))
   | _ -> 
     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
     %% setf (foo, foo << {foo,x = v})
     %%  =>
     %% setf (foo.x, v)
     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
     reviseProjectionUpdates (lhs, rhs)
     
op makeUpdate (ms_spec      : Spec)
              (setf_entries : SetfEntries)
              (lhs          : MSTerm)
              (rhs          : MSTerm)
 : MSTerm =
 case rhs of
   | IfThenElse (p, tm1, tm2, _) ->
     IfThenElse (p, 
                 makeUpdate ms_spec setf_entries lhs tm1, 
                 makeUpdate ms_spec setf_entries lhs tm2, 
                 noPos)
     
   | Record (pairs, _) | forall? (fn (index,_) -> natConvertible index) pairs ->
     (let dom_type = inferType (ms_spec, lhs) in
      let updates = 
          map (fn (index, value) ->
                 let rng_type = inferType (ms_spec, value)             in
                 let new_type = Arrow (dom_type, rng_type,      noPos) in
                 let new_proj = Fun   (Project index, new_type, noPos) in
                 let new_lhs  = Apply (new_proj, lhs,           noPos) in
                 makeUpdate ms_spec setf_entries new_lhs value)
              pairs
      in
      case updates of
        | [update] -> update
        | _ -> Seq (updates, noPos))
     
   | _ ->
     reviseUpdate (ms_spec, setf_entries, lhs, rhs)
 
op makeVarBindings (template : MSTerm, tm : MSTerm) : Option (List (MSTerm * MSTerm)) =
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
       
op reviseTemplate (template : MSTerm, bindings : List (MSTerm * MSTerm)) : MSTerm =
 let 
   def subst tm =
     case findLeftmost (fn (x, y) -> equalTerm? (x, tm)) bindings of
       | Some (_, y) -> y
       | _ ->
         case tm of
           | Apply  (x, y,   _) -> Apply  (subst x, subst y, noPos)
           | Record (fields, _) -> Record (map (fn (x, y) -> (x, subst y)) fields, noPos)
           | _ -> tm
 in
 subst template

end-spec
