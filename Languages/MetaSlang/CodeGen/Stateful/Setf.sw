Setf qualifying spec

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Setf is used for stateful code generation, 
%% We include it under the Transformations directory because many of the prepatory 
%% actions for using Setf can be done in specs that remain functional.
%% These actions includes:
%%  Finding the Access/Update axioms.                      (done here)
%%  Deconflicting acessses and udpates in executable code. (see DeconflctUpdates.sw)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

import /Languages/MetaSlang/Specs/MSTerm
import /Languages/MetaSlang/Specs/Utilities
import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements  % for addOp of Setf op

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op equalTerms? (tms1 : MSTerms, tms2 : MSTerms) : Bool =
 case (tms1, tms2) of
   | ([], []) -> true
   | (tm1 :: tms1, tm2 :: tms2) -> 
     equalTerm? (tm1,tm2) && equalTerms? (tms1, tms2)
   | _ ->
     false

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op setfPos  : Position    = Internal "Setf"
op setfName : QualifiedId = Qualified ("System", "setf")

type SetfEntries = List SetfEntry
type SetfEntry   = {accesser_name       : OpName, 
                    updater_name        : OpName, 
                    accesser_arg_counts : List Nat,  % used to create names such as foo-1-1 in code generation
                    updater_arg_counts  : List Nat,
                    accesser            : MSTerm, 
                    updater             : MSTerm, 
                    update_template     : MSTerm,
                    setf_lhs_template   : MSTerm,
                    setf_rhs_template   : MSTerm,
                    element             : SpecElement}


op make_setf_type (arg_type : MSType) : MSType = 
  Arrow (Product ([("1", arg_type),
                   ("2", arg_type)],
                  setfPos), 
         Product ([], setfPos),
         setfPos)

op make_setf_ref (arg_type : MSType) : MSTerm = 
  Fun (Op (setfName, Nonfix), 
       make_setf_type arg_type, 
       setfPos)

op setfDef : MSTerm = 
 TypedTerm (Any setfPos, 
            make_setf_type (TyVar ("A", setfPos)), 
            setfPos)

op makeSetf (lhs : MSTerm, rhs : MSTerm) : MSTerm =
 if equalTerm? (lhs, rhs) then
   Record ([], setfPos) % no-op
 else
   let arg_type = termType lhs in
   Apply (make_setf_ref arg_type, 
          Record ([("1", lhs), ("2", rhs)], setfPos), 
          setfPos)

op addSetfOpM (spc : Spec) : Env Spec =
 case findTheOp (spc, setfName) of
   | Some _ -> return spc
   | _ -> addOp [setfName] Nonfix false setfDef spc setfPos

op addSetfOp (spc : Spec) : Spec =
 run (addSetfOpM spc)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op make_setf_template (tm     : MSTerm, 
                       vpairs : List (MSTerm * MSTerm), 
                       value  : MSTerm) 
 : Option (MSTerm * MSTerm) =
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
                 setfPos)
       | _ ->
         arg

   def revise tm =
     case tm of 
       | Apply (f, arg, _) ->
         (case f of
            | Apply _ ->
              (case revise f of
                 | Some new_f ->
                   Some (Apply (new_f, subst_vars arg, setfPos))
                 | _ ->
                   None)
            | _ ->
              case (arg : MSTerm) of
                | Record ((x, update) :: fields, _) ->
                  (case first_arg_of update of
                     | Some container ->
                       let new_fields = map (fn (x, arg) -> (x, subst_vars arg)) fields in
                       Some (Apply (f, Record ((x, container) :: new_fields, setfPos), setfPos))
                     | _ ->
                       None)
                | _ ->
                  case first_arg_of arg of
                    | Some container ->
                      Some (Apply (f, container, setfPos))
                    | _ ->
                      None)
       | _ ->
         None
 in
 case revise tm of
   | Some tm ->
     Some (tm, value)
   | _ ->
     None

op vars_compared (tm : MSTerm) : Option (List (MSTerm * MSTerm)) =
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
     (case (vars_compared t1, vars_compared t2) of
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
      
op semantics_of_get_set? (get_args  : MSTerms,
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
 %% then_tm must be an argument of the set
 termIn?(then_tm, set_args)

 &&
 %% the get in lhs should use same indices as the get in the else term
 (case opAndArgs else_tm of
    | Some (_, _, get2_args) ->
      let get2_args = flattenArgs get2_args in
      (case get2_args of
         | accessed_container :: get2_indices ->
           equalTerm? (updated_container, accessed_container) && 
           equalTerms? (get_indices, get2_indices)
         | _ -> 
           false)
    | _ -> 
      false)

%%%   get (set (m, i, x), j) = if i = j then x else get (m, j)
%%%   get (set  m  i  x,  j) = if i = j then x else get (m, j)
%%%   get (set (m, i, x)) j  = if i = j then x else get (m, j)
%%%   get (set  m  i  x)  j  = if i = j then x else get (m, j)

op flattenArgs (args : MSTerms) : MSTerms =
 foldl (fn (args, arg) ->
          args ++
          (case arg of
             | Record (pairs, _) -> map (fn (_, arg) -> arg)  pairs
             | _  ->  [arg]))
       []
       args
                               
op extract_setf_entry (element : SpecElement) : Option SetfEntry =
 let 
   def aux fm =
     case fm of
       | Pi   (_, fm,    _) -> aux fm
       | And  (fm :: _,  _) -> aux fm
       | Bind (_, _, fm, _) -> aux fm
       | Apply(Fun (Implies, _, _), Record ([(_, lhs), (_, rhs)], _), _) -> aux rhs

       | Apply (Fun (Equals, _, _), 
                Record ([(_, lhs), 
                         (_, IfThenElse (pred, then_tm, else_tm, _))], 
                        _), 
                _) 
         ->
         (case vars_compared pred of
            | Some vpairs ->
              (case opAndArgs lhs of
                 | Some (accesser_name, accesser, get_args) -> 
                   (case flattenArgs get_args of
                      | update_template :: _ :: _ ->
                        (case opAndArgs update_template of
                           | Some (updater_name, updater, set_args) ->
                             if semantics_of_get_set? (get_args, set_args, vpairs, then_tm, else_tm) then
                               case make_setf_template (lhs, vpairs, then_tm) of % then_tm is same as value assigned in updater
                                 | Some (setf_lhs_template, setf_rhs_template) ->
                                   % let _ = writeLine ("extractSetfEntry: accesser_name     = " ^ anyToString accesser_name  ) in
                                   % let _ = writeLine ("extractSetfEntry: updater_name      = " ^ anyToString updater_name   ) in
                                   % let _ = writeLine ("extractSetfEntry: accesser          = " ^ printTerm accesser         ) in
                                   % let _ = writeLine ("extractSetfEntry: updater           = " ^ printTerm updater          ) in
                                   % let _ = writeLine ("extractSetfEntry: update_template   = " ^ printTerm update_template  ) in
                                   % let _ = writeLine ("extractSetfEntry: setf_lhs_template = " ^ printTerm setf_lhs_template) in
                                   % let _ = writeLine ("extractSetfEntry: setf_rhs_template = " ^ printTerm setf_rhs_template) in
                                   % let _ = writeLine ("--------------------")                                                 in
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
                                         setf_lhs_template   = setf_lhs_template,
                                         setf_rhs_template   = setf_rhs_template,
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
                           (case extract_setf_entry elt of
                              | Some entry -> entries <| entry
                              | _ -> entries)
                        | _ ->
                          entries)
                   []
                   spc.elements

end-spec
