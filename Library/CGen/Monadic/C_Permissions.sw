(* FIXME: top-level documentation *)

C_Permissions qualifying spec
  import C_Predicates
  import /Library/Structures/Data/OptLens
  import SplittingAlg


  (***
   *** Functional Values and Heaps
   ***)

  (* To represent C values in logic, we define a universal type for "functional
     values", i.e., values in MetaSlang proper that represent C values. This
     type can be refined to an actual type using finalizeInductiveType *)
  type FValue

  (* FValue includes lists (FIXME: add other ops for FValue_list) *)
  op FValue_list : List FValue -> FValue

  (* A "functional heap" gives values for portions of an object designator,
  where "portions" are given by splittings (see SplittingAlg.sw). Functional
  heaps must be closed under smaller portions as well as under combining
  portions together. *)
  type FHeap = { h : Map (ObjectDesignator * Splitting, FValue) |
                  (fa (d,spl1,spl2)
                     splitting_leq (spl1,spl2) => (d,spl2) in? (domain h) =>
                     (d,spl1) in? (domain h)) &&
                  (fa (d,spl1,spl2)
                     splittings_combinable? (spl1,spl2) =>
                     (d,spl1) in? (domain h) => (d,spl2) in? (domain h) =>
                     (d,combine_splittings (spl1,spl2)) in? (domain h))
                  }


  (***
   *** Value Abstractions
   ***)

  (* FIXME: document all of this! *)

  (* FIXME: abs_rel needs to take in R, or some abstraction of it, in order to
  abstract function pointers *)

  (* An AbsDepDesig designates a set of possible dependencies on a value (FIXME:
  explain this a little better) *)
  type AbsDepDesig1 =
     | AbsDep_Member Identifier
     | AbsDep_Subscript
     | AbsDep_Deref
  type AbsDepDesig = List AbsDepDesig1

  type ValueAbsH a =
    {abs_type_name : TypeName,
     abs_rel : Splitting -> FHeap -> a -> Value -> Bool,
     abs_combines_to : a * a -> a -> Bool}

  type ValueAbs a =
    ValueAbsH a * List (AbsDepDesig * ValueAbsH FValue * OptLens (a, FValue))

  (* Helper type for value abstractions using the FValue type *)
  type FValueAbs = ValueAbs FValue

  (* Well-formedness of a ValueAbsH w.r.t. a predicate on the R type *)
  op [a] valueAbsH_well_formed (r_pred : R -> Bool) (absh : ValueAbsH a) : Bool =
    (* Any Value related by the relation has the correct type *)
    (fa (w,s,v,fv,r)
       r_pred r && absh.abs_rel w s fv v =>
       expandTypeName (r.r_xenv, absh.abs_type_name) = Some (typeOfValue v))
    &&

    (* The combine relation commutes with the abstraction relation (read right
    to left) and any abstraction can always be split into left and right
    portions (read left to right) *)
    (fa (w,s,v,fv)
       absh.abs_rel w s fv v <=>
       (ex (fv1,fv2)
          absh.abs_rel (SplitL::w) s fv1 v &&
          absh.abs_rel (SplitR::w) s fv2 v &&
          absh.abs_combines_to (fv1,fv2) fv
          ))

  (* Well-formedness of a ValueAbs; requires the top-level ValueAbsH and all
  the dependent ValueAbsHs to be well-formed *)
  op [a] valueAbs_well_formed (r_pred : R -> Bool) (abs : ValueAbs a) : Bool =
    valueAbsH_well_formed r_pred abs.1 &&
    (fa (s,v,d,absh,l)
       (d,absh,l) in? abs.2 => valueAbsH_well_formed r_pred absh)

  (* FIXME HERE: abs can only depend on values in its deps list *)


  (***
   *** Scope Abstractions
   ***)

  type ScopeAbs a = List (Identifier * FValueAbs * OptLens (a, FValue))

  op [a] scope_abs_well_formed? (r_pred: R -> Bool) (scabs: ScopeAbs a) : Bool =
    case scabs of
      | [] -> true
      | (x,abs,olens) :: scabs' ->
        valueAbs_well_formed r_pred abs &&
        forall? (fn (x',abs',olens') -> x ~= x' &&
                   optlens_separate? (olens,olens')) scabs'



  (***
   *** Correctness w.r.t. Permissions
   ***)

  (*
  op stmt_correct (r_pred : R -> Bool)
                  (perms_in : PermSetTerm, perms_out : PermSetTerm)
                  (f : List FValue -> List FValue) (m : Monad ()) () : Bool =
    fa (other_held,heap_in,srepr_in,ws)
      ex (heap_out,srepr_out)
        totally_correct
        (fn r -> fn s_in ->
           (* The r_predicate holds *)
           r_pred r &&
           (* srepr_in is a valid representation of s_in *)
           storage_repr_as? (r,ws) (heap_in, perms_in, other_held) (s_in, srepr_in)
           )
        m
        (fn r -> fn s_in -> fn s_out ->
           (* The pre-conditions still hold on the input state *)
           r_pred r &&
           storage_repr_as? (r,ws) (heap_in, perms_in, other_held) (s_in, srepr_in) &&
           (* srepr_out is a valid representation of s_out *)
           storage_repr_as? (r,ws) (heap_out, perms_out, other_held) (s_out, srepr_out) &&
           (* The function f relates my input and output representations *)
           valsForPermSetTerm (r, ws) (srepr_out, perms_out)
           = valsForPermSetTerm (r, ws) (srepr_in, perms_in) &&
           (* The other representations do not change on output *)
           valsForPermSetTerm (r, ws) (srepr_in, other_held)
           = valsForPermSetTerm (r, ws) (srepr_out, other_held)
           )
  *)

end-spec
