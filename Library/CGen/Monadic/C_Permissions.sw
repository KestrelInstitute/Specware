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

  (* A "functional heap" gives values for portions of a pointer, where
  "portions" are given by splittings (see SplittingAlg.sw). Functional heaps
  must be closed under smaller portions as well as under combining portions
  together. *)
  (* FIXME HERE: FHeap also needs a map from FunctionDesignators to functions on
  FValues *)
  type FHeap = { h : Map (ObjectDesignator * Splitting, FValue) |
                  (fa (d,spl1,spl2)
                     splitting_leq (spl1,spl2) => (d,spl2) in? (domain h) =>
                     (d,spl1) in? (domain h)) &&
                  (fa (d,spl1,spl2)
                     splittings_combinable? (spl1,spl2) =>
                     (d,spl1) in? (domain h) => (d,spl2) in? (domain h) =>
                     (d,combine_splittings (spl1,spl2)) in? (domain h))
                  }

  (* Whether two heaps are equal on all pointers in pred *)
  op heaps_equal_on (pred: Pointer -> Bool) (heap1: FHeap, heap2: FHeap) : Bool =
    fa (d, spl) pred (ObjPointer d) => heap1 (d,spl) = heap2 (d,spl)


  (***
   *** Pointer Projections
   ***)

  (* A pointer projection intuitively represents a set of possible ways to
  extract a pointer from a value. These "ways" are zero or more steps of taking
  a struct member and/or taking an array element. For array elements, the
  designator explicitly does not give an index, but instead implicitly
  quantifies over all possible indices. *)
  type PtrProjStep =
     | PPStep_Member Identifier
     | PPStep_Subscript
  type PtrProj = List PtrProjStep

  (* projects_to (pproj, val, ptr) holds iff pproj describes a "way" to project
  the pointer ptr out of the value val. *)
  op projects_to (pproj: PtrProj) (val:Value) (ptr:Pointer) : Bool =
    case (pproj, val) of
      | ([], V_pointer (_, ptr')) ->
        ptr = ptr'
      | ((PPStep_Member memb) :: pproj', V_struct (_, members)) ->
        (case assoc members memb of
           | Some val' ->
             projects_to pproj' val' ptr
           | None -> false)
      | (PPStep_Subscript :: pproj', V_array (_, elems)) ->
        exists? (fn val' -> projects_to pproj' val' ptr) elems


  (***
   *** Value Abstractions
   ***)

  (* A value abstraction relates C values of a given type with some abstract
  type a. This relation is modulo a functional heap, that abstracts the current
  storage. An abstraction can be "split" (see SplittingAlg.sw) into a left and a
  right half, where combines_to relates the possible left- and right-hand sides
  of an abstraction and their combination. An abstraction can also be dependent
  on other abstractions on projections of the abstracted value; a value
  abstraction contains lenses for updating these dependent values in the full
  value being abstracted. These dependencies are formalized in the following way
  so that they do not also talk about the dependencies of the dependencies,
  etc., as this would not be well-founded. *)
  type ValueAbs_NoDeps a =
    {abs_type_name : TypeName,
     abs_rel : Splitting -> FHeap -> a -> Value -> Bool,
     abs_combines_to : a * a -> a -> Bool}
  type ValueAbs a =
    ValueAbs_NoDeps a * List (PtrProj * ValueAbs_NoDeps FValue * OptLens (a, FValue))

  (* Helper type for value abstractions using the FValue type *)
  type FValueAbs = ValueAbs FValue

  (* Well-formedness of a ValueAbs_NoDeps w.r.t. a predicate on the R type *)
  op [a] valueAbsND_well_formed? (r_pred : R -> Bool) (absh : ValueAbs_NoDeps a) : Bool =
    (* Any Value related by the relation has the correct type *)
    (fa (r,w,heap,val,fval)
       r_pred r && absh.abs_rel w heap fval val =>
       expandTypeName (r.r_xenv, absh.abs_type_name) = Some (typeOfValue val))
    &&
    (* The combine relation commutes with the abstraction relation (read right
    to left), and any abstraction can always be split into left and right
    portions (read left to right) *)
    (fa (w,heap,val,fval)
       absh.abs_rel w heap fval val <=>
       (ex (fval1,fval2)
          absh.abs_rel (SplitL::w) heap fval1 val &&
          absh.abs_rel (SplitR::w) heap fval2 val &&
          absh.abs_combines_to (fval1,fval2) fval
          ))

  (* Well-formedness of a ValueAbs *)
  op [a] valueAbs_well_formed? (r_pred : R -> Bool) (abs : ValueAbs a) : Bool =
    (* The top-level ValueAbs_NoDeps in abs is well-formed *)
    valueAbsND_well_formed? r_pred abs.1 &&
    (* All ValueAbs_NoDeps's in the dependencies are well-formed *)
    (fa (s,v,dep)
       dep in? abs.2 => valueAbsND_well_formed? r_pred dep.2) &&
    (* The ValueAbs_NoDeps can only depend on its dependencies *)
    (fa (w,heap1,heap2,val,fval)
       abs.1.abs_rel w heap1 fval val =>
       heaps_equal_on (fn ptr -> exists? (fn (pproj,_,_) ->
                                            projects_to pproj val ptr) abs.2)
                      (heap1, heap2) =>
       abs.1.abs_rel w heap2 fval val)
    (* FIXME HERE: relate the lenses... *)


  (***
   *** Scope Abstractions
   ***)

  type ScopeAbs a = List (Identifier * FValueAbs * OptLens (a, FValue))

  op [a] scopeAbs_well_formed? (r_pred: R -> Bool) (scabs: ScopeAbs a) : Bool =
    case scabs of
      | [] -> true
      | (x,abs,olens) :: scabs' ->
        valueAbs_well_formed? r_pred abs &&
        scopeAbs_well_formed? r_pred scabs' &&
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
