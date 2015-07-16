(* FIXME: top-level documentation *)

C_Permissions qualifying spec
  import C_Predicates
  import /Library/Structures/Data/OptLens
  import /Library/Structures/Data/SeparableView
  import SplittingAlg


  (***
   *** Functional Values
   ***)

  (* To represent C values in logic, we define a universal type for "functional
     values", i.e., values in MetaSlang proper that represent C values. This
     type can be refined to an actual type using finalizeInductiveType *)
  type FValue

  (* FValue includes lists (FIXME: add other ops for FValue_list) *)
  op FValue_list : List FValue -> FValue


  (***
   *** Value Abstractions
   ***)

  (* Trees of storages *)
  type StorageTree = Splitting -> Storage

  (* A storage view is a view of the current storage tree, dependent on the
  current C environment. Defining the type this way, with the R type outside
  SeparableView, means that the separate equality relation of the separable view
  only defines whether two storage views are separate in terms of their views of
  the heap (the storage tree), which is what we want because, intuitively, the C
  environment of type R is read-only. *)
  type StorageView a = R -> SeparableView (StorageTree, a)

  (* An abstraction of a C "object" (e.g., value, pointer, etc.) of type c at
  type a is essentially a relation from elements of type c and the current C
  environment and storage (tree) to some abstract functional type a. Defining
  the type this way means that it can only talk about separation of two
  abstractions with respect to the portions of the heap that they view, not the
  environment or the C objects they use. As with storage views, this is because
  the C heap is the only thing that is modifiable; i.e., when viewing a C value
  or pointer, we only want to talk about the separation w.r.t. how that view
  looks at the heap. Abstractions are also defined to be "splittable", by
  parameterizing them with a splitting set. *)
  (* FIXME: do separate splitting sets have to yield separate storage views? *)
  type CAbstraction (c, a) = SplittingSet -> c -> StorageView a

  (* A value abstraction relates C values with some abstract type a *)
  type ValueAbs a = CAbstraction (Value, a)

  (* Helper type for value abstractions using the FValue type *)
  type FValueAbs = ValueAbs FValue

  (* A value abstraction is said to have a particular C type iff it only relates
  C values of that type. This judgment requires a predicate on the C environment
  type R, to, for example, ensure that the correct struct type tags are in
  scope, or that the correct type definitions have been included. *)
  op [a] value_abs_has_type (r_pred: R -> Bool) (abs: ValueAbs a) (tp_name: TypeName): Bool =
    fa (splset, val, r, fv, stree)
      r_pred r && (abs splset val r).view (stree, fv) =>
      (ex (tp) expandTypeName (r.r_xenv, tp_name) = Some tp
               && valueHasType (val, tp))


  (***
   *** Permission Sets
   ***)

  (* FIXME HERE: documentation! *)

  type PermSet (c, a) =
    {l:List (SplSetExpr * CAbstraction (c, FValue) * Lens (a, FValue)) |
       forall? (fn (_,_,l1) -> forall? (fn (_,_,l2) -> separate_lenses? (l1,l2)) l) l}

  op [a,c] perm_set_relates (perms: PermSet (c, a)) (asgn: SplAssign) (r:R) (stree:StorageTree) (c:c) (a:a) : Bool =
    forall? (fn (spls,abs,l) ->
               (abs (instantiate_splexpr_list asgn spls) c r).view (stree, l.lens_get a)) perms

(*
  op [c1,c2,a,b] abstracts_computation (r_pred: R -> Bool)
                                       (perms_in: PermSet (c1, a))
                                       (perms_out: PermSet (c1*c2, b))
                                       (f: a -> b) (m: c1 -> Monad c2) : Bool =
    fa (a,c1)
      totally_correct
        (fn r -> fn st_in ->
         ex (stree) stree [] = st_in && )
*)

end-spec
