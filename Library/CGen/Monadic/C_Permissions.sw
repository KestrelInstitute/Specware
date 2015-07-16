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

  (* FIXME HERE: update the documentation! *)

  (* Trees of storages *)
  type StorageTree = Splitting -> Storage

  (* A storage view is a view of the current storage tree, dependent on the
  current C environment. Defining the type this way, with the R type outside
  SeparableView, means that the separate equality relation of the separable view
  only defines whether two storage views are separate in terms of their views of
  the heap (the storage tree), which is what we want because, intuitively, the C
  environment of type R is read-only. *)
  (*
  type StorageView a = R -> SeparableBiView (StorageTree, a)
  *)

  (* An abstraction of a C "object" (e.g., value, pointer, etc.) of type c at
  type a is essentially a relation from elements of type c and the current C
  environment and storage (tree) to some abstract functional type a. Defining
  the type this way means that it can only talk about separation of two
  abstractions with respect to the portions of the heap that they view, not the
  environment or the C objects they use. As with storage views, this is because
  the C heap is the only thing that is modifiable; i.e., when viewing a C value
  or pointer, we only want to talk about the separation w.r.t. how that view
  looks at the heap. *)
  (* FIXME: update this documentation! *)
  type CAbstraction (c, a) = R -> SeparableBiView (Splitting -> (Storage * c), a)

  (* A value abstraction relates C values with some abstract type a. Value
  abstractions are also splittable, as they take in a SplittingSet. *)
  (* FIXME HERE: separate splitting sets should give separate abstractions *)
  type ValueAbs a = SplittingSet -> CAbstraction (Value, a)

  (* Helper type for value abstractions using the FValue type *)
  type FValueAbs = ValueAbs FValue

  (* A value abstraction is said to have a particular C type iff it only relates
  C values of that type. This judgment requires a predicate on the C environment
  type R, to, for example, ensure that the correct struct type tags are in
  scope, or that the correct type definitions have been included. *)
  (*
  op [a] value_abs_has_type (r_pred: R -> Bool) (abs: ValueAbs a) (tp_name: TypeName): Bool =
    fa (splset, vtree, r, fv, stree)
      r_pred r && (abs splset vtree r).biview (stree, fv) =>
      (ex (tp) expandTypeName (r.r_xenv, tp_name) = Some tp
               && (fa (spl) valueHasType (vtree spl, tp)))
  *)


  (***
   *** Permission Sets
   ***)

  (* FIXME HERE: documentation! *)

  type ObjPerm a = LValue * SplSetExpr * ValueAbs a

  op [a] obj_perm_to_abstraction (asgn: SplAssign) (perm: ObjPerm a) : CAbstraction ((), a) =
    fn r ->
      {biview =
         (fn (tree, a) ->
            ex (tp,d,vtree)
              (* Each storage in the tree gives the lvalue the same pointer
              value, and vtree gives the values at that pointer for each spl *)
              (fa (spl)
                 lvalue_has_result r (tree spl).1 perm.1 (tp, ObjPointer d) &&
                 objectHasValue (tree spl).1 d (vtree spl))
              &&
              (* The value abstraction relates the storages+values to a *)
              (perm.3 (instantiate_splset_expr asgn perm.2) r).biview
                ((fn spl -> ((tree spl).1, vtree spl)), a)),
       sep_eq1 =
         (fn (tree1, tree2) ->
            (* The pointer values of the lvalue must be equal in both trees *)
            (fa (tp,d,spl)
               lvalue_has_result r (tree1 spl).1 perm.1 (tp, ObjPointer d) <=>
               lvalue_has_result r (tree2 spl).1 perm.1 (tp, ObjPointer d))
            &&
            (* The value abstraction must see the values+storages as sep_eq *)
            (fa (vtree1,vtree2)
               (fa (spl)
                  expression_has_value r (tree1 spl).1 (E_lvalue perm.1) (vtree1 spl)
                  &&
                  expression_has_value r (tree2 spl).1 (E_lvalue perm.1) (vtree2 spl)) =>
               (perm.3 (instantiate_splset_expr asgn perm.2) r).sep_eq1
                 ((fn spl -> ((tree1 spl).1, vtree1 spl)),
                  (fn spl -> ((tree2 spl).1, vtree2 spl))))),
       sep_eq2 =
         (fn (a1, a2) ->
            (perm.3 (instantiate_splset_expr asgn perm.2) r).sep_eq2 (a1, a2))
         }


  type PermSet a = List (ObjPerm a)

(*
  op [a] perm_set_to_abstraction (asgn: SplAssign) (perms: PermSet a) : CAbstraction ((), a) =
    fn () -> fn r ->
*)

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
