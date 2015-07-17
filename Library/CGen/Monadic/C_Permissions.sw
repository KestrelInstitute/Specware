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
   *** Abstraction Relations
   ***)

  (* FIXME HERE: update the documentation! *)

  (* Splitting trees *)
  type SplTree a = Splitting -> a

  op [a,b] spltree_pair (tree1: SplTree a, tree2: SplTree b) : SplTree (a * b) =
    fn spl -> (tree1 spl, tree2 spl)

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
  type CAbstraction (c, a) = R -> SeparableBiView (SplTree Storage * SplTree c, a)

  (* Two abstractions are separate iff their views are separate for all r's *)
  op [c,a] separate_abstractions? (abs1: CAbstraction (c, a),
                                   abs2: CAbstraction (c, a)) : Bool =
    fa (r) (separate_biviews? (abs1 r, abs2 r))

  (* The trivial abstraction that relates, and is separate, from everything *)
  op [c,a] trivial_abstraction : CAbstraction (c, a) =
    fn r -> {biview = fn _ -> true, sep_eq1 = (=), sep_eq2 = (=)}

  (* The trivial abstraction is separate from all other abstractions *)
  theorem trivial_abstraction_separate is [c,a]
    fa (abs:CAbstraction (c, a)) separate_abstractions? (trivial_abstraction, abs)

  (* Combine two abstractions, only allowing the view to work if the two
  abstractions are separate. We use the rst_closure for the sep_eq relations to
  make sure they are equivalences even if abs1 and abs2 are not separate, but
  this is equivalent to relCompose (abs1.sep_eq,abs2.sep_eq) if they are. *)
  op [c,a] combine_abstractions2 (abs1: CAbstraction (c,a),
                                  abs2: CAbstraction (c,a)) : CAbstraction (c,a) =
    fn r ->
      {biview = fn (c,a) ->
         separate_biviews? (abs1 r, abs2 r) &&
         iSetInter ((abs1 r).biview, (abs2 r).biview) (c,a),
       sep_eq1 = rst_closure (relCompose ((abs1 r).sep_eq1, (abs2 r).sep_eq1)),
       sep_eq2 = rst_closure (relCompose ((abs1 r).sep_eq2, (abs2 r).sep_eq2))}

  (* Combine a list of abstractions *)
  op [c,a] combine_abstractions (abses: List (CAbstraction (c,a))) : CAbstraction (c,a) =
    foldr combine_abstractions2 trivial_abstraction abses

  (* FIXME: documentation! *)
  op [c1,c2,a,b] abstracts_computation (r_pred: R -> Bool)
                                       (abs_in: CAbstraction (c1, a))
                                       (abs_out: CAbstraction (c1*c2, b))
                                       (f: a -> b) (m: c1 -> Monad c2) : Bool =

    (* The sep_eq1 of abs_in must be at least as strong as that of abs_out;
    i.e., more things can be separate from us at the end of the computation *)
    (fa (r, stree1, stree2, c1tree1, c1tree2, c2tree1, c2tree2)
       (abs_in r).sep_eq1 ((stree1, c1tree1), (stree2, c1tree2)) =>
       (abs_out r).sep_eq1 ((stree1, spltree_pair (c1tree1, c2tree1)),
                            (stree2, spltree_pair (c1tree2, c2tree2))))
    &&
    (fa (a,c1)
       totally_correct
       (fn r -> fn st_in ->
          r_pred r &&
          (ex (stree_in, c1tree_in)
             stree_in [] = st_in && c1tree_in [] = c1 &&
             (abs_in r).biview ((stree_in, c1tree_in), a)))
       (m c1)
       (fn r -> fn st_in -> fn (st_out, c2) ->
          (fa (stree_in, c1tree_in)
             (stree_in [] = st_in && c1tree_in [] = c1 &&
                (abs_in r).biview ((stree_in, c1tree_in), a)) =>
             (ex (stree_out, c2tree_out)
                stree_out [] = st_out && c2tree_out [] = c2 &&
                (abs_out r).biview ((stree_out, spltree_pair (c1tree_in, c2tree_out)), (f a)) &&
                (abs_out r).sep_eq1 ((stree_in, spltree_pair (c1tree_in, c2tree_out)),
                                     (stree_out, spltree_pair (c1tree_in, c2tree_out)))
                ))))


  (* A value abstraction relates C values with some abstract type a. Value
  abstractions are also splittable (see SplittingAlg), which is modeled by
  having them take in a SplittingSet and requiring that different "portions" of
  a value abstraction be separate. *)
  type ValueAbs a = {f: SplittingSet -> CAbstraction (Value, a) |
                     fa (splset1,splset2)
                       splitting_sets_compatible? (splset1,splset2) =>
                       separate_abstractions? (f splset1, f splset2)}

  (* Helper type for value abstractions using the FValue type *)
  type FValueAbs = ValueAbs FValue

  (* A value abstraction is said to have a particular C type iff it only relates
  C values of that type. This judgment requires a predicate on the C environment
  type R, to, for example, ensure that the correct struct type tags are in
  scope, or that the correct type definitions have been included. *)
  op [a] value_abs_has_type (r_pred: R -> Bool) (abs: ValueAbs a) (tp_name: TypeName): Bool =
    fa (splset, stree, vtree, r, fv)
      r_pred r && (abs splset r).biview ((stree, vtree), fv) =>
      (ex (tp) expandTypeName (r.r_xenv, tp_name) = Some tp
               && (fa (spl) valueHasType (vtree spl, tp)))


  (***
   *** Permission Sets
   ***)

  (* FIXME HERE: documentation! *)

  type ObjPerm a = LValue * SplSetExpr * ValueAbs a

  op [a] obj_perm_to_abstraction (asgn: SplAssign) (perm: ObjPerm a) : CAbstraction ((), a) =
    fn r ->
      {biview =
         (fn ((stree, _), a) ->
            ex (tp,d,vtree)
              (* Each storage in the tree gives the lvalue the same pointer
              value, and vtree gives the values at that pointer for each spl *)
              (fa (spl)
                 lvalue_has_result r (stree spl) perm.1 (tp, ObjPointer d) &&
                 objectHasValue (stree spl) d (vtree spl))
              &&
              (* The value abstraction relates the storages+values to a *)
              (perm.3 (instantiate_splset_expr asgn perm.2) r).biview ((stree, vtree), a)),
       sep_eq1 =
         (fn ((stree1, _), (stree2, _)) ->
            (* The pointer values of the lvalue must be equal in both trees *)
            (fa (tp,d,spl)
               lvalue_has_result r (stree1 spl) perm.1 (tp, ObjPointer d) <=>
               lvalue_has_result r (stree2 spl) perm.1 (tp, ObjPointer d))
            &&
            (* The value abstraction must see the values+storages as sep_eq *)
            (fa (vtree1,vtree2)
               (fa (spl)
                  expression_has_value r (stree1 spl) (E_lvalue perm.1) (vtree1 spl)
                  &&
                  expression_has_value r (stree2 spl) (E_lvalue perm.1) (vtree2 spl)) =>
               (perm.3 (instantiate_splset_expr asgn perm.2) r).sep_eq1
                 ((stree1, vtree1), (stree2, vtree2)))),
       sep_eq2 =
         (fn (a1, a2) ->
            (perm.3 (instantiate_splset_expr asgn perm.2) r).sep_eq2 (a1, a2))
         }


  type PermSet a = List (ObjPerm a)

  op [a] perm_set_to_abstraction (asgn: SplAssign) (perms: PermSet a) : CAbstraction ((), a) =
    combine_abstractions (map (obj_perm_to_abstraction asgn) perms)

end-spec
