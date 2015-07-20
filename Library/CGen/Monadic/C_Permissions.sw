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

  op [a,b] spltree_map (f: a -> b) (tree: SplTree a) : SplTree b =
    fn spl -> f (tree spl)

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
    fn r -> trivial_biview

  (* Build an abstraction from a relation *)
  op [c,a] abstraction_of_relation (R: ISet.Relation (SplTree c,a)) : CAbstraction (c,a) =
    fn r -> biview_of_relation (fn ((_,ctree),a) -> R (ctree, a))

  (* Conjoin two abstractions *)
  op [c,a] conjoin_abstractions2 (abs1: CAbstraction (c,a),
                                  abs2: CAbstraction (c,a)) : CAbstraction (c,a) =
    fn r -> conjoin_biviews2 (abs1 r, abs2 r)

  (* Conjoin a list of abstractions *)
  op [c,a] conjoin_abstractions (abses: List (CAbstraction (c,a))) : CAbstraction (c,a) =
    fn r -> conjoin_biviews (map (fn abs -> abs r) abses)

  (* Compose two abstractions *)
  op [c1,c2,a] compose_abstractions (abs1: CAbstraction (c1, SplTree c2),
                                     abs2: CAbstraction (c2, a)) : CAbstraction (c1, a) =
    fn r -> compose_biviews (biview_post_compose (abs1 r) (fn p -> p.2), abs2 r)

  (* Pre-compose an abstraction with a projection function *)
  op [c1,c2,a] pre_compose_abstraction (f: c1 -> c2)
                                       (abs: CAbstraction (c2,a)) : CAbstraction (c1,a) =
    fn r -> biview_pre_compose (fn (stree,c1tree) ->
                                  (stree,spltree_map f c1tree)) (abs r)


  (***
   *** Proving Abstraction Properties of Computations
   ***)

  (* This property states that monadic function m can be modeled using function
  f using the given input and output abstractions *)
  op [c1,c2,a,b] abstracts_computation_fun (r_pred: R -> Bool)
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

  (* Same as above, but for computations not computation functions *)
  op [c2,a,b] abstracts_computation (r_pred: R -> Bool)
                                    (abs_in: CAbstraction ((), a))
                                    (abs_out: CAbstraction (c2, b))
                                    (f: a -> b) (m: Monad c2) : Bool =
    abstracts_computation_fun
      r_pred abs_in
      (pre_compose_abstraction (fn ((),c2) -> c2) abs_out)
      f
      (fn _ -> m)


  (***
   *** Value Abstractions
   ***)

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

  type ObjPerm a = SplSetExpr * ValueAbs a

  (* Build the CAbstraction that relates an lvalue to its value(s) *)
  op lvalue_abstraction (lv:LValue) : CAbstraction ((), SplTree Value) =
    fn r ->
      {biview = fn ((stree,_),vtree) ->
         (* Each storage in the tree gives the lvalue the same pointer value, and
            vtree gives the values at that pointer for each spl *)
         (fa (spl,tp,d)
            lvalue_has_result r (stree spl) lv (tp, ObjPointer d) &&
            objectHasValue (stree spl) d (vtree spl)),
       sep_eq1 = fn ((stree1,_),(stree2,_)) ->
         (* Intuitively, this view "looks at" the whole storage tree, so nothing
         about the storage tree is separate; but we also promise not to change the
         pointer value of lv, so we put that in sep_eq as well... *)
         (fa (tp,d,spl)
            lvalue_has_result r (stree1 spl) lv (tp, ObjPointer d) <=>
            lvalue_has_result r (stree2 spl) lv (tp, ObjPointer d)),
       sep_eq2 = fn (vtree1,vtree2) ->
         (* The backwards view "looks at" everything, so sep_eq2 doesn't care *)
         true}

  (* Convert an ObjPerm to an abstraction on values *)
  op [a] obj_perm_abstraction (asgn: SplAssign) (perm: ObjPerm a) : CAbstraction (Value, a) =
    perm.2 (instantiate_splset_expr asgn perm.1)


  type Perm a = LValue * ObjPerm a

  op [a] perm_abstraction (asgn: SplAssign) ((lv,perm): Perm a) : CAbstraction ((), a) =
    compose_abstractions (lvalue_abstraction lv,
                          obj_perm_abstraction asgn perm)


  type PermSet a = List (Perm a)

  op [a] perm_set_abstraction (asgn: SplAssign) (perms: PermSet a) : CAbstraction ((), a) =
    conjoin_abstractions (map (perm_abstraction asgn) perms)


  type ValuePermSet a = PermSet a * ObjPerm a

  op [a] value_perm_set_abstraction (asgn: SplAssign)
                                    ((perms,operm): ValuePermSet a) : CAbstraction (Value, a) =
    conjoin_abstractions2
      (pre_compose_abstraction (fn _ -> ()) (perm_set_abstraction asgn perms),
       operm.2 (instantiate_splset_expr asgn operm.1))

  type OptValuePermSet a = PermSet a * Option (ObjPerm a)

  op [a] opt_value_perm_set_abstraction
      (asgn: SplAssign) ((perms,opt_operm): OptValuePermSet a) : CAbstraction (Option Value, a) =
    case opt_operm of
      | Some operm ->
        compose_abstractions (abstraction_of_relation
                                (fn (optv_tree,vtree) ->
                                   fa (spl) optv_tree spl = Some (vtree spl)),
                              value_perm_set_abstraction asgn (perms,operm))
      | None ->
        compose_abstractions (abstraction_of_relation
                                (fn (optv_tree,_) -> fa (spl) optv_tree spl = None),
                              perm_set_abstraction asgn perms)


  type ValueListPermSet a = PermSet a * List (ObjPerm a)

  op [a] value_list_perm_set_abstraction
      (asgn: SplAssign) ((perms,operms): ValueListPermSet a) : CAbstraction (List Value, a) =
    foldr
      (fn (operm, abs) ->
         conjoin_abstractions2
           (compose_abstractions
              (abstraction_of_relation (fn (vs_tree, vtree) ->
                                          fa (spl) ex (l) vs_tree spl = (vtree spl)::l),
               obj_perm_abstraction asgn operm),
            compose_abstractions
              (abstraction_of_relation (fn (vs_tree1, vs_tree2) ->
                                          fa (spl) ex (x) vs_tree1 spl = x::(vs_tree2 spl)),
               abs)))
      (compose_abstractions
         (abstraction_of_relation (fn (vs_tree,_) -> fa (spl) vs_tree spl = []),
          perm_set_abstraction asgn perms))
      operms

end-spec
