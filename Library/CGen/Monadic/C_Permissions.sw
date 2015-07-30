(* FIXME: top-level documentation *)

C_Permissions qualifying spec
  import C_Predicates
  import /Library/Structures/Data/OptLens
  import /Library/Structures/Data/BisimView
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
  type CAbstraction (c, a) = R -> BisimView (SplTree Storage * SplTree c, a)

  (* An abstraction whose output is still in "C land" and still has a storage *)
  type CToCAbstraction (c1,c2) = CAbstraction (c1, SplTree Storage * SplTree c2)

  (* Two abstractions are separate iff their views are separate for all r's *)
  op [c,a] separate_abstractions? (abs1: CAbstraction (c, a),
                                   abs2: CAbstraction (c, a)) : Bool =
    fa (r) (separate_biviews? (abs1 r, abs2 r))

  (* The constant abstraction that relates, and is separate, from everything *)
  op [c,a] constant_abstraction : CAbstraction (c, a) =
    fn r -> constant_biview

  (* Build an abstraction from a relation R and a preorder on c1 that is used to
  build sep_leq1 for the SplTree c1 type. Note that bv_leq1 does not constrain
  the Storage tree at all: this is because the C abstraction that is composed
  with the returned CToCAbstraction will take care of that. *)
  op [c1,c2] ctoc_abstraction_of_relation (bv_leq:ISet.PreOrder c1,
                                           R: ISet.Relation (c1,c2)) : CToCAbstraction (c1,c2) =
    fn r ->
      {biview = fn ((stree,c1tree),(stree',c2tree)) ->
         stree = stree' && (fa (spl) R (c1tree spl, c2tree spl)),
       bv_leq1 = fn ((stree,c1tree),(stree',c1tree')) ->
         fa (spl) bv_leq (c1tree spl, c1tree' spl),
       bv_leq2 = fn _ -> true}

  (* Conjoin two abstractions *)
  op [c,a] conjoin_abstractions2 (abs1: CAbstraction (c,a),
                                  abs2: CAbstraction (c,a)) : CAbstraction (c,a) =
    fn r -> conjoin_biviews2 (abs1 r, abs2 r)

  (* Conjoin a list of abstractions *)
  op [c,a] conjoin_abstractions (abses: List (CAbstraction (c,a))) : CAbstraction (c,a) =
    fn r -> conjoin_biviews (map (fn abs -> abs r) abses)

  (* FIXME HERE NOW: don't use pre- and post-compose! *)
  (* Compose two abstractions *)
  op [c1,c2,a] compose_abstractions (abs1: CToCAbstraction (c1,c2),
                                     abs2: CAbstraction (c2, a)) : CAbstraction (c1, a) =
    fn r -> compose_biviews (abs1 r, abs2 r)

  (* The abstraction for viewing the first elements of a tree of pairs *)
  op [c1,c2] proj1_abstraction : CToCAbstraction (c1*c2, c1) =
    fn r ->
      {biview = fn ((stree,c12tree),(stree',c1tree)) ->
         fa (spl) stree spl = stree' spl && (c12tree spl).1 = c1tree spl,
       bv_leq1 = fn ((stree1,c12tree1),(stree2,c12tree2)) ->
         fa (spl) (c12tree1 spl).2 = (c12tree2 spl).2,
       bv_leq2 = fn (_,_) -> true}

  (* The abstraction for viewing the second elements of a tree of pairs *)
  op [c1,c2] proj2_abstraction : CToCAbstraction (c1*c2, c2) =
    fn r ->
      {biview = fn ((stree,c12tree),(stree',c2tree)) ->
         fa (spl) stree spl = stree' spl && (c12tree spl).2 = c2tree spl,
       bv_leq1 = fn ((stree1,c12tree1),(stree2,c12tree2)) ->
         fa (spl) (c12tree1 spl).1 = (c12tree2 spl).1,
       bv_leq2 = fn (_,_) -> true}

  (* Tensor two abstractions on the left *)
  op [c1,c2,a] tensor_abstractions_l (abs1: CAbstraction (c1,a),
                                      abs2: CAbstraction (c2,a)) : CAbstraction (c1*c2,a) =
    conjoin_abstractions2 (compose_abstractions (proj1_abstraction, abs1),
                           compose_abstractions (proj2_abstraction, abs2))

  (* Compose an abstraction with a bi-view on a *)
  op [c,a,b] compose_abstraction_with_biview
      (abs: CAbstraction (c,a), sbv: BisimView (a,b)) : CAbstraction (c,b) =
    fn r -> compose_biviews (abs r, sbv)

  (* Tensor two abstractions on the right *)
  op [c,a,b] tensor_abstractions_r (abs1: CAbstraction (c,a),
                                    abs2: CAbstraction (c,b)) : CAbstraction (c,a*b) =
    conjoin_abstractions2 (compose_abstraction_with_biview
                             (abs1, invert_biview proj1_biview),
                           compose_abstraction_with_biview
                             (abs2, invert_biview proj2_biview))


  (***
   *** The Allocation Abstraction
   ***)

  (* True iff map1 has at least all the bindings of map2 *)
  (* FIXME: should this be in the Map spec? *)
  op [a,b] submap? (map1: Map (a,b), map2: Map (a,b)) : Bool =
    fa (x) x in? (domain map1) => map1 x = map2 x

  (* The abstraction that allows storage to be allocated *)
  op [c,a] allocation_abstraction : CAbstraction (c,a) =
    fn _ ->
      {biview = fn _ -> true,
       bv_leq1 = fn ((stree1,ctree1),(stree2,ctree2)) ->
         (* Allocation will not change the non-storage C object *)
         ctree1 = ctree2 &&
         (fa (spl)
            (* stree2 has all the static bindings of stree1 *)
            submap? ((stree1 spl).static, (stree2 spl).static) &&
            (* stree2 has at least as many automatic scopes as stree1 *)
            length (stree1 spl).automatic <= length (stree1 spl).automatic &&
            (* stree2 has all the automatic bindings of stree1 *)
            forall? (fn opt_scopes ->
                       case opt_scopes of
                         | (None, None) -> true
                         | (Some scope1, Some scope2) ->
                           scope1.scope_parent = scope2.scope_parent &&
                           submap? (scope1.scope_bindings, scope2.scope_bindings)
                         | _ -> false)
              (zip ((stree1 spl).automatic,
                    prefix ((stree2 spl).automatic,
                            length (stree1 spl).automatic))) &&
            (* stree2 has at least as many allocated bindings as stree1 *)
            length (stree1 spl).allocated <= length (stree1 spl).allocated &&
            (* All the allocated objects in stree1 are present and equal in stree2 *)
            forall? (fn opt_bindings ->
                       case opt_bindings of
                         | (None,None) -> true
                         | (Some b1, Some b2) -> b1 = b2
                         | _ -> false)
              (zip ((stree1 spl).allocated,
                    prefix ((stree2 spl).allocated,
                            length (stree1 spl).allocated)))),
       bv_leq2 = fn (a1,a2) ->
         (* Allocation will not change the functional object a being viewed *)
         a1 = a2}

  op [c,a] conjoin_alloc_abs (abs: CAbstraction (c,a)) : CAbstraction (c,a) =
    conjoin_abstractions2 (abs, allocation_abstraction)


  (***
   *** Value Abstractions
   ***)

  (* A value abstraction relates C values with some abstract type a. Value
  abstractions are also splittable (see SplittingAlg), which is modeled by
  having them take in a SplittingSet and requiring that different "portions" of
  a value abstraction be separate, though they only need to be separate in their
  views of the storage. *)
  (* FIXME: make this post-condition a little less ugly *)
  type ValueAbs a = {f: SplittingSet -> CAbstraction (Value, a) |
                     fa (splset1,splset2)
                       splitting_sets_compatible? (splset1,splset2) =>
                       separate_abstractions?
                         (compose_abstractions
                            (ctoc_abstraction_of_relation ((=), fn ((),v) -> true),
                             f splset1),
                          compose_abstractions
                            (ctoc_abstraction_of_relation ((=), fn ((),v) -> true),
                             f splset2))}

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

  (* Compose a value abstraction with a bi-view *)
  op [a,b] value_abs_map (sbv: BisimView (a,b)) (vabs: ValueAbs a) : ValueAbs b =
    fn splset -> compose_abstraction_with_biview (vabs splset, sbv)

  (* Use lens to turn a ValueAbs a into a ValueAbs b, where the latter relates C
  values to elements of type b by first applying the lens get function and then
  calling the former to relate C values to type a *)
  op [a,b] value_abs_add_lens (vabs: ValueAbs a, lens: Lens (b,a)) : ValueAbs b =
    value_abs_map (invert_biview (biview_of_lens lens)) vabs

  (* Build a value abstraction that does not look at the heap *)
  op [a] scalar_value_abstraction (R: ISet.Relation (Value,a)) : ValueAbs a =
    fn splset -> fn r ->
      {biview = fn ((stree,vtree),a) -> fa (spl) R (vtree spl, a),
       bv_leq1 = fn ((stree1,vtree1),(stree2,vtree2)) -> stree1 = stree2,
       bv_leq2 = fn _ -> true}

  (* Turn a value abstraction into a constant value abstraction, by adding a
  side condition that prevents the value itself from being modified *)
  op [a] mk_const_value_abs (vabs: ValueAbs a) : ValueAbs a =
    fn splset -> fn r ->
      {biview = (vabs splset r).biview,
       bv_leq1 = fn ((stree1,vtree1),(stree2,vtree2)) ->
         (vabs splset r).bv_leq1 ((stree1,vtree1),(stree2,vtree2)) &&
         vtree1 = vtree2,
       bv_leq2 = (vabs splset r).bv_leq2}


  (***
   *** Value Permissions
   ***)

  (* Value permissions allow viewing a value using a given value abstraction *)
  type ValuePerm a = SplSetExpr * ValueAbs a

  (* Convert a ValuePerm to an abstraction on values *)
  op [a] value_perm_abstraction (asgn: SplAssign) (perm: ValuePerm a) : CAbstraction (Value, a) =
    perm.2 (instantiate_splset_expr asgn perm.1)

  (* Whether vperm maintains equality of the value it looks at (but maybe not
  the parts of the storage the value points to) *)
  op [a] constant_value_perm? (vperm: ValuePerm a) : Bool =
    fa (asgn,r,stree1,vtree1,stree2,vtree2)
      (value_perm_abstraction asgn vperm r).bv_leq1 ((stree1,vtree1),(stree2,vtree2)) =>
      vtree1 = vtree2

  (* mk_const_value_perm does indeed yield a constant value permission. This
  theorem is qualified with CGen so it can be seen by the C generator. *)
  theorem CGen.mk_const_value_perm_constant is [a]
    fa (splexpr,vabs:ValueAbs a)
      true => constant_value_perm? (splexpr, mk_const_value_abs vabs)


  (***
   *** Permission Sets
   ***)

  (* Build the CAbstraction that relates an lvalue to its value(s) *)
  op lvalue_abstraction (lv:LValue) : CAbstraction ((), SplTree Storage * SplTree Value) =
    fn r ->
      {biview = fn ((stree,_),(stree',vtree)) ->
         (* The input and output storages should be the same *)
         stree = stree' &&
         (* Each storage in the tree gives the lvalue the same pointer value, and
            vtree gives the values at that pointer for each spl *)
         (fa (spl,tp,d)
            lvalue_has_result r (stree spl) lv (tp, ObjPointer d) &&
            objectHasValue (stree spl) d (vtree spl)),
       bv_leq1 = fn ((stree1,_),(stree2,_)) ->
         (* Intuitively, this view "looks at" the whole storage tree, so nothing
         about the storage tree is separate; but we also promise not to change the
         pointer value of lv, so we put that in bv_leq as well... *)
         (fa (tp,d,spl)
            lvalue_has_result r (stree1 spl) lv (tp, ObjPointer d) <=>
            lvalue_has_result r (stree2 spl) lv (tp, ObjPointer d)),
       bv_leq2 = fn (vtree1,vtree2) ->
         (* The backwards view "looks at" everything, so bv_leq2 is always true *)
         true}

  (* A permission allows viewing an lvalue with a given value permission *)
  type Perm a = LValue * ValuePerm a

  (* Build the abstraction of a permission by composing the lvalue abstraction,
  which gets the value of an lvalue, with the abstraction for the value perm *)
  op [a] perm_abstraction (asgn: SplAssign) ((lv,perm): Perm a) : CAbstraction ((), a) =
    compose_abstractions (lvalue_abstraction lv,
                          value_perm_abstraction asgn perm)

  (* A permission set is a list of lvalue permissions *)
  type PermSet a = List (Perm a)

  (* Build the abstraction of a permission set by conjoining the abstractions in
  the list *)
  op [a] perm_set_abstraction (asgn: SplAssign) (perms: PermSet a) : CAbstraction ((), a) =
    conjoin_abstractions (map (perm_abstraction asgn) perms)

  (* FIXME HERE NOW: define this!! *)
  op [a] perms_weaker? (perms1: PermSet a, perms2: PermSet a) : Bool


  (***
   *** Perm Sets for Values, Lists of Values, and Optional Values
   ***)

  (* A value permission set is a permission to view the currrent values of some
  lvalues as well as some designated additional value *)
  type ValuePermSet a = PermSet a * ValuePerm a

  (* Build the abstraction for a value perm set by conjoining the value perm
  abstraction with the perm set abstraction *)
  op [a] value_perm_set_abstraction (asgn: SplAssign)
                                    ((perms,vperm): ValuePermSet a) : CAbstraction (Value, a) =
    conjoin_abstractions2
      (compose_abstractions (constant_abstraction, perm_set_abstraction asgn perms),
       vperm.2 (instantiate_splset_expr asgn vperm.1))

  (* An optional value perm is like a value perm set but for optional values;
  the optional value perm can view None if it is None and Some v if it is Some
  vperm for a vperm that can view v *)
  type OptValuePerm a = Option (ValuePerm a)

  (* Build the abstraction for an optional value perm set *)
  op [a] opt_value_perm_abstraction
      (asgn: SplAssign) (opt_vperm: OptValuePerm a) : CAbstraction (Option Value, a) =
    case opt_vperm of
      | Some vperm ->
        compose_abstractions (ctoc_abstraction_of_relation
                                ((=), fn (optv,v) -> optv = Some v),
                              value_perm_abstraction asgn vperm)
      | None ->
        compose_abstractions (ctoc_abstraction_of_relation
                                ((=), fn (optv,_) -> optv = None),
                              constant_abstraction)

  (* A value list perm set is like a value perm but for a list of values, where
  each value in the list is viewed by its corresponding value perm *)
  type ValueListPerm a = List (ValuePerm a)

  (* Return true iff l1 and l2 have the same heads or are both nil *)
  op [a] list_head_eq (l1: List a, l2: List a) : Bool =
    case (l1,l2) of
      | ([], []) -> true
      | (x1::l1', x2::l2') -> x1 = x2

  (* Return true iff l1 and l2 have the same tails or are both nil *)
  op [a] list_tail_eq (l1: List a, l2: List a) : Bool =
    case (l1,l2) of
      | ([], []) -> true
      | (x1::l1', x2::l2') -> l1' = l2'

  (* Build the abstraction for a value list perm set *)
  op [a] value_list_perm_abstraction
      (asgn: SplAssign) (vperms: ValueListPerm a) : CAbstraction (List Value, a) =
    foldr
      (fn (vperm, abs) ->
         conjoin_abstractions2
           (compose_abstractions
              (ctoc_abstraction_of_relation
                 (list_tail_eq,
                  fn (vs, v) -> ex (l) vs = v::l),
               value_perm_abstraction asgn vperm),
            compose_abstractions
              (ctoc_abstraction_of_relation
                 (list_head_eq,
                  fn (vs1,vs2) -> ex (x) vs1 = x::vs2),
               abs)))
      constant_abstraction
      vperms


  (***
   *** Operations on Perms and Perm Sets
   ***)

  (* Map a value perm to another type using a bi-view *)
  op [a,b] val_perm_map (sbv: BisimView (a,b)) ((splexpr,vabs): ValuePerm a) : ValuePerm b =
    (splexpr, value_abs_map sbv vabs)

  (* Map a perm to another type using a bi-view *)
  op [a,b] perm_map (sbv: BisimView (a,b)) ((lv,vperm): Perm a) : Perm b =
    (lv, val_perm_map sbv vperm)

  (* Map a perm set to another type using a bi-view *)
  op [a,b] perm_set_map (sbv: BisimView (a,b)) (perms: PermSet a) : PermSet b =
    map (perm_map sbv) perms


  (***
   *** Proving Abstraction Properties of Computations
   ***)

  type EnvPred = TranslationEnv * FunctionTable -> Bool

  (* This property states that monadic function m can be modeled using function
  f using the given input and output abstractions. Note that it has the
  allocation abstraction built in, meaning that intuitively that all
  computations are allowed to allocate and also that all abstractions being used
  must be compatible with allocation. *)
  op [c1,c2,a,b] abstracts_computation_fun (env_pred : EnvPred)
                                           (abs_in: CAbstraction (c1, a))
                                           (abs_out: CAbstraction (c1*c2, b))
                                           (f: a -> b) (m: c1 -> Monad c2) : Bool =
    let abs_in' = conjoin_alloc_abs abs_in in
    let abs_out' = conjoin_alloc_abs abs_out in
    (* The bv_leq1 of abs_in must be at least as permissive as that of abs_out;
    i.e., any changes allowed at the end of the computation were already allowed
    at the beginning *)
    (fa (r, stree1, stree2, c1tree1, c1tree2, c2tree1, c2tree2)
       (abs_out' r).bv_leq1 ((stree1, spltree_pair (c1tree1, c2tree1)),
                            (stree2, spltree_pair (c1tree2, c2tree2))) =>
       (abs_in' r).bv_leq1 ((stree1, c1tree1), (stree2, c1tree2)))
    &&
    (fa (a,c1)
       totally_correct
       (fn r -> fn st_in ->
          (* Pre-condition: env_pred holds, and there are some splitting trees
          for the input storage and the C input (c1) that are related to the
          functional input (a) via abs_in *)
          (env_pred (r.r_xenv, r.r_functions)) &&
          (ex (stree_in, c1tree_in)
             stree_in [] = st_in && c1tree_in [] = c1 &&
             (abs_in' r).biview ((stree_in, c1tree_in), a)))
       (m c1)
       (fn r -> fn st_in -> fn (st_out, c2) ->
          (* Post-condition: for all splitting trees for the input storage and
          c1 that are related to a via abs_in, there are splitting trees for the
          output storage and the output value (c2) that are related to the
          functional output (f a) via abs_out; further, the changes to the C
          side of things were allowed by abs_in. *)
          (fa (stree_in, c1tree_in)
             (stree_in [] = st_in && c1tree_in [] = c1 &&
                (abs_in' r).biview ((stree_in, c1tree_in), a)) =>
             (ex (stree_out, c2tree_out)
                stree_out [] = st_out && c2tree_out [] = c2 &&
                (abs_out' r).biview ((stree_out, spltree_pair (c1tree_in, c2tree_out)), (f a)) &&
                (abs_in' r).bv_leq1 ((stree_in, c1tree_in), (stree_out, c1tree_in))
                ))))

  (* Same as above, but for computations not computation functions *)
  op [c2,a,b] abstracts_computation (env_pred : EnvPred)
                                    (abs_in: CAbstraction ((), a))
                                    (abs_out: CAbstraction (c2, b))
                                    (f: a -> b) (m: Monad c2) : Bool =
    abstracts_computation_fun
      env_pred abs_in
      (compose_abstractions (proj2_abstraction, abs_out))
      f
      (fn _ -> m)

  (* Abstraction for expressions, which are Value computations; this states
  that, for all splitting assignments, the given function abstracts the given
  Value computation using the abstractions obtained from the given perms *)
  op [a,b] abstracts_expression (env_pred : EnvPred)
                                (perms_in: PermSet a)
                                (perms_out: PermSet a, vperms_out: ValuePerm b)
                                (f: a -> b) (m: Monad Value) : Bool =
    fa (asgn)
      abstracts_computation
        env_pred
        (perm_set_abstraction asgn perms_in)
        (tensor_abstractions_r
           (compose_abstractions (constant_abstraction,
                                  perm_set_abstraction asgn perms_out),
            value_perm_abstraction asgn vperms_out))
        (fn x -> (x, f x))
        m

  (* Abstraction for statements, which are unit computations *)
  op [a,b] abstracts_statement (env_pred : EnvPred)
                               (perms_in: PermSet a) (perms_out: PermSet b)
                               (f: a -> b) (m: Monad ()) : Bool =
    fa (asgn)
      abstracts_computation
        env_pred
        (perm_set_abstraction asgn perms_in)
        (perm_set_abstraction asgn perms_out)
        f
        m

  (* Abstraction for statements that optionally do a return at the end *)
  op [a,b] abstracts_ret_statement (env_pred : EnvPred) (perms_in: PermSet a)
                                   (perms_out: PermSet b * OptValuePerm b)
                                   (f: a -> b) (m: Monad ()) : Bool =
    fa (asgn)
      abstracts_computation
        env_pred
        (perm_set_abstraction asgn perms_in)
        (conjoin_abstractions2
           (opt_value_perm_abstraction asgn perms_out.2,
            compose_abstractions
              (ctoc_abstraction_of_relation ((fn _ -> true), (fn _ -> true)),
               perm_set_abstraction asgn perms_out.1)))
        f
        (catchReturns m)

  (* Abstraction for C functions, which are computation functions mapping lists
  of values, for the arguments, to an optional return value. Note that perms_out
  gives abstractions for viewing the same values that were passed in as
  arguments, *not* the values of those variables at the end of the function *)
  op [a,b] abstracts_c_function (env_pred : EnvPred) (perms_in: List (ValuePerm a))
                                (perms_out: List (ValuePerm b) * OptValuePerm b)
                                (f: a -> b)
                                (m: CFunction) : Bool =
    fa (asgn)
      abstracts_computation_fun
        env_pred
        (value_list_perm_abstraction asgn perms_in)
        (tensor_abstractions_l
           (value_list_perm_abstraction asgn perms_out.1,
            opt_value_perm_abstraction asgn perms_out.2))
        f
        m

  (* Abstraction for top-level function declarations: states that m generates a
  single function binding of name to a function that is abstracted by f *)
  op [a,b] abstracts_c_function_decl
      (env_pred : EnvPred) (perms_in: List (ValuePerm a))
      (perms_out: List (ValuePerm b) * OptValuePerm b)
      (f: a -> b)
      (retTypeName: TypeName, name: Identifier, paramDecls : ParameterList)
      (m: XUMonad ()) : Bool =
    let pre =
      (fn incls -> fn funtab -> fn xenv_in -> env_pred (xenv_in, funtab))
    in
    xu_computation_correct
      pre
      m
      (fn incls -> fn funtab -> fn xenv_in -> fn (xenv_out, (opt_obj, ())) ->
         case opt_obj of
           | Some ([(name', ObjFile_Function (cfun, funtp))]) ->
             name' = name &&
             xu_computation_has_value
               (incls, funtab, xenv_out)
               (evalCFunctionType (retTypeName, paramDecls)) funtp &&
             xenv_out.xenv_funtypes name = Some funtp &&
             abstracts_c_function (fn _ -> true) perms_in perms_out f cfun
           | _ -> false)


end-spec
