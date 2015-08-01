(* FIXME: top-level documentation *)

C_Permissions qualifying spec
  import C_Predicates
  import /Library/Structures/Data/OptLens
  import /Library/Structures/Data/BisimView
  import SplittingAlg


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

  (* The trivial abstraction that relates, and is separate, from everything *)
  op [c,a] trivial_abstraction : CAbstraction (c, a) =
    fn r -> trivial_biview

  (* Conjoin two abstractions *)
  op [c,a] conjoin_abstractions (abs1: CAbstraction (c,a),
                                  abs2: CAbstraction (c,a)) : CAbstraction (c,a) =
    fn r -> conjoin_biviews (abs1 r, abs2 r)

  (* Conjoin a list of abstractions *)
  op [c,a] conjoin_abstractionsN (abses: List (CAbstraction (c,a))) : CAbstraction (c,a) =
    fn r -> conjoin_biviewsN (map (fn abs -> abs r) abses)

  (* Compose two abstractions *)
  op [c1,c2,a] compose_abstractions (abs1: CToCAbstraction (c1,c2),
                                     abs2: CAbstraction (c2, a)) : CAbstraction (c1, a) =
    fn r -> compose_biviews (abs1 r, abs2 r)

  (* The strength preorder lifted to C abstractions *)
  op [c,a] abstraction_weaker? (abs1: CAbstraction (c,a),
                                abs2: CAbstraction (c,a)) : Bool =
    fa (r) biview_weaker? (abs1 r, abs2 r)

  (* Build the C-to-C abstraction that applies relations pointwise *)
  op [c1,c2] pointwise_ctoc_abs (R: ISet.Relation (c1,c2), leq1: ISet.PreOrder c1,
                                 leq2: ISet.PreOrder c2) : CToCAbstraction (c1,c2) =
    fn r ->
      {biview = (fn ((stree1,c1tree),(stree2,c2tree)) ->
                   stree1 = stree2 && (fa (spl) R (c1tree spl, c2tree spl))),
       bv_leq1 = (fn ((stree1,c1tree1),(stree2,c1tree2)) ->
                    stree1 = stree2 &&
                    (fa (spl) leq1 (c1tree1 spl, c1tree2 spl))),
       bv_leq2 = (fn ((stree1,c2tree1),(stree2,c2tree2)) ->
                    stree1 = stree2 &&
                    (fa (spl) leq2 (c2tree1 spl, c2tree2 spl)))}

  (* The abstraction for viewing the first elements of a tree of pairs *)
  op [c1,c2] proj1_abstraction : CToCAbstraction (c1*c2, c1) =
    pointwise_ctoc_abs ((fn ((c1,c2),c1') -> c1=c1'),
                        (fn ((c11,c21),(c12,c22)) -> c21 = c22),
                        (fn _ -> true))

  (* The abstraction for viewing the second elements of a tree of pairs *)
  op [c1,c2] proj2_abstraction : CToCAbstraction (c1*c2, c2) =
    pointwise_ctoc_abs ((fn ((c1,c2),c2') -> c2=c2'),
                        (fn ((c11,c21),(c12,c22)) -> c11 = c12),
                        (fn _ -> true))

  (* Take the cross product of two abstractions on the left *)
  op [c1,c2,a] abstractions_cross_l (abs1: CAbstraction (c1,a),
                                     abs2: CAbstraction (c2,a)) : CAbstraction (c1*c2,a) =
    conjoin_abstractions (compose_abstractions (proj1_abstraction, abs1),
                          compose_abstractions (proj2_abstraction, abs2))

  (* Compose an abstraction with a bi-view on the a type *)
  op [c,a,b] compose_abstraction_with_biview
      (abs: CAbstraction (c,a), sbv: BisimView (a,b)) : CAbstraction (c,b) =
    fn r -> compose_biviews (abs r, sbv)

  (* Take the cross product of two abstractions on the left *)
  op [c,a,b] abstractions_cross_r (abs1: CAbstraction (c,a),
                                   abs2: CAbstraction (c,b)) : CAbstraction (c,a*b) =
    conjoin_abstractions (compose_abstraction_with_biview
                             (abs1, invert_biview proj1_biview),
                           compose_abstraction_with_biview
                             (abs2, invert_biview proj2_biview))

  (* Map an abstraction to only look at the global scope *)
  op [c,a] abs_in_global_scope (abs: CAbstraction (c,a)) : CAbstraction (c,a) =
    fn r -> abs (r << {r_curScope = GlobalScope})


  (***
   *** Value Abstractions
   ***)

  (* A splittable C abstraction is a CAbstraction that is splittable. This is
  modeled as a function from splitting sets to C abstractions such that separate
  (aka "compatible") splitting sets map to separate abstractions. *)
  type SplittableAbs (c,a) = {f: SplittingSet -> CAbstraction (c, a) |
                                fa (splset1,splset2)
                                  splitting_sets_compatible? (splset1,splset2) =>
                                  separate_abstractions? (f splset1, f splset2)}

  type UnitAbs a = SplittableAbs ((), a)
  type ValueAbs a = SplittableAbs (Value, a)

  (* Conjoin two splittable abstractions *)
  op [c,a] conjoin_splittable_abstractions2 (abs1:SplittableAbs (c,a),
                                             abs2:SplittableAbs (c,a)) : SplittableAbs (c,a) =
    fn spl -> conjoin_abstractions (abs1 spl, abs2 spl)

  (* A value abstraction is said to have a particular C type iff it only relates
  C values of that type. This judgment requires a predicate on the C environment
  type R, to, for example, ensure that the correct struct type tags are in
  scope, or that the correct type definitions have been included. *)
  op [a] value_abs_has_type (r_pred: R -> Bool) (abs: ValueAbs a) (tp_name: TypeName): Bool =
    fa (splset, stree, vtree, r, fv)
      r_pred r && (abs splset r).biview ((stree, vtree), fv) =>
      (ex (tp) expandTypeName (r.r_xenv, tp_name) = Some tp
               && (fa (spl) valueHasType (vtree spl, tp)))

  (* Compose a splittable abstraction with a bi-view *)
  op [c,a,b] splittable_abs_compose (vabs: SplittableAbs (c,a),
                                     sbv: BisimView (a,b)) : SplittableAbs (c,b) =
    fn splset -> compose_abstraction_with_biview (vabs splset, sbv)

  (* Use lens to turn a SplittableAbs a into a SplittableAbs b, where the latter
  relates C values to elements of type b by first applying the lens get function
  and then calling the former to relate C values to type a *)
  op [c,a,b] splittable_abs_compose_lens (abs: SplittableAbs (c,a),
                                          lens: Lens (b,a)) : SplittableAbs (c,b) =
    splittable_abs_compose (abs, invert_biview (biview_of_lens lens))

  op [a,b] value_abs_add_lens : ValueAbs a * Lens (b,a) -> ValueAbs b =
    splittable_abs_compose_lens

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
   *** Implicational Permissions
   ***)

  (* An implicational permission is an implicational bisimilarity view in the
  same way that a C abstraction is a (regular) bisimilarity view *)
  type ImplPerm c = R -> ImplBisimView (SplTree Storage * SplTree c)

  (* The empty impl perm *)
  op [c] trivial_impl_perm : ImplPerm c = fn _ -> []

  (* Conjoin two impl perms *)
  op [c] conjoin_impl_perms (impl1: ImplPerm c,impl2: ImplPerm c) : ImplPerm c =
    fn r -> impl1 r ++ impl2 r

  (* Compose an abstraction with an impl perm *)
  op [c1,c2] compose_abs_impl_perm (abs: CToCAbstraction (c1,c2),
                                    impl: ImplPerm c2) : ImplPerm c1 =
    fn r -> compose_rel_impl_biview (abs r).biview (impl r)

  (* Pre-compose an impl perm with a relation R, which is applied pointwise *)
  op [c1,c2] compose_rel_impl_perm (R:ISet.Relation (c1,c2),
                                    impl: ImplPerm c2) : ImplPerm c1 =
    fn r -> (compose_rel_impl_biview
               (fn ((stree1,c1tree),(stree2,c2tree)) ->
                   stree1 = stree2 && (fa (spl) R (c1tree spl, c2tree spl)))
               (impl r))


  (***
   *** Permission Evaluations
   ***)

  (* The result of evaluating a permission or permission set *)
  type PermEval (c,a) = CAbstraction (c, a) * ImplPerm c

  (* The trivial perm eval *)
  op [c,a] trivial_perm_eval : PermEval (c,a) =
    (trivial_abstraction, trivial_impl_perm)

  (* Evaluate a splittable abstraction with splitting set expression *)
  op [c,a] eval_splittable_abs (asgn: SplAssign)
                               (splexpr: SplSetExpr,
                                abs: SplittableAbs (c,a)) : PermEval (c,a) =
    (abs (instantiate_splset_expr asgn splexpr), trivial_impl_perm)

  (* Turn an ImplPerm into a PermEval *)
  op [c,a] eval_impl_perm (impl: ImplPerm c) : PermEval (c,a) =
    (trivial_abstraction, impl)

  (* Conjoin two permission evaluation results *)
  op [c,a] conjoin_perm_evals (ev1:PermEval (c,a),
                               ev2:PermEval (c,a)) : PermEval (c,a) =
    (conjoin_abstractions (ev1.1,ev2.1),
     conjoin_impl_perms (ev1.2, ev2.2))

  (* Conjoin N permission evaluation results *)
  op [c,a] conjoin_perm_evalsN (evs:List (PermEval (c,a))) : PermEval (c,a) =
    foldr conjoin_perm_evals trivial_perm_eval evs

  (* Turn a PermEval into a CAbstraction *)
  op [c,a] abs_of_perm_eval (ev: PermEval (c,a)) : CAbstraction (c,a) =
    fn r -> conjoin_biview_impl (ev.1 r, ev.2 r)

  (* Compose an abstraction with a PermEval *)
  op [c1,c2,a] compose_abs_perm_eval (abs:CToCAbstraction (c1,c2),
                                      ev:PermEval (c2,a)) : PermEval (c1,a) =
    (compose_abstractions (abs, ev.1),
     compose_abs_impl_perm (abs, ev.2))

  (* The strength preorder for permission evaluation results, which maps to the
  C abstraction strength preorder of all abstractions obtained from the related
  permission evaluation results after possibly conjoining with another abs *)
  op [c,a] perm_eval_weaker? : ISet.PreOrder (PermEval (c,a)) =
    fn (ev1,ev2) ->
      (fa (abs) abstraction_weaker? (abs_of_perm_eval
                                       (conjoin_perm_evals
                                          (ev1, (abs, trivial_impl_perm))),
                                     abs_of_perm_eval
                                       (conjoin_perm_evals
                                          (ev2, (abs, trivial_impl_perm)))))


  (***
   *** Building PermEvals for List and Option Types
   ***)

  (* Relate two lists iff both are empty or their heads and tails are related by
  R1 and R2, respectively *)
  op [a] list_head_tail_rel (R1:ISet.EndoRelation a,
                             R2:ISet.EndoRelation (List a)) : ISet.EndoRelation (List a) =
    fn (l1,l2) ->
      case (l1,l2) of
        | ([],[]) -> true
        | (x1::l1',x2::l2') -> R1 (x1,x2) && R2 (l1',l2')
        | _ -> false

  (* Build the abstraction that can only look at the head of a list *)
  op [c] list_head_ctoc_abs : CToCAbstraction (List c, c) =
    pointwise_ctoc_abs ((fn (l,x) -> length l > 0 && head l = x),
                        list_head_tail_rel ((fn _ -> true), (=)),
                        (fn _ -> true))

  (* Build the abstraction that can only look at the tail of a list *)
  op [c] list_tail_ctoc_abs : CToCAbstraction (List c, List c) =
    pointwise_ctoc_abs ((fn (l1,l2) -> length l1 > 0 && tail l1 = l2),
                        list_head_tail_rel ((=), (fn _ -> true)),
                        (fn _ -> true))

  (* Turn a list of PermEvals into a PermEval for lists *)
  op [c,a] list_perm_eval (evs: List (PermEval (c,a))) : PermEval (List c, a) =
    case evs of
      | [] -> trivial_perm_eval
      | ev::evs' ->
        conjoin_perm_evals (compose_abs_perm_eval (list_head_ctoc_abs, ev),
                            compose_abs_perm_eval (list_tail_ctoc_abs,
                                                   list_perm_eval evs'))

  (* Build the abstraction that can only look at a Some option type *)
  op [c] opt_some_ctoc_abs : CToCAbstraction (Option c, c) =
    pointwise_ctoc_abs ((fn (opt_x,x) -> opt_x = Some x),
                        (fn (opt_x1,opt_x2) ->
                           opt_x1 = opt_x2 || (some? opt_x1 && some? opt_x2)),
                        (fn _ -> true))

  (* Build the abstraction that can only look at a None option type *)
  op [c,a] opt_none_abs : CAbstraction (Option c, a) =
    fn r ->
      {biview = (fn ((stree,opttree),a) -> fa (spl) opttree spl = None),
       bv_leq1 = (=),
       bv_leq2 = (=)}

  (* Turn an optional PermEval into a PermEval for the option type *)
  op [c,a] opt_perm_eval (ev_opt: Option (PermEval (c,a))) : PermEval (Option c,a) =
    case ev_opt of
      | Some ev -> compose_abs_perm_eval (opt_some_ctoc_abs, ev)
      | None -> (opt_none_abs, trivial_impl_perm)

  op [c,a,b] perm_eval_pair_r (ev1: PermEval (c,a),
                               ev2: PermEval (c,b)) : PermEval (c,a * b) =
    (abstractions_cross_r (ev1.1, ev2.1),
     conjoin_impl_perms (ev1.2, ev2.2))

  op [c1,c2,a] perm_eval_pair_l (ev1: PermEval (c1,a),
                                 ev2: PermEval (c2,a)) : PermEval (c1*c2, a) =
    conjoin_perm_evals (compose_abs_perm_eval (proj1_abstraction, ev1),
                        compose_abs_perm_eval (proj2_abstraction, ev2))

  (* Turn a PermEval with unit C type into one with an arbitrary C type c, by
  pre-composing with an abstraction that ignores the c *)
  op [c,a] lift_unit_perm_eval (ev: PermEval ((), a)) : PermEval (c, a) =
    compose_abs_perm_eval (pointwise_ctoc_abs
                             ((fn _ -> true), (=), (fn _ -> true)),
                           ev)


  (***
   *** Permissions and Permission Sets
   ***)

  type Perm a =
    | LVPerm (LValue * SplSetExpr * ValueAbs a)
    | LVIPerm (LValue * ImplPerm Value)
    | StPerm (SplSetExpr * UnitAbs a)
    | StIPerm (ImplPerm ())

  type PermSet a = List (Perm a)

  (* Use a lens for viewing b at a to turn a Perm a into a Perm b *)
  op [a,b] perm_add_lens (perm: Perm a, lens: Lens (b,a)) : Perm b =
    case perm of
      | LVPerm (lv, splexpr, vabs) ->
        LVPerm (lv, splexpr,
                splittable_abs_compose_lens (vabs, lens))
      | LVIPerm (lv, impl) -> LVIPerm (lv, impl)
      | StPerm (splexpr, uabs) ->
        StPerm (splexpr,
                splittable_abs_compose_lens (uabs, lens))
      | StIPerm impl -> StIPerm impl

  (* Use a lens for viewing b at a to turn a PermSet a into a PermSet b *)
  op [a,b] perm_set_add_lens (perms: PermSet a, lens: Lens (b,a)) : PermSet b =
    map (fn p -> perm_add_lens (p, lens)) perms

  (* Build the CAbstraction that relates an lvalue to its value(s) *)
  op lvalue_abstraction (lv:LValue) : CToCAbstraction ((), Value) =
    fn r ->
      {biview = fn ((stree,_),(stree',vtree)) ->
         (* The input and output storages should be the same *)
         stree = stree' &&
         (* Each storage in the tree gives the lvalue the same pointer value, and
            vtree gives the values at that pointer for each spl *)
         (fa (spl)
            (ex (tp,d)
               lvalue_has_result r (stree spl) lv (tp, ObjPointer d) &&
               objectHasValue (stree spl) d (vtree spl))),
       bv_leq1 = fn ((stree1,_),(stree2,_)) ->
         (* This view could modify anything, because who knows what could be
         considered "dependent" on this lvalue; restrictions on what can be
         changed come when we compose lvalue_abstraction with other abstractions
         on the value that is seen by the biview *)
         true,
       bv_leq2 = fn (vtree1,vtree2) ->
         (* The backwards view "looks at" everything, so bv_leq2 is always true *)
         true}

  (* Evaluate a permission to a PermEval *)
  op [a] eval_perm (asgn: SplAssign) (perm: Perm a) : PermEval ((), a) =
    case perm of
      | LVPerm (lv, splexpr, vabs) ->
        compose_abs_perm_eval (lvalue_abstraction lv,
                               eval_splittable_abs asgn (splexpr, vabs))
      | LVIPerm (lv, impl) ->
        compose_abs_perm_eval (lvalue_abstraction lv, eval_impl_perm impl)
      | StPerm (splexpr, uabs) -> eval_splittable_abs asgn (splexpr, uabs)
      | StIPerm impl -> eval_impl_perm impl

  (* Evaluate a permission set *)
  op [a] eval_perm_set (asgn: SplAssign) (perms: PermSet a) : PermEval ((),a) =
    conjoin_perm_evalsN (map (eval_perm asgn) perms)

  (* The strength preorder for permission sets *)
  op [a] perm_set_weaker? : ISet.PreOrder (PermSet a) =
    fn (perms1,perms2) ->
      (fa (asgn) perm_eval_weaker? (eval_perm_set asgn perms1,
                                    eval_perm_set asgn perms2))


  (***
   *** Perm Sets for Inputs and Output of C Functions
   ***)

  (* Permissions for a value *)
  type ValPerm a =
    | ValPerm (SplSetExpr * ValueAbs a)
    | ValIPerm (ImplPerm Value)

  (* Permissions for the storage used to pass to and from functions *)
  type FunStPerm a =
    | FunStPerm (SplSetExpr * UnitAbs a)
    | FunStIPerm (ImplPerm ())

  (* Zero or more permissions for each value in a list, along *)
  type ArgListPerms a = List (FunStPerm a) * List (List (ValPerm a))

  (* Build a perm from a value perm and an lvalue *)
  op [a] perm_of_val_perm (lv:LValue) (vperm: ValPerm a) : Perm a =
    case vperm of
      | ValPerm (splexpr, vabs) -> LVPerm (lv, splexpr, vabs)
      | ValIPerm impl -> LVIPerm (lv, impl)

  (* Build a perm from a function storage perm *)
  op [a] perm_of_fun_st_perm (fstperm: FunStPerm a) : Perm a =
    case fstperm of
      | FunStPerm (splexpr, uabs) -> StPerm (splexpr, uabs)
      | FunStIPerm impl -> StIPerm impl

  (* Build a perm set from a list of function storage perm *)
  op [a] perm_set_of_fun_st_perms (fstperms: List (FunStPerm a)) : PermSet a =
    map perm_of_fun_st_perm fstperms

  (* Use a lens for viewing b at a to turn a ValPerm a into a ValPerm b *)
  op [a,b] val_perm_add_lens (vperm: ValPerm a, lens: Lens (b,a)) : ValPerm b =
    case vperm of
      | ValPerm (splexpr, vabs) ->
        ValPerm (splexpr, splittable_abs_compose_lens (vabs, lens))
      | ValIPerm impl -> ValIPerm impl

  (* Compose a list of value perms with a lens *)
  op [a,b] val_perms_add_lens (vperms: List (ValPerm a),
                               lens: Lens (b,a)) : List (ValPerm b) =
    map (fn vperm -> val_perm_add_lens (vperm, lens)) vperms

  (* Evaluate a value permission *)
  op [a] eval_val_perm (asgn: SplAssign) (vperm: ValPerm a) : PermEval (Value,a) =
    case vperm of
      | ValPerm (splexpr, vabs) -> eval_splittable_abs asgn (splexpr, vabs)
      | ValIPerm impl -> eval_impl_perm impl

  (* Evaluate a list of value permissions *)
  op [a] eval_val_perms (asgn: SplAssign) (vperms: List (ValPerm a)) : PermEval (Value,a) =
    conjoin_perm_evalsN (map (eval_val_perm asgn) vperms)

  (* Evaluate a function storage permission *)
  op [a] eval_fun_st_perm (asgn: SplAssign) (fstperm: FunStPerm a) : PermEval ((), a) =
    eval_perm asgn (perm_of_fun_st_perm fstperm)

  op [a] eval_arg_list_perms (asgn: SplAssign)
                             (perms: ArgListPerms a) : PermEval (List Value,a) =
    (conjoin_perm_evals
       (lift_unit_perm_eval (eval_perm_set asgn (perm_set_of_fun_st_perms perms.1)),
        list_perm_eval (map (eval_val_perms asgn) perms.2)))

  (* Construct a perm set from an ArgListPerms and a list of variable names;
  note that the value permissions are all made into constant value permissions,
  because function arguments are not allowed to be modified in its body *)
  op [a] perm_set_of_arg_perms (perms: ArgListPerms a, vars: List Identifier |
                                  equiLong (perms.2, vars)) : PermSet a =
    perm_set_of_fun_st_perms perms.1 ++
    flatten (map (fn (var,vperms) ->
                    map (perm_of_val_perm (LV_ident var)) vperms)
               (zip (vars,perms.2)))

  (* Permissions for a return value of a function *)
  type RetValPerm a = Option (List (ValPerm a))

  op [a] eval_ret_val_perm (asgn: SplAssign)
                           (rvperm: RetValPerm a) : PermEval (Option Value, a) =
    opt_perm_eval (mapOption (eval_val_perms asgn) rvperm)


  (***
   *** Proving Abstraction Properties of Computations
   ***)

  type EnvPred = TranslationEnv * FunctionTable -> Bool

  (* This property states that monadic function m can be modeled using function
  f using the given input and output abstractions. Note that it has the
  automatic allocation abstraction built in, meaning intuitively that all
  computations are allowed to allocate stack frames and also that all
  abstractions being used must be compatible with allocation of stack frames. *)
  op [c1,c2,a,b] abstracts_computation_fun (env_pred : EnvPred)
                                           (abs_in: CAbstraction (c1, a))
                                           (abs_out: CAbstraction (c1*c2, b))
                                           (f: a -> b) (m: c1 -> Monad c2) : Bool =
    (* The bv_leq1 of abs_in must be at least as permissive as that of abs_out;
    i.e., any changes allowed at the end of the computation were already allowed
    at the beginning *)
    (fa (r, stree1, stree2, c1tree1, c1tree2, c2tree1, c2tree2)
       (abs_out r).bv_leq1 ((stree1, spltree_pair (c1tree1, c2tree1)),
                            (stree2, spltree_pair (c1tree2, c2tree2))) =>
       (abs_in r).bv_leq1 ((stree1, c1tree1), (stree2, c1tree2)))
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
             (abs_in r).biview ((stree_in, c1tree_in), a)))
       (m c1)
       (fn r -> fn st_in -> fn (st_out, c2) ->
          (* Post-condition: for all splitting trees for the input storage and
          c1 that are related to a via abs_in, there are splitting trees for the
          output storage and the output value (c2) that are related to the
          functional output (f a) via abs_out; further, the changes to the C
          side of things were allowed by abs_in. *)
          (fa (stree_in, c1tree_in)
             (stree_in [] = st_in && c1tree_in [] = c1 &&
                (abs_in r).biview ((stree_in, c1tree_in), a)) =>
             (ex (stree_out, c2tree_out)
                stree_out [] = st_out && c2tree_out [] = c2 &&
                (abs_out r).biview ((stree_out, spltree_pair (c1tree_in, c2tree_out)), (f a)) &&
                (abs_in r).bv_leq1 ((stree_in, c1tree_in), (stree_out, c1tree_in))
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
                                (perms_out: PermSet a, vperms_out: List (ValPerm b))
                                (f: a -> b) (m: Monad Value) : Bool =
    fa (asgn)
      abstracts_computation
        env_pred
        (abs_of_perm_eval (eval_perm_set asgn perms_in))
        (abs_of_perm_eval
           (perm_eval_pair_r
              (lift_unit_perm_eval (eval_perm_set asgn perms_out),
               conjoin_perm_evalsN (map (eval_val_perm asgn) vperms_out))))
        (fn x -> (x, f x))
        m

  (* Abstraction for statements, which are unit computations *)
  op [a,b] abstracts_statement (env_pred : EnvPred)
                               (perms_in: PermSet a)
                               (perms_out: PermSet b)
                               (f: a -> b) (m: Monad ()) : Bool =
    fa (asgn)
      abstracts_computation
        env_pred
        (abs_of_perm_eval (eval_perm_set asgn perms_in))
        (abs_of_perm_eval (eval_perm_set asgn perms_out))
        f
        m

  (* Abstraction for statements that optionally do a return at the end *)
  op [a,b] abstracts_ret_statement (env_pred : EnvPred)
                                   (perms_in: PermSet a)
                                   (perms_out: PermSet b, ret_perms: RetValPerm b)
                                   (f: a -> b) (m: Monad ()) : Bool =
    fa (asgn)
      abstracts_computation
        env_pred
        (abs_of_perm_eval (eval_perm_set asgn perms_in))
        (abs_of_perm_eval
           (conjoin_perm_evals
              (lift_unit_perm_eval (eval_perm_set asgn perms_out),
               eval_ret_val_perm asgn ret_perms)))
        f
        (catchReturns m)

  (* Abstraction for C functions, which are computation functions mapping lists
  of values, for the arguments, to an optional return value. Note that perms_out
  gives abstractions for viewing the same values that were passed in as
  arguments, *not* the values of those variables at the end of the function *)
  op [a,b] abstracts_c_function (env_pred : EnvPred)
                                (perms_in: ArgListPerms a)
                                (perms_out: ArgListPerms b * RetValPerm b)
                                (f: a -> b)
                                (m: CFunction) : Bool =
    fa (asgn)
      abstracts_computation_fun
        env_pred
        (abs_of_perm_eval (eval_arg_list_perms asgn perms_in))
        (abs_of_perm_eval
           (perm_eval_pair_l
              (eval_arg_list_perms asgn perms_out.1,
               eval_ret_val_perm asgn perms_out.2)))
        f
        m

  (* Abstraction for top-level function declarations: states that m generates a
  single function binding of name to a function that is abstracted by f *)
  op [a,b] abstracts_c_function_decl
      (env_pred : EnvPred) (perms_in: ArgListPerms a)
      (perms_out: ArgListPerms b * RetValPerm b)
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


  (***
   *** Permissions for Allocation and Deallocation
   ***)

  (* True iff map1 has at least all the bindings of map2 *)
  (* FIXME: should this be in the Map spec? *)
  op [a,b] submap? (map1: Map (a,b), map2: Map (a,b)) : Bool =
    fa (x) x in? (domain map1) => map1 x = map2 x

  (* Lift preorders on the components of a storage to a preorder on storage trees *)
  op storage_preorder (leq_static: ISet.PreOrder NamedStorage,
                       leq_automatic: ISet.PreOrder (List (Option LocalScope)),
                       leq_allocated: ISet.PreOrder AllocatedStorage)
      : ISet.PreOrder (SplTree Storage * SplTree ()) =
    fn ((stree1,_), (stree2,_)) ->
      (fa (spl)
         leq_static ((stree1 spl).static, (stree2 spl).static) &&
         leq_automatic ((stree1 spl).automatic, (stree2 spl).automatic) &&
         leq_allocated ((stree1 spl).allocated, (stree2 spl).allocated))

  (* Permission allowing allocation of automatic storage, i.e., stack frames *)
  op auto_allocation_perm : ImplPerm () =
    fn _ ->
      always_impl_biview
        (storage_preorder
           ((=),
            (fn (auto1,auto2) ->
               (* auto2 has at least as many automatic scopes as auto1 *)
               length auto1 <= length auto2 &&
               (* auto2 has all the automatic bindings of auto1 *)
               forall? (fn opt_scopes ->
                          case opt_scopes of
                            | (None, None) -> true
                            | (Some scope1, Some scope2) ->
                              scope1.scope_parent = scope2.scope_parent &&
                              submap? (scope1.scope_bindings, scope2.scope_bindings)
                            | _ -> false)
                 (zip (auto1, prefix (auto2, length auto1)))),
            (=)))

  (* Permission allowing malloc *)
  op malloc_allocation_perm : ImplPerm () =
    fn _ ->
      always_impl_biview
        (storage_preorder
           ((=),(=),
            (fn (alloc1,alloc2) ->
              (* alloc2 has at least as many allocated bindings as alloc1 *)
              length alloc1 <= length alloc2 &&
              (* All the allocated objects in alloc1 are present and equal in alloc2 *)
              forall? (fn opt_bindings ->
                         case opt_bindings of
                           | (None,None) -> true
                           | (Some b1, Some b2) -> b1 = b2
                           | _ -> false)
                (zip (alloc1, prefix (alloc2, length alloc1))))))

  (*  *)
  op equal_except_current_scope (r:R,leq:ISet.PreOrder (Option LocalScope))
      : ISet.PreOrder (SplTree Storage * SplTree ()) =
    storage_preorder
      ((=),
       (fn (auto1,auto2) ->
         (* The same number of automatic scopes have been allocated *)
         length auto1 = length auto2 &&
         (* All automatic scopes but the current are the same *)
         (fa (i)
            i < length auto1 =>
            LocalScope (ScopeID i) ~= r.r_curScope =>
            auto1 @ i = auto2 @ i) &&
         (* The current scopes are related by leq, if there is a current scope *)
         (fa (i)
            LocalScope (ScopeID i) ~= r.r_curScope =>
            i < length auto1 =>
            leq (auto1 @ i, auto2 @ i))),
       (=))

  (* Permission for deallocating the current stack frame assuming that we have
  permission to arbitrarily modify any variable in vars *)
  op current_frame_dealloc_perm (vars: List Identifier) : ImplPerm () =
    fn r ->
      [{implview_ant =
          equal_except_current_scope
            (r,
             fn (scope1_opt,scope2_opt) ->
               case (scope1_opt,scope2_opt) of
                 | (None,None) -> true
                 | (Some scope1, Some scope2) ->
                   fa (x) x nin? vars =>
                   scope1.scope_parent = scope2.scope_parent &&
                   scope1.scope_bindings x = scope2.scope_bindings x
                 | _ -> false),
        implview_succ =
          equal_except_current_scope
            (r,
             fn (scope1_opt,scope2_opt) ->
               case (scope1_opt,scope2_opt) of
                 | (None,None) -> true
                 | (Some scope1, Some scope2) ->
                   fa (x) x nin? vars =>
                   scope1.scope_parent = scope2.scope_parent &&
                   scope1.scope_bindings x = scope2.scope_bindings x
                 | (Some _, None) -> true
                 | (None, Some _) -> false)}]


end-spec
