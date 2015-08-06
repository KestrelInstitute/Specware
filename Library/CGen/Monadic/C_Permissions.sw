(* FIXME: top-level documentation *)

C_Permissions qualifying spec
  import C_Predicates
  import /Library/Structures/Data/BisimView
  import SplittingAlg


  (***
   *** Abstraction Relations
   ***)

  (* FIXME: update the documentation! *)

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

  (* Invert the direction of an abstraction *)
  op [c1,c2] invert_abstraction (abs: CToCAbstraction (c1,c2)) : CToCAbstraction (c2,c1) =
    fn r -> invert_biview (abs r)

  (* The strength preorder lifted to C abstractions *)
  op [c,a] abstraction_weaker? (abs1: CAbstraction (c,a),
                                abs2: CAbstraction (c,a)) : Bool =
    fa (r) biview_weaker? (abs1 r, abs2 r)

  (* Build a C-to-C abstraction from a biview from c1 to c2, "allowing"
  arbitrary updates to the storage *)
  op [c1,c2] ctoc_abs_of_view (bv: BisimView (c1,c2)) : CToCAbstraction (c1,c2) =
    fn r ->
      {biview = (fn ((stree1,c1tree),(stree2,c2tree)) ->
                   stree1 = stree2 &&
                   (fa (spl) bv.biview (c1tree spl, c2tree spl))),
       bv_leq1 = (fn ((stree1,c1tree1),(stree2,c1tree2)) ->
                    (fa (spl) bv.bv_leq1 (c1tree1 spl, c1tree2 spl))),
       bv_leq2 = (fn ((stree1,c2tree1),(stree2,c2tree2)) ->
                    (fa (spl) bv.bv_leq2 (c2tree1 spl, c2tree2 spl)))}

  (* Build a C-to-C abstraction from a lens *)
  op [c1,c2] ctoc_abs_of_lens (lens: Lens (c1,c2)) : CToCAbstraction (c1,c2) =
    ctoc_abs_of_view (biview_of_lens lens)

  (* Build a C-to-C abstraction from an option lens *)
  op [c1,c2] ctoc_abs_of_opt_lens (optlens: OptLens (c1,c2)) : CToCAbstraction (c1,c2) =
    ctoc_abs_of_view (biview_of_opt_lens optlens)

  (* The abstraction for viewing the first elements of a tree of pairs *)
  op [c1,c2] proj1_abstraction : CToCAbstraction (c1*c2, c1) =
    ctoc_abs_of_view proj1_biview

  (* The abstraction for viewing the second elements of a tree of pairs *)
  op [c1,c2] proj2_abstraction : CToCAbstraction (c1*c2, c2) =
    ctoc_abs_of_view proj2_biview

  (* Take the cross product of two abstractions on the left *)
  op [c1,c2,a] abstractions_cross_l (abs1: CAbstraction (c1,a),
                                     abs2: CAbstraction (c2,a)) : CAbstraction (c1*c2,a) =
    conjoin_abstractions (compose_abstractions (proj1_abstraction, abs1),
                          compose_abstractions (proj2_abstraction, abs2))

  (* Compose an abstraction with a biview on the a type. It turns out to be most
  useful to have the biview inverted, since it is generally used as a view of
  the right-hand side type of the result; i.e., type b is usually "bigger". *)
  op [c,a,b] compose_abstraction_with_biview
      (abs: CAbstraction (c,a), sbv: BisimView (b,a)) : CAbstraction (c,b) =
    fn r -> compose_biviews (abs r, invert_biview sbv)

  (* Take the cross product of two abstractions on the left *)
  op [c,a,b] abstractions_cross_r (abs1: CAbstraction (c,a),
                                   abs2: CAbstraction (c,b)) : CAbstraction (c,a*b) =
    conjoin_abstractions (compose_abstraction_with_biview (abs1, proj1_biview),
                          compose_abstraction_with_biview (abs2, proj2_biview))

  (* Map an abstraction to only look at the global scope *)
  op [c,a] abs_in_global_scope (abs: CAbstraction (c,a)) : CAbstraction (c,a) =
    fn r -> abs (r << {r_curScope = GlobalScope})


  (***
   *** Value Abstractions
   ***)

  (* A splittable C abstraction is a CAbstraction that is splittable. This is
  modeled as a function from splitting sets to C abstractions such that
  combining splittings sets yields a conjoined abstraction. *)
  type SplittableAbs (c,a) = {f: SplTree (CAbstraction (c, a)) |
                                fa (spl)
                                  conjoin_abstractions (f (SplitL::spl),
                                                        f (SplitR::spl)) = f spl}

  type UnitAbs a = SplittableAbs ((), a)
  type ValueAbs a = SplittableAbs (Value, a)

  (* Conjoin the abstractions in abs for the splittings in the splitting set *)
  op [c,a] abs_of_spl_abs (splset: SplittingSet,
                           abs: SplittableAbs (c,a)) : CAbstraction (c,a) =
    foldr (fn (spl,rest) ->
             conjoin_abstractions (abs spl, rest)) trivial_abstraction splset

  (* Compose an abstraction with a splittable abstractions *)
  op [c1,c2,a] compose_splittable_abstraction (abs:CToCAbstraction (c1,c2),
                                               sabs:SplittableAbs (c2,a)) : SplittableAbs (c1,a) =
    fn spl -> compose_abstractions (abs, sabs spl)

  (* Conjoin two splittable abstractions *)
  op [c,a] conjoin_splittable_abstractions (abs1:SplittableAbs (c,a),
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

  (* Compose a splittable abstraction with a bi-view on the output type *)
  op [c,a,b] splittable_abs_add_view (vabs: SplittableAbs (c,a),
                                      bv: BisimView (b,a)) : SplittableAbs (c,b) =
    fn splset -> compose_abstraction_with_biview (vabs splset, bv)

  op [a,b] value_abs_add_view : ValueAbs a * BisimView (b,a) -> ValueAbs b =
    splittable_abs_add_view
  op [a,b] unit_abs_add_view : UnitAbs a * BisimView (b,a) -> UnitAbs b =
    splittable_abs_add_view


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
  op [c1,c2] compose_rel_impl_perm (R:Relation (c1,c2),
                                    impl: ImplPerm c2) : ImplPerm c1 =
    fn r -> (compose_rel_impl_biview
               (fn ((stree1,c1tree),(stree2,c2tree)) ->
                   stree1 = stree2 && (fa (spl) R (c1tree spl, c2tree spl)))
               (impl r))


  (***
   *** Permissions
   ***)

  (* A gneric permission is a splittable abstraction + implicational perm *)
  type CPermission (c,a) = SplittableAbs (c, a) * ImplPerm c
  type CValPerm a = CPermission (Value, a)
  type CUnitPerm a = CPermission ((), a)

  (* The trivial permission *)
  op [c,a] trivial_perm : CPermission (c,a) =
    ((fn spl -> trivial_abstraction), trivial_impl_perm)

  op [c,a] conjoin_perms (perm1: CPermission (c,a),
                          perm2: CPermission (c,a)) : CPermission (c,a) =
    (conjoin_splittable_abstractions (perm1.1, perm2.1),
     conjoin_impl_perms (perm1.2, perm2.2))

  (* Evaluate a splittable abstraction with splitting set expression *)
  op [c,a] perm_of_spl_abs (abs: SplittableAbs (c,a)) : CPermission (c,a) =
    (abs, trivial_impl_perm)

  (* Turn an ImplPerm into a permission *)
  op [c,a] perm_of_impl_perm (impl: ImplPerm c) : CPermission (c,a) =
    ((fn spl -> trivial_abstraction), impl)

  (* Turn a CPermission into a CAbstraction *)
  op [c,a] abs_of_perm (splset: SplittingSet,
                        perm: CPermission (c,a)) : CAbstraction (c,a) =
    fn r -> conjoin_biview_impl (abs_of_spl_abs (splset, perm.1) r,
                                 perm.2 r)

  (* Compose an abstraction with a permission *)
  op [c1,c2,a] compose_abs_perm (abs:CToCAbstraction (c1,c2),
                                 perm:CPermission (c2,a)) : CPermission (c1,a) =
    (compose_splittable_abstraction (abs, perm.1),
     compose_abs_impl_perm (abs, perm.2))

  (* Compose a permission with a lens *)
  op [c,a,b] cperm_add_lens (perm: CPermission (c,b),
                             lens: Lens (a,b)) : CPermission (c,a) =
    (splittable_abs_add_view (perm.1, biview_of_lens lens), perm.2)

  (* Compose a permission with the trivial biview, meaning it is ignored *)
  op [c,a,b] cperm_ignore (perm: CPermission (c,b)) : CPermission (c,a) =
    (splittable_abs_add_view (perm.1, trivial_biview), perm.2)

  (* The strength preorder for permissions, which maps to the C abstraction
  strength preorder of all abstractions obtained from the related permissions
  after possibly conjoining with another abs *)
  op [c,a] cperm_weaker? : PreOrder (CPermission (c,a)) =
    fn (perm1,perm2) ->
      (fa (spl_abs,splset)
         abstraction_weaker? (abs_of_perm
                                (splset,
                                 conjoin_perms
                                   (perm1, perm_of_spl_abs spl_abs)),
                              abs_of_perm
                                (splset,
                                 conjoin_perms
                                   (perm2, perm_of_spl_abs spl_abs))))

  (***
   *** Permission Evaluations
   ***)

  (* A PermEval is a permisson where we have already passed in a splitting set
  to the splittable abstraction *)
  type PermEval (c, a) = CAbstraction (c, a) * ImplPerm c

  op [c,a] trivial_perm_eval : PermEval (c,a) =
    (trivial_abstraction, trivial_impl_perm)

  op [c,a] conjoin_perm_evals (ev1: PermEval (c,a),
                               ev2: PermEval (c,a)) : PermEval (c,a) =
    (conjoin_abstractions (ev1.1, ev2.1),
     conjoin_impl_perms (ev1.2, ev2.2))

  (* Conjoin N permission evaluation results *)
  op [c,a] conjoin_perm_evalsN (evs:List (PermEval (c,a))) : PermEval (c,a) =
    foldr conjoin_perm_evals trivial_perm_eval evs

  (* Compose an abstraction with a permission evaluation *)
  op [c1,c2,a] compose_abs_perm_eval (abs:CToCAbstraction (c1,c2),
                                      ev:PermEval (c2,a)) : PermEval (c1,a) =
    (compose_abstractions (abs, ev.1),
     compose_abs_impl_perm (abs, ev.2))

  (* Turn a PermEval into a CAbstraction *)
  op [c,a] abs_of_perm_eval (ev: PermEval (c,a)) : CAbstraction (c,a) =
    fn r -> conjoin_biview_impl (ev.1 r, ev.2 r)

  (* Evaluate a permission *)
  op [c,a] eval_cperm (asgn:SplAssign, splexpr:SplSetExpr)
                      (perm:CPermission (c,a)) : PermEval (c,a) =
    (abs_of_spl_abs (instantiate_splset_expr asgn splexpr, perm.1), perm.2)

  (* The strength preorder for permission evaluations, which maps to the C
  abstraction strength preorder of all abstractions obtained from the related
  permission evaluations after possibly conjoining with another abs *)
  op [c,a] perm_eval_weaker? : PreOrder (PermEval (c,a)) =
    fn (ev1,ev2) ->
      (fa (abs) abstraction_weaker? (abs_of_perm_eval
                                       (conjoin_perm_evals
                                          (ev1, (abs, trivial_impl_perm))),
                                     abs_of_perm_eval
                                       (conjoin_perm_evals
                                          (ev2, (abs, trivial_impl_perm)))))


  (***
   *** Building Permission Evaluations for List and Option Types
   ***)

  (* Build the abstraction that can only look at the head of a list *)
  op [c] list_head_ctoc_abs : CToCAbstraction (List c, c) =
    ctoc_abs_of_opt_lens list_head_opt_lens

  (* Build the abstraction that can only look at the tail of a list *)
  op [c] list_tail_ctoc_abs : CToCAbstraction (List c, List c) =
    ctoc_abs_of_opt_lens list_tail_opt_lens

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
    ctoc_abs_of_opt_lens option_opt_lens

  (* Build the abstraction that can only look at a None *)
  op [c,a] opt_none_abs : CAbstraction (Option c, a) =
    fn r ->
      {biview = (fn ((stree,opttree),a) -> fa (spl) opttree spl = None),
       bv_leq1 = (=),
       bv_leq2 = (=)}

  (* Turn an optional Permission into a Permission for the option type *)
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
  pre-composing with the unit lens on c *)
  op [c,a] lift_unit_perm_eval (ev: PermEval ((), a)) : PermEval (c, a) =
    compose_abs_perm_eval (ctoc_abs_of_lens unit_lens, ev)


  (***
   *** Value and Storage Permissions
   ***)

  (* Permissions for just the storage *)
  type StPerm a =
    | StPerm (SplSetExpr * CPermission ((), a))

  (* Add a view to a storage permission *)
  op [a,b] st_perm_add_lens (stperm: StPerm a, lens: Lens (b,a)) : StPerm b =
    case stperm of
      | StPerm (splexpr, cperm) ->
        StPerm (splexpr, cperm_add_lens (cperm, lens))

  (* Compose a list of unit perms with a bv *)
  op [a,b] st_perms_add_lens (stperms: List (StPerm a),
                              lens: Lens (b,a)) : List (StPerm b) =
    map (fn stperm -> st_perm_add_lens (stperm, lens)) stperms

  (* Evaluate a storage permission *)
  op [a] eval_st_perm (asgn: SplAssign) (stperm: StPerm a) : PermEval ((),a) =
    case stperm of
      | StPerm (splexpr, cperm) ->
        eval_cperm (asgn, splexpr) cperm

  op [a] eval_st_perms (asgn: SplAssign) (stperms: List (StPerm a)) : PermEval ((),a) =
    conjoin_perm_evalsN (map (eval_st_perm asgn) stperms)

  (* The strength preorder for storage permissions *)
  op [a] st_perm_weaker? : PreOrder (StPerm a) =
    fn (stperm1,stperm2) ->
      (fa (asgn) perm_eval_weaker? (eval_st_perm asgn stperm1,
                                    eval_st_perm asgn stperm2))

  (* Permissions for a value *)
  type ValPerm a =
    | ValPerm (SplSetExpr * CValPerm a)
    | ValEqPerm (SplSetExpr * CValPerm a * LValue)

  (* Use a lens from b to a to turn a ValPerm a into a ValPerm b *)
  op [a,b] val_perm_add_lens (vperm: ValPerm a, lens: Lens (b,a)) : ValPerm b =
    case vperm of
      | ValPerm (splexpr, cperm) ->
        ValPerm (splexpr, cperm_add_lens (cperm, lens))
      | ValEqPerm (splexpr, cperm, lv) ->
        ValEqPerm (splexpr, cperm_add_lens (cperm, lens), lv)

  (* Compose a list of value perms with a bv *)
  op [a,b] val_perms_add_lens (vperms: List (ValPerm a),
                               lens: Lens (b,a)) : List (ValPerm b) =
    map (fn vperm -> val_perm_add_lens (vperm, lens)) vperms

  (* The CAbstraction that relates an lvalue to its value, if any *)
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

  (* Evaluate a value permission *)
  op [a] eval_val_perm (asgn: SplAssign) (vperm: ValPerm a) : PermEval (Value,a) =
    case vperm of
      | ValPerm (splexpr, cperm) -> eval_cperm (asgn, splexpr) cperm
      | ValEqPerm (splexpr, cperm, lv) ->
        eval_cperm (asgn, splexpr)
          (compose_abs_perm (compose_abstractions
                               (invert_abstraction (lvalue_abstraction lv),
                                lvalue_abstraction lv),
                             cperm))

  (* Evaluate a list of value permissions *)
  op [a] eval_val_perms (asgn: SplAssign) (vperms: List (ValPerm a)) : PermEval (Value,a) =
    conjoin_perm_evalsN (map (eval_val_perm asgn) vperms)

  (* The strength preorder for value permissions *)
  op [a] val_perm_weaker? : PreOrder (ValPerm a) =
    fn (vperm1,vperm2) ->
      (fa (asgn) perm_eval_weaker? (eval_val_perm asgn vperm1,
                                    eval_val_perm asgn vperm2))

  (* The strength preorder for lists of value permissions *)
  op [a] val_perms_weaker? : PreOrder (List (ValPerm a)) =
    fn (vperms1,vperms2) ->
      (fa (asgn) perm_eval_weaker? (eval_val_perms asgn vperms1,
                                    eval_val_perms asgn vperms2))

  (* The strength preorder for lists of storage permissions *)
  op [a] st_perms_weaker? : PreOrder (List (StPerm a)) =
    fn (stperms1,stperms2) ->
      (fa (asgn) perm_eval_weaker? (eval_st_perms asgn stperms1,
                                    eval_st_perms asgn stperms2))


  (***
   *** Permissions and Permission Sets
   ***)

  type Perm a =
    | VarPerm (Identifier * ValPerm a)
    | NoVarPerm (StPerm a)

  type PermSet a = List (Perm a)

  (* Use a view of b at a to turn a Perm a into a Perm b *)
  op [a,b] perm_add_lens (perm: Perm a, lens: Lens (b,a)) : Perm b =
    case perm of
      | VarPerm (x, vperm) -> VarPerm (x, val_perm_add_lens (vperm, lens))
      | NoVarPerm stperm -> NoVarPerm (st_perm_add_lens (stperm, lens))

  (* Use a view of b at a to turn a PermSet a into a PermSet b *)
  op [a,b] perm_set_add_lens (perms: PermSet a, lens: Lens (b,a)) : PermSet b =
    map (fn p -> perm_add_lens (p, lens)) perms

  (* Evaluate a permission to a PermEval *)
  op [a] eval_perm (asgn: SplAssign) (perm: Perm a) : PermEval ((), a) =
    case perm of
      | VarPerm (x, vperm) ->
        compose_abs_perm_eval (lvalue_abstraction (LV_ident x),
                               eval_val_perm asgn vperm)
      | NoVarPerm stperm -> eval_st_perm asgn stperm

  (* Evaluate a permission set *)
  op [a] eval_perm_set (asgn: SplAssign) (perms: PermSet a) : PermEval ((),a) =
    conjoin_perm_evalsN (map (eval_perm asgn) perms)

  (* The strength preorder for permissions *)
  op [a] perm_weaker? : PreOrder (Perm a) =
    fn (perm1,perm2) ->
      (fa (asgn) perm_eval_weaker? (eval_perm asgn perm1,
                                    eval_perm asgn perm2))

  (* The strength preorder for permission sets *)
  op [a] perm_set_weaker? : PreOrder (PermSet a) =
    fn (perms1,perms2) ->
      (fa (asgn) perm_eval_weaker? (eval_perm_set asgn perms1,
                                    eval_perm_set asgn perms2))


  (***
   *** Perm Sets for Inputs and Output of C Functions
   ***)

  (* Zero or more permissions for each value in a list, along *)
  type ArgListPerms a = List (StPerm a) * List (List (ValPerm a))

  op [a] eval_arg_list_perms (asgn: SplAssign)
                             (perms: ArgListPerms a) : PermEval (List Value,a) =
    (conjoin_perm_evals
       (lift_unit_perm_eval (eval_st_perms asgn perms.1),
        list_perm_eval (map (eval_val_perms asgn) perms.2)))

  (* Construct a perm set from an ArgListPerms and a list of variable names;
  note that the value permissions are all made into constant value permissions,
  because function arguments are not allowed to be modified in its body *)
  op [a] perm_set_of_arg_perms (perms: ArgListPerms a, vars: List Identifier |
                                  equiLong (perms.2, vars)) : PermSet a =
    map NoVarPerm perms.1 ++
    flatten (map2 (fn (var,vperms) ->
                         map (fn vperm -> VarPerm (var, vperm)) vperms)
               (vars,perms.2))

  (* Permissions for a return value of a function *)
  type RetValPerm a = Option (List (ValPerm a))

  op [a] eval_ret_val_perm (asgn: SplAssign)
                           (rvperm: RetValPerm a) : PermEval (Option Value, a) =
    opt_perm_eval (mapOption (eval_val_perms asgn) rvperm)

  op [a] ret_val_perm_weaker? : PreOrder (RetValPerm a) =
    fn (rvperm1,rvperm2) ->
      (fa (asgn) perm_eval_weaker? (eval_ret_val_perm asgn rvperm1,
                                    eval_ret_val_perm asgn rvperm2))


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
                                (perms_out: PermSet a) (vperms_out: List (ValPerm b))
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

  (* Abstraction for blocks, which are lists of unit computations *)
  op [a,b] abstracts_block (env_pred : EnvPred)
                           (perms_in: PermSet a)
                           (perms_out: PermSet b)
                           (f: a -> b) (ms: List (Monad ())) : Bool =
    abstracts_statement env_pred perms_in perms_out f {_ <- mapM id ms; return ()}

  (* Abstraction for statements that optionally do a return at the end *)
  op [a,b] abstracts_ret_statement (env_pred : EnvPred)
                                   (perms_in: PermSet a)
                                   (perms_out: PermSet b) (ret_perms: RetValPerm b)
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

  (* Abstraction for blocks that return a value *)
  op [a,b] abstracts_ret_block (env_pred : EnvPred)
                               (perms_in: PermSet a)
                               (perms_out: PermSet b) (ret_perms: RetValPerm b)
                               (f: a -> b) (ms: List (Monad ())) : Bool =
    abstracts_ret_statement
      env_pred perms_in perms_out ret_perms f
      {_ <- mapM id ms; return ()}


  (* Abstraction for C functions, which are computation functions mapping lists
  of values, for the arguments, to an optional return value. Note that perms_out
  gives abstractions for viewing the same values that were passed in as
  arguments, *not* the values of those variables at the end of the function *)
  op [a,b] abstracts_c_function (env_pred : EnvPred)
                                (perms_in: ArgListPerms a)
                                (perms_out: ArgListPerms b) (ret_perms:RetValPerm b)
                                (f: a -> b)
                                (m: CFunction) : Bool =
    fa (asgn)
      abstracts_computation_fun
        env_pred
        (abs_of_perm_eval (eval_arg_list_perms asgn perms_in))
        (abs_of_perm_eval
           (perm_eval_pair_l
              (eval_arg_list_perms asgn perms_out,
               eval_ret_val_perm asgn ret_perms)))
        f
        m

  (* Abstraction for top-level function declarations: states that m generates a
  single function binding of name to a function that is abstracted by f *)
  op [a,b] abstracts_c_function_decl
      (env_pred : EnvPred) (perms_in: ArgListPerms a)
      (perms_out: ArgListPerms b) (ret_perms:RetValPerm b)
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
             abstracts_c_function (fn _ -> true) perms_in perms_out ret_perms f cfun
           | _ -> false)


  (***
   *** Permissions for Allocation and Deallocation
   ***)

  (* Lift preorders on the components of a storage to a preorder on storage trees *)
  op storage_preorder (leq_static: PreOrder NamedStorage,
                       leq_automatic: PreOrder (List (Option LocalScope)),
                       leq_allocated: PreOrder AllocatedStorage)
      : PreOrder (SplTree Storage * SplTree ()) =
    fn ((stree1,_), (stree2,_)) ->
      (fa (spl)
         leq_static ((stree1 spl).static, (stree2 spl).static) &&
         leq_automatic ((stree1 spl).automatic, (stree2 spl).automatic) &&
         leq_allocated ((stree1 spl).allocated, (stree2 spl).allocated))

  (* Permission allowing allocation of automatic storage, i.e., stack frames *)
  op auto_allocation_impl_perm : ImplPerm () =
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

  op auto_allocation_perm : CPermission ((), ()) =
    perm_of_impl_perm auto_allocation_impl_perm

  (* Permission allowing malloc *)
  op malloc_allocation_impl_perm : ImplPerm () =
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

  op [a] malloc_allocation_perm : CPermission ((), a) =
    perm_of_impl_perm malloc_allocation_impl_perm

  (*  *)
  op equal_except_current_scope (r:R,leq:PreOrder (Option LocalScope))
      : PreOrder (SplTree Storage * SplTree ()) =
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
  op current_frame_dealloc_impl_perm (vars: List Identifier) : ImplPerm () =
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

  op [a] current_frame_dealloc_perm (vars: List Identifier) : CPermission ((), a) =
    perm_of_impl_perm (current_frame_dealloc_impl_perm vars)


  (***
   *** Some Useful Value Permissions
   ***)

  (* Build a value abstraction that does not look at the heap *)
  (* FIXME: this should involve a type... *)
  op [a] non_heap_valueabs (R: Relation (Value,a)) : ValueAbs a =
    fn spl -> fn r ->
      {biview = fn ((stree,vtree),a) ->
         (fa (spl')
            splitting_leq (spl,spl') || splitting_leq (spl',spl) =>
            vtree spl' = vtree spl &&
            R (vtree spl', a)),
       bv_leq1 = fn ((stree1,vtree1),(stree2,vtree2)) ->
         stree1 = stree2 &&
         (fa (spl')
            splitting_leq (spl',spl) || vtree1 spl' = vtree2 spl'),
       bv_leq2 = fn _ -> true}

  op [a] non_heap_cperm (R: Relation (Value,a)) : CValPerm a =
    perm_of_spl_abs (non_heap_valueabs R)

  (* The permission for boolean values *)
  op bool_R : Relation (Value,Bool) = (fn (v,b) -> zeroScalarValue? v = return b)
  op bool_cperm : CValPerm Bool = non_heap_cperm bool_R

  (* Turn a value abstraction into a constant value abstraction, by adding a
  side condition that prevents the value itself from being modified *)
  (*
  op [a] mk_const_value_abs (vabs: ValueAbs a) : ValueAbs a =
    fn splset -> fn r ->
      {biview = (vabs splset r).biview,
       bv_leq1 = fn ((stree1,vtree1),(stree2,vtree2)) ->
         (vabs splset r).bv_leq1 ((stree1,vtree1),(stree2,vtree2)) &&
         vtree1 = vtree2,
       bv_leq2 = (vabs splset r).bv_leq2}
   *)

  (* Build a standard pointer-based value abstraction, where non-unity
  fractional permissions = read-only permissions *)
  (*
  op [a] pointer_valueabs (bv:BisimView (Storage * Type
                                           * ObjectDesignator, a)) : ValueAbs a =
    fn spl -> fn r ->
      {biview = fn ((stree,vtree),a) ->
         (case vtree spl of
            | V_pointer (tp, ObjPointer d) ->
              bv.biview ((stree spl, tp, d), a) &&
              (fa (spl')
                 splitting_leq (spl,spl') || splitting_leq (spl',spl) =>
                 vtree spl' = vtree spl &&
                 bv.biview ((stree spl', tp, d), a))),
       bv_leq1 = fn ((stree1,vtree1),(stree2,vtree2)) ->
         (fa (spl')
            (splitting_leq (spl',spl) =>
               (case (vtree1 spl', vtree2 spl') of
                  | (V_pointer (tp1, ObjPointer d1),
                     V_pointer (tp2, ObjPointer d2)) ->
                    bv.bv_leq1 ((stree1 spl', tp1, d1),(stree2 spl', tp2, d2))
                  | (V_pointer (_, ObjPointer _), _) -> false
                  | (_, V_pointer (_, ObjPointer _)) -> false
                  | (_, _) -> true)) &&
            (~(splitting_leq (spl',spl)) =>
               stree1 spl' = stree2 spl' && vtree1 spl' = vtree2 spl')),
       bv_leq2 = bv.bv_leq2}
   *)


  (* FIXME: define all these! *)

  op [a] pointer_cperm (perm:CValPerm a) : CValPerm a

  (* FIXME: need to borrow individual fields from an array... *)
  op [a] arary_pointer_cperm (perm:CValPerm a) : CValPerm a

  type StructFieldCPerms a = List (Identifier * Option (CValPerm a))

  op [a] struct_cperm (fields: StructFieldCPerms a) : CValPerm a

  op [a] struct_pointer_cperm (fields: StructFieldCPerms a) : CValPerm a

  (* FIXME: figure out the monotonicity condition here... *)
  op [a] struct_pointer_rec_cperm (fields: CValPerm a ->
                                     StructFieldCPerms a) : CValPerm a

  (* Same as struct_pointer_cperm, but folded_fields is a hint to the C
  generator that we should view this as a single unfolding of
  struct_pointer_rec_cperm, and try to fold it back when possible *)
  op [a] struct_pointer_rec_unfolded_cperm (fields: StructFieldCPerms a,
                                            folded_fields: CValPerm a ->
                                              StructFieldCPerms a) : CValPerm a =
    struct_pointer_cperm fields

end-spec
