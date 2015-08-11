CGen qualifying spec
  import C_Permissions, C_DSL


  (***
   *** "Control" Predicates
   ***)

  (* Dummy predicate that "enables" a predicate, allowing the strengthening
  rules to attempt to simplify it. To make this work, all the rules in this file
  only prove results of the form enabled? P for some predicate P. *)
  op enabled? (b:Bool) : Bool = b

  (* Special form of conjunction that enables the second argument as soon as the
  first argument is proved. *)
  op &&&& (b1: Bool, b2: Bool) infixr 15 : Bool = b1 && b2

  (* Discharge an enabled rule that has been proved *)
  theorem discharge_enabled_true is
    fa (u:()) true => enabled? true

  (* Move normal equations out of enabled? *)
  theorem enabled_equation is [a]
    fa (x,y:a) x = y => enabled? (x = y)

  (* If an &&&& is enabled, enable its first argument *)
  theorem enable_first_conjunct is
    fa (b1,b2) (enabled? b1) &&&& b2 => enabled? (b1 &&&& b2)

  (* When the first conjunct is proved, then enable the second one *)
  theorem enable_second_conjunct is
    fa (b2) enabled? b2 => true &&&& b2

  (* When the first conjunct is an equality, then enable the second conjunct,
  because the rewriter can already see the equality anyway and maybe cannot
  progress (as in post-conditions...) *)
  theorem enable_second_conjunct_eq is [a]
    fa (x:a,y:a,b2) x=y && enabled? b2 => x=y &&&& b2

  (* When the second conjunct is already proved, we can drop it *)
  theorem discharge_true_second_conjunct is
    fa (b1) b1 => b1 &&&& true

  (* An equality that is disabled: the standard simplifier won't "see" it, until
  it is enabled (by the following theorem) *)
  op [a] === (x:a,y:a) infixl 20 : Bool = x = y

  (* Prove an enabled === equality *)
  theorem prove_enabled_equality is [a]
    fa (x,y:a) x = y => enabled? (x === y)

  (* Special form of disjunction that chooses the first branch that becomes
  "enabled?". *)
  op |||| (b1: Bool, b2: Bool) infixr 14 : Bool = b1 || b2

  theorem disj_choose_enabled_left is
    fa (b1, b2)
      enabled? b1 => (enabled? b1) |||| b2

  theorem disj_true_left is
    fa (b2) true => true |||| b2

  theorem disj_choose_enabled_right is
    fa (b1, b2)
      enabled? b2 => b1 |||| (enabled? b2)

  theorem disj_true_right is
    fa (b1) true => b1 |||| true

  (* Conjunctive clause, to be used in ||||, that only becomes enabled if the
  first argument is rewritten to true. *)
  op clause (b1: Bool, b2: Bool) : Bool = b1 && b2

  theorem enable_clause is
    fa (b2) enabled? b2 => clause (true, b2)

  (* A false that is debuggable, as it doesn't turn everything else to false *)
  op unprovable : Bool = false

  (* Helper predicate to test if two objects are equal, and conditionally choose
  which "continuation" to keep proving *)
  op [a] ifequal (x:a,y:a,res1:Bool,res2:Bool) : Bool =
    if x = y then res1 else res2
  theorem ifequal_eq is [a]
    fa (x:a,res1,res2)
      enabled? res1 => enabled? (ifequal (x,x,res1,res2))
  theorem ifequal_neq is [a]
    fa (x:a,y,res1,res2)
      x ~= y && enabled? res2 => enabled? (ifequal (x,y,res1,res2))


  (***
   *** Relational Versions of List Functions
   ***)

  (* NOTE: this predicate is for ground terms pred and l only *)
  op [a] forall_pred (pred: a -> Bool) (l: List a) : Bool =
    forall? pred l

  theorem forall_pred_nil is [a]
    fa (pred: a -> Bool)
      true => enabled? (forall_pred pred [])

  theorem forall_pred_cons is [a]
    fa (pred: a -> Bool, x, l)
      enabled? (pred x) &&
      enabled? (forall_pred pred l) =>
      enabled? (forall_pred pred (x::l))

  (* NOTE: this predicate is for ground terms pred and l only *)
  op [a] exists_pred (pred: a -> Bool) (l: List a) : Bool =
    exists? pred l

  theorem exists_pred_nil is [a]
    fa (pred: a -> Bool)
      true => enabled? (exists_pred pred [])

  theorem exists_pred_cons is [a]
    fa (pred: a -> Bool, x, l)
      clause (enabled? (pred x), true) ||||
      clause (enabled? (exists_pred pred l), true) =>
      enabled? (exists_pred pred (x::l))

  op [a] in_pred (x:a, l:List a) : Bool =
    ex (i) l@@i = Some x

  theorem in_pred_base is [a]
    fa (x:a,l)
      true => enabled? (in_pred (x, x::l))

  theorem in_pred_cons is [a]
    fa (x:a,x',l)
      enabled? (in_pred (x,l)) => enabled? (in_pred (x, x'::l))

  op [a] is_append (l1: List a, l2: List a, l_out: List a) : Bool =
    l_out = l1 ++ l2

  theorem is_append_nil is [a]
    fa (l2, l_out:List a)
      l_out = l2 =>
      enabled? (is_append ([], l2, l_out))

  theorem is_append_cons is [a]
    fa (x:a, l1, l2, l_out', l_out)
      enabled? (is_append (l1, l2, l_out')) &&&&
      l_out === x::l_out' =>
      enabled? (is_append (x::l1, l2, l_out))

  op [a,b] is_map_of (f: a -> b) (inl: List a, outl: List b) : Bool =
    outl = map f inl

  theorem is_map_of_nil is [a,b]
    fa (f:a->b,outl)
      outl = [] => enabled? (is_map_of f ([], outl))

  theorem is_map_of_cons is [a,b]
    fa (f:a->b, x, inl, outl, outl')
      enabled? (is_map_of f (inl, outl')) &&
      outl = (f x)::outl' =>
      enabled? (is_map_of f (x::inl, outl))

  op [a,b,c] is_map2_of (f: a*b -> c) (in1: List a, in2: List b,
                                       outl: List c) : Bool =
    equiLong (in1,in2) &&
    outl = map2 f (in1,in2)

  theorem is_map2_of_nil is [a,b,c]
    fa (f:a*b->c,outl)
      outl = [] => enabled? (is_map2_of f ([], [], outl))

  theorem is_map2_of_cons is [a,b,c]
    fa (f:a*b->c, x1, in1, x2, in2, outl, outl')
      enabled? (is_map2_of f (in1, in2, outl')) &&
      outl = (f (x1,x2))::outl' =>
      enabled? (is_map2_of f (x1::in1, x2::in2, outl))

  op [a,b] is_map_pred_of (pred: a*b -> Bool) (inl: List a, outl: List b) : Bool =
    equiLong (inl, outl) &&
    forall? pred (zip (inl, outl))

  theorem is_map_pred_of_nil is [a,b]
    fa (pred:a*b->Bool, outl)
      outl = [] => enabled? (is_map_pred_of pred ([], outl))

  theorem is_map_pred_of_cons is [a,b]
    fa (pred:a*b->Bool, x, inl, y, outl, outl')
      enabled? (pred (x, y)) &&
      enabled? (is_map_pred_of pred (inl, outl')) &&
      outl = y::outl' =>
      enabled? (is_map_pred_of pred (x::inl, outl))

  op [a,b,c] is_map2_pred_of (pred: a*b*c -> Bool) (inl1: List a, inl2: List b,
                                                    outl: List c) : Bool =
    equiLong (inl1, inl2) &&
    equiLong (inl2, outl) &&
    forall? pred (zip3 (inl1, inl2, outl))

  theorem is_map2_pred_of_nil is [a,b,c]
    fa (pred:a*b*c->Bool, outl)
      outl = [] => enabled? (is_map2_pred_of pred ([], [], outl))

  theorem is_map_pred_of_cons is [a,b,c]
    fa (pred:a*b*c->Bool, x1, inl1, x2, inl2, y, outl, outl')
      enabled? (pred (x1, x2, y)) &&
      enabled? (is_map2_pred_of pred (inl1, inl2, outl')) &&
      outl = y::outl' =>
      enabled? (is_map2_pred_of pred (x1::inl1, x2::inl2, outl))

  op [a] is_flatten_of (xss: List (List a), xs: List a) : Bool =
    xs = flatten xss

  theorem is_flatten_of_nil is [a]
    fa (xs:List a)
      xs = [] => enabled? (is_flatten_of ([], xs))

  theorem is_flatten_of_cons is [a]
    fa (xss, xs1, xs', xs:List a)
      enabled? (is_flatten_of (xss, xs')) &&&&
      is_append (xs1, xs', xs) =>
      enabled? (is_flatten_of (xs1::xss, xs))

  op [a] is_fold_pred_of (pred: a*Bool -> Bool) (l: List a, base: Bool) : Bool =
    foldr pred base l

  theorem is_fold_pred_of_nil is [a]
    fa (pred:a*Bool->Bool, base)
      enabled? base => enabled? (is_fold_pred_of pred ([], base))

  theorem is_fold_pred_of_cons is [a]
    fa (pred:a*Bool->Bool, x, l, base)
      enabled? (pred (x, is_fold_pred_of pred (l, base))) =>
      enabled? (is_fold_pred_of pred (x::l, base))


  (***
   *** Relational Versions of Operations on Permissions
   ***)

  (* We define relational versions of all these operations on permissions, as
  well as theorems to "compute" them, as strengthening rules *)

  (* lens_compose *)

  op [a,b,c] is_lens_compose (lens1: Lens (a,b), lens2: Lens (b,c),
                              lens_out: Lens (a,c)) : Bool =
    lens_compose (lens1, lens2) = lens_out

(*
  theorem is_lens_compose_rule is [a,b,c]
    fa (l1: Lens (a,b), l2: Lens (b,c), lens_out)
      lens_out = {lens_get = (fn a -> l2.lens_get (l1.lens_get a)),
                  lens_set = (fn a -> fn c ->
                                l1.lens_set a (l2.lens_set (l1.lens_get a) c))} =>
      enabled? (is_lens_compose (l1, l2, lens_out))
*)

  theorem is_lens_compose_id_l is [a,b]
    fa (lens:Lens (a,b), lens_out:Lens (a,b))
      lens_out = lens =>
      enabled? (is_lens_compose (id_lens, lens, lens_out))

  theorem is_lens_compose_id_r is [a,b]
    fa (lens:Lens (a,b), lens_out:Lens (a,b))
      lens_out = lens =>
      enabled? (is_lens_compose (lens, id_lens, lens_out))

  theorem is_lens_compose_iso_id_l is [a,b]
    fa (lens:Lens (a,b), lens_out:Lens (a,b))
      lens_out = lens =>
      enabled? (is_lens_compose (iso_lens (fn x -> x), lens, lens_out))

  theorem is_lens_compose_iso_id_r is [a,b]
    fa (lens:Lens (a,b), lens_out:Lens (a,b))
      lens_out = lens =>
      enabled? (is_lens_compose (lens, iso_lens (fn x -> x), lens_out))

  theorem is_lens_compose_iso_inv_id_l is [a,b]
    fa (lens:Lens (a,b), lens_out:Lens (a,b))
      lens_out = lens =>
      enabled? (is_lens_compose (iso_lens (inverse (fn x -> x)), lens, lens_out))

  theorem is_lens_compose_iso_inv_id_r is [a,b]
    fa (lens:Lens (a,b), lens_out:Lens (a,b))
      lens_out = lens =>
      enabled? (is_lens_compose (lens, iso_lens (inverse (fn x -> x)), lens_out))

  theorem is_lens_compose_unit is [a,b]
    fa (lens:Lens (a,b), lens_out)
      lens_out = unit_lens =>
      enabled? (is_lens_compose (lens, unit_lens, lens_out))



  (* compose_biviews *)

  op [a,b,c] is_compose_biviews (bv1: BisimView (a,b), bv2: BisimView (b,c),
                                 bv_out: BisimView (a,c)) : Bool =
    compose_biviews (bv1, bv2) = bv_out

  theorem compose_biview_of_lenses is [a,b,c]
    fa (l1: Lens (a,b), l2: Lens (b,c), bv_out)
      bv_out = biview_of_lens
                {lens_get = (fn a -> l2.lens_get (l1.lens_get a)),
                 lens_set = (fn a -> fn c ->
                               l1.lens_set a (l2.lens_set (l1.lens_get a) c))} =>
      enabled? (is_compose_biviews (biview_of_lens l1, biview_of_lens l2, bv_out))

  theorem compose_lens_trivial is [a,b,c]
    fa (lens: Lens (a,b), bv_out: BisimView (a,c))
      bv_out = trivial_biview =>
      enabled? (is_compose_biviews (biview_of_lens lens, trivial_biview, bv_out))

  theorem compose_lens_identity_l is [a,b]
    fa (bv: BisimView (a,b), bv_out)
      bv_out = bv =>
      enabled? (is_compose_biviews (identity_biview, bv, bv_out))

  theorem compose_lens_identity_r is [a,b]
    fa (bv: BisimView (a,b), bv_out)
      bv_out = bv =>
      enabled? (is_compose_biviews (bv, identity_biview, bv_out))


  (* proving pseudo_monic *)

  theorem pseudo_monic_of_lens_pair is [a,b,c]
    fa (lens1:Lens (a,b), lens2:Lens (c,b))
      true => enabled? (pseudo_monic? (biview_of_lens_pair (lens1,lens2)))


  (* cperm_add_lens *)

  op [a,b,c] is_cperm_add_lens (lens: Lens (b,a)) (cperm: CPermission (c, a),
                                                   cperm_out: CPermission (c, b)) : Bool =
    cperm_add_lens (cperm, lens) = cperm_out

  theorem is_cperm_add_lens_lens is [a,b,c,d]
    fa (cperm:CPermission (c,d),lens1,lens:Lens (b,a),lens_out,cperm_out:CPermission (c,b))
      enabled? (is_lens_compose (lens, lens1, lens_out)) &&&&
      cperm_out === cperm_add_lens (cperm, lens_out) =>
      enabled? (is_cperm_add_lens lens (cperm_add_lens (cperm, lens1), cperm_out))

  theorem is_cperm_add_lens_ignore is [a,b,c,d]
    fa (cperm:CPermission (c,d),lens:Lens (b,a),cperm_out:CPermission (c,b))
      cperm_out = cperm_ignore cperm =>
      enabled? (is_cperm_add_lens lens (cperm_ignore cperm, cperm_out))


  (* val_perm_add_lens *)

  op [a,b,c,d] is_val_perm_add_lens (lens: Lens (c,b)) (vperm: ValPerm (a,b),
                                                        vperm_out: ValPerm (d,c)) : Bool =
    val_perm_add_lens (vperm, lens) = vperm_out

  theorem is_val_perm_add_lens_val is [a,b,c,d]
    fa (splexpr,cperm,lens:Lens (c,b),cperm_out,vperm_out:ValPerm (d,c))
      enabled? (is_cperm_add_lens lens (cperm, cperm_out)) &&&&
      vperm_out === ValPerm (splexpr, cperm_out) =>
      enabled? (is_val_perm_add_lens lens (ValPerm (splexpr, cperm):ValPerm (a,b), vperm_out))

  theorem is_val_perm_add_lens_valeq is [a,b,c,d]
    fa (splexpr,cperm,lv,l:Lens (a,b),lens,cperm_out,vperm_out:ValPerm (d,c))
      enabled? (is_cperm_add_lens lens (cperm, cperm_out)) &&&&
      vperm_out === ValPerm (splexpr, cperm_out) =>
      enabled? (is_val_perm_add_lens lens (ValEqPerm (splexpr, cperm, lv, l), vperm_out))


  (* val_perms_add_lens *)

  op [a,b,c,d] is_val_perms_add_lens (lens: Lens (c,b))
                                     (vperms: List (ValPerm (a,b)),
                                      vperms_out: List (ValPerm (d,c))) : Bool =
    val_perms_add_lens (vperms, lens) = vperms_out

  theorem is_val_perms_add_lens_rule is [a,b,c,d]
    fa (vperms:List (ValPerm (a,b)), lens, vperms_out:List (ValPerm (d,c)))
      enabled? (is_map_pred_of (is_val_perm_add_lens lens) (vperms, vperms_out)) =>
      enabled? (is_val_perms_add_lens lens (vperms, vperms_out))


  (* st_perm_add_lens *)

  op [a,b] is_st_perm_add_lens (lens: Lens (b,a)) (stperm: StPerm a,
                                                   stperm_out: StPerm b) : Bool =
    st_perm_add_lens (stperm, lens) = stperm_out

  theorem is_st_perm_add_lens_st is [a,b]
    fa (splexpr,cperm:CUnitPerm a,lens:Lens (b,a),cperm_out,stperm_out)
      enabled? (is_cperm_add_lens lens (cperm, cperm_out)) &&&&
      stperm_out === StPerm (splexpr, cperm_out) =>
      enabled? (is_st_perm_add_lens lens (StPerm (splexpr, cperm), stperm_out))


  (* st_perms_add_lens *)

  op [a,b] is_st_perms_add_lens (lens: Lens (b,a))
                                (stperms: List (StPerm a),
                                 stperms_out: List (StPerm b)) : Bool =
    st_perms_add_lens (stperms, lens) = stperms_out

  theorem is_st_perms_add_lens_rule is [a,b]
    fa (stperms, lens:Lens (b,a), stperms_out)
      enabled? (is_map_pred_of (is_st_perm_add_lens lens) (stperms, stperms_out)) =>
      enabled? (is_st_perms_add_lens lens (stperms, stperms_out))


  (* perm_add_lens *)

  op [a,b] is_perm_add_lens (lens: Lens (b,a)) (perm: Perm a,
                                                   perm_out: Perm b) : Bool =
    perm_add_lens (perm, lens) = perm_out

  theorem is_perm_add_lens_var is [a,b]
    fa (x,vperm,lens:Lens (b,a),vperm_out,perm_out)
      enabled? (is_val_perm_add_lens lens (vperm, vperm_out)) &&
      perm_out = VarPerm (x, vperm_out) =>
      enabled? (is_perm_add_lens lens (VarPerm (x, vperm), perm_out))

  theorem is_perm_add_lens_novar is [a,b]
    fa (stperm,lens:Lens (b,a),stperm_out,perm_out)
      enabled? (is_st_perm_add_lens lens (stperm, stperm_out)) &&
      perm_out = NoVarPerm stperm_out =>
      enabled? (is_perm_add_lens lens (NoVarPerm stperm, perm_out))


  (* perm_set_add_lens *)

  op [a,b] is_perm_set_add_lens (lens: Lens (b,a)) (perms: PermSet a,
                                                       perms_out: PermSet b) : Bool =
    perm_set_add_lens (perms, lens) = perms_out

  theorem is_perm_set_add_lens_rule is [a,b]
    fa (perms,lens:Lens (b,a),perms_out)
      enabled? (is_map_pred_of (is_perm_add_lens lens) (perms, perms_out)) =>
      enabled? (is_perm_set_add_lens lens (perms, perms_out))


  (* perm_set_of_arg_perms *)

  op [a] is_perm_set_of_arg_perms (perms: ArgListPerms a, vars: ParameterList,
                                   perm_set: PermSet a) : Bool =
    equiLong (perms.2, vars) &&
    perm_set = perm_set_of_arg_perms (perms, map (fn x -> x.2) vars)

  theorem is_perm_set_of_arg_perms_rule is [a]
    fa (st_perms,vperms,params,perm_set_out:PermSet a,perms_out1,perms_out2)
      enabled? (is_map_of NoVarPerm (st_perms, perms_out1)) &&
      enabled? (is_map2_of (fn ((_,var),vperm) -> VarPerm (var,vperm))
                  (params, vperms, perms_out2)) &&&&
      is_append (perms_out1, perms_out2, perm_set_out) =>
      enabled? (is_perm_set_of_arg_perms ((st_perms,vperms), params,
                                          perm_set_out))


  (***
   *** Unfolding / Simplifying Things
   ***)

  (* The user needs to supply theorems for this to unfold the definition of any
  cperm they use *)
  op [a] USER_unfold_cperm (cperm: CValPerm a,
                            cperm_unfolded: CValPerm a) : Bool =
    cperm = cperm_unfolded

  theorem unfold_bool_cperm is
    fa (cperm')
      cperm' = non_heap_cperm (fn (v,b) -> zeroScalarValue? v = return b) =>
      enabled? (USER_unfold_cperm (bool_cperm, cperm'))

(*
  op [a,b] USER_simplify_biview (bv: BisimView (a,b),
                                 bv_simp: BisimView (a,b)) : Bool =
    bv = bv_simp

  theorem USER_simplify_biview_id_biview is [a]
    fa (bv_simp:BisimView (a,a))
      bv_simp = biview_of_lens id_lens =>
      enabled? (USER_simplify_biview (identity_biview, bv_simp))

  theorem USER_simplify_biview_proj1_biview is [a,b]
    fa (bv_simp:BisimView (a*b,a))
      bv_simp = biview_of_lens proj1_lens =>
      enabled? (USER_simplify_biview (proj1_biview, bv_simp))

  theorem USER_simplify_biview_proj2_biview is [a,b]
    fa (bv_simp:BisimView (a*b,b))
      bv_simp = biview_of_lens proj2_lens =>
      enabled? (USER_simplify_biview (proj2_biview, bv_simp))
*)

  (***
   *** Factoring Permission Sets
   ***)

  (* FIXME: update this documentation to "factoring" *)
  (* The following predicates are to "un-map" a permission of type a into a
  permission of type b, where, intuitively, b is "smaller" than a. This
  "smaller-ness" is described by a pseudo-monic biview bv_prefix. Un-mapping
  replaces any permission whose view of type a includes bv_prefix as a prefix
  view by the permission formed by removing bv_prefix. For example, if a is the
  triple type t1*t2*t3 and b is the pair type t2*t1, then any permission of type
  a that relates C values / storages with the first projection of type a can be
  un-mapped to the same relation with the second projection of type b, by
  viewing the permission of type a as the composition of the obvious mapping
  from a to b with the given permission of type b.  Sometimes this re-mapping is
  not possible; e.g., in this same example, a permission that relates C values /
  storages with the third projection of type a has no correlating permission of
  type b. In this case the trivial biview is used in the output permission,
  which in essence ignores the C value / storage viewed by the permission. *)


  op [a,b,c] if_lens_factors (lens_prefix: Lens (a,b), lens: Lens (a,c),
                              res1: Lens (b,c) -> Bool, res2: Bool) : Bool =
    (ex (lens_suffix)
       lens = lens_compose (lens_prefix, lens_suffix) &&
       res1 lens_suffix) ||
    res2

  (* The unit lens always factors w.r.t. any prefix *)
  theorem if_lens_factors_unit is [a,b]
    fa (lens_prefix: Lens (a,b), res1, res2)
      enabled? (res1 unit_lens) =>
      enabled? (if_lens_factors (lens_prefix, unit_lens, res1, res2))

  (* Nothing factors w.r.t. the unit lens... except the unit lens, above *)
  theorem if_lens_factors_unit_id is [a]
    fa (res1:Lens ((),a)->Bool, res2)
      enabled? res2 =>
      enabled? (if_lens_factors (unit_lens, id_lens, res1, res2))
  theorem if_lens_factors_unit_proj1 is [a,b]
    fa (res1, res2)
      enabled? res2 =>
      enabled? (if_lens_factors (unit_lens, proj1_lens:Lens (a*b,a), res1, res2))
  theorem if_lens_factors_unit_proj2 is [a,b]
    fa (res1, res2)
      enabled? res2 =>
      enabled? (if_lens_factors (unit_lens, proj2_lens:Lens (a*b,b), res1, res2))

  (* Everything factors w.r.t. the identity lens *)
  theorem if_lens_factors_unit is [a,c]
    fa (lens: Lens (a,c), res1, res2)
      enabled? (res1 lens) =>
      enabled? (if_lens_factors (id_lens, lens, res1, res2))


  (* FIXME HERE: theorems for decomposing lenses *)


  (* Predicate for when a lens *must* factor *)
  op [a,b,c] lens_factors_to (lens_prefix: Lens (a,b), lens: Lens (a,c),
                              lens_out: Lens (b,c)) : Bool =
    lens = lens_compose (lens_prefix, lens_out)

  theorem lens_factors_to_rule is [a,b,c]
    fa (lens_prefix:Lens (a,b), lens:Lens (a,c), lens_out)
      enabled? (if_lens_factors (lens_prefix, lens,
                                 (fn lens_suffix -> lens_out === lens_suffix),
                                 unprovable)) =>
      enabled? (lens_factors_to (lens_prefix, lens, lens_out))


  (* Predicate for factoring value permissions *)
  op [a,b] val_perms_factor_to (lens_prefix: Lens (a,b))
                               (vperms_in: List (ValPerm (a,a)),
                                vperms_out: List (ValPerm (b,b))) : Bool =
    val_perms_weaker? (val_perms_add_lens (vperms_out, lens_prefix), vperms_in)

  theorem val_perms_factor_to_cons is [a,b,c]
    fa (splexpr,cperm:CValPerm c,lens,vperms,lens_prefix:Lens (a,b),vperms_out,vperms_out1)
      enabled? (val_perms_factor_to lens_prefix (vperms, vperms_out1)) &&&&
      (if_lens_factors
         (lens_prefix, lens,
          (fn lens_suffix ->
             vperms_out === ValPerm (splexpr,
                                     cperm_add_lens
                                       (cperm, lens_suffix))::vperms_out1),
          vperms_out === vperms_out1)) =>
      enabled? (val_perms_factor_to
                  lens_prefix
                  (ValPerm (splexpr,cperm_add_lens (cperm, lens))::vperms, vperms_out))

  theorem val_perms_factor_to_cons_eq is [a,b,c]
    fa (splexpr,cperm:CValPerm c,lens',lens,lv,vperms,lens_prefix:Lens (a,b),vperms_out,vperms_out1)
      enabled? (val_perms_factor_to lens_prefix (vperms, vperms_out1)) &&&&
      (if_lens_factors
         (lens_prefix, lens,
          (fn lens_suffix ->
             vperms_out === ValPerm (splexpr,
                                     cperm_add_lens (cperm, lens_suffix))::vperms_out1),
          vperms_out === vperms_out1)) =>
      enabled? (val_perms_factor_to
                  lens_prefix
                  (ValEqPerm (splexpr,
                              cperm_add_lens (cperm, lens),
                              lv,lens')::vperms, vperms_out))

  theorem val_perms_factor_to_cons_nil is [a,b]
    fa (lens_prefix:Lens (a,b), vperms_out)
      vperms_out = [] =>
      enabled? (val_perms_factor_to lens_prefix ([], vperms_out))


  (* Predicate for factoring storage permissions *)
  op [a,b] st_perms_factor_to (lens_prefix: Lens (a,b))
                               (stperms_in: List (StPerm a),
                                stperms_out: List (StPerm b)) : Bool =
    st_perms_weaker? (st_perms_add_lens (stperms_out, lens_prefix), stperms_in)

  theorem st_perms_factor_to_cons is [a,b,c]
    fa (splexpr,cperm:CUnitPerm c,lens,stperms,lens_prefix:Lens (a,b),stperms_out,stperms_out1)
      enabled? (st_perms_factor_to lens_prefix (stperms, stperms_out1)) &&&&
      (if_lens_factors
         (lens_prefix, lens,
          (fn lens_suffix ->
             stperms_out === StPerm (splexpr,
                                     cperm_add_lens
                                       (cperm, lens_suffix))::stperms_out1),
          stperms_out === stperms_out1)) =>
      enabled? (st_perms_factor_to
                  lens_prefix
                  (StPerm (splexpr,cperm_add_lens (cperm, lens))::stperms, stperms_out))

  theorem st_perms_factor_to_cons_nil is [a,b]
    fa (lens_prefix:Lens (a,b), stperms_out)
      stperms_out = [] =>
      enabled? (st_perms_factor_to lens_prefix ([], stperms_out))


  (* Predicate factoring permission sets *)
  op [a,b] perm_set_factors_to (lens_prefix: Lens (a,b))
                               (perms_in: PermSet a,
                                perms_out: PermSet b) : Bool =
    perm_set_weaker? (perm_set_add_lens (perms_out, lens_prefix), perms_in)

  theorem perm_set_factors_to_cons_var is [a,b,c]
    fa (x,splexpr,cperm:CValPerm c,lens,perms,lens_prefix:Lens (a,b),perms_out,perms_out1)
      enabled? (perm_set_factors_to lens_prefix (perms, perms_out1)) &&&&
      (if_lens_factors
         (lens_prefix, lens,
          (fn lens_suffix ->
             perms_out ===
             VarPerm (x, ValPerm (splexpr,
                                  cperm_add_lens
                                    (cperm, lens_suffix)))::perms_out1),
          perms_out ===
            VarPerm (x, ValPerm (splexpr,
                                 cperm_ignore cperm))::perms_out1)) =>
      enabled? (perm_set_factors_to
                  lens_prefix
                  (VarPerm (x, (ValPerm
                                  (splexpr,
                                   cperm_add_lens (cperm, lens))))::perms,
                   perms_out))

  theorem perm_set_factors_to_cons_var_ign is [a,b,c]
    fa (x,splexpr,cperm:CValPerm c,perms,lens_prefix:Lens (a,b),perms_out,perms_out1)
      enabled? (perm_set_factors_to lens_prefix (perms, perms_out1)) &&&&
      perms_out === VarPerm (x, ValPerm (splexpr,
                                         cperm_ignore cperm))::perms_out1 =>
      enabled? (perm_set_factors_to
                  lens_prefix
                  (VarPerm (x, (ValPerm (splexpr, cperm_ignore cperm)))::perms,
                   perms_out))

  theorem perm_set_factors_to_cons_var_eq is [a,b,c]
    fa (x,lv,lens',splexpr,cperm:CValPerm c,lens,perms,lens_prefix:Lens (a,b),perms_out,perms_out1)
      enabled? (perm_set_factors_to lens_prefix (perms, perms_out1)) &&&&
      (if_lens_factors
         (lens_prefix, lens,
          (fn lens_suffix ->
             perms_out ===
             VarPerm (x, ValPerm (splexpr,
                                  cperm_add_lens
                                    (cperm, lens_suffix)))::perms_out1),
          perms_out ===
            VarPerm (x, ValPerm (splexpr, cperm_ignore cperm))::perms_out1))
      =>
      enabled? (perm_set_factors_to
                  lens_prefix
                  (VarPerm (x, (ValEqPerm
                                  (splexpr,
                                   cperm_add_lens (cperm, lens),
                                   lv, lens')))::perms,
                   perms_out))

  theorem perm_set_factors_to_cons_var_eq_ign is [a,b,c]
    fa (x,splexpr,cperm:CValPerm c,lv,lens',perms,lens_prefix:Lens (a,b),perms_out,perms_out1)
      enabled? (perm_set_factors_to lens_prefix (perms, perms_out1)) &&&&
      perms_out === VarPerm (x, ValPerm (splexpr,
                                         cperm_ignore cperm))::perms_out1 =>
      enabled? (perm_set_factors_to
                  lens_prefix
                  (VarPerm (x, (ValEqPerm (splexpr, cperm_ignore cperm,
                                           lv, lens')))::perms,
                   perms_out))

  theorem perm_set_factors_to_cons_novar is [a,b,c]
    fa (splexpr,cperm:CUnitPerm c,lens,perms,lens_prefix:Lens (a,b),perms_out,perms_out1)
      enabled? (perm_set_factors_to lens_prefix (perms, perms_out1)) &&&&
      (if_lens_factors
         (lens_prefix, lens,
          (fn lens_suffix ->
             perms_out ===
             NoVarPerm (StPerm (splexpr,
                                cperm_add_lens
                                  (cperm, lens_suffix)))::perms_out1),
          perms_out ===
            NoVarPerm (StPerm (splexpr,
                               cperm_ignore cperm))::perms_out1)) =>
      enabled? (perm_set_factors_to
                  lens_prefix
                  (NoVarPerm (StPerm (splexpr,cperm_add_lens (cperm, lens)))::perms,
                   perms_out))

  theorem perm_set_factors_to_cons_novar_ign is [a,b,c]
    fa (splexpr,cperm:CUnitPerm c,perms,lens_prefix:Lens (a,b),perms_out,perms_out1)
      enabled? (perm_set_factors_to lens_prefix (perms, perms_out1)) &&&&
      perms_out === NoVarPerm (StPerm (splexpr,
                                       cperm_ignore cperm))::perms_out1 =>
      enabled? (perm_set_factors_to
                  lens_prefix
                  (NoVarPerm (StPerm (splexpr,cperm_ignore cperm))::perms,
                   perms_out))

  theorem perm_set_factors_to_cons_nil is [a,b]
    fa (lens_prefix:Lens (a,b), perms_out)
      perms_out = [] =>
      enabled? (perm_set_factors_to lens_prefix ([], perms_out))



  (***
   *** Proving perm_set_weaker?
   ***)

  (* FIXME: the rules for stperms and vperms should consider the splexprs... *)

  (* cperm_weaker? *)

  theorem cperm_weaker_lens is [a,b,c]
    fa (lens:Lens (a,b),cperm1,cperm2:CPermission (c,b))
      enabled? (cperm_weaker? (cperm1,cperm2)) =>
      enabled? (cperm_weaker? (cperm_add_lens (cperm1, lens),
                               cperm_add_lens (cperm2, lens)))

  theorem cperm_weaker_ignore is [a,b,c]
    fa (cperm1,cperm2:CPermission (a,b))
      enabled? (cperm_weaker? (cperm1,cperm2)) =>
      enabled? (cperm_weaker? (cperm_ignore cperm1:CPermission (a,c),
                               cperm_ignore cperm2))

  theorem cperm_weaker_no_heap is [a]
    fa (R: Relation (Value,a))
      true => enabled? (cperm_weaker? (non_heap_cperm R, non_heap_cperm R))

  (* Short-circuit for equal cperms *)
  theorem cperm_weaker_id is [a,c]
    fa (cperm:CPermission (c,a))
      true => enabled? (cperm_weaker? (cperm,cperm))

  (* val_perm_weaker? *)

  theorem val_perm_weaker_noeq is [a]
    fa (splexpr,cperm1,cperm2:CValPerm a)
      enabled? (cperm_weaker? (cperm1,cperm2)) =>
      enabled? (val_perm_weaker? (ValPerm (splexpr,cperm1):ValPerm (a,a),
                                  ValPerm (splexpr,cperm2)))

  theorem val_perm_weaker_noeq_eq is [a,b]
    fa (splexpr,lv,lens:Lens (a,b),cperm1,cperm2)
      enabled? (cperm_weaker? (cperm1,cperm2)) =>
      enabled? (val_perm_weaker? (ValPerm (splexpr,cperm1),
                                  ValEqPerm (splexpr,cperm2,lv,lens)))

  theorem val_perm_weaker_eq is [a,b]
    fa (splexpr,lv,lens:Lens (a,b),cperm1,cperm2)
      enabled? (cperm_weaker? (cperm1,cperm2)) =>
      enabled? (val_perm_weaker? (ValEqPerm (splexpr,cperm1,lv,lens),
                                  ValEqPerm (splexpr,cperm2,lv,lens)))

  (* Short-circuit for equal val perms *)
  theorem val_perm_weaker_id is [a,b]
    fa (vperm:ValPerm (a,b))
      true => enabled? (val_perm_weaker? (vperm,vperm))

  (* val_perms_weaker? *)

  theorem val_perms_weaker_rule is [a,b]
    fa (vperms1,vperms2:List (ValPerm (a,b)))
      enabled? (forall_pred
                  (fn vperm1 ->
                     exists_pred (fn vperm2 ->
                                    val_perm_weaker? (vperm1, vperm2)) vperms2)
                  vperms1) =>
      enabled? (val_perms_weaker? (vperms1,vperms2))

  (* ret_val_perm_weaker? *)

  theorem ret_val_perm_weaker_some is [a]
    fa (vperm1,vperm2:ValPerm (a,a))
      enabled? (val_perm_weaker? (vperm1,vperm2)) =>
      enabled? (ret_val_perm_weaker? (Some vperm1, Some vperm2))

  (* perm_weaker? *)

  theorem perm_weaker_novar is [a]
    fa (stperm: StPerm a)
      true => enabled? (perm_weaker? (NoVarPerm stperm, NoVarPerm stperm))

  theorem perm_weaker_var is [a]
    fa (x,vperm1,vperm2: ValPerm (a,a))
      enabled? (val_perm_weaker? (vperm1,vperm2)) =>
      enabled? (perm_weaker? (VarPerm (x, vperm1), VarPerm (x, vperm2)))

  (* Short-circuit for equal perms *)
  theorem perm_weaker_id is [a]
    fa (perm:Perm a)
      true => enabled? (perm_weaker? (perm,perm))

  (* perm_set_weaker? *)

  theorem perm_set_weaker_rule is [a]
    fa (perms1,perms2:PermSet a)
      enabled? (forall_pred
                  (fn perm1 ->
                     exists_pred (fn perm2 ->
                                    perm_weaker? (perm1, perm2)) perms2)
                  perms1)
      =>
      enabled? (perm_set_weaker? (perms1, perms2))

  (* arg_list_perms_perm_set_weaker? *)
  (* Special-purpose predicate to reduce the rewriting we need to do *)
  op [a] arg_list_perms_perm_set_weaker? (alperms: ArgListPerms a,
                                          vars: List (TypeName * Identifier),
                                          perms: PermSet a) : Bool =
    perm_set_weaker? (perm_set_of_arg_perms (alperms, map (fn x -> x.2) vars),
                      perms)

  theorem arg_list_perms_perm_set_weaker_1 is [a]
    fa (stperm:StPerm a,stperms,vperms,vars,perms)
      enabled? (exists_pred
                  (fn perm ->
                     perm_weaker? (NoVarPerm stperm, perm)) perms) &&
      enabled? (arg_list_perms_perm_set_weaker? ((stperms,vperms), vars, perms)) =>
      enabled? (arg_list_perms_perm_set_weaker?
                  ((stperm::stperms,vperms), vars, perms))

  theorem arg_list_perms_perm_set_weaker_2 is [a]
    fa (vperm,vperms,tp,var,vars,perms:PermSet a)
      enabled? (exists_pred
                  (fn perm ->
                     perm_weaker? (VarPerm (var,vperm), perm)) perms) &&
      enabled? (arg_list_perms_perm_set_weaker? (([],vperms), vars, perms)) =>
      enabled? (arg_list_perms_perm_set_weaker?
                  (([],vperm::vperms), ((tp,var)::vars), perms))

  theorem arg_list_perms_perm_set_weaker_3 is [a]
    fa (perms:PermSet a)
      true => enabled? (arg_list_perms_perm_set_weaker? (([],[]), [], perms))


  (***
   *** Giving Equality Permissions Back to the Current Permission Set
   ***)

  (* FIXME: documentation... *)

  type LValueAccessor =
   | LVA_Member Identifier
   | LVA_Memberp Identifier
   | LVA_Deref

  type UnzippedLValue = (Identifier * List LValueAccessor)

  op rezip_lvalue (uz: UnzippedLValue) : LValue =
    foldl (fn (lv,lva) ->
             case lva of
               | LVA_Member mem -> LV_member (lv, mem)
               | LVA_Memberp mem -> LV_memberp (E_lvalue lv, mem)
               | LVA_Deref -> LV_star (E_lvalue lv)) (LV_ident uz.1) uz.2

  op abs_of_lvalue_accessors (lvas: List LValueAccessor) : CToCAbstraction (Value, Value) =
    case lvas of
      | [] -> identity_abstraction
      | (LVA_Member mem)::lvas' ->
        compose_abstractions (struct_member_abstraction mem,
                              abs_of_lvalue_accessors lvas')
      | (LVA_Memberp mem)::lvas' ->
        compose_abstractions (compose_abstractions
                                (deref_abstraction,
                                 struct_member_abstraction mem),
                              abs_of_lvalue_accessors lvas')
      | LVA_Deref::lvas' ->
        compose_abstractions (deref_abstraction,
                              abs_of_lvalue_accessors lvas')

  op [a,b] give_back_permH (cperm_in: CValPerm a, splexpr: SplSetExpr,
                            lvas: List LValueAccessor, eq_lens: Lens (a,b),
                            cperm: CValPerm b, cperm_out: CValPerm a) : Bool =
    fa (asgn)
      perm_eval_weaker? (eval_cperm (asgn, splexpr) cperm_out,
                         conjoin_perm_evals
                           (eval_cperm (asgn, splexpr) cperm_in,
                            compose_abs_perm_eval
                              (abs_of_lvalue_accessors lvas,
                               eval_cperm (asgn, splexpr)
                                 (cperm_add_lens (cperm, eq_lens)))))

(*
  theorem give_back_permH_struct is [a,b]
    fa ()
      is_fold_pred_of (fn ((mem',cperm_opt), cperm_out, rest, cperm_out') ->
                         ifequal (mem, mem',
                                  caseopt
                                    (cperm_opt,
                                     (fn cperm_in' ->
                                        
)
)
                                  cperm_out ===
                                  
,
                                  rest)
)
      enabled? (give_back_permH (struct_cperm field_perms_in, splexpr,
                                 LVA_Member mem::lvas, eq_lens,
                                 cperm, cperm_out))
*)

  op [a,b] give_back_perm (perms_in: PermSet a, splexpr: SplSetExpr,
                           lv: LValue, eq_lens: Lens (a,b),
                           cperm: CValPerm b, perms_out: PermSet a) : Bool =
    fa (asgn)
      perm_eval_weaker? (eval_perm_set asgn perms_out,
                         conjoin_perm_evals
                           (eval_perm_set asgn perms_in,
                            compose_abs_perm_eval
                              (lvalue_abstraction lv,
                               eval_cperm (asgn, splexpr)
                                 (cperm_add_lens (cperm, eq_lens)))))


  (***
   *** Extracting Variable Perms from the Current Permission Set
   ***)

  (* Predicate to test if two lenses with possibly different output types are
  equal. We can't express equality at different types in Specware / Isabelle,
  however, so we state this by requiring an isomorphism between the output
  types, but only "choose" the "then" branch when they are actually equal. *)
  op [a,b,c] if_lens_eq (lens1:Lens (a,b), lens2:Lens (a,c),
                         res1: Bijection (b,c) -> Bool, res2: Bool) : Bool =
    (ex (iso) lens2 = lens_compose (lens1, iso_lens iso) && res1 iso) || res2

  theorem is_lens_eq_true is [a,b]
    fa (lens:Lens (a,b),res1,res2)
      enabled? (res1 (fn x -> x)) =>
      enabled? (if_lens_eq (lens, lens, res1, res2))

  theorem is_lens_eq_false is [a,b,c]
    fa (lens1:Lens (a,b),lens2:Lens (a,c),res1,res2)
      enabled? res2 =>
      enabled? (if_lens_eq (lens1, lens2, res1, res2))


  (* This predicate is used, when an lvalue lv is read to which we hold
  permission lv_cperm, to determine both the permissions that go along with the
  value being read from x as well as the remaining permissions to x that we hold
  after the read. *)
  (* NOTE: lv_perm need not be an application of cperm_add_lens; val_cperm and
  rem_lv_cperm will be applications of cperm_add_lens iff lv_perm is *)
  op [a] extract_perm_for_lv_read (lv_cperm: CValPerm a,
                                   val_cperm: CValPerm a,
                                   rem_lv_cperm: CValPerm a) : Bool =
    fa (lv)
      cperm_weaker?
        (conjoin_perms
           (compose_abs_perm
              (invert_abstraction (ctoc_abs_of_lens unit_lens), val_cperm),
            compose_abs_perm (lvalue_abstraction lv, rem_lv_cperm)),
         compose_abs_perm (lvalue_abstraction lv, lv_cperm))


  theorem extract_perm_for_lv_read_lens is [a,b]
    fa (lv_cperm, val_cperm, rem_lv_cperm, lens:Lens (a,b), val_cperm', rem_lv_cperm')
      enabled? (extract_perm_for_lv_read (lv_cperm, val_cperm', rem_lv_cperm')) &&&&
      val_cperm === cperm_add_lens (val_cperm', lens) &&
      rem_lv_cperm === cperm_add_lens (rem_lv_cperm', lens) =>
      enabled? (extract_perm_for_lv_read (cperm_add_lens (lv_cperm, lens),
                                          val_cperm, rem_lv_cperm))


  theorem extract_perm_for_lv_read_non_heap is [a]
    fa (R, val_cperm, rem_lv_cperm: CValPerm a)
      val_cperm = non_heap_cperm R &&
      rem_lv_cperm = non_heap_cperm R =>
      enabled? (extract_perm_for_lv_read (non_heap_cperm R,
                                          val_cperm, rem_lv_cperm))

  (* FIXME HERE: rules for structs, pointers, and arrays *)


  (* This predicate is used to find the variable in the current permission set
  that correponds to a given lens, and extract all permissions for that variable
  as value permissions *)
  op [a,b] extract_var_perm_for_lens (perms_in: PermSet a,
                                      var_lens: Lens (a,b),
                                      var: Identifier,
                                      vperm: ValPerm (a,b),
                                      perms_out: PermSet a) : Bool =
    perm_set_weaker? (VarPerm (var, val_perm_add_lens (vperm, var_lens))::perms_out,
                      perms_in)

  theorem extract_var_perm_for_lens_var is [a,b,c]
    fa (x,splexpr,cperm,lens:Lens (a,c),perms_in,var_lens:Lens (a,b),
        var,vperm_out,perms_out,perms_out',val_cperm,rem_cperm)
      enabled?
        (if_lens_eq (var_lens, lens,
                     (fn iso ->
                        extract_perm_for_lv_read (cperm, val_cperm, rem_cperm) &&&&
                        var === x &&&&
                        vperm_out === ValEqPerm (splexpr,
                                                 cperm_add_lens (val_cperm,
                                                                 iso_lens iso),
                                                 LV_ident x, var_lens) &&&&
                        perms_out ===
                        VarPerm (x, ValPerm (splexpr,
                                             cperm_add_lens
                                               (rem_cperm,lens))) :: perms_in
                        ),
                     (extract_var_perm_for_lens
                        (perms_in,var_lens,var,vperm_out,perms_out')) &&&&
                       perms_out ===
                       VarPerm (x, ValPerm (splexpr,
                                            cperm_add_lens
                                              (cperm, lens)))::perms_out'
                       ))
      =>
      enabled? (extract_var_perm_for_lens
                  (VarPerm
                     (x, ValPerm (splexpr,
                                  cperm_add_lens (cperm, lens)))::perms_in,
                   var_lens,var,vperm_out,perms_out))

  theorem extract_var_perm_for_lens_vareq is [a,b,c]
    fa (x,splexpr,cperm,lens',lens:Lens (a,c),lv,perms_in,var_lens:Lens (a,b),
        var,vperm_out,perms_out,perms_out',val_cperm,rem_cperm)
      enabled?
        (if_lens_eq (var_lens, lens,
                     (fn iso ->
                        extract_perm_for_lv_read (cperm, val_cperm, rem_cperm) &&&&
                        var === x &&&&
                        vperm_out === ValEqPerm (splexpr,
                                                 cperm_add_lens (val_cperm,
                                                                 iso_lens iso),
                                                 LV_ident x, var_lens) &&&&
                        perms_out ===
                        VarPerm (x, ValEqPerm (splexpr,
                                               cperm_add_lens
                                                 (rem_cperm,lens),
                                               lv, lens')) :: perms_in
                        ),
                     (extract_var_perm_for_lens
                        (perms_in,var_lens,var,vperm_out,perms_out')) &&&&
                       perms_out ===
                       VarPerm (x, ValEqPerm (splexpr,
                                              cperm_add_lens
                                                (cperm, lens),
                                              lv, lens'))::perms_out'
                       ))
      =>
      enabled? (extract_var_perm_for_lens
                  (VarPerm
                     (x, ValEqPerm (splexpr,
                                    cperm_add_lens (cperm, lens),
                                    lv, lens'))::perms_in,
                   var_lens,var,vperm_out,perms_out))


  theorem extract_var_perm_for_lens_novar is [a,b]
    fa (stperm,perms_in,var_lens:Lens (a,b),var,vperm_out,perms_out,perms_out')
      enabled? (extract_var_perm_for_lens
                  (perms_in,var_lens,var,vperm_out,perms_out')) &&
      perms_out = (NoVarPerm stperm)::perms_out'
      =>
      enabled? (extract_var_perm_for_lens
                  (NoVarPerm stperm::perms_in,
                   var_lens,var,vperm_out,perms_out))

  (* No rule for nil, because that means we couldn't find any perms! *)


  (***
   *** Extracting Structure Field Perms from Value Permissions
   ***)

  op [a,b] extract_field_perm_for_lensH (field_perms_in: StructFieldCPerms a,
                                         field_lens: Lens (a,b),
                                         field: Identifier,
                                         field_perms_out: StructFieldCPerms a,
                                         cperm_out: CValPerm b) : Bool =
    forall? (fn (mem,cperm_opt) ->
               if mem = field then
                 cperm_opt = None &&
                 (mem, Some (cperm_add_lens
                               (cperm_out, field_lens))) in? field_perms_in
               else
                 (mem,cperm_opt) in? field_perms_in) field_perms_out


  theorem extract_field_perm_for_lensH_cons is [a,b,c]
    fa (mem,cperm,lens:Lens (a,c),field_perms_in,field_lens:Lens (a,b),field,
        field_perms_out,field_perms_out',cperm_out)
      enabled? (if_lens_factors
                  (field_lens, lens,
                   (fn lens_suffix ->
                      cperm_out === cperm_add_lens (cperm, lens_suffix) &&&&
                      field === mem &&&&
                      field_perms_out === (mem, None)::field_perms_in
                    ),
                   extract_field_perm_for_lensH
                     (field_perms_in, field_lens, field,
                      field_perms_out', cperm_out) &&&&
                   field_perms_out ===
                     (mem, Some (cperm_add_lens (cperm,lens)))::field_perms_out'
                   ))
      =>
      enabled? (extract_field_perm_for_lensH
                  ((mem,Some (cperm_add_lens (cperm,lens)))::field_perms_in,
                   field_lens, field, field_perms_out, cperm_out))

  (* No rule for extract_field_perm_for_lensH_nil (that's failure!) *)


  (* FIXME: documentation *)
  op [a,b,c] extract_field_perm_for_lens (perms_in: PermSet a,
                                          vperm_in: ValPerm (a,b),
                                          field_lens: Lens (b,c),
                                          field: Identifier,
                                          deref?: Bool,
                                          perms_out: PermSet a,
                                          vperm_out: ValPerm (a,c)) : Bool =
    (fa (asgn)
       perm_eval_weaker? (conjoin_perm_evals
                            (perm_eval_add_view
                               (lift_unit_perm_eval (eval_perm_set asgn perms_out),
                                proj1_biview),
                             compose_abs_perm_eval
                               (if deref? then
                                compose_abstractions (deref_abstraction,
                                                      struct_member_abstraction field)
                                else struct_member_abstraction field,
                                eval_val_perm_any asgn (val_perm_add_lens (vperm_out, field_lens)))),
                          conjoin_perm_evals
                            (perm_eval_add_view
                               (lift_unit_perm_eval (eval_perm_set asgn perms_in),
                                proj1_biview),
                             eval_val_perm_any asgn vperm_in)))


  theorem extract_field_perm_for_lens_struct is [a,b,c,d]
    fa (perms_in,splexpr,field_perms_in,lens:Lens (b,d),field_lens,field_lens':Lens(d,c),
        field,deref?,perms_out,vperm_out:ValPerm (a,c),field_perms_out,cperm_out)
      enabled? (lens_factors_to (lens, field_lens, field_lens')) &&&&
      extract_field_perm_for_lensH (field_perms_in, field_lens', field,
                                    field_perms_out, cperm_out) &&&&
      deref? === false &&&&
      perms_out === perms_in &&&&
      vperm_out === ValPerm (splexpr, cperm_out)
      =>
      enabled? (extract_field_perm_for_lens
                  (perms_in,
                   ValPerm (splexpr,
                            cperm_add_lens (struct_cperm field_perms_in, lens)),
                   field_lens, field, deref?, perms_out, vperm_out))

  theorem extract_field_perm_for_lens_struct_eq is [a,b,c,d]
    fa (perms_in,splexpr,field_perms_in,lens:Lens (b,d),lv,eq_lens,field_lens,
        field_lens':Lens(d,c),field,deref?,perms_out,vperm_out:ValPerm (a,c),
        field_perms_out,cperm_out,lens_out)
      enabled? (lens_factors_to (lens, field_lens, field_lens')) &&&&
      extract_field_perm_for_lensH (field_perms_in, field_lens', field,
                                    field_perms_out, cperm_out) &&&&
      is_lens_compose (eq_lens, field_lens, lens_out) &&&&
      deref? === false &&&&
      give_back_perm (perms_in, splexpr, lv, eq_lens,
                      cperm_add_lens (struct_cperm field_perms_out, lens),
                      perms_out) &&&&
      vperm_out === ValEqPerm (splexpr, cperm_out,
                               LV_member (lv, field), lens_out)
      =>
      enabled? (extract_field_perm_for_lens
                  (perms_in,
                   ValEqPerm (splexpr,
                              cperm_add_lens (struct_cperm field_perms_in, lens),
                              lv, eq_lens),
                   field_lens, field, deref?, perms_out, vperm_out))

  theorem extract_field_perm_for_lens_struct_ptr is [a,b,c,d]
    fa (perms_in,splexpr,field_perms_in,lens:Lens (b,d),field_lens,field_lens':Lens(d,c),
        field,deref?,perms_out,vperm_out:ValPerm (a,c),field_perms_out,cperm_out)
      enabled? (lens_factors_to (lens, field_lens, field_lens')) &&&&
      extract_field_perm_for_lensH (field_perms_in, field_lens', field,
                                    field_perms_out, cperm_out) &&&&
      deref? === true &&&&
      perms_out === perms_in &&&&
      vperm_out === ValPerm (splexpr, cperm_add_lens (cperm_out, id_lens))
      =>
      enabled? (extract_field_perm_for_lens
                  (perms_in,
                   ValPerm (splexpr,
                            cperm_add_lens
                              (pointer_cperm (struct_cperm field_perms_in), lens)),
                   field_lens, field, deref?, perms_out, vperm_out))


  (***
   *** Constant Expressions
   ***)

  op [a,b] fun_matches_constant (f: a -> b, c:b) : Bool =
    f = (fn _ -> c)

  theorem fun_matches_constant_rule is [a,b]
    fa (c:b)
      true => enabled? (fun_matches_constant ((fn (x:a) -> c), c))

  (* Specialization of abstracts_expression to constants *)
  op [a,b] abstracts_expression_constant (envp: EnvPred) (perms_in: PermSet a)
                                         (perms_out: PermSet a)
                                         (vperm_out: ValPerm (a,b))
                                         (c: b) (m: Monad Value) : Bool =
    abstracts_expression envp perms_in perms_out vperm_out (fn _ -> c) m

  (* User-proved predicate: this is what "users" need to prove in order to
  refine constant a into an integer constant i, using a non-heap permission
  built with R. It holds iff iff R relates i to a. *)
  op [a] USER_abstracts_constant (c:a) (R: Relation (Value,a))
                                 (i:IntegerConstant) : Bool =
    integerConstant? i &&
    (case integerConstantType i of
       | None -> false
       | Some tp ->
         R (valueOfInt (tp, integerConstantValue i), c))

  theorem abstracts_expression_constant_rule is [a,b]
    fa (envp,perms_in:PermSet a,perms_out,vperm_out,c:b,m,R,i)
      enabled? (USER_abstracts_constant c R i) &&&&
      perms_out === perms_in &&&&
      vperm_out === ValPerm ([([],None)],
                             cperm_add_lens (non_heap_cperm R, id_lens)) &&&&
      m === ICONST_m i =>
      enabled? (abstracts_expression_constant envp perms_in
                  perms_out vperm_out c m)


  (***
   *** Boolean Expressions
   ***)

  theorem abstracts_constant_true is
    fa (R,i)
      R = bool_R && i = "1" =>
      enabled? (USER_abstracts_constant true R i)

  theorem abstracts_constant_false is
    fa (R,i)
      R = bool_R && i = "0" =>
      enabled? (USER_abstracts_constant false R i)


  (***
   *** Variable Expressions
   ***)

  (* abstracts_expression for variables, which are represented as lenses *)
  op [a,b] abstracts_expression_var (envp: EnvPred) (perms_in: PermSet a)
                                    (perms_out: PermSet a)
                                    (vperm_out: ValPerm (a,b))
                                    (lens: Lens (a,b))
                                    (m: Monad Value) : Bool =
    abstracts_expression envp perms_in perms_out vperm_out lens.lens_get m

  theorem abstracts_expression_var_rule is [a,b]
    fa (envp,perms_in,perms_out,vperm,lens:Lens (a,b),x,m)
      enabled? (extract_var_perm_for_lens
                  (perms_in, lens, x, vperm, perms_out)) &&&&
      m === VAR_m x =>
      enabled? (abstracts_expression_var envp perms_in perms_out vperm lens m)

  (* User-proved predicate: states that f should be seen as a lens for the
  purpose of synthesizing a variable expression *)
  op [a,b] USER_variable_lens (f: a -> b, lens: Lens (a,b)) : Bool =
    f = lens.lens_get

  (* Some useful lvalue-lenses *)
  theorem lvalue_lens_identity is [a]
    fa (lens:Lens (a,a))
      lens = id_lens =>
      enabled? (USER_variable_lens ((fn x -> x), lens))
  theorem lvalue_lens_proj1 is [a,b]
    fa (u:())
      true => enabled? (USER_variable_lens ((fn x -> x.1), proj1_lens:Lens (a*b,a)))
  theorem lvalue_lens_proj2 is [a,b]
    fa (u:())
      true => enabled? (USER_variable_lens ((fn x -> x.2), proj2_lens:Lens (a*b,b)))


  (***
   *** Unary Operations
   ***)

(*
  op [a,b] USER_abstracts_unary_op (envp: EnvPred) (g: a->b) (f: a->b)
                                   (oper: b->b) (uop:UnaryOp)
                                   (vabs: ValueAbs b) : Bool =
    fa (stree,vtree,r,a)
      envp (r.r_xenv, r.r_functions) &&
      g = (fn x -> oper (f x)) &&
      (vabs [] r).biview ((stree,vtree), f a) =>
      (ex (vtree')
         (computation_has_value r (stree [])
            (evaluatorForUnaryOp uop (return (vtree [])))
            (vtree' [])) &&
         (vabs [] r).biview ((stree,vtree'), oper (f a)))

  op [a,b] abstracts_expression_unary (envp: EnvPred) (perms_in: PermSet a)
                                      (perms_out: PermSet a)
                                      (vabs: ValueAbs b)
                                      (f: a -> b) (oper: b -> b) (uop:UnaryOp)
                                      (m: Monad Value) : Bool =
    USER_abstracts_unary_op envp (fn x -> oper (f x)) f oper uop vabs =>
    abstracts_expression
      envp perms_in perms_out
      [ValPerm ([([],None)], vabs)]
      (fn x -> oper (f x))
      m

  theorem abstracts_expression_unary_rule is [a,b]
    fa (envp,perms_in,perms_out,vperm_out,f:a->b,oper,m,uop,expr,vabs)
      enabled? (abstracts_expression envp perms_in perms_out vperm_out f expr) &&&&
      m === UNARYOP_m uop expr &&&&
      (* FIXME: the below should be the rhs is weaker than the left *)
      vperm_out === ValPerm ([([],None)], vabs) =>
      enabled? (abstracts_expression_unary envp perms_in
                  perms_out vabs f oper uop m)
*)


  (***
   *** Binary Operations
   ***)


  (***
   *** Struct Accesses
   ***)

  op make_member_maybe_deref (m: Monad Value, deref?: Bool,
                              mem: Identifier, m_out: Monad Value) : Bool =
    m_out = (if deref? then MEMBERP_m (m, mem) else MEMBER_m (m, mem))

  theorem make_member_maybe_deref_true is
    fa (m, mem, m_out)
      m_out = MEMBERP_m (m, mem) =>
      enabled? (make_member_maybe_deref (m, true, mem, m_out))

  theorem make_member_maybe_deref_false is
    fa (m, mem, m_out)
      m_out = MEMBER_m (m, mem) =>
      enabled? (make_member_maybe_deref (m, false, mem, m_out))


  op [a,b,c] abstracts_expression_struct_access (envp: EnvPred) (perms_in: PermSet a)
                                                (perms_out: PermSet a)
                                                (vperm_out: ValPerm (a,c))
                                                (field_lens: Lens (b,c))
                                                (e: a -> b) (m: Monad Value) : Bool =
    abstracts_expression envp perms_in perms_out vperm_out (fn x -> field_lens.lens_get (e x)) m


  theorem abstracts_expression_struct_access is [a,b,c]
    fa (envp,perms_in,perms_out,vperm_out,field_lens:Lens (b,c),e:a->b,m,
        perms_out',vperm',expr,field,deref?)
      enabled? (abstracts_expression envp perms_in perms_out' vperm' e expr) &&&&
      extract_field_perm_for_lens (perms_out', vperm', field_lens,
                                   field, deref?, perms_out, vperm_out) &&&&
      make_member_maybe_deref (expr, deref?, field, m)
      =>
      enabled? (abstracts_expression_struct_access
                  envp perms_in perms_out vperm_out field_lens e m)


  op [a,b,c] USER_struct_access (f:a->c, lens:Lens (b,c), e: a->b) : Bool =
    f = (fn x -> lens.lens_get (e x))


  (***
   *** General Rule for Expressions
   ***)

  theorem abstracts_expression_rule is [a,b,str]
    fa (envp,perms_in,perms_out,vperm_out,f:a->b,m,
        c,lens, (*,f_sub,oper,uop,vabs*)
        struct_lens,struct_e:a->str)
      clause (enabled? (fun_matches_constant (f, c)),
              abstracts_expression_constant envp perms_in perms_out vperm_out c m)
      ||||
      clause (enabled? (USER_variable_lens (f, lens)),
              abstracts_expression_var envp perms_in perms_out vperm_out lens m)
      (*
      ||
      (enabled? (USER_abstracts_unary_op envp f f_sub oper uop vabs) &&&&
       abstracts_expression_unary envp perms_in perms_out vabs f_sub oper uop m &&&&
       vperm_out === [ValPerm ([([],None)], vabs)])
         *)
      ||||
      clause (enabled? (USER_struct_access (f, struct_lens, struct_e)),
              abstracts_expression_struct_access
                envp perms_in perms_out vperm_out struct_lens struct_e m)
      =>
      enabled? (abstracts_expression envp perms_in perms_out vperm_out f m)


  (***
   *** If Statements
   ***)

  op [a,b] abstracts_ret_statement_if
      (envp:EnvPred) (perms_in:PermSet a) (perms_out:PermSet b)
      (ret_vperm:RetValPerm b) (e:a->Bool) (f1:a->b) (f2:a->b) (m:Monad ()) : Bool =
    abstracts_ret_statement
      envp perms_in perms_out ret_vperm (fn x -> if e x then f1 x else f2 x) m

  (* This generates an if statement all of whose branches must return *)
  theorem if_ret_correct is [a,b]
    fa (envp,perms_in,perms_out,ret_perms,eperms_out,evperm,
        perms_out1,ret_perms1,perms_out2,ret_perms2,
        e:a->Bool,expr,f1:a->b,f2,m1,m2,m)
      (enabled? (abstracts_expression envp perms_in eperms_out evperm e expr) &&&&
       (* FIXME: give back the evperm to eperms_out *)
       abstracts_ret_statement envp eperms_out perms_out1 ret_perms1 f1 m1 &&&&
       abstracts_ret_statement envp eperms_out perms_out2 ret_perms2 f2 m2 &&&&
       (* FIXME: unify these permissions, instead of just equating them... *)
       perms_out === perms_out1 &&&&
       perms_out === perms_out2 &&&&
       ret_perms === ret_perms1 &&&&
       ret_perms === ret_perms2 &&&&
       m === IFTHENELSE_m (expr, m1, m2)) =>
      enabled? (abstracts_ret_statement_if
                  envp perms_in perms_out ret_perms e f1 f2 m)

  op [a,b] fun_matches_if_expression (f:a->b, e:a->Bool, f1:a->b, f2:a->b) : Bool =
    f = (fn x -> if e x then f1 x else f2 x)

  theorem fun_matches_if_expression_rule is [a,b]
    fa (e,f1,f2:a->b)
      true => fun_matches_if_expression ((fn x -> if e x then f1 x else f2 x),
                                         e, f1, f2)


  (***
   *** Blocks
   ***)

  (* FIXME: documentation! *)


  (* FIXME: a block of length 1 still creates a fresh scope, so is not equal to
  the statement it contains; figure out another way to do this... *)
  (* Relation to turn a list of statements into a statement, omitting the block
  for the special case of a list of length 1 *)
  (*
  op block_as_statement? (block: List (Monad ()), stmt: Monad ()) : Bool =
    BLOCK_m block = stmt

  theorem block_as_statement_1 is
    fa (stmt,stmt_out)
      stmt_out = stmt => block_as_statement? ([STMT_m stmt], stmt_out)
  theorem block_as_statement_nil is
    fa (stmt_out)
      stmt_out = BLOCK_m [] => block_as_statement? ([], stmt_out)
  theorem block_as_statement_N is
    fa (stmt1,stmt2,stmts,stmt_out)
      stmt_out = BLOCK_m (stmt1::stmt2::stmts) =>
      block_as_statement? (stmt1::stmt2::stmts, stmt_out)
      *)


  (***
   *** Return Statements and Assignments to Output Variables
   ***)

  op [a,b,c,d] USER_is_return_expr (f:a->d, st_lens:Lens (a,b), e: a->c,
                                    iso:Bijection (b*c,d)) : Bool =
    f = (fn x -> iso (st_lens.lens_get x, e x))

  op [a,b,c,d] abstracts_ret_statement_return
      (envp:EnvPred) (perms_in:PermSet a) (perms_out:PermSet d)
      (ret_vperm:RetValPerm d) (st_lens:Lens (a,b)) (e:a->c)
      (iso:Bijection (b*c,d)) (m:Monad ()) : Bool =
    abstracts_ret_statement
      envp perms_in perms_out ret_vperm
      (fn x -> iso (st_lens.lens_get x, e x))
      m

  (* The core correctness theorem for returns that return a value; all other
  theorems for generating return statements should be reduced to this one,
  basically by adding a lens and/or some isomorphisms. This theorem is actually
  doing two things at once: it is generating a return statement from the
  expression given in the second projection of the pair, but is also
  "forgetting" permissions that are not represented in the first projection of
  the pair. This latter task is handled by the unmapping. *)
  (* FIXME: update above documentation... *)
  theorem return_correct is [a,b,c,d]
    fa (envp,perms_in,perms_out,ret_vperm,eperms_out,evperm,
        st_lens,e:a->c,iso:Bijection (b*c,d),
        expr,stmt,perms_out1,perms_out2,ret_vperm1,
        perms_out_lens,ret_vperm_lens)
      enabled? (abstracts_expression envp perms_in eperms_out evperm e expr) &&&&
      perm_set_factors_to st_lens (eperms_out, perms_out1) &&&&
      is_lens_compose (iso_lens (inverse iso), proj1_lens, perms_out_lens) &&&&
      is_perm_set_add_lens perms_out_lens (perms_out1, perms_out2) &&&&
      is_lens_compose (iso_lens (inverse iso), proj2_lens, ret_vperm_lens) &&&&
      is_val_perm_add_lens ret_vperm_lens (evperm, ret_vperm1) &&&&
      perms_out === perms_out2 &&&&
      ret_vperm === Some ret_vperm1 &&
      stmt = RETURN_m expr =>
      enabled? (abstracts_ret_statement_return
                  envp perms_in perms_out ret_vperm st_lens e iso stmt)


  op [a,b] USER_is_return_void (f:a->b, lens:Lens (a,b)) : Bool =
    f = lens.lens_get

  op [a,b] abstracts_ret_statement_return_void
      (envp:EnvPred) (perms_in:PermSet a) (perms_out:PermSet b)
      (ret_vperm:RetValPerm b) (st_lens:Lens (a,b)) (m:Monad ()) : Bool =
    abstracts_ret_statement envp perms_in perms_out ret_vperm st_lens.lens_get m

  (* The core correctness theorem for void returns, similar to
  return_correct. As with that theorem, the lens is for "forgetting"
  permissions, which is handled by the unmapping. *)
  theorem return_void_correct is [a,b]
    fa (envp,perms_in,lens:Lens (a,b),stmt,ret_perms,perms_out,perms_out1)
      perm_set_factors_to lens (perms_in, perms_out1) &&&&
      perms_out = perms_out1 &&
      ret_perms = None &&
      stmt = RETURN_VOID_m =>
      enabled? (abstracts_ret_statement_return_void
                  envp perms_in perms_out ret_perms lens stmt)


  (* Common patterns for matching return statements *)

  theorem USER_return_expr_unit_pair is [a,b]
    fa (st_lens,e_out,iso,e:a->b)
      st_lens = unit_lens &&
      e_out = e &&
      iso = (fn x -> x) =>
      enabled? (USER_is_return_expr ((fn x -> ((), e x)), st_lens, e_out, iso))

  theorem USER_return_expr_unit_pair_bool is [a]
    fa (st_lens,e_out,iso,e:a->Bool)
      st_lens = unit_lens &&
      e_out = e &&
      iso = (fn x -> x) =>
      enabled? (USER_is_return_expr ((fn x -> ((), e x)), st_lens, e_out, iso))

  theorem USER_return_expr_in_pair_unit_pair is [a]
    fa (st_lens,e_out,iso,e:a)
      st_lens = unit_lens &&
      e_out = (fn _ -> e) &&
      iso = (fn x -> x) =>
      enabled? (USER_is_return_expr ((fn () -> ((), e)), st_lens, e_out, iso))

  theorem USER_return_expr_in_pair_unit_pair_bool is
    fa (st_lens,e_out,iso,e:Bool)
      st_lens = unit_lens &&
      e_out = (fn _ -> e) &&
      iso = (fn x -> x) =>
      enabled? (USER_is_return_expr ((fn () -> ((), e)), st_lens, e_out, iso))


  (***
   *** General Rules for Statements
   ***)

  theorem abstracts_ret_statement_rule is [a,b,c,d]
    fa (envp,perms_in:PermSet a,perms_out:PermSet b,ret_vperm,f,m,
        ret_lens,ret_e,ret_iso:Bijection (c*d,b),
        retv_lens,if_cond,if_f1,if_f2)
      clause (enabled? (USER_is_return_expr (f, ret_lens, ret_e, ret_iso)),
              (abstracts_ret_statement_return
                 envp perms_in perms_out ret_vperm ret_lens ret_e ret_iso m))
      ||||
      clause (enabled? (USER_is_return_void (f, retv_lens)),
              (abstracts_ret_statement_return_void
                 envp perms_in perms_out ret_vperm retv_lens m))
      ||||
      clause (enabled? (fun_matches_if_expression (f, if_cond, if_f1, if_f2)),
              (abstracts_ret_statement_if
                 envp perms_in perms_out ret_vperm if_cond if_f1 if_f2 m))
      =>
      enabled? (abstracts_ret_statement envp perms_in perms_out ret_vperm f m)


  (***
   *** Functions
   ***)

  (* FIXME: need permissions to deallocate the current stack from at the end of body *)
  (* FIXME: also need a value_abs_has_type precondition *)
  theorem FUNCTION_correct is [a,b]
    fa (envp,perms_in,perms_in_sub,perms_out,ret_perms,perms_out_sub,ret_perms_sub,
        f:a->b,m,prototype,body)
      m = FUNCTION_m (prototype.1, prototype.2, prototype.3, body) &&
      enabled? (in_pred (StPerm ([([], None)],
                                 cperm_add_lens (auto_allocation_perm, unit_lens)),
                         perms_out.1)) &&&&
      is_perm_set_of_arg_perms (perms_in, prototype.3, perms_in_sub) &&&&
      (* perms_in_sub === perm_set_of_arg_perms (perms_in, map (fn x -> x.2) prototype.3) &&&& *)
      (abstracts_ret_statement
         envp
         perms_in_sub
         perms_out_sub
         ret_perms_sub
         f
         body) &&&&
      arg_list_perms_perm_set_weaker? (perms_out, prototype.3, perms_out_sub) &&&&
      ret_val_perm_weaker? (ret_perms, ret_perms_sub) =>
      abstracts_c_function_decl envp perms_in perms_out ret_perms f prototype m

end-spec
