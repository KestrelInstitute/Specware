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
  theorem enable_second_conjunct is [a]
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
      forall_pred pred (x::l)

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


  (***
   *** Relational Versions of Operations on Permissions
   ***)

  (* We define relational versions of all these operations on permissions, as
  well as theorems to "compute" them, as strengthening rules *)


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


  (* val_perm_add_view *)

  op [a,b] is_val_perm_add_view (bv: BisimView (b,a)) (vperm: ValPerm a,
                                                       vperm_out: ValPerm b) : Bool =
    val_perm_add_view (vperm, bv) = vperm_out

  theorem is_val_perm_add_view_val is [a,b,c]
    fa (splexpr,vabs:ValueAbs c,bv1,bv:BisimView (b,a),bv_out,vperm_out)
      enabled? (is_compose_biviews (bv, bv1, bv_out)) &&
      vperm_out = ValPerm (splexpr, value_abs_add_view (vabs, bv_out)) =>
      enabled? (is_val_perm_add_view bv (ValPerm (splexpr,
                                               value_abs_add_view (vabs, bv1)),
                                         vperm_out))

  theorem is_val_perm_add_view_valeq is [a,b,c]
    fa (splexpr,vabs:ValueAbs c,bv1,bv:BisimView (b,a),bv_out,vperm_out,lv)
      enabled? (is_compose_biviews (bv, bv1, bv_out)) &&
      vperm_out = ValEqPerm (splexpr, value_abs_add_view (vabs, bv_out), lv) =>
      enabled? (is_val_perm_add_view bv
                  (ValEqPerm (splexpr, value_abs_add_view (vabs, bv1), lv),
                   vperm_out))

  theorem is_val_perm_add_view_vali is [a,b]
    fa (impl,bv:BisimView (b,a),vperm_out)
      vperm_out = ValIPerm impl =>
      enabled? (is_val_perm_add_view bv (ValIPerm impl, vperm_out))


  (* val_perms_add_view *)

  op [a,b] is_val_perms_add_view (bv: BisimView (b,a))
                                 (vperms: List (ValPerm a),
                                  vperms_out: List (ValPerm b)) : Bool =
    val_perms_add_view (vperms, bv) = vperms_out

  theorem is_val_perms_add_view_rule is [a,b]
    fa (vperms, bv:BisimView (b,a), vperms_out)
      enabled? (is_map_pred_of (is_val_perm_add_view bv) (vperms, vperms_out)) =>
      enabled? (is_val_perms_add_view bv (vperms, vperms_out))


  (* st_perm_add_view *)

  op [a,b] is_st_perm_add_view (bv: BisimView (b,a)) (stperm: StPerm a,
                                                       stperm_out: StPerm b) : Bool =
    st_perm_add_view (stperm, bv) = stperm_out

  theorem is_st_perm_add_view_1 is [a,b,c]
    fa (splexpr,uabs:UnitAbs c,bv1,bv:BisimView (b,a),bv_out,stperm_out)
      enabled? (is_compose_biviews (bv, bv1, bv_out)) &&
      stperm_out = StPerm (splexpr, unit_abs_add_view (uabs, bv_out)) =>
      enabled? (is_st_perm_add_view bv (StPerm (splexpr,
                                                unit_abs_add_view (uabs, bv1)),
                                         stperm_out))

  theorem is_st_perm_add_view_2 is [a,b]
    fa (impl,bv:BisimView (b,a),stperm_out)
      stperm_out = StIPerm impl =>
      enabled? (is_st_perm_add_view bv (StIPerm impl, stperm_out))


  (* st_perms_add_view *)

  op [a,b] is_st_perms_add_view (bv: BisimView (b,a))
                                (stperms: List (StPerm a),
                                 stperms_out: List (StPerm b)) : Bool =
    st_perms_add_view (stperms, bv) = stperms_out

  theorem is_st_perms_add_view_rule is [a,b]
    fa (stperms, bv:BisimView (b,a), stperms_out)
      enabled? (is_map_pred_of (is_st_perm_add_view bv) (stperms, stperms_out)) =>
      enabled? (is_st_perms_add_view bv (stperms, stperms_out))


  (* perm_add_view *)

  op [a,b] is_perm_add_view (bv: BisimView (b,a)) (perm: Perm a,
                                                   perm_out: Perm b) : Bool =
    perm_add_view (perm, bv) = perm_out

  theorem is_perm_add_view_var is [a,b]
    fa (x,vperm,bv:BisimView (b,a),vperm_out,perm_out)
      enabled? (is_val_perm_add_view bv (vperm, vperm_out)) &&
      perm_out = VarPerm (x, vperm_out) =>
      enabled? (is_perm_add_view bv (VarPerm (x, vperm), perm_out))

  theorem is_perm_add_view_novar is [a,b]
    fa (stperm,bv:BisimView (b,a),stperm_out,perm_out)
      enabled? (is_st_perm_add_view bv (stperm, stperm_out)) &&
      perm_out = NoVarPerm stperm_out =>
      enabled? (is_perm_add_view bv (NoVarPerm stperm, perm_out))


  (* perm_set_add_view *)

  op [a,b] is_perm_set_add_view (bv: BisimView (b,a)) (perms: PermSet a,
                                                       perms_out: PermSet b) : Bool =
    perm_set_add_view (perms, bv) = perms_out

  theorem is_perm_set_add_view_rule is [a,b]
    fa (perms,bv:BisimView (b,a),perms_out)
      enabled? (is_map_pred_of (is_perm_add_view bv) (perms, perms_out)) =>
      enabled? (is_perm_set_add_view bv (perms, perms_out))


  (* perm_set_of_arg_perms *)

  op [a] is_perm_set_of_arg_perms (perms: ArgListPerms a, vars: ParameterList,
                                   perm_set: PermSet a) : Bool =
    equiLong (perms.2, vars) &&
    perm_set = perm_set_of_arg_perms (perms, map (fn x -> x.2) vars)

  theorem is_perm_set_of_arg_perms_rule is [a]
    fa (st_perms,vpermss,params,perm_set_out:PermSet a,perms_out1,permss_out2,perms_out2)
      enabled? (is_map_of NoVarPerm (st_perms, perms_out1)) &&
      enabled? (is_map2_pred_of
                  (fn ((_,var),vperms,var_out_perms) ->
                     is_map_of (fn vperm -> VarPerm (var, vperm))
                       (vperms, var_out_perms))
                  (params, vpermss, permss_out2)) &&&&
      is_flatten_of (permss_out2, perms_out2) &&&&
      is_append (perms_out1, perms_out2, perm_set_out) =>
      enabled? (is_perm_set_of_arg_perms ((st_perms,vpermss), params,
                                          perm_set_out))


  (***
   *** Unfolding / Simplifying Things
   ***)

  (* The user needs to supply theorems for this to unfold the definition of any
  value abstraction they use *)
  op [a] USER_unfold_value_abs (vabs: ValueAbs a,
                                vabs_unfolded: ValueAbs a) : Bool =
    vabs = vabs_unfolded

  theorem unfold_bool_valueabs is
    fa (vabs')
      vabs' = non_heap_abstraction (fn (v,b) -> zeroScalarValue? v = return b) =>
      enabled? (USER_unfold_value_abs (bool_valueabs, vabs'))

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


  (***
   *** Extracting Variable Perms from the Current Permission Set
   ***)

  (* This predicate is used, when a variable x is read to which we hold
  permission var_perm, to determine the both the permissions that go along with
  the value being read from x as well as the remaining permissions to x that we
  hold after the read. *)
  op [a] extract_perm_for_var_read_pred (var_abs: ValueAbs a,
                                         read_abs: ValueAbs a,
                                         rem_var_abs: ValueAbs a) : Bool =
    fa (x,spl)
      abstraction_weaker?
        (conjoin_abstractions
           (read_abs spl,
            compose_abstractions
              (ctoc_abs_of_lens unit_lens,
               compose_abstractions
                 (lvalue_abstraction (LV_ident x),
                  rem_var_abs spl))),
         compose_abstractions
           (ctoc_abs_of_lens unit_lens,
            compose_abstractions
              (lvalue_abstraction (LV_ident x),
               var_abs spl)))

  (* Same as the above, but will only be applied to unfolded value
  abstractions (as defined above) *)
  op [a] extract_perm_for_var_read_pred_SIMP (var_abs: ValueAbs a,
                                              read_abs: ValueAbs a,
                                              rem_var_abs: ValueAbs a) : Bool =
    extract_perm_for_var_read_pred (var_abs, read_abs, rem_var_abs)


  theorem extract_perm_for_var_read_pred_rule is [a]
    fa (var_abs, read_abs, rem_var_abs, var_abs': ValueAbs a)
      enabled? (USER_unfold_value_abs (var_abs, var_abs')) &&&&
      extract_perm_for_var_read_pred_SIMP (var_abs', read_abs, rem_var_abs) =>
      extract_perm_for_var_read_pred (var_abs', read_abs, rem_var_abs)

  theorem extract_perm_for_var_read_pred_rule1 is [a]
    fa (R, read_abs, rem_var_abs: ValueAbs a)
      read_abs = non_heap_abstraction R &&
      rem_var_abs = non_heap_abstraction R =>
      enabled? (extract_perm_for_var_read_pred_SIMP (non_heap_abstraction R,
                                                     read_abs, rem_var_abs))

  (* FIXME HERE: rules for structs, pointers, and arrays *)


  (* This predicate is used to find the variable in the current permission set
  that correponds to a given lens, and extract all permissions for that variable
  as value permissions *)
  op [a,b] extract_var_perms_for_lens_pred (perms_in: PermSet a,
                                            var_bv: BisimView (a,b),
                                            var: Identifier,
                                            vperms: List (ValPerm b),
                                            perms_out: PermSet a) : Bool =
    perm_set_weaker? (perms_out ++
                      map (fn vperm ->
                             VarPerm (var, val_perm_add_view (vperm, var_bv)))
                        vperms,
                      perms_in)


  op [a,b] extract_var_perms_for_lens_pred_SIMP (perms_in: PermSet a,
                                                 var_bv: BisimView (a,b),
                                                 var: Identifier,
                                                 vperms: List (ValPerm b),
                                                 perms_out: PermSet a) : Bool =
    extract_var_perms_for_lens_pred (perms_in, var_bv, var, vperms, perms_out)


  theorem extract_var_perms_for_lens_pred_var1 is [a,b]
    fa (x,splexpr,vabs,perms_in,var_bv:BisimView (a,b),
        var,vperms_out,perms_out,vperms',perms_out',read_vabs,rem_vabs)
      enabled? (extract_var_perms_for_lens_pred
                  (perms_in,var_bv,var,vperms',perms_out')) &&
      enabled? (extract_perm_for_var_read_pred (vabs, read_vabs, rem_vabs)) &&
      var = x &&
      vperms_out = ValPerm (splexpr,
                            value_abs_add_view
                              (read_vabs, identity_biview))::vperms' &&
      perms_out = VarPerm (x,
                           ValEqPerm (splexpr,
                                      value_abs_add_view (rem_vabs, var_bv),
                                      LV_ident x))::perms_out'
      =>
      enabled? (extract_var_perms_for_lens_pred_SIMP
                  (VarPerm
                     (x, ValPerm (splexpr, value_abs_add_view (vabs, var_bv)))
                     ::perms_in,
                   var_bv,var,vperms_out,perms_out))


  theorem extract_var_perms_for_lens_pred_var2 is [a,b,c]
    fa (x,splexpr,vabs,bv:BisimView (a,b),perms_in,var_bv:BisimView (a,c),
        var,vperms_out,perms_out,vperms',perms_out')
      enabled? (extract_var_perms_for_lens_pred
                  (perms_in,var_bv,var,vperms',perms_out')) &&
      vperms_out = vperms' &&
      perms_out = VarPerm (x, ValPerm (splexpr,
                                       value_abs_add_view (vabs, bv)))::perms_out'
      =>
      enabled? (extract_var_perms_for_lens_pred_SIMP
                  (VarPerm
                     (x, ValPerm (splexpr,
                                    value_abs_add_view (vabs, bv)))
                     ::perms_in,
                   var_bv,var,vperms_out,perms_out))

  theorem extract_var_perms_for_lens_pred_novar is [a,b]
    fa (stperm,perms_in,var_bv:BisimView (a,b),var,vperms_out,perms_out,perms_out')
      enabled? (extract_var_perms_for_lens_pred
                  (perms_in,var_bv,var,vperms_out,perms_out')) &&
      perms_out = (NoVarPerm stperm)::perms_out'
      =>
      enabled? (extract_var_perms_for_lens_pred_SIMP
                  (NoVarPerm stperm::perms_in,
                   var_bv,var,vperms_out,perms_out))


  theorem extract_var_perms_for_lens_pred_rule is [a,b]
    fa (perms_in, var_bv:BisimView (a,b), var_bv_simp, var, vperms, perms_out)
      enabled? (USER_simplify_biview (var_bv, var_bv_simp)) &&&&
      extract_var_perms_for_lens_pred_SIMP (perms_in, var_bv_simp,
                                            var, vperms, perms_out) =>
      enabled? (extract_var_perms_for_lens_pred (perms_in, var_bv,
                                                 var, vperms, perms_out))


  (***
   *** Unmapping Permission Sets
   ***)

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


  (* This predicate is used to attempt to decompose bv into the composition of
  bv_prefix and some bv_suffix. If this is not possible, then we can always use
  bv_suffix = the trivial biview, so we define this predicate using
  biview_weaker? instead of equality. *)
  op [a,b,c] biview_decomposes_to (bv: BisimView (a,c), bv_prefix: BisimView (a,b),
                                   bv_suffix: BisimView (b,c)) : Bool =
    biview_weaker? (compose_biviews (bv_prefix, bv_suffix), bv)

  (* A double-lens biview can always be used for decomposition by decomposing
  w.r.t the first lens and then post-composing the second afterwards *)
  theorem biview_decomposes_lens_pair is [a,b,c,d]
    fa (bv,lens1:Lens (a,b),lens2:Lens (c,b),bv_suffix:BisimView (c,d),bv_suffix')
      enabled? (biview_decomposes_to (bv, biview_of_lens lens1, bv_suffix')) &&&&
      is_compose_biviews (biview_of_lens (lens2), bv_suffix', bv_suffix) =>
      enabled? (biview_decomposes_to (bv, biview_of_lens_pair (lens1,lens2),
                                      bv_suffix))

  (* The unit lens is not a prefix of anything, so bv_suffix here is trivial. *)
  theorem biview_decomposes_unit_lens is [a,b]
    fa (bv:BisimView (a,b),bv_suffix)
      bv_suffix = trivial_biview =>
      enabled? (biview_decomposes_to (bv, biview_of_lens unit_lens, bv_suffix))


  (* FIXME HERE: theorems for decomposing biviews *)


  (* Predicate for un-mapping value permissions *)
  op [a,b] val_perm_unmaps_to (bv_prefix: BisimView (a,b))
                              (vperm_in: ValPerm a, vperm_out: ValPerm b) : Bool =
    val_perm_weaker? (val_perm_add_view (vperm_out, bv_prefix), vperm_in)

  theorem val_perm_unmaps_to_1 is [a,b,c]
    fa (splexpr,vabs:ValueAbs c,bv,bv_prefix:BisimView (a,b),bv_suffix,vperm_out)
      enabled? (biview_decomposes_to (bv, bv_prefix, bv_suffix)) &&&&
      vperm_out === ValPerm (splexpr,value_abs_add_view (vabs, bv_suffix)) =>
      enabled? (val_perm_unmaps_to
                  bv_prefix
                  (ValPerm (splexpr,value_abs_add_view (vabs, bv)), vperm_out))

  theorem val_perm_unmaps_to_2 is [a,b,c]
    fa (impl,bv_prefix:BisimView (a,b),vperm_out)
      vperm_out = ValIPerm impl =>
      enabled? (val_perm_unmaps_to bv_prefix (ValIPerm impl, vperm_out))


  (* Predicate for un-mapping storage permissions *)
  op [a,b] st_perm_unmaps_to (bv_prefix: BisimView (a,b))
                              (stperm_in: StPerm a, stperm_out: StPerm b) : Bool =
    st_perm_weaker? (st_perm_add_view (stperm_out, bv_prefix), stperm_in)

  theorem st_perm_unmaps_to_1 is [a,b,c]
    fa (splexpr,uabs:UnitAbs c,bv,bv_prefix:BisimView (a,b),bv_suffix,stperm_out)
      enabled? (biview_decomposes_to (bv, bv_prefix, bv_suffix)) &&&&
      stperm_out === StPerm (splexpr,unit_abs_add_view (uabs, bv_suffix)) =>
      enabled? (st_perm_unmaps_to
                  bv_prefix
                  (StPerm (splexpr,unit_abs_add_view (uabs, bv)), stperm_out))

  theorem st_perm_unmaps_to_2 is [a,b,c]
    fa (impl,bv_prefix:BisimView (a,b),stperm_out)
      stperm_out = StIPerm impl =>
      enabled? (st_perm_unmaps_to bv_prefix (StIPerm impl, stperm_out))


  (* Predicate for un-mapping individual permissions *)
  op [a,b] perm_unmaps_to (bv_prefix: BisimView (a,b))
                          (perm_in: Perm a, perm_out: Perm b) : Bool =
    perm_weaker? (perm_add_view (perm_out, bv_prefix), perm_in)

  theorem perm_unmaps_to_var is [a,b]
    fa (x,bv_prefix:BisimView (a,b),vperm,vperm_out,perm_out)
      enabled? (val_perm_unmaps_to bv_prefix (vperm, vperm_out)) &&&&
      perm_out === VarPerm (x, vperm_out) =>
      enabled? (perm_unmaps_to bv_prefix (VarPerm (x, vperm), perm_out))

  theorem perm_unmaps_to_novar is [a,b]
    fa (stperm,stperm_out,perm_out,bv_prefix:BisimView (a,b))
      enabled? (st_perm_unmaps_to bv_prefix (stperm, stperm_out)) &&&&
      perm_out = NoVarPerm stperm_out =>
      enabled? (perm_unmaps_to bv_prefix (NoVarPerm stperm, perm_out))


  (* Predicate for un-mapping permission sets *)
  op [a,b] perm_set_unmaps_to (bv_prefix: BisimView (a,b))
                              (perms_in: PermSet a,
                               perms_out: PermSet b) : Bool =
    perm_set_weaker? (perm_set_add_view (perms_out, bv_prefix), perms_in)

  theorem perm_set_unmaps_to_rule is [a,b]
    fa (bv_prefix: BisimView (a,b),perms_in,perms_out)
      enabled? (is_map_pred_of (perm_unmaps_to bv_prefix) (perms_in, perms_out)) =>
      enabled? (perm_set_unmaps_to bv_prefix (perms_in, perms_out))


  (***
   *** Proving perm_set_weaker?
   ***)

  theorem perm_weaker_id is [a]
    fa (perm: Perm a)
      true => perm_weaker? (perm, perm)

  op [a] perm_weaker_than_set? (perm: Perm a, perms: PermSet a) : Bool =
    perm_set_weaker? ([perm], perms)

  theorem perm_weaker_than_set_rule is [a]
    fa (perm:Perm a, perm1, perms)
      enabled? (perm_weaker? (perm, perm1)) ||
      enabled? (perm_weaker_than_set? (perm, perms)) =>
      perm_weaker_than_set? (perm, perm1::perms)


  (* perm_set_weaker *)

  theorem perm_set_weaker_rule is [a]
    fa (perms_l,perms_r:PermSet a)
      enabled? (forall_pred
                  (fn perm -> perm_weaker_than_set? (perm, perms_r))
                  perms_l)
      =>
      enabled? (perm_set_weaker? (perms_l, perms_r))


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
                                         (vperms_out: List (ValPerm b))
                                         (c: b) (m: Monad Value) : Bool =
    abstracts_expression envp perms_in perms_out vperms_out (fn _ -> c) m

  (* User-proved predicate: this is what "users" need to prove in order to
  refine constant a into an integer constant i. It holds iff iff vabs relates i,
  in any storage tree, to a. *)
  op [a] user_abstracts_constant (envp:EnvPred) (c:a) (vabs:ValueAbs a)
                                 (i:IntegerConstant) : Bool =
    integerConstant? i &&
    (case integerConstantType i of
       | None -> false
       | Some tp ->
         (fa (stree,r)
            envp (r.r_xenv, r.r_functions) =>
            (vabs [] r).biview
              ((stree,(fn _ -> valueOfInt (tp, integerConstantValue i))), c)))

  theorem abstracts_expression_constant_rule is [a,b]
    fa (envp,perms_in:PermSet a,perms_out,vperms_out,c:b,m,vabs,i)
      enabled? (user_abstracts_constant envp c vabs i) &&&&
      perms_out === perms_in &&&&
      vperms_out === [ValPerm ([([],None)],
                               value_abs_add_view (vabs, identity_biview))] &&&&
      m === ICONST_m i =>
      enabled? (abstracts_expression_constant envp perms_in
                  perms_out vperms_out c m)


  (***
   *** Boolean Expressions
   ***)

  theorem abstracts_constant_true is
    fa (envp,vabs,i)
      vabs = bool_valueabs && i = "1" =>
      enabled? (user_abstracts_constant envp true vabs i)

  theorem abstracts_constant_false is
    fa (envp,vabs,i)
      vabs = bool_valueabs && i = "0" =>
      enabled? (user_abstracts_constant envp false vabs i)


  (***
   *** Variable Expressions
   ***)

  (* abstracts_expression for variables, which are represented as lenses *)
  op [a,b] abstracts_expression_var (envp: EnvPred) (perms_in: PermSet a)
                                    (perms_out: PermSet a)
                                    (vperms_out: List (ValPerm b))
                                    (lens: Lens (a,b))
                                    (m: Monad Value) : Bool =
    abstracts_expression envp perms_in perms_out vperms_out lens.lens_get m

  theorem abstracts_expression_var_rule is [a,b]
    fa (envp,perms_in,perms_out,vperms,lens:Lens (a,b),x,m)
      enabled? (extract_var_perms_for_lens_pred
                  (perms_in, biview_of_lens lens, x, vperms, perms_out)) &&&&
      m === VAR_m x =>
      enabled? (abstracts_expression_var envp perms_in perms_out vperms lens m)

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
    fa (envp,perms_in,perms_out,vperms_out,f:a->b,oper,m,uop,expr,vabs)
      enabled? (abstracts_expression envp perms_in perms_out vperms_out f expr) &&&&
      m === UNARYOP_m uop expr &&&&
      (* FIXME: the below should be the rhs is weaker than the left *)
      vperms_out === [ValPerm ([([],None)], vabs)] =>
      enabled? (abstracts_expression_unary envp perms_in
                  perms_out vabs f oper uop m)


  (***
   *** Binary Operations
   ***)


  (***
   *** General Rule for Expressions
   ***)

  theorem abstracts_expression_rule is [a,b]
    fa (envp,perms_in,perms_out,vperms_out,f:a->b,m,
        c,lens,f_sub,oper,uop,vabs)
      (enabled? (fun_matches_constant (f, c)) &&&&
       abstracts_expression_constant envp perms_in perms_out vperms_out c m)
      ||
      (enabled? (USER_variable_lens (f, lens)) &&&&
       abstracts_expression_var envp perms_in perms_out vperms_out lens m)
      ||
      (enabled? (USER_abstracts_unary_op envp f f_sub oper uop vabs) &&&&
       abstracts_expression_unary envp perms_in perms_out vabs f_sub oper uop m &&&&
       vperms_out === [ValPerm ([([],None)], vabs)]) =>
      enabled? (abstracts_expression envp perms_in perms_out vperms_out f m)


  (***
   *** If Statements
   ***)

  (* This generates an if statement all of whose branches must return *)
  theorem if_ret_correct is [a,b]
    fa (envp,perms_in,perms_out,ret_perms,eperms_out,evperms,
        perms_out1,ret_perms1,perms_out2,ret_perms2,
        e:a->Bool,expr,f1:a->b,f2,m1,m2,m)
      (enabled? (abstracts_expression envp perms_in eperms_out evperms e expr) &&&&
       (* FIXME: give back the evperms to eperms_out *)
       abstracts_ret_statement envp eperms_out perms_out1 ret_perms1 f1 m1 &&&&
       abstracts_ret_statement envp eperms_out perms_out2 ret_perms2 f2 m2 &&&&
       (* FIXME: unify these permissions, instead of just equating them... *)
       perms_out = perms_out1 &&
       perms_out = perms_out2 &&
       ret_perms = ret_perms1 &&
       ret_perms = ret_perms2 &&
       m = IFTHENELSE_m (expr, m1, m2)) =>
      enabled? (abstracts_ret_statement
                  envp perms_in perms_out ret_perms
                  (fn x -> if e x then f1 x else f2 x)
                  m)


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

  (* The core correctness theorem for returns that return a value; all other
  theorems for generating return statements should be reduced to this one,
  basically by adding a lens and/or some isomorphisms. This theorem is actually
  doing two things at once: it is generating a return statement from the
  expression given in the second projection of the pair, but is also
  "forgetting" permissions that are not represented in the first projection of
  the pair. This latter task is handled by the unmapping. *)
  theorem return_correct is [a,b,c]
    fa (envp,perms_in,perms_out,ret_perms,eperms_out,evperms,
        lens:Lens (a,b),e:a->c,
        expr,stmt,perm_set_out,val_perms_out)
      (enabled? (abstracts_expression envp perms_in eperms_out evperms e expr) &&&&
       perm_set_unmaps_to (biview_of_lens_pair
                             (lens, proj1_lens)) (eperms_out, perm_set_out) &&&&
       is_val_perms_add_view (biview_of_lens (proj2_lens)) (evperms,
                                                            val_perms_out) &&&&
       perms_out = perm_set_out &&
       ret_perms = Some val_perms_out &&
       stmt = RETURN_m expr) =>
      enabled? (abstracts_ret_statement
                  envp perms_in perms_out ret_perms
                  (fn x -> (lens.lens_get x, e x))
                  stmt)

  (* Special case of return where all variables are forgotten. This is
  represented by using a unit type in the first projection of the tuple. Note
  that the precondition just adds in the unit lens, which in turn causes the
  general return_correct theorem to be used. *)
  theorem return_correct_unit_left is [a,b]
    fa (envp,perms_in,perms_out,ret_perms,e:a->b,stmt)
      enabled? (abstracts_ret_statement
                  envp perms_in perms_out ret_perms
                  (fn x -> (unit_lens.lens_get x, e x))
                  stmt) =>
      enabled? (abstracts_ret_statement
                  envp perms_in perms_out ret_perms
                  (fn x -> ((), e x))
                  stmt)

  (* The core correctness theorem for void returns, similar to
  return_correct. As with that theorem, the lens is for "forgetting"
  permissions, which is handled by the unmapping. *)
  theorem return_void_correct is [a,b]
    fa (envp,perms_in,lens:Lens (a,b),stmt,ret_perms,perms_out,perms_out')
      enabled? (perm_set_unmaps_to (biview_of_lens lens)
                  (perms_in, perms_out')) &&
      perms_out = perms_out' &&
      ret_perms = None &&
      stmt = RETURN_VOID_m =>
      enabled? (abstracts_ret_statement
                  envp perms_in perms_out ret_perms
                  (fn x -> lens.lens_get x)
                  stmt)

  (* Special case of return void where all variables are preserved. This is
  represented as the identity function. *)
  theorem return_void_correct_identity is [a]
    fa (envp,perms_in,stmt,ret_perms,perms_out)
      enabled? (abstracts_ret_statement
                  envp perms_in perms_out ret_perms
                  (fn x -> id_lens.lens_get x)
                  stmt) =>
      enabled? (abstracts_ret_statement
                  envp perms_in perms_out ret_perms
                  (fn x -> x)
                  stmt)


  (***
   *** Functions
   ***)

  (* FIXME: need permissions to deallocate the current stack from at the end of body *)
  (* FIXME: also need a value_abs_has_type precondition *)
  theorem FUNCTION_correct is [a,b]
    fa (envp,perms_in,perms_in_sub,perms_out,ret_perms,perms_out_sub,ret_perms_sub,
        perms_out_sub',f:a->b,m,prototype,body)
      (enabled? (abstracts_ret_statement
                   envp
                   perms_in_sub
                   perms_out_sub
                   ret_perms_sub
                   f
                   body) &&&&
       m = FUNCTION_m (prototype.1, prototype.2, prototype.3, body) &&&&
       StIPerm auto_allocation_perm in? perms_out.1 &&&&
       is_perm_set_of_arg_perms (perms_out, prototype.3, perms_out_sub') &&&&
       is_perm_set_of_arg_perms (perms_in, prototype.3, perms_in_sub) &&&&
       perm_set_weaker? (perms_out_sub', perms_out_sub) &&&&
       ret_perms === ret_perms_sub) =>
      abstracts_c_function_decl envp perms_in perms_out ret_perms f prototype m

end-spec
