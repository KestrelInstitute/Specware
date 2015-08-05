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

  (* lens_compose *)

  op [a,b,c] is_lens_compose (lens1: Lens (a,b), lens2: Lens (b,c),
                              lens_out: Lens (a,c)) : Bool =
    lens_compose (lens1, lens2) = lens_out

  theorem is_lens_compose_rule is [a,b,c]
    fa (l1: Lens (a,b), l2: Lens (b,c), lens_out)
      lens_out = {lens_get = (fn a -> l2.lens_get (l1.lens_get a)),
                  lens_set = (fn a -> fn c ->
                                l1.lens_set a (l2.lens_set (l1.lens_get a) c))} =>
      enabled? (is_lens_compose (l1, l2, lens_out))



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

  theorem is_cperm_add_lens_rule is [a,b,c]
    fa (cperm:CPermission (c,a),lens1,lens:Lens (b,a),lens_out,cperm_out)
      enabled? (is_lens_compose (lens, lens1, lens_out)) &&&&
      cperm_out === cperm_add_lens (cperm, lens_out) =>
      enabled? (is_cperm_add_lens lens (cperm_add_lens (cperm, lens1), cperm_out))


  (* val_perm_add_lens *)

  op [a,b] is_val_perm_add_lens (lens: Lens (b,a)) (vperm: ValPerm a,
                                                    vperm_out: ValPerm b) : Bool =
    val_perm_add_lens (vperm, lens) = vperm_out

  theorem is_val_perm_add_lens_val is [a,b]
    fa (splexpr,cperm:CValPerm a,lens:Lens (b,a),cperm_out,vperm_out)
      enabled? (is_cperm_add_lens lens (cperm, cperm_out)) &&&&
      vperm_out === ValPerm (splexpr, cperm_out) =>
      enabled? (is_val_perm_add_lens lens (ValPerm (splexpr, cperm), vperm_out))

  theorem is_val_perm_add_lens_valeq is [a,b]
    fa (splexpr,cperm:CValPerm a,lens:Lens (b,a),cperm_out,vperm_out,lv)
      enabled? (is_cperm_add_lens lens (cperm, cperm_out)) &&&&
      vperm_out === ValEqPerm (splexpr, cperm_out, lv) =>
      enabled? (is_val_perm_add_lens lens (ValEqPerm (splexpr, cperm, lv), vperm_out))


  (* val_perms_add_lens *)

  op [a,b] is_val_perms_add_lens (lens: Lens (b,a))
                                 (vperms: List (ValPerm a),
                                  vperms_out: List (ValPerm b)) : Bool =
    val_perms_add_lens (vperms, lens) = vperms_out

  theorem is_val_perms_add_lens_rule is [a,b]
    fa (vperms, lens:Lens (b,a), vperms_out)
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
  op [a,b] extract_var_perms_for_lens (perms_in: PermSet a,
                                       var_lens: Lens (a,b),
                                       var: Identifier,
                                       vperms: List (ValPerm b),
                                       perms_out: PermSet a) : Bool =
    perm_set_weaker? (perms_out ++
                      map (fn vperm ->
                             VarPerm (var, val_perm_add_lens (vperm, var_lens)))
                        vperms,
                      perms_in)


  theorem extract_var_perms_for_lens_var is [a,b,c]
    fa (x,splexpr,cperm,lens:Lens (a,c),perms_in,var_lens:Lens (a,b),
        var,vperms_out,perms_out,vperms_out',perms_out',
        val_cperm,rem_cperm)
      enabled? (extract_var_perms_for_lens
                  (perms_in,var_lens,var,vperms_out',perms_out')) &&&&
      if_lens_eq (var_lens, lens,
                  (fn iso ->
                     extract_perm_for_lv_read (cperm, val_cperm, rem_cperm) &&&&
                     var === x &&&&
                     vperms_out === ValEqPerm (splexpr,
                                               cperm_add_lens (val_cperm,
                                                               iso_lens iso),
                                               LV_ident x) :: vperms_out' &&&&
                     perms_out ===
                     VarPerm (x, ValPerm (splexpr,
                                          cperm_add_lens
                                            (rem_cperm,lens))) :: perms_out'
                   ),
                  vperms_out === vperms_out' &&&&
                  perms_out === VarPerm (x, ValPerm (splexpr,
                                                     cperm_add_lens
                                                       (cperm, lens)))::perms_out'
                  )
      =>
      enabled? (extract_var_perms_for_lens
                  (VarPerm
                     (x, ValPerm (splexpr,
                                  cperm_add_lens (cperm, lens)))::perms_in,
                   var_lens,var,vperms_out,perms_out))


  theorem extract_var_perms_for_lens_vareq is [a,b,c]
    fa (x,splexpr,cperm,lens:Lens (a,c),lv,perms_in,var_lens:Lens (a,b),
        var,vperms_out,perms_out,vperms_out',perms_out',
        val_cperm,rem_cperm)
      enabled? (extract_var_perms_for_lens
                  (perms_in,var_lens,var,vperms_out',perms_out')) &&&&
      if_lens_eq (var_lens, lens,
                  (fn iso ->
                     extract_perm_for_lv_read (cperm, val_cperm, rem_cperm) &&&&
                     var === x &&&&
                     vperms_out === ValEqPerm (splexpr,
                                               cperm_add_lens (val_cperm,
                                                               iso_lens iso),
                                               LV_ident x) :: vperms_out' &&&&
                     perms_out ===
                     VarPerm (x, ValEqPerm (splexpr,
                                            cperm_add_lens
                                              (rem_cperm,lens), lv)) :: perms_out'
                   ),
                  vperms_out === vperms_out' &&&&
                  perms_out === VarPerm (x, ValEqPerm (splexpr,
                                                       cperm_add_lens
                                                         (cperm, lens), lv))::perms_out'
                  )
      =>
      enabled? (extract_var_perms_for_lens
                  (VarPerm
                     (x, ValEqPerm (splexpr,
                                    cperm_add_lens (cperm, lens), lv))::perms_in,
                   var_lens,var,vperms_out,perms_out))


  theorem extract_var_perms_for_lens_novar is [a,b]
    fa (stperm,perms_in,var_lens:Lens (a,b),var,vperms_out,perms_out,perms_out')
      enabled? (extract_var_perms_for_lens
                  (perms_in,var_lens,var,vperms_out,perms_out')) &&
      perms_out = (NoVarPerm stperm)::perms_out'
      =>
      enabled? (extract_var_perms_for_lens
                  (NoVarPerm stperm::perms_in,
                   var_lens,var,vperms_out,perms_out))


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

  (* Nothing factors w.r.t. the unit lens *)
  theorem if_lens_factors_unit is [a,c]
    fa (lens: Lens (a,c), res1, res2)
      enabled? res2 =>
      enabled? (if_lens_factors (unit_lens, lens, res1, res2))

  (* Everything factors w.r.t. the identity lens *)
  theorem if_lens_factors_unit is [a,c]
    fa (lens: Lens (a,c), res1, res2)
      enabled? (res1 lens) =>
      enabled? (if_lens_factors (id_lens, lens, res1, res2))


  (* FIXME HERE: theorems for decomposing lenses *)


  (* FIXME HERE NOW: add rules! *)
  op [a,b] perm_set_factors_to (lens_prefix: Lens (a,b)) (perms: PermSet a,
                                                          perms_out: PermSet b) : Bool =
    perm_set_weaker? (perm_set_add_lens (perms_out, lens_prefix), perms)

(*
  (* Predicate for factoring value permissions *)
  op [a,b] val_perm_unmaps_to (lens_prefix: BisimView (a,b))
                              (vperm_in: ValPerm a, vperm_out: ValPerm b) : Bool =
    val_perm_weaker? (val_perm_add_view (vperm_out, lens_prefix), vperm_in)

  theorem val_perm_unmaps_to_1 is [a,b,c]
    fa (splexpr,vabs:ValueAbs c,lens,lens_prefix:BisimView (a,b),lens_suffix,vperm_out)
      enabled? (biview_decomposes_to (lens, lens_prefix, lens_suffix)) &&&&
      vperm_out === ValPerm (splexpr,value_abs_add_view (vabs, lens_suffix)) =>
      enabled? (val_perm_unmaps_to
                  lens_prefix
                  (ValPerm (splexpr,value_abs_add_view (vabs, lens)), vperm_out))

  theorem val_perm_unmaps_to_2 is [a,b,c]
    fa (impl,lens_prefix:BisimView (a,b),vperm_out)
      vperm_out = ValIPerm impl =>
      enabled? (val_perm_unmaps_to lens_prefix (ValIPerm impl, vperm_out))


  (* Predicate for un-mapping storage permissions *)
  op [a,b] st_perm_unmaps_to (lens_prefix: BisimView (a,b))
                              (stperm_in: StPerm a, stperm_out: StPerm b) : Bool =
    st_perm_weaker? (st_perm_add_view (stperm_out, lens_prefix), stperm_in)

  theorem st_perm_unmaps_to_1 is [a,b,c]
    fa (splexpr,uabs:UnitAbs c,lens,lens_prefix:BisimView (a,b),lens_suffix,stperm_out)
      enabled? (biview_decomposes_to (lens, lens_prefix, lens_suffix)) &&&&
      stperm_out === StPerm (splexpr,unit_abs_add_view (uabs, lens_suffix)) =>
      enabled? (st_perm_unmaps_to
                  lens_prefix
                  (StPerm (splexpr,unit_abs_add_view (uabs, lens)), stperm_out))

  theorem st_perm_unmaps_to_2 is [a,b,c]
    fa (impl,lens_prefix:BisimView (a,b),stperm_out)
      stperm_out = StIPerm impl =>
      enabled? (st_perm_unmaps_to lens_prefix (StIPerm impl, stperm_out))


  (* Predicate for un-mapping individual permissions *)
  op [a,b] perm_unmaps_to (lens_prefix: BisimView (a,b))
                          (perm_in: Perm a, perm_out: Perm b) : Bool =
    perm_weaker? (perm_add_view (perm_out, lens_prefix), perm_in)

  theorem perm_unmaps_to_var is [a,b]
    fa (x,lens_prefix:BisimView (a,b),vperm,vperm_out,perm_out)
      enabled? (val_perm_unmaps_to lens_prefix (vperm, vperm_out)) &&&&
      perm_out === VarPerm (x, vperm_out) =>
      enabled? (perm_unmaps_to lens_prefix (VarPerm (x, vperm), perm_out))

  theorem perm_unmaps_to_novar is [a,b]
    fa (stperm,stperm_out,perm_out,lens_prefix:BisimView (a,b))
      enabled? (st_perm_unmaps_to lens_prefix (stperm, stperm_out)) &&&&
      perm_out = NoVarPerm stperm_out =>
      enabled? (perm_unmaps_to lens_prefix (NoVarPerm stperm, perm_out))


  (* Predicate for un-mapping permission sets *)
  op [a,b] perm_set_unmaps_to (lens_prefix: BisimView (a,b))
                              (perms_in: PermSet a,
                               perms_out: PermSet b) : Bool =
    perm_set_weaker? (perm_set_add_view (perms_out, lens_prefix), perms_in)

  theorem perm_set_unmaps_to_rule is [a,b]
    fa (lens_prefix: BisimView (a,b),perms_in,perms_out)
      enabled? (is_map_pred_of (perm_unmaps_to lens_prefix) (perms_in, perms_out)) =>
      enabled? (perm_set_unmaps_to lens_prefix (perms_in, perms_out))
*)


  (***
   *** Proving perm_set_weaker?
   ***)

  theorem perm_weaker_id is [a]
    fa (perm: Perm a)
      true => enabled? (perm_weaker? (perm, perm))

  op [a] perm_weaker_than_set? (perm: Perm a, perms: PermSet a) : Bool =
    perm_set_weaker? ([perm], perms)

  theorem perm_weaker_than_set_rule is [a]
    fa (perm:Perm a, perm1, perms)
      enabled? (perm_weaker? (perm, perm1)) ||
      enabled? (perm_weaker_than_set? (perm, perms)) =>
      enabled? (perm_weaker_than_set? (perm, perm1::perms))


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
    fa (envp,perms_in:PermSet a,perms_out,vperms_out,c:b,m,R,i)
      enabled? (USER_abstracts_constant c R i) &&&&
      perms_out === perms_in &&&&
      vperms_out === [ValPerm ([([],None)],
                               cperm_add_lens (non_heap_cperm R, id_lens))] &&&&
      m === ICONST_m i =>
      enabled? (abstracts_expression_constant envp perms_in
                  perms_out vperms_out c m)


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
                                    (vperms_out: List (ValPerm b))
                                    (lens: Lens (a,b))
                                    (m: Monad Value) : Bool =
    abstracts_expression envp perms_in perms_out vperms_out lens.lens_get m

  theorem abstracts_expression_var_rule is [a,b]
    fa (envp,perms_in,perms_out,vperms,lens:Lens (a,b),x,m)
      enabled? (extract_var_perms_for_lens
                  (perms_in, lens, x, vperms, perms_out)) &&&&
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
    fa (envp,perms_in,perms_out,vperms_out,f:a->b,oper,m,uop,expr,vabs)
      enabled? (abstracts_expression envp perms_in perms_out vperms_out f expr) &&&&
      m === UNARYOP_m uop expr &&&&
      (* FIXME: the below should be the rhs is weaker than the left *)
      vperms_out === [ValPerm ([([],None)], vabs)] =>
      enabled? (abstracts_expression_unary envp perms_in
                  perms_out vabs f oper uop m)
*)


  (***
   *** Binary Operations
   ***)


  (***
   *** General Rule for Expressions
   ***)

  theorem abstracts_expression_rule is [a,b]
    fa (envp,perms_in,perms_out,vperms_out,f:a->b,m,
        c,lens(*,f_sub,oper,uop,vabs*))
      clause (enabled? (fun_matches_constant (f, c)),
              abstracts_expression_constant envp perms_in perms_out vperms_out c m)
      ||||
      clause (enabled? (USER_variable_lens (f, lens)),
              abstracts_expression_var envp perms_in perms_out vperms_out lens m)
      (*
      ||
      (enabled? (USER_abstracts_unary_op envp f f_sub oper uop vabs) &&&&
       abstracts_expression_unary envp perms_in perms_out vabs f_sub oper uop m &&&&
       vperms_out === [ValPerm ([([],None)], vabs)])
         *)
      =>
      enabled? (abstracts_expression envp perms_in perms_out vperms_out f m)


  (***
   *** If Statements
   ***)

  op [a,b] abstracts_ret_statement_if
      (envp:EnvPred) (perms_in:PermSet a) (perms_out:PermSet b)
      (ret_vperms:RetValPerm b) (e:a->Bool) (f1:a->b) (f2:a->b) (m:Monad ()) : Bool =
    abstracts_ret_statement
      envp perms_in perms_out ret_vperms (fn x -> if e x then f1 x else f2 x) m

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
      (ret_vperms:RetValPerm d) (st_lens:Lens (a,b)) (e:a->c)
      (iso:Bijection (b*c,d)) (m:Monad ()) : Bool =
    abstracts_ret_statement
      envp perms_in perms_out ret_vperms
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
    fa (envp,perms_in,perms_out,ret_vperms,eperms_out,evperms,
        st_lens,e:a->c,iso:Bijection (b*c,d),
        expr,stmt,perms_out1,perms_out2,ret_vperms1,
        perms_out_lens,ret_vperms_lens)
      enabled? (abstracts_expression envp perms_in eperms_out evperms e expr) &&&&
      perm_set_factors_to st_lens (eperms_out, perms_out1) &&&&
      is_lens_compose (iso_lens (inverse iso), proj1_lens, perms_out_lens) &&&&
      is_perm_set_add_lens perms_out_lens (perms_out1, perms_out2) &&&&
      is_lens_compose (iso_lens (inverse iso), proj2_lens, ret_vperms_lens) &&&&
      is_val_perms_add_lens ret_vperms_lens (evperms, ret_vperms1) &&&&
      perms_out === perms_out2 &&&&
      ret_vperms === Some ret_vperms1 &&
      stmt = RETURN_m expr =>
      enabled? (abstracts_ret_statement_return
                  envp perms_in perms_out ret_vperms st_lens e iso stmt)


  op [a,b] USER_is_return_void (f:a->b, lens:Lens (a,b)) : Bool =
    f = lens.lens_get

  op [a,b] abstracts_ret_statement_return_void
      (envp:EnvPred) (perms_in:PermSet a) (perms_out:PermSet b)
      (ret_vperms:RetValPerm b) (st_lens:Lens (a,b)) (m:Monad ()) : Bool =
    abstracts_ret_statement envp perms_in perms_out ret_vperms st_lens.lens_get m

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

(*
  theorem USER_return_expr_test1 is [a]
    fa (st_lens,e_out,iso,e:a)
      st_lens = unit_lens &&
      e_out = (fn _ -> e) &&
      iso = (fn x -> x) =>
      enabled? (USER_is_return_expr ((fn (x:()) -> ((), e)), st_lens, e_out, iso))

  theorem USER_return_expr_test2 is
    fa (st_lens,e_out,iso,e:Bool)
      st_lens = unit_lens &&
      e_out = (fn _ -> e) &&
      iso = (fn x -> x) =>
      enabled? (USER_is_return_expr ((fn (x:()) -> ((), e)), st_lens, e_out, iso))
*)


  (***
   *** General Rules for Statements
   ***)

  theorem abstracts_ret_statement_rule is [a,b,c,d]
    fa (envp,perms_in:PermSet a,perms_out:PermSet b,ret_vperms,f,m,
        ret_lens,ret_e,ret_iso:Bijection (c*d,b),
        retv_lens,if_cond,if_f1,if_f2)
      clause (enabled? (USER_is_return_expr (f, ret_lens, ret_e, ret_iso)),
              (abstracts_ret_statement_return
                 envp perms_in perms_out ret_vperms ret_lens ret_e ret_iso m))
      ||||
      clause (enabled? (USER_is_return_void (f, retv_lens)),
              (abstracts_ret_statement_return_void
                 envp perms_in perms_out ret_vperms retv_lens m))
      ||||
      clause (enabled? (fun_matches_if_expression (f, if_cond, if_f1, if_f2)),
              (abstracts_ret_statement_if
                 envp perms_in perms_out ret_vperms if_cond if_f1 if_f2 m))
      =>
      enabled? (abstracts_ret_statement envp perms_in perms_out ret_vperms f m)


  (***
   *** Functions
   ***)

  (* FIXME: need permissions to deallocate the current stack from at the end of body *)
  (* FIXME: also need a value_abs_has_type precondition *)
  theorem FUNCTION_correct is [a,b]
    fa (envp,perms_in,perms_in_sub,perms_out,ret_perms,perms_out_sub,ret_perms_sub,
        perms_out_sub',f:a->b,m,prototype,body)
      m = FUNCTION_m (prototype.1, prototype.2, prototype.3, body) &&
      enabled? (in_pred (StPerm ([([], None)], auto_allocation_perm), perms_out.1)) &&&&
      is_perm_set_of_arg_perms (perms_out, prototype.3, perms_out_sub') &&&&
      is_perm_set_of_arg_perms (perms_in, prototype.3, perms_in_sub) &&&&
      (abstracts_ret_statement
         envp
         perms_in_sub
         perms_out_sub
         ret_perms_sub
         f
         body) &&&&
      perm_set_weaker? (perms_out_sub', perms_out_sub) &&&&
      ret_perms === ret_perms_sub =>
      abstracts_c_function_decl envp perms_in perms_out ret_perms f prototype m

end-spec
