CGen qualifying spec
  import C_Permissions, C_DSL


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
      is_compose_biviews (biview_of_lens l1, biview_of_lens l2, bv_out)

  theorem compose_lens_trivial is [a,b,c]
    fa (lens: Lens (a,b), bv_out: BisimView (a,c))
      bv_out = trivial_biview =>
      is_compose_biviews (biview_of_lens lens, trivial_biview, bv_out)


  (* perm_add_view *)

  op [a,b] is_perm_add_view (perm: Perm a, bv: BisimView (b,a),
                             perm_out: Perm b) : Bool =
    perm_add_view (perm, bv) = perm_out

  theorem is_perm_add_view_lv is [a,b,c]
    fa (lv,splexpr,vabs:ValueAbs c,bv1,bv:BisimView (b,a),bv_out,perm_out)
      is_compose_biviews (bv, bv1, bv_out) &&
      perm_out = LVPerm (lv, splexpr, value_abs_add_view (vabs, bv_out)) =>
      is_perm_add_view (LVPerm (lv, splexpr,
                                value_abs_add_view (vabs, bv1)),
                        bv, perm_out)

  theorem is_perm_add_view_lvi is [a,b]
    fa (lv,impl,bv:BisimView (b,a),perm_out)
      perm_out = LVIPerm (lv, impl) =>
      is_perm_add_view (LVIPerm (lv, impl), bv, perm_out)

  theorem is_perm_add_view_sti is [a,b,c]
    fa (splexpr,uabs:UnitAbs c,bv1,bv:BisimView (b,a),bv_out,perm_out)
      is_compose_biviews (bv, bv1, bv_out) &&
      perm_out = StPerm (splexpr, unit_abs_add_view (uabs, bv_out)) =>
      is_perm_add_view (StPerm (splexpr,
                                unit_abs_add_view (uabs, bv1)),
                        bv, perm_out)

  theorem is_perm_add_view_sti is [a,b]
    fa (impl,bv:BisimView (b,a),perm_out)
      perm_out = StIPerm impl =>
      is_perm_add_view (StIPerm impl, bv, perm_out)


  (* perm_set_add_view *)

  op [a,b] is_perm_set_add_view (perms: PermSet a, bv: BisimView (b,a),
                                 perms_out: PermSet b) : Bool =
    perm_set_add_view (perms, bv) = perms_out

  theorem is_perm_set_add_view_cons is [a,b]
    fa (perm,perms,bv:BisimView (b,a),perms_out,perms_out',perm')
      is_perm_add_view (perm, bv, perm') &&
      is_perm_set_add_view (perms, bv, perms_out') &&
      perms_out = perm'::perms_out' =>
      is_perm_set_add_view (perm::perms, bv, perms_out)

  theorem is_perm_set_add_view_nil is [a,b]
    fa (bv:BisimView (b,a),perms_out)
      perms_out = [] =>
      is_perm_set_add_view ([], bv, perms_out)


  (* perm_set_of_arg_perms *)

  op [a] is_perm_set_of_arg_perms (perms: ArgListPerms a, vars: ParameterList,
                                   perm_set: PermSet a) : Bool =
    equiLong (perms.2, vars) &&
    perm_set = perm_set_of_arg_perms (perms, map (fn x -> x.2) vars)

  theorem is_perm_set_of_arg_perms_cons1 is [a]
    fa (splexpr,uabs,fst_perms,argperms,vars,perm_set,perm_set':PermSet a)
      perm_set = StPerm (splexpr, uabs) :: perm_set' &&
      is_perm_set_of_arg_perms ((fst_perms,argperms),vars, perm_set') =>
      is_perm_set_of_arg_perms ((FunStPerm (splexpr, uabs)::fst_perms,argperms),
                                vars, perm_set)

  theorem is_perm_set_of_arg_perms_cons2 is [a]
    fa (impl,fst_perms,argperms,vars,perm_set,perm_set':PermSet a)
      perm_set = StIPerm impl :: perm_set' &&
      is_perm_set_of_arg_perms ((fst_perms,argperms),vars, perm_set') =>
      is_perm_set_of_arg_perms ((FunStIPerm impl::fst_perms,argperms),
                                vars, perm_set)

  theorem is_perm_set_of_arg_perms_cons3 is [a]
    fa (splexpr,vabs,vperms,argperms,x,tp,vars,perm_set,perm_set':PermSet a)
      perm_set = LVPerm (LV_ident x, splexpr, vabs) :: perm_set' &&
      is_perm_set_of_arg_perms (([], vperms::argperms),(tp,x)::vars, perm_set') =>
      is_perm_set_of_arg_perms (([], (ValPerm (splexpr, vabs)::vperms)::argperms),
                                (tp,x)::vars, perm_set)

  theorem is_perm_set_of_arg_perms_cons4 is [a]
    fa (argperms,var,vars,perm_set:PermSet a)
      is_perm_set_of_arg_perms (([], argperms),vars, perm_set) =>
      is_perm_set_of_arg_perms (([], []::argperms),
                                var::vars, perm_set)

  theorem is_perm_set_of_arg_perms_nil is [a]
    fa (perm_set:PermSet a)
      perm_set = [] =>
      is_perm_set_of_arg_perms (([],[]), [], perm_set)


  op [a,b] is_val_perm_add_view (vperm: ValPerm a, bv: BisimView (b,a),
                                 vperm_out: ValPerm b) : Bool =
    val_perm_add_view (vperm, bv) = vperm_out


  op [a,b] is_val_perms_add_view (vperms: List (ValPerm a), bv: BisimView (b,a),
                                  vperms_out: List (ValPerm b)) : Bool =
    val_perms_add_view (vperms, bv) = vperms_out


  (***
   *** Extracting LValue Perms from the Current Permission Set
   ***)

  op [a] ifequal (x:a,y:a,res1:Bool,res2:Bool) : Bool =
    if x = y then res1 else res2

  theorem ifequal_eq is [a]
    fa (x:a,res1,res2)
      res1 => ifequal (x,x,res1,res2)

  theorem ifequal_neq is [a]
    fa (x:a,y,res1,res2)
      x ~= y && res2 => ifequal (x,y,res1,res2)

  (* When an expression reads the value of an lvalue, the resulting value might
  have some aliasing with the lvalue, specifically if the value is a pointer
  value. This splits a value abstraction that was originally on an lvalue into
  value abstractions for the expression and to remain with the lvalue. *)
  (* FIXME HERE: figure out how to define this!! *)
  op [a] lvalue_expr_and_lvalue_abses? (lv:LValue, vabs: ValueAbs a,
                                        expr_vabs: ValueAbs a,
                                        lv_vabs: ValueAbs a) : Bool

  (* This predicate says it is allowable (as in, it does not result in any more
  perms) to go from perms_in to perms_out plus the given perms on the lvalue lv,
  and that the given perms actually allow reading the given lvalue; the latter
  is ensured by requiring at least on permission on the lvalue.  This predicate
  is used below to search for all the permissions in perms_in that correspond to
  a given biview. *)
  op [a,b] view_perms_extract_to? (perms_in: PermSet a, bv: BisimView (a,b),
                                   lv: LValue, vperms: List (ValPerm b),
                                   perms_out: PermSet a) : Bool =
    length vperms > 0 &&
    perm_set_weaker? (perms_in,
                      perms_out ++
                        map_exec (fn vperm ->
                                    (perm_of_val_perm lv
                                       (val_perm_add_view (vperm, bv)))) vperms)

  (* Helper predicate for the rules below, that allows vperms = [] *)
  op [a,b] view_perms_extract_toH (perms_in: PermSet a, bv: BisimView (a,b),
                                   lv: LValue, vperms: List (ValPerm b),
                                   perms_out: PermSet a) : Bool =
    perm_set_weaker? (perms_in,
                      perms_out ++
                        map_exec (fn vperm ->
                                    (perm_of_val_perm lv
                                       (val_perm_add_view (vperm, bv)))) vperms)

  (* The following rules essentially form a logic program for proving
  view_perms_extract_to? for a given perms_in and bv *)

  theorem view_perms_extract_from_H is [a,b]
    fa (perms_in,bv:BisimView (a,b),lv,vperms,perms_out)
      view_perms_extract_toH (perms_in,bv,lv,vperms,perms_out) &&
      length vperms > 0 =>
      view_perms_extract_to? (perms_in,bv,lv,vperms,perms_out)

  theorem view_perms_extract_nil is [a,b]
    fa (bv:BisimView (a,b),lv,vperms,perms_out)
      vperms = [] && perms_out = [] =>
      view_perms_extract_toH ([],bv,lv,vperms,perms_out)

  theorem view_perms_extract_cons_lv is [a,b]
    fa (lv1,splexpr,vabs,bv1,perms_in,bv:BisimView (a,b),lv,vperms,perms_out,
        vperms',perms_out',expr_vabs,lv_vabs)
      view_perms_extract_toH (perms_in,bv,lv,vperms',perms_out') &&
      ifequal (bv,bv1,
               (lv = lv1 &&
                  lvalue_expr_and_lvalue_abses? (lv, vabs, expr_vabs, lv_vabs) &&
                  vperms = ValPerm (splexpr, expr_vabs)::vperms' &&
                  perms_out = LVPerm (lv,splexpr,
                                      value_abs_add_view (lv_vabs, bv1))::perms_out'),
               (vperms = vperms' &&
                  perms_out = LVPerm (lv1, splexpr,
                                      value_abs_add_view (vabs, bv1))::perms_out')
               ) =>
      view_perms_extract_toH (LVPerm (lv1, splexpr,
                                      value_abs_add_view (vabs, bv1))::perms_in,
                              bv,lv,vperms,perms_out)

  (* FIXME: give implicational permissions to the value *)
  theorem view_perms_extract_cons_lvi is [a,b]
    fa (lv1,impl,perms_in,bv:BisimView (a,b),lv,vperms,perms_out,perms_out')
      perms_out = LVIPerm (lv1, impl)::perms_out' &&
      view_perms_extract_toH (perms_in,bv,lv,vperms,perms_out') =>
      view_perms_extract_toH (LVIPerm (lv1, impl)::perms_in,
                              bv,lv,vperms,perms_out)

  theorem view_perms_extract_cons_st is [a,b]
    fa (splexpr,uabs,perms_in,bv:BisimView (a,b),lv,vperms,perms_out,perms_out')
      perms_out = StPerm (splexpr, uabs)::perms_out' &&
      view_perms_extract_toH (perms_in,bv,lv,vperms,perms_out') =>
      view_perms_extract_toH (StPerm (splexpr, uabs)::perms_in,
                              bv,lv,vperms,perms_out)

  theorem view_perms_extract_cons_sti is [a,b]
    fa (impl,perms_in,bv:BisimView (a,b),lv,vperms,perms_out,perms_out')
      perms_out = StIPerm impl::perms_out' &&
      view_perms_extract_toH (perms_in,bv,lv,vperms,perms_out') =>
      view_perms_extract_toH (StIPerm impl::perms_in,
                              bv,lv,vperms,perms_out)


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


  (* We say that bv_prefix and bv_suffix iff composing the latter two yields a
  possibly weaker biview than bv *)
  op [a,b,c] biview_decomposes_to (bv: BisimView (a,c), bv_prefix: BisimView (a,b),
                                   bv_suffix: BisimView (b,c) |
                                     pseudo_monic? bv_prefix) : Bool =
    biview_weaker? (compose_biviews (bv_prefix, bv_suffix), bv)

  (* A double-lens biview can always be used for decomposition by decomposing
  w.r.t the first lens and then post-composing the second afterwards *)
  theorem biview_decomposes_lens_pair is [a,b,c,d]
    fa (bv,lens1:Lens (a,b),lens2:Lens (c,b),bv_suffix:BisimView (c,d),bv_suffix')
      biview_decomposes_to (bv, biview_of_lens lens1, bv_suffix') &&
      is_compose_biviews (biview_of_lens (lens2), bv_suffix', bv_suffix) =>
      biview_decomposes_to (bv, biview_of_lens_pair (lens1,lens2),
                            bv_suffix)


  (* FIXME HERE: theorems for decomposing biviews *)


  (* Predicate for un-mapping individual permissions *)
  op [a,b] perm_unmaps_to (perm_in: Perm a, bv_prefix: BisimView (a,b),
                           perm_out: Perm b |
                             pseudo_monic? bv_prefix) : Bool =
    perm_weaker? (perm_add_view (perm_out, bv_prefix), perm_in)

  theorem perm_unmaps_to_lv is [a,b,c]
    fa (lv,splexpr,vabs:ValueAbs c,bv,bv_prefix:BisimView (a,b),bv_suffix,perm_out)
      pseudo_monic? bv_prefix &&
      perm_out = LVPerm (lv,splexpr,value_abs_add_view (vabs, bv_suffix)) &&
      biview_decomposes_to (bv, bv_prefix, bv_suffix) =>
      perm_unmaps_to (LVPerm (lv,splexpr,value_abs_add_view (vabs, bv)),
                      bv_prefix, perm_out)

  theorem perm_unmaps_to_lvi is [a,b,c]
    fa (lv,impl,bv_prefix:BisimView (a,b),perm_out)
      pseudo_monic? bv_prefix &&
      perm_out = LVIPerm (lv,impl) =>
      perm_unmaps_to (LVIPerm (lv,impl), bv_prefix, perm_out)

  theorem perm_unmaps_to_lv is [a,b,c]
    fa (splexpr,uabs:UnitAbs c,bv,bv_prefix:BisimView (a,b),bv_suffix,perm_out)
      pseudo_monic? bv_prefix &&
      perm_out = StPerm (splexpr,unit_abs_add_view (uabs, bv_suffix)) &&
      biview_decomposes_to (bv, bv_prefix, bv_suffix) =>
      perm_unmaps_to (StPerm (splexpr,unit_abs_add_view (uabs, bv)),
                      bv_prefix, perm_out)

  theorem perm_unmaps_to_sti is [a,b,c]
    fa (impl,bv_prefix:BisimView (a,b),perm_out)
      pseudo_monic? bv_prefix &&
      perm_out = StIPerm impl =>
      perm_unmaps_to (StIPerm impl, bv_prefix, perm_out)


  (* Predicate for un-mapping permission sets *)
  op [a,b] perm_set_unmaps_to (perms_in: PermSet a, bv_prefix: BisimView (a,b),
                               perms_out: PermSet b |
                                 pseudo_monic? bv_prefix) : Bool =
    perm_set_weaker? (perm_set_add_view (perms_out, bv_prefix), perms_in)

  theorem perm_set_unmaps_to_nil is [a,b]
    fa (bv_prefix: BisimView (a,b),perms_out)
      pseudo_monic? bv_prefix &&
      perms_out = [] =>
      perm_set_unmaps_to ([], bv_prefix, perms_out)

  theorem perm_set_unmaps_to_cons is [a,b]
    fa (perm_in,perms_in,bv_prefix: BisimView (a,b),perm_out,perms_out,perms_out')
      pseudo_monic? bv_prefix &&
      perm_unmaps_to (perm_in, bv_prefix, perm_out) &&
      perm_set_unmaps_to (perms_in, bv_prefix, perms_out') &&
      perms_out = perm_out::perms_out' =>
      perm_set_unmaps_to (perm_in::perms_in, bv_prefix, perms_out)


  (* Predicate for un-mapping value permissions *)
  op [a,b] val_perm_unmaps_to (vperm_in: ValPerm a, bv_prefix: BisimView (a,b),
                               vperm_out: ValPerm b |
                                 pseudo_monic? bv_prefix) : Bool =
    val_perm_weaker? (val_perm_add_view (vperm_out, bv_prefix), vperm_in)

  theorem val_perm_unmaps_to_1 is [a,b,c]
    fa (splexpr,vabs:ValueAbs c,bv,bv_prefix:BisimView (a,b),bv_suffix,vperm_out)
      pseudo_monic? bv_prefix &&
      vperm_out = ValPerm (splexpr,value_abs_add_view (vabs, bv_suffix)) &&
      biview_decomposes_to (bv, bv_prefix, bv_suffix) =>
      val_perm_unmaps_to (ValPerm (splexpr,value_abs_add_view (vabs, bv)),
                          bv_prefix, vperm_out)

  theorem val_perm_unmaps_to_2 is [a,b,c]
    fa (impl,bv_prefix:BisimView (a,b),vperm_out)
      pseudo_monic? bv_prefix &&
      vperm_out = ValIPerm impl =>
      val_perm_unmaps_to (ValIPerm impl, bv_prefix, vperm_out)


  (* Predicate for un-mapping lists of value permissions *)
  op [a,b] val_perms_unmap_to (vperms_in: List (ValPerm a),
                               bv_prefix: BisimView (a,b),
                               vperms_out: List (ValPerm b) |
                                 pseudo_monic? bv_prefix) : Bool =
    val_perms_weaker? (val_perms_add_view (vperms_out, bv_prefix), vperms_in)


  (***
   *** Canonicalizing Permission Sets by Proving perm_set_weaker?
   ***)

  (* FIXME *)


  (***
   *** Boolean Expressions
   ***)

  op bool_valueabs : ValueAbs Bool =
    scalar_value_abstraction (fn (v,b) -> zeroScalarValue? v = return b)

  (* No aliasing between a Boolean value and the lvalue it came from *)
  theorem bool_valueabs_expr_and_lvalue_abses is
    fa (lv, expr_vabs, lv_vabs)
      expr_vabs = bool_valueabs && lv_vabs = bool_valueabs =>
      lvalue_expr_and_lvalue_abses? (lv, bool_valueabs, expr_vabs, lv_vabs)

  theorem true_correct is [a]
    fa (envp,perms_in:PermSet a,perms_out,m)
      m = ICONST_m "1" &&
      perms_out = (perms_in, [ValPerm ([], bool_valueabs)]) =>
      abstracts_expression envp perms_in perms_out (fn _ -> true) m

  theorem false_correct is [a]
    fa (envp,perms_in:PermSet a,perms_out,m)
      m = ICONST_m "0" &&
      perms_out = (perms_in, [ValPerm ([], bool_valueabs)]) =>
      abstracts_expression envp perms_in perms_out (fn _ -> false) m


  (***
   *** Variable Expressions
   ***)

  (* The following theorems all prove that a variable expression is correct. The
  general form is var_i_j_correct, which proves that the jth variable in a
  context with i variables (represented as an i-tuple) is correct. *)

  theorem var_1_1_correct is [a]
    fa (envp,perms_in:PermSet a,eperms_out,perms_out,vperms,m,x)
      m = VAR_m x &&
      view_perms_extract_to? (perms_in, identity_biview,
                              LV_ident x, vperms, perms_out) &&
      eperms_out = (perms_out, vperms) =>
      abstracts_expression envp perms_in eperms_out (fn a -> a) m

  theorem var_2_1_correct is [a,b]
    fa (envp,perms_in:PermSet (a*b),eperms_out,perms_out,vperms,m,x)
      m = VAR_m x &&
      view_perms_extract_to? (perms_in, proj1_biview,
                              LV_ident x, vperms, perms_out) &&
      eperms_out = (perms_out, vperms) =>
      abstracts_expression envp perms_in eperms_out (fn (a,b) -> a) m

  theorem var_2_2_correct is [a,b]
    fa (envp,perms_in:PermSet (a*b),eperms_out,perms_out,vperms,m,x)
      m = VAR_m x &&
      view_perms_extract_to? (perms_in, proj2_biview,
                              LV_ident x, vperms, perms_out) &&
      eperms_out = (perms_out, vperms) =>
      abstracts_expression envp perms_in eperms_out (fn (a,b) -> b) m


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
    fa (envp,perms_in,perms_out,eperms_out,
        lens:Lens (a,b),e:a->c,
        expr,stmt,perm_set_out,val_perms_out)
      abstracts_expression envp perms_in eperms_out e expr &&
      perm_set_unmaps_to (eperms_out.1, biview_of_lens_pair (lens, proj1_lens),
                          perm_set_out) &&
      is_val_perms_add_view (eperms_out.2, biview_of_lens (proj2_lens),
                             val_perms_out) &&
      perms_out = (perm_set_out, Some val_perms_out) &&
      stmt = RETURN_m expr =>
      abstracts_ret_statement
        envp perms_in perms_out
        (fn x -> (lens.lens_get x, e x))
        stmt

  (* Special case of return where all variables are forgotten. This is
  represented by using a unit type in the first projection of the tuple. Note
  that the precondition just adds in the unit lens, which in turn causes the
  general return_correct theorem to be used. *)
  theorem return_correct_unit_left is [a,b]
    fa (envp,perms_in,perms_out,e:a->b,stmt)
      abstracts_ret_statement
        envp perms_in perms_out
        (fn x -> (unit_lens.lens_get x, e x))
        stmt =>
      abstracts_ret_statement
        envp perms_in perms_out
        (fn x -> ((), e x))
        stmt

  (* The core correctness theorem for void returns, similar to
  return_correct. As with that theorem, the lens is for "forgetting"
  permissions, which is handled by the unmapping. *)
  theorem return_void_correct is [a,b]
    fa (envp,perms_in,lens:Lens (a,b),stmt,perms_out,perms_out')
      perm_set_unmaps_to (perms_in, biview_of_lens lens, perms_out') &&
      perms_out = (perms_out', None) &&
      stmt = RETURN_VOID_m =>
      abstracts_ret_statement
        envp perms_in perms_out
        (fn x -> lens.lens_get x)
        stmt


  (***
   *** Functions
   ***)

  (* FIXME: need permissions to deallocate the current stack from at the end of body *)
  (* FIXME: also need a value_abs_has_type precondition *)
  theorem FUNCTION_correct is [a,b]
    fa (envp,perms_in,perms_in_sub,perms_out,perms_out_sub,perms_out_sub',
        f:a->b,m,prototype,body)
      m = FUNCTION_m (prototype.1, prototype.2, prototype.3, body) &&
      FunStIPerm auto_allocation_perm in? perms_out.1.1 &&
      is_perm_set_of_arg_perms (perms_out.1, prototype.3, perms_out_sub') &&
      is_perm_set_of_arg_perms (perms_in, prototype.3, perms_in_sub) &&
      perm_set_weaker? (perms_out_sub.1, perms_out_sub') &&
      perms_out.2 = perms_out_sub.2 &&
      abstracts_ret_statement
        envp
        perms_in_sub
        perms_out_sub
        f
        body =>
      abstracts_c_function_decl envp perms_in perms_out f prototype m

end-spec
